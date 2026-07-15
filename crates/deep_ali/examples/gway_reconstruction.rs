//! gway_reconstruction.rs — CLEAN two-process measurement of the coordinator
//! RECONSTRUCTION (verify + splice) RSS for the G-way stranded ECDSA-verify
//! proof.
//!
//! ## Why two processes
//! In a single process that both proves and verifies, peak RSS is
//! contaminated by allocator RETENTION: the prover LDE/Merkle allocations
//! (GBs) are freed back to the allocator but not returned to the OS, so the
//! resident set stays high during the verify phase.  The true coordinator
//! footprint is only the deserialized proof bundle + the FRI-verify working
//! set.  To measure it cleanly we split into two phases:
//!
//!   PHASE=prove  — prove all G strands (memory-light rebuild mode), assemble
//!                  StrandedProofG, and CanonicalSerialize it to a file.
//!                  Reports the serialized (transmitted) proof size.
//!   PHASE=verify — a FRESH process: recompute the (deterministic) cut/layout/
//!                  pubin, deserialize the proof, run `verify_stranded_g`, and
//!                  report accept/reject.  Peak RSS (measured externally via
//!                  `/usr/bin/time -l`) is the clean reconstruction footprint.
//!
//! The same fixed sig-case + (k, g) are used in both phases, so cut/layout/
//! pubin are recomputed identically without transmitting them.
//!
//! Run:
//!   F=/tmp/gway_g64.proof
//!   STRAND_G=64 PHASE=prove  BENCH_PROOF_FILE=$F \
//!     cargo run --release --features "parallel,sha3-256" -p deep_ali \
//!     --example gway_reconstruction
//!   STRAND_G=64 PHASE=verify BENCH_PROOF_FILE=$F /usr/bin/time -l \
//!     cargo run --release --features "parallel,sha3-256" -p deep_ali \
//!     --example gway_reconstruction

use std::io::{Read, Seek, SeekFrom, Write};
use std::time::Instant;

use ark_ff::Zero;
use ark_goldilocks::Goldilocks as F;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use sha2::{Digest as _, Sha256};

use p256::ecdsa::{signature::Signer, Signature as P256Signature, SigningKey, VerifyingKey};
use p256::elliptic_curve::sec1::ToEncodedPoint;

use deep_ali::{
    binding_cells_commit::{verify_ood_consistency, BindingCellsCommit},
    ecdsa_verify_stranded_gway::{
        compute_gway_cut, prove_one_strand, strand_domain, verify_one_strand,
    },
    fri::DeepFriParams,
    p256_ecdsa::{
        reduce_digest_mod_n, verify as ecdsa_verify_native, PublicKey as EcdsaPublicKey,
        Signature as EcdsaSignature,
    },
    p256_ecdsa_verify_multirow_air::{
        build_ecdsa_verify_multirow_layout, ecdsa_verify_multirow_constraints,
        fill_ecdsa_verify_multirow, EcdsaVerifyMultirowLayout, EcdsaVerifyPublicInputs,
    },
    p256_field::FieldElement,
    p256_group::GENERATOR as P256_GENERATOR,
    p256_scalar::ScalarElement,
    sub_air_with_trace::SubAirProofWithTrace,
};

fn rss_mib() -> f64 {
    let pid = std::process::id();
    let out = std::process::Command::new("ps")
        .args(["-o", "rss=", "-p", &pid.to_string()])
        .output();
    match out {
        Ok(o) => String::from_utf8_lossy(&o.stdout).trim().parse::<f64>().unwrap_or(0.0) / 1024.0,
        Err(_) => 0.0,
    }
}

fn scalar_to_msb_bits_256(s: &ScalarElement) -> Vec<bool> {
    let bytes = s.to_be_bytes();
    let mut bits = Vec::with_capacity(256);
    for byte in bytes.iter() {
        for shift in (0..8).rev() {
            bits.push((byte >> shift) & 1 == 1);
        }
    }
    bits
}

fn mk_params(n0: usize, r: usize, use_stir: bool, ph: [u8; 32]) -> DeepFriParams {
    DeepFriParams {
        schedule: (0..n0.trailing_zeros() as usize).map(|_| 2).collect(),
        r,
        seed_z: 0xDEEFu64,
        coeff_commit_final: true,
        d_final: 1,
        stir: use_stir,
        s0: r,
        public_inputs_hash: Some(ph),
    }
}

struct SigCase {
    native_ok: bool,
    u1_bits: Vec<bool>,
    u2_bits: Vec<bool>,
    qx: FieldElement,
    qy: FieldElement,
    r_fe: FieldElement,
    pi_hash: [u8; 32],
    pub_inputs: EcdsaVerifyPublicInputs,
}

/// Deterministic sig case (identical in both phases → identical cut/layout).
fn derive_case(key_bytes: &[u8; 32], msg: &[u8], k: usize) -> SigCase {
    let sk = SigningKey::from_slice(key_bytes).expect("valid P256 key");
    let sig: P256Signature = sk.sign(msg);
    let vk = VerifyingKey::from(&sk);
    let ep = vk.to_encoded_point(false);
    let epb = ep.as_bytes();
    let mut qx = [0u8; 32];
    qx.copy_from_slice(&epb[1..33]);
    let mut qy = [0u8; 32];
    qy.copy_from_slice(&epb[33..65]);
    let sb = sig.to_bytes();
    let mut rbytes = [0u8; 32];
    rbytes.copy_from_slice(&sb[0..32]);
    let mut sbytes = [0u8; 32];
    sbytes.copy_from_slice(&sb[32..64]);
    let digest: [u8; 32] = Sha256::digest(msg).into();

    let pk = EcdsaPublicKey::from_be_bytes(&qx, &qy).expect("pk parse");
    let signature = EcdsaSignature::from_be_bytes(&rbytes, &sbytes).expect("sig parse");
    let native_ok = ecdsa_verify_native(&digest, &pk, &signature);

    let e = reduce_digest_mod_n(&digest);
    let w = signature.s.invert();
    let u_1 = e.mul(&w);
    let u_2 = signature.r.mul(&w);
    let u1_bits = scalar_to_msb_bits_256(&u_1);
    let u2_bits = scalar_to_msb_bits_256(&u_2);
    assert_eq!(u1_bits.len(), k);

    let r_fe = FieldElement::from_be_bytes(&rbytes);
    let g = *P256_GENERATOR;
    let pub_inputs =
        EcdsaVerifyPublicInputs::new(&u1_bits, &u2_bits, &g.x, &g.y, &pk.point.x, &pk.point.y, &r_fe);

    let mut hasher = Sha256::new();
    hasher.update(rbytes);
    hasher.update(sbytes);
    hasher.update(qx);
    hasher.update(qy);
    hasher.update(digest);
    let pi_hash: [u8; 32] = hasher.finalize().into();

    SigCase { native_ok, u1_bits, u2_bits, qx: pk.point.x, qy: pk.point.y, r_fe, pi_hash, pub_inputs }
}

fn build_full(
    case: &SigCase,
    layout: &EcdsaVerifyMultirowLayout,
    n_trace: usize,
    total: usize,
) -> Vec<Vec<F>> {
    let g = *P256_GENERATOR;
    let z_one = {
        let mut t = FieldElement::zero();
        t.limbs[0] = 1;
        t
    };
    let id_x = FieldElement::zero();
    let id_y = {
        let mut t = FieldElement::zero();
        t.limbs[0] = 1;
        t
    };
    let id_z = FieldElement::zero();
    let mut trace = vec![vec![F::zero(); n_trace]; total];
    fill_ecdsa_verify_multirow(
        &mut trace, layout, n_trace,
        (&id_x, &id_y, &id_z), (&g.x, &g.y, &z_one), &case.u1_bits,
        (&id_x, &id_y, &id_z), (&case.qx, &case.qy, &z_one), &case.u2_bits,
        &case.r_fe,
    );
    trace
}

fn extract(full: &[Vec<F>], cols: &[usize]) -> Vec<Vec<F>> {
    cols.iter().map(|&c| full[c].clone()).collect()
}

fn main() {
    let level = deep_ali::stark_level::NIST_LEVEL;
    let ext_deg = deep_ali::permutation_argument::EXT_DEGREE;
    let use_stir = matches!(std::env::var("BENCH_LDT").as_deref(), Ok("stir") | Ok("STIR"));
    let g = std::env::var("STRAND_G").ok().and_then(|s| s.parse().ok()).unwrap_or(64usize);
    let blowup = std::env::var("BENCH_BLOWUP").ok().and_then(|s| s.parse().ok()).unwrap_or(4usize);
    let r = deep_ali::stark_level::num_queries_for_blowup(blowup);
    let k = std::env::var("KSTEPS").ok().and_then(|s| s.parse().ok()).unwrap_or(256usize);
    let n_trace = (k + 1).next_power_of_two();
    let phase = std::env::var("PHASE").unwrap_or_else(|_| "prove".into());
    let proof_file = std::env::var("BENCH_PROOF_FILE")
        .unwrap_or_else(|_| format!("/tmp/gway_g{g}_k{k}.proof"));

    // Deterministic — identical in prove & verify phases.
    let case = derive_case(&[0x42u8; 32], b"STARK-DNS low-mem G-way ECDSA verify: msg A", k);
    assert!(case.native_ok, "signature must natively verify");
    let (layout, total) = build_ecdsa_verify_multirow_layout(0, k);
    let mono = ecdsa_verify_multirow_constraints(&layout);
    let cut = compute_gway_cut(&layout, k, g);
    let params = |n0: usize, ph: [u8; 32]| mk_params(n0, r, use_stir, ph);

    eprintln!(
        "=== gway_reconstruction PHASE={phase} G={g} K={k} n_trace={n_trace} \
         NIST L{level} Fp{ext_deg} r={r} blowup={blowup} full_width={total} constraints={mono} \
         proof_file={proof_file} ===",
    );

    if phase == "prove" {
        // Memory-light rebuild-mode prove of every strand → StrandedProofG.
        eprintln!("    [rss] prove start: cur={:.0} MiB", rss_mib());
        let t = Instant::now();
        let mut proofs: Vec<Option<deep_ali::sub_air_with_trace::SubAirProofWithTrace>> =
            (0..g).map(|_| None).collect();
        let mut seam_commits: Vec<
            Vec<(usize, Vec<deep_ali::binding_cells_commit::BindingCellsCommit>)>,
        > = vec![vec![]; g];

        for s in 0..g {
            let full = build_full(&case, &layout, n_trace, total);
            let strand = extract(&full, &cut.strand_cols[s]);
            drop(full);
            let sep = strand_domain(s);
            let (p, c) = prove_one_strand(
                &strand, &cut, s, &layout, &case.pub_inputs, n_trace, blowup, case.pi_hash, &sep,
                params,
            );
            drop(strand);
            proofs[s] = Some(p);
            seam_commits[s] = c;
            if s % 8 == 0 || s + 1 == g {
                eprintln!("    [rss] strand {s}/{g} proved: cur={:.0} MiB", rss_mib());
            }
        }
        let prove_ms = t.elapsed().as_secs_f64() * 1000.0;
        let proofs: Vec<SubAirProofWithTrace> = proofs.into_iter().map(|p| p.unwrap()).collect();
        let fri_total: usize = proofs.iter().map(|p| p.fri_proof_bytes.len()).sum();

        // ── INDEXED STREAMING FORMAT (one strand + one seam-PAIR resident) ──
        //   [u64 g]
        //   for s in 0..g:            [u64 len][SubAirProofWithTrace blob]
        //   [u64 n_seam_entries N]
        //   index:  for each entry:   [u64 strand][u64 gid][u64 blob_len]
        //   blobs:  for each entry:   [Vec<BindingCellsCommit> blob]  (index order)
        // Per-strand seam commits are split into individually-addressable
        // (strand, gid) entries so the verifier can SEEK+load only the two
        // commits a given OOD check compares — never the whole 4.7 GB.
        let f = std::fs::File::create(&proof_file).expect("create proof file");
        let mut w = std::io::BufWriter::with_capacity(1 << 20, f);
        w.write_all(&(g as u64).to_le_bytes()).unwrap();

        let mut strand_bytes_total = 0usize;
        for p in &proofs {
            let mut sb: Vec<u8> = Vec::new();
            p.serialize_compressed(&mut sb).expect("serialize strand proof");
            w.write_all(&(sb.len() as u64).to_le_bytes()).unwrap();
            w.write_all(&sb).unwrap();
            strand_bytes_total += sb.len();
        }
        drop(proofs);

        // Seam entries: (strand, gid, serialized Vec<BCC>).  Two-pass so the
        // index (all lens) precedes the blob region without holding every
        // blob resident: pass 1 records lens, pass 2 re-serializes to write.
        let mut index: Vec<(usize, usize, usize)> = Vec::new(); // (strand, gid, len)
        for (s, entries) in seam_commits.iter().enumerate() {
            for (gid, bccs) in entries.iter() {
                let mut blob: Vec<u8> = Vec::new();
                bccs.serialize_compressed(&mut blob).expect("serialize seam entry");
                index.push((s, *gid, blob.len()));
            }
        }
        w.write_all(&(index.len() as u64).to_le_bytes()).unwrap();
        for (s, gid, len) in &index {
            w.write_all(&(*s as u64).to_le_bytes()).unwrap();
            w.write_all(&(*gid as u64).to_le_bytes()).unwrap();
            w.write_all(&(*len as u64).to_le_bytes()).unwrap();
        }
        let mut seam_bytes_total = 0usize;
        for (s, entries) in seam_commits.iter().enumerate() {
            for (gid, bccs) in entries.iter() {
                let _ = (s, gid);
                let mut blob: Vec<u8> = Vec::new();
                bccs.serialize_compressed(&mut blob).expect("serialize seam entry");
                w.write_all(&blob).unwrap();
                seam_bytes_total += blob.len();
            }
        }
        w.flush().unwrap();
        let total_mib =
            (strand_bytes_total + seam_bytes_total) as f64 / (1024.0 * 1024.0);

        println!(
            "PROVE G={g} K={k} strands={g} prove_ms={prove_ms:.0} fri_total_kib={} \
             seam_entries={} seam_mib={:.2} strands_mib={:.2} total_mib={:.2} proof_file={proof_file}",
            fri_total / 1024,
            index.len(),
            seam_bytes_total as f64 / (1024.0 * 1024.0),
            strand_bytes_total as f64 / (1024.0 * 1024.0),
            total_mib,
        );
        eprintln!(
            "    indexed proof written: {} strands {:.1} MiB + {} seam entries {:.1} MiB",
            g,
            strand_bytes_total as f64 / (1024.0 * 1024.0),
            index.len(),
            seam_bytes_total as f64 / (1024.0 * 1024.0),
        );
    } else {
        // ── FULLY-STREAMING RECONSTRUCTION (fresh process) ──
        // Two passes over the file, each holding O(1) heavy objects:
        //   (1) strand pass  — stream each SubAirProofWithTrace, verify, DROP.
        //   (2) seam pass    — for each OOD check, SEEK+load only the two
        //                      (strand, gid) commit entries it compares, DROP.
        // Peak RSS ≈ max(one strand's openings, one seam PAIR), never the
        // aggregate 5 GB proof.
        eprintln!("    [rss] verify start: cur={:.0} MiB", rss_mib());
        let file = std::fs::File::open(&proof_file).expect("open proof file (run PHASE=prove first)");
        let mut rdr = std::io::BufReader::with_capacity(1 << 20, file);

        let read_u64 = |rdr: &mut std::io::BufReader<std::fs::File>| -> u64 {
            let mut b = [0u8; 8];
            rdr.read_exact(&mut b).expect("read length prefix");
            u64::from_le_bytes(b)
        };
        // Sequential frame read (strand pass): buffer bounds the frame so the
        // file cursor stays aligned regardless of codec byte count.
        fn read_frame<T: CanonicalDeserialize>(
            rdr: &mut std::io::BufReader<std::fs::File>,
            len: u64,
        ) -> T {
            let mut buf = vec![0u8; len as usize];
            rdr.read_exact(&mut buf).expect("read frame body");
            T::deserialize_compressed(&buf[..]).expect("deserialize frame")
        }
        // Random-access entry load (seam pass): seek to `off`, read `len`.
        fn load_entry<T: CanonicalDeserialize>(
            rdr: &mut std::io::BufReader<std::fs::File>,
            off: u64,
            len: u64,
        ) -> T {
            rdr.seek(SeekFrom::Start(off)).expect("seek seam entry");
            let mut buf = vec![0u8; len as usize];
            rdr.read_exact(&mut buf).expect("read seam entry");
            T::deserialize_compressed(&buf[..]).expect("deserialize seam entry")
        }

        let t_de = Instant::now();
        let g_file = read_u64(&mut rdr) as usize;
        assert_eq!(g_file, g, "file G ({g_file}) != env STRAND_G ({g})");

        // ── (1) strand pass ──
        let t_strands = Instant::now();
        let mut fri_total = 0usize;
        let mut peak = 0.0f64;
        for s in 0..g {
            let len = read_u64(&mut rdr);
            let sp: SubAirProofWithTrace = read_frame(&mut rdr, len);
            fri_total += sp.fri_proof_bytes.len();
            let sep = strand_domain(s);
            verify_one_strand(
                &sp, &cut, s, &layout, &case.pub_inputs, n_trace, blowup, case.pi_hash, &sep,
                &params,
            )
            .unwrap_or_else(|e| panic!("strand {s} must verify: {e}"));
            peak = peak.max(rss_mib());
            drop(sp);
            if s % 16 == 0 || s + 1 == g {
                eprintln!("    [rss] strand {s}/{g} verified+dropped: cur={:.0} MiB", rss_mib());
            }
        }
        let strands_ms = t_strands.elapsed().as_secs_f64() * 1000.0;
        eprintln!("    [rss] strand pass done: peak-so-far {peak:.0} MiB");

        // ── seam index ──  (strand, gid) -> (file offset, len)
        let n_entries = read_u64(&mut rdr) as usize;
        let mut index: Vec<(usize, usize, u64)> = Vec::with_capacity(n_entries);
        for _ in 0..n_entries {
            let s = read_u64(&mut rdr) as usize;
            let gid = read_u64(&mut rdr) as usize;
            let len = read_u64(&mut rdr);
            index.push((s, gid, len));
        }
        let blob_start = rdr.stream_position().expect("stream_position");
        let mut off_map: std::collections::HashMap<(usize, usize), (u64, u64)> =
            std::collections::HashMap::with_capacity(n_entries);
        let mut off = blob_start;
        for (s, gid, len) in &index {
            off_map.insert((*s, *gid), (off, *len));
            off += *len;
        }

        // ── (2) seam pass — load only the compared PAIR per OOD check ──
        let t_seams = Instant::now();
        let mut ood_checks = 0usize;
        for (gid, sg) in cut.seams.iter().enumerate() {
            let refs = sg.holders[0];
            let (roff, rlen) = off_map[&(refs, gid)];
            let ref_commits: Vec<BindingCellsCommit> = load_entry(&mut rdr, roff, rlen);
            for &h in &sg.holders[1..] {
                let (hoff, hlen) = off_map[&(h, gid)];
                let hc: Vec<BindingCellsCommit> = load_entry(&mut rdr, hoff, hlen);
                assert!(
                    ref_commits.len() == hc.len() && hc.len() == sg.cols.len(),
                    "seam group {gid}: commit-count mismatch"
                );
                for (j, (ca, cb)) in ref_commits.iter().zip(hc.iter()).enumerate() {
                    verify_ood_consistency(ca, cb, case.pi_hash, params).unwrap_or_else(|e| {
                        panic!("seam group {gid} col {} (strands {refs}~{h}): {e}", sg.cols[j])
                    });
                    ood_checks += 1;
                }
                peak = peak.max(rss_mib());
                drop(hc);
            }
            drop(ref_commits);
            if gid % 16 == 0 || gid + 1 == cut.seams.len() {
                eprintln!(
                    "    [rss] seam group {gid}/{} checked: cur={:.0} MiB",
                    cut.seams.len(),
                    rss_mib()
                );
            }
        }
        let seams_ms = t_seams.elapsed().as_secs_f64() * 1000.0;
        let total_ms = t_de.elapsed().as_secs_f64() * 1000.0;

        eprintln!(
            "    [rss] ALL verified ({ood_checks} OOD checks): peak-sampled(cur) {peak:.0} MiB, \
             end cur={:.0} MiB",
            rss_mib()
        );
        println!(
            "VERIFY-STREAM G={g} K={k} strands_ms={strands_ms:.0} seams_ms={seams_ms:.0} \
             total_ms={total_ms:.0} fri_total_kib={} seam_entries={n_entries} ood_checks={ood_checks} \
             peak_cur_mib={peak:.0} ok=true \
             (peak RSS via /usr/bin/time -l is the clean streaming reconstruction footprint)",
            fri_total / 1024,
        );
    }
}

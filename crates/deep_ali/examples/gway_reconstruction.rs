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
        fill_ecdsa_verify_multirow_strand, EcdsaVerifyMultirowLayout, EcdsaVerifyPublicInputs,
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

fn fill_strand_direct(
    case: &SigCase,
    layout: &EcdsaVerifyMultirowLayout,
    cols: &[usize],
    n_trace: usize,
) -> Vec<Vec<F>> {
    // DIRECT-FILL: materialise ONLY this strand's columns — the full
    // ~196k-col trace is never allocated, so per-sliver peak RSS is the
    // strand trace + its LDE (the IoT-class working set), not the monolith.
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
    let mut strand: Vec<Vec<F>> = vec![vec![F::zero(); n_trace]; cols.len()];
    fill_ecdsa_verify_multirow_strand(
        cols, &mut strand, layout, n_trace,
        (&id_x, &id_y, &id_z), (&g.x, &g.y, &z_one), &case.u1_bits,
        (&id_x, &id_y, &id_z), (&case.qx, &case.qy, &z_one), &case.u2_bits,
        &case.r_fe,
    );
    strand
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
        // ── STREAMING-WRITE PROVE (nothing accumulated) ──
        // Prove each sliver, WRITE its proof + seam entries to disk, DROP, so
        // only one sliver's working set is ever live.  Interleaved format:
        //   [u64 g]
        //   repeat g: [u64 sp_len][SubAirProofWithTrace]
        //             [u64 n_entries_s]
        //             repeat: [u64 gid][u64 blob_len][Vec<BindingCellsCommit>]
        //
        // SLIVER=<s> proves ONLY sliver s and APPENDS its record (writing the
        // [g] header iff s==0).  A shell loop over SLIVER=0..g then runs one
        // FRESH process per sliver — the fleet-realistic mode where each IoT
        // device carries one sliver and the allocator resets between slivers,
        // so peak RSS is a single sliver's ~430 MiB, not the in-process
        // retention of an all-in-one run.
        let single: Option<usize> = std::env::var("SLIVER").ok().and_then(|s| s.parse().ok());
        eprintln!("    [rss] prove start: cur={:.0} MiB", rss_mib());
        let t = Instant::now();

        // Record-writer for one sliver; returns (fri, strand_bytes, seam_bytes, n_entries).
        let write_sliver = |w: &mut std::io::BufWriter<std::fs::File>, s: usize| {
            let strand = fill_strand_direct(&case, &layout, &cut.strand_cols[s], n_trace);
            let sep = strand_domain(s);
            let (p, c) = prove_one_strand(
                &strand, &cut, s, &layout, &case.pub_inputs, n_trace, blowup, case.pi_hash, &sep,
                params,
            );
            drop(strand);
            let fri = p.fri_proof_bytes.len();
            let mut sb: Vec<u8> = Vec::new();
            p.serialize_compressed(&mut sb).expect("serialize strand proof");
            w.write_all(&(sb.len() as u64).to_le_bytes()).unwrap();
            w.write_all(&sb).unwrap();
            let strand_bytes = sb.len();
            drop(p);
            drop(sb);
            w.write_all(&(c.len() as u64).to_le_bytes()).unwrap();
            let (mut seam_bytes, mut n) = (0usize, 0usize);
            for (gid, bccs) in &c {
                let mut blob: Vec<u8> = Vec::new();
                bccs.serialize_compressed(&mut blob).expect("serialize seam entry");
                w.write_all(&(*gid as u64).to_le_bytes()).unwrap();
                w.write_all(&(blob.len() as u64).to_le_bytes()).unwrap();
                w.write_all(&blob).unwrap();
                seam_bytes += blob.len();
                n += 1;
            }
            drop(c);
            (fri, strand_bytes, seam_bytes, n)
        };

        let mut prove_peak = 0.0f64;
        let (mut fri_total, mut strand_bytes_total, mut seam_bytes_total, mut seam_entries) =
            (0usize, 0usize, 0usize, 0usize);

        if let Some(s) = single {
            // One sliver, one process; append (create+header iff s==0).
            let f = if s == 0 {
                let f = std::fs::File::create(&proof_file).expect("create proof file");
                let mut w = std::io::BufWriter::with_capacity(1 << 20, f);
                w.write_all(&(g as u64).to_le_bytes()).unwrap();
                w.flush().unwrap();
                std::fs::OpenOptions::new().append(true).open(&proof_file).expect("reopen append")
            } else {
                std::fs::OpenOptions::new().append(true).open(&proof_file).expect("open append")
            };
            let mut w = std::io::BufWriter::with_capacity(1 << 20, f);
            let (fri, strand_b, seam_b, n) = write_sliver(&mut w, s);
            w.flush().unwrap();
            fri_total = fri;
            strand_bytes_total = strand_b;
            seam_bytes_total = seam_b;
            seam_entries = n;
            prove_peak = prove_peak.max(rss_mib());
        } else {
            // All slivers, one process (retention accumulates across slivers).
            let f = std::fs::File::create(&proof_file).expect("create proof file");
            let mut w = std::io::BufWriter::with_capacity(1 << 20, f);
            w.write_all(&(g as u64).to_le_bytes()).unwrap();
            for s in 0..g {
                let (fri, strand_b, seam_b, n) = write_sliver(&mut w, s);
                fri_total += fri;
                strand_bytes_total += strand_b;
                seam_bytes_total += seam_b;
                seam_entries += n;
                prove_peak = prove_peak.max(rss_mib());
                if s % 16 == 0 || s + 1 == g {
                    eprintln!(
                        "    [rss] sliver {s}/{g} (w={}) proved+written+dropped: cur={:.0} MiB",
                        cut.width(s),
                        rss_mib()
                    );
                }
            }
            w.flush().unwrap();
        }
        let prove_ms = t.elapsed().as_secs_f64() * 1000.0;
        let total_mib = (strand_bytes_total + seam_bytes_total) as f64 / (1024.0 * 1024.0);
        eprintln!("    [rss] prove pass done: per-sliver peak {prove_peak:.0} MiB");

        let tag = single.map(|s| format!("SLIVER={s} ")).unwrap_or_default();
        println!(
            "PROVE {tag}G={g} K={k} prove_ms={prove_ms:.0} per_sliver_peak_mib={prove_peak:.0} \
             fri_total_kib={} seam_entries={seam_entries} seam_mib={:.2} strands_mib={:.2} \
             total_mib={:.2} proof_file={proof_file}",
            fri_total / 1024,
            seam_bytes_total as f64 / (1024.0 * 1024.0),
            strand_bytes_total as f64 / (1024.0 * 1024.0),
            total_mib,
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

        // ── (1) strand pass — verify each strand AND index its seam blobs ──
        // The interleaved file lets one pass do both: read+verify the strand
        // proof, then for each of its seam entries record (strand, gid) ->
        // (offset, len) and SEEK PAST the blob (never load it here).
        let t_strands = Instant::now();
        let mut fri_total = 0usize;
        let mut peak = 0.0f64;
        let mut n_entries = 0usize;
        let mut off_map: std::collections::HashMap<(usize, usize), (u64, u64)> =
            std::collections::HashMap::new();
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

            let n_s = read_u64(&mut rdr) as usize;
            for _ in 0..n_s {
                let gid = read_u64(&mut rdr) as usize;
                let blob_len = read_u64(&mut rdr);
                let off = rdr.stream_position().expect("stream_position");
                off_map.insert((s, gid), (off, blob_len));
                rdr.seek(SeekFrom::Current(blob_len as i64)).expect("skip seam blob");
                n_entries += 1;
            }
            if s % 16 == 0 || s + 1 == g {
                eprintln!("    [rss] strand {s}/{g} verified+dropped: cur={:.0} MiB", rss_mib());
            }
        }
        let strands_ms = t_strands.elapsed().as_secs_f64() * 1000.0;
        eprintln!("    [rss] strand pass done: peak-so-far {peak:.0} MiB");

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

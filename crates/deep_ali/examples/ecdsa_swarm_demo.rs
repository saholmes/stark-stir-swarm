//! ECDSA SWARM DEMO — proves a REAL P256 ECDSA signature with the committed
//! G-way "stranded" STARK, using INDEPENDENT OS PROCESSES as swarm elements.
//!
//! One strand per process, each ≤1 GB RSS, run in parallel by the
//! `scripts/swarm-ecdsa-demo.sh` orchestrator, then spliced + verified.
//!
//! This example ONLY orchestrates already-committed, already-verified
//! machinery (`compute_gway_cut`, `fill_ecdsa_verify_multirow_strand`,
//! `prove_one_strand`, `verify_stranded_g`, the F2b OOD seam commits and
//! their (de)serializers).  It re-derives NO soundness — the stranded
//! prover's soundness lives in `ecdsa_verify_stranded_gway.rs` + its tests.
//!
//! Roles (env SWARM_ROLE):
//!   coordinator — real keygen/sign, print pub inputs (h(m)=e, PK, r, s),
//!                 print the G-strand cut summary, write $SWARM_DIR/job.json.
//!   worker      — read job.json, re-derive the SAME case + cut, DIRECT-FILL
//!                 only strand STRAND_ID's columns (never the ~196k trace),
//!                 prove it, serialize sub-proof + seam commits to
//!                 $SWARM_DIR/strand_<id>.bin.
//!   verify      — read strand_0..G-1.bin, reconstruct a StrandedProofG,
//!                 verify_stranded_g (PASS/FAIL), then a tamper NEGATIVE
//!                 check (corrupt one strand's proof bytes → must REJECT).
//!
//! Env: SWARM_DIR (work dir), SWARM_ROLE, STRAND_ID, G, BENCH_BLOWUP, K,
//!      SWARM_KEY (hex, optional), SWARM_MSG (optional).

use std::io::{Read, Write};
use std::time::Instant;

use ark_ff::Zero;
use ark_goldilocks::Goldilocks as F;
use sha2::{Digest as _, Sha256};

use p256::ecdsa::{signature::Signer, Signature as P256Signature, SigningKey, VerifyingKey};

use deep_ali::{
    binding_cells_commit::BindingCellsCommit,
    ecdsa_verify_stranded_gway::{
        compute_gway_cut, prove_one_strand, strand_domain, verify_stranded_g, StrandedProofG,
    },
    fri::DeepFriParams,
    p256_ecdsa::{
        reduce_digest_mod_n, verify as ecdsa_verify_native, PublicKey as EcdsaPublicKey,
        Signature as EcdsaSignature,
    },
    p256_ecdsa_verify_multirow_air::{
        build_ecdsa_verify_multirow_layout, fill_ecdsa_verify_multirow_strand,
        EcdsaVerifyPublicInputs,
    },
    p256_field::FieldElement,
    p256_group::GENERATOR as P256_GENERATOR,
    p256_scalar::ScalarElement,
    sub_air_with_trace::{deserialize_proof, serialize_proof, SubAirProofWithTrace},
};

// ─── FRI params (identical to the committed gway bench) ───────────────
fn mk_params(n0: usize, r: usize, ph: [u8; 32]) -> DeepFriParams {
    DeepFriParams {
        schedule: (0..n0.trailing_zeros() as usize).map(|_| 2).collect(),
        r,
        seed_z: 0xDEEFu64,
        coeff_commit_final: true,
        d_final: 1,
        stir: false,
        s0: r,
        public_inputs_hash: Some(ph),
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

/// Real keygen/sign + all derived public inputs.  Deterministic in
/// (`key_bytes`, `msg`, `k`) so every process reconstructs the SAME case.
struct SigCase {
    native_ok: bool,
    // pub inputs / witness handles
    u1_bits: Vec<bool>,
    u2_bits: Vec<bool>,
    qx: FieldElement,
    qy: FieldElement,
    r_fe: FieldElement,
    pi_hash: [u8; 32],
    pub_inputs: EcdsaVerifyPublicInputs,
    // printable scalars
    qx_bytes: [u8; 32],
    qy_bytes: [u8; 32],
    e_bytes: [u8; 32],
    r_bytes: [u8; 32],
    s_bytes: [u8; 32],
    digest: [u8; 32],
}

fn derive_case(key_bytes: &[u8; 32], msg: &[u8], k: usize) -> SigCase {
    // ── REAL P256 keygen + ECDSA signature ──
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

    // ── native verify (ground truth) ──
    let pk = EcdsaPublicKey::from_be_bytes(&qx, &qy).expect("pk parse");
    let signature = EcdsaSignature::from_be_bytes(&rbytes, &sbytes).expect("sig parse");
    let native_ok = ecdsa_verify_native(&digest, &pk, &signature);

    // ── ECDSA-verify scalars → STARK public inputs ──
    let e = reduce_digest_mod_n(&digest); // the ECDSA message scalar
    let w = signature.s.invert();
    let u_1 = e.mul(&w);
    let u_2 = signature.r.mul(&w);
    let u1_bits = scalar_to_msb_bits_256(&u_1);
    let u2_bits = scalar_to_msb_bits_256(&u_2);
    assert_eq!(u1_bits.len(), k);

    let r_fe = FieldElement::from_be_bytes(&rbytes);
    let g = *P256_GENERATOR;
    let pub_inputs = EcdsaVerifyPublicInputs::new(
        &u1_bits, &u2_bits, &g.x, &g.y, &pk.point.x, &pk.point.y, &r_fe,
    );

    // pi_hash binds (r,s,Qx,Qy,h(m)) — the public statement.
    let mut hasher = Sha256::new();
    hasher.update(rbytes);
    hasher.update(sbytes);
    hasher.update(qx);
    hasher.update(qy);
    hasher.update(digest);
    let pi_hash: [u8; 32] = hasher.finalize().into();

    SigCase {
        native_ok,
        u1_bits,
        u2_bits,
        qx: pk.point.x,
        qy: pk.point.y,
        r_fe,
        pi_hash,
        pub_inputs,
        qx_bytes: qx,
        qy_bytes: qy,
        e_bytes: e.to_be_bytes(),
        r_bytes: rbytes,
        s_bytes: sbytes,
        digest,
    }
}

fn identity_and_z_one() -> (FieldElement, FieldElement, FieldElement, FieldElement) {
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
    (id_x, id_y, id_z, z_one)
}

// ═══════════════════════════════════════════════════════════════════
//  Tiny length-prefixed serialization for a single strand file
// ═══════════════════════════════════════════════════════════════════
fn write_lp(buf: &mut Vec<u8>, bytes: &[u8]) {
    buf.extend_from_slice(&(bytes.len() as u64).to_le_bytes());
    buf.extend_from_slice(bytes);
}
fn read_lp(cur: &mut &[u8]) -> Result<Vec<u8>, String> {
    if cur.len() < 8 {
        return Err("truncated length prefix".into());
    }
    let mut lb = [0u8; 8];
    lb.copy_from_slice(&cur[..8]);
    *cur = &cur[8..];
    let n = u64::from_le_bytes(lb) as usize;
    if cur.len() < n {
        return Err(format!("truncated payload: need {n}, have {}", cur.len()));
    }
    let out = cur[..n].to_vec();
    *cur = &cur[n..];
    Ok(out)
}
fn read_u32(cur: &mut &[u8]) -> Result<u32, String> {
    if cur.len() < 4 {
        return Err("truncated u32".into());
    }
    let mut b = [0u8; 4];
    b.copy_from_slice(&cur[..4]);
    *cur = &cur[4..];
    Ok(u32::from_le_bytes(b))
}

/// Serialize (sub-proof, seam commits) for one strand file.
fn serialize_strand(
    proof: &SubAirProofWithTrace,
    seam: &[(usize, Vec<BindingCellsCommit>)],
) -> Vec<u8> {
    let mut buf = Vec::new();
    write_lp(&mut buf, &serialize_proof(proof));
    buf.extend_from_slice(&(seam.len() as u32).to_le_bytes());
    for (gid, commits) in seam {
        buf.extend_from_slice(&(*gid as u32).to_le_bytes());
        buf.extend_from_slice(&(commits.len() as u32).to_le_bytes());
        for c in commits {
            write_lp(&mut buf, &c.to_bytes());
        }
    }
    buf
}

fn deserialize_strand(
    bytes: &[u8],
) -> Result<(SubAirProofWithTrace, Vec<(usize, Vec<BindingCellsCommit>)>), String> {
    let mut cur = bytes;
    let proof = deserialize_proof(&read_lp(&mut cur)?)?;
    let ngroups = read_u32(&mut cur)? as usize;
    let mut seam = Vec::with_capacity(ngroups);
    for _ in 0..ngroups {
        let gid = read_u32(&mut cur)? as usize;
        let ncols = read_u32(&mut cur)? as usize;
        let mut commits = Vec::with_capacity(ncols);
        for _ in 0..ncols {
            commits.push(BindingCellsCommit::from_bytes(&read_lp(&mut cur)?)?);
        }
        seam.push((gid, commits));
    }
    Ok((proof, seam))
}

/// Serialize a full spliced `StrandedProofG` to ONE artifact:
///   [u32 G][ lp(strand_0) ][ lp(strand_1) ] … [ lp(strand_{G-1}) ]
/// (each strand = its sub-proof bytes + seam-commit bytes, per
/// `serialize_strand`).  Strands are in `compute_gway_cut` order.
fn serialize_stranded(proof: &StrandedProofG) -> Vec<u8> {
    let g = proof.proofs.len();
    let mut buf = Vec::new();
    buf.extend_from_slice(&(g as u32).to_le_bytes());
    for s in 0..g {
        let sb = serialize_strand(&proof.proofs[s], &proof.seam_commits[s]);
        write_lp(&mut buf, &sb);
    }
    buf
}

fn deserialize_stranded(bytes: &[u8]) -> Result<StrandedProofG, String> {
    let mut cur = bytes;
    let g = read_u32(&mut cur)? as usize;
    let mut proofs: Vec<SubAirProofWithTrace> = Vec::with_capacity(g);
    let mut seam_commits: Vec<Vec<(usize, Vec<BindingCellsCommit>)>> = Vec::with_capacity(g);
    for _ in 0..g {
        let sb = read_lp(&mut cur)?;
        let (p, c) = deserialize_strand(&sb)?;
        proofs.push(p);
        seam_commits.push(c);
    }
    Ok(StrandedProofG { proofs, seam_commits })
}

// ═══════════════════════════════════════════════════════════════════
//  Manifest (job.json) — shared, deterministic case definition
// ═══════════════════════════════════════════════════════════════════
struct Job {
    key: [u8; 32],
    msg: Vec<u8>,
    k: usize,
    g: usize,
    blowup: usize,
}

fn dir() -> String {
    std::env::var("SWARM_DIR").expect("SWARM_DIR must be set")
}

fn write_job(job: &Job) {
    let j = serde_json::json!({
        "seed_key_hex": hex::encode(job.key),
        "msg_hex": hex::encode(&job.msg),
        "k": job.k,
        "g": job.g,
        "blowup": job.blowup,
    });
    let path = format!("{}/job.json", dir());
    std::fs::write(&path, serde_json::to_vec_pretty(&j).unwrap()).expect("write job.json");
}

fn read_job() -> Job {
    let path = format!("{}/job.json", dir());
    let raw = std::fs::read(&path).expect("read job.json — run coordinator first");
    let j: serde_json::Value = serde_json::from_slice(&raw).expect("parse job.json");
    let key_v = hex::decode(j["seed_key_hex"].as_str().unwrap()).unwrap();
    let mut key = [0u8; 32];
    key.copy_from_slice(&key_v);
    Job {
        key,
        msg: hex::decode(j["msg_hex"].as_str().unwrap()).unwrap(),
        k: j["k"].as_u64().unwrap() as usize,
        g: j["g"].as_u64().unwrap() as usize,
        blowup: j["blowup"].as_u64().unwrap() as usize,
    }
}

fn hx(b: &[u8]) -> String {
    hex::encode(b)
}

// ═══════════════════════════════════════════════════════════════════
//  Roles
// ═══════════════════════════════════════════════════════════════════
fn role_coordinator() {
    let key: [u8; 32] = std::env::var("SWARM_KEY")
        .ok()
        .and_then(|h| hex::decode(h).ok())
        .and_then(|v| <[u8; 32]>::try_from(v.as_slice()).ok())
        .unwrap_or([0x42u8; 32]);
    let msg = std::env::var("SWARM_MSG")
        .unwrap_or_else(|_| "STARK-DNS swarm demo: real P256 ECDSA verify".into())
        .into_bytes();
    let g = std::env::var("G").ok().and_then(|s| s.parse().ok()).unwrap_or(16usize);
    let blowup = std::env::var("BENCH_BLOWUP").ok().and_then(|s| s.parse().ok()).unwrap_or(4usize);
    let k = std::env::var("K").ok().and_then(|s| s.parse().ok()).unwrap_or(256usize);
    let n_trace = (k + 1).next_power_of_two();

    let case = derive_case(&key, &msg, k);
    let (layout, total) = build_ecdsa_verify_multirow_layout(0, k);
    let cut = compute_gway_cut(&layout, k, g);
    let widths: Vec<usize> = (0..g).map(|s| cut.width(s)).collect();
    let wmax = *widths.iter().max().unwrap();
    let wmin = *widths.iter().min().unwrap();

    println!("╔══════════════════════════════════════════════════════════════════╗");
    println!("║  COORDINATOR — real P256 ECDSA keygen + sign                       ║");
    println!("╚══════════════════════════════════════════════════════════════════╝");
    println!("  seed key (sk bytes) : {}", hx(&key));
    println!("  message             : {:?}", String::from_utf8_lossy(&msg));
    println!("  SHA-256 h(m)        : {}", hx(&case.digest));
    println!("  ── ECDSA public key Q ──");
    println!("     Qx : {}", hx(&case.qx_bytes));
    println!("     Qy : {}", hx(&case.qy_bytes));
    println!("  ── signature (r,s) ──");
    println!("     r  : {}", hx(&case.r_bytes));
    println!("     s  : {}", hx(&case.s_bytes));
    println!("  ── STARK public scalar h(m) mod n (e) ──");
    println!("     e  : {}", hx(&case.e_bytes));
    println!("  native ECDSA verify : {}", if case.native_ok { "OK ✓" } else { "FAIL ✗" });
    assert!(case.native_ok, "signature must natively verify");
    println!();
    println!("  ── STARK cut (public inputs = h(m) + PK; witness = verify comp) ──");
    println!("     full AIR width   : {total} columns");
    println!("     G strands        : {g}   (K={k}, n_trace={n_trace}, blowup={blowup})");
    println!("     per-strand widths: {widths:?}");
    println!("     width min/max    : {wmin} / {wmax}   (ratio {:.3})", wmax as f64 / wmin as f64);
    println!("     seam groups      : {}", cut.seams.len());
    println!(
        "     Σ strand_nc      : {}   (= monolith constraints, by construction)",
        cut.strand_nc.iter().sum::<usize>()
    );

    write_job(&Job { key, msg, k, g, blowup });
    println!();
    println!("  wrote manifest → {}/job.json  (every worker re-derives this case)", dir());
}

fn role_worker() {
    let job = read_job();
    let sid: usize = std::env::var("STRAND_ID")
        .expect("STRAND_ID must be set")
        .parse()
        .expect("STRAND_ID int");
    assert!(sid < job.g, "STRAND_ID out of range");
    let n_trace = (job.k + 1).next_power_of_two();
    let r = deep_ali::stark_level::num_queries_for_blowup(job.blowup);

    let case = derive_case(&job.key, &job.msg, job.k);
    let (layout, _total) = build_ecdsa_verify_multirow_layout(0, job.k);
    let cut = compute_gway_cut(&layout, job.k, job.g);
    let cols = &cut.strand_cols[sid];
    let width = cut.width(sid);

    // ── DIRECT-FILL only this strand's columns.  The full ~196k trace is
    //    NEVER allocated in this process (that is the whole point). ──
    let (id_x, id_y, id_z, z_one) = identity_and_z_one();
    let g_pt = *P256_GENERATOR;
    let mut strand: Vec<Vec<F>> = vec![vec![F::zero(); n_trace]; cols.len()];
    let t_fill = Instant::now();
    fill_ecdsa_verify_multirow_strand(
        cols, &mut strand, &layout, n_trace,
        (&id_x, &id_y, &id_z), (&g_pt.x, &g_pt.y, &z_one), &case.u1_bits,
        (&id_x, &id_y, &id_z), (&case.qx, &case.qy, &z_one), &case.u2_bits,
        &case.r_fe,
    );
    let fill_ms = t_fill.elapsed().as_secs_f64() * 1000.0;

    let params = |n0: usize, ph: [u8; 32]| mk_params(n0, r, ph);
    let sep = strand_domain(sid);
    let t_prove = Instant::now();
    let (proof, commits) = prove_one_strand(
        &strand, &cut, sid, &layout, &case.pub_inputs, n_trace, job.blowup, case.pi_hash, &sep,
        params,
    );
    let prove_ms = t_prove.elapsed().as_secs_f64() * 1000.0;
    drop(strand);

    let bytes = serialize_strand(&proof, &commits);
    let path = format!("{}/strand_{sid}.bin", dir());
    std::fs::write(&path, &bytes).expect("write strand file");

    // record width + times for the orchestrator table
    let meta = format!("{width} {fill_ms:.0} {prove_ms:.0} {}", bytes.len());
    let _ = std::fs::write(format!("{}/strand_{sid}.meta", dir()), meta);

    eprintln!(
        "[worker {sid}] width={width} fill={fill_ms:.0}ms prove={prove_ms:.0}ms \
         proof={} KiB seam_groups={} → strand_{sid}.bin (NO full trace built)",
        bytes.len() / 1024,
        commits.len(),
    );
}

/// PROVER-SIDE splice: the coordinator collects the G independently-produced
/// strand sub-proofs + F2b binding commits and ASSEMBLES them into ONE proof
/// artifact `proof.bin` on disk.  This is proof PRODUCTION (no verification
/// here — honest assembly), so its cost is charged to the prover.
fn role_splice() {
    let job = read_job();

    // Collect worker outputs (I/O; deserialization of each worker's file).
    // Not part of the timed splice — this is worker-output ingestion.
    let mut proofs: Vec<SubAirProofWithTrace> = Vec::with_capacity(job.g);
    let mut seam_commits: Vec<Vec<(usize, Vec<BindingCellsCommit>)>> = Vec::with_capacity(job.g);
    for s in 0..job.g {
        let path = format!("{}/strand_{s}.bin", dir());
        let mut f = std::fs::File::open(&path).unwrap_or_else(|e| panic!("open {path}: {e}"));
        let mut buf = Vec::new();
        f.read_to_end(&mut buf).expect("read strand file");
        let (p, c) = deserialize_strand(&buf).expect("deserialize strand");
        proofs.push(p);
        seam_commits.push(c);
    }

    println!("╔══════════════════════════════════════════════════════════════════╗");
    println!("║  SPLICE (prover-side) — assemble {g} strands → one proof.bin       ║", g = job.g);
    println!("╚══════════════════════════════════════════════════════════════════╝");

    // ── TIMED: assemble StrandedProofG + serialize + write to disk ──
    let t = Instant::now();
    let proof = StrandedProofG { proofs, seam_commits };
    let bytes = serialize_stranded(&proof);
    let out = format!("{}/proof.bin", dir());
    std::fs::write(&out, &bytes).expect("write proof.bin");
    let splice_ms = t.elapsed().as_secs_f64() * 1000.0;

    let fri_total: usize = proof.proofs.iter().map(|p| p.fri_proof_bytes.len()).sum();
    println!(
        "  assembled {} strand sub-proofs + F2b seam commits → proof.bin",
        job.g
    );
    println!(
        "  splice_ms      : {splice_ms:.1} ms   (assemble + serialize + write)"
    );
    println!(
        "  proof.bin size : {:.1} MiB   (FRI portion {} KiB)",
        bytes.len() as f64 / (1024.0 * 1024.0),
        fri_total / 1024,
    );
    // machine-readable line for the orchestrator report.
    println!("SPLICE splice_ms={splice_ms:.1} proof_bytes={}", bytes.len());
}

/// CONSUMER-SIDE verify: a relying party reads `proof.bin` and checks it
/// (per-strand FRI + F2b OOD seam consistency).  Only the cryptographic
/// verification is timed.
fn role_verify() {
    let job = read_job();
    let n_trace = (job.k + 1).next_power_of_two();
    let r = deep_ali::stark_level::num_queries_for_blowup(job.blowup);
    let case = derive_case(&job.key, &job.msg, job.k);
    let (layout, _total) = build_ecdsa_verify_multirow_layout(0, job.k);
    let cut = compute_gway_cut(&layout, job.k, job.g);
    let params = |n0: usize, ph: [u8; 32]| mk_params(n0, r, ph);

    println!("╔══════════════════════════════════════════════════════════════════╗");
    println!("║  VERIFY (consumer-side) — read proof.bin & check                   ║");
    println!("╚══════════════════════════════════════════════════════════════════╝");

    // Read the ONE spliced artifact from disk (I/O; not the timed check).
    let art = format!("{}/proof.bin", dir());
    let raw = std::fs::read(&art).expect("read proof.bin — run splice first");
    let proof = deserialize_stranded(&raw).expect("deserialize proof.bin");
    let fri_total: usize = proof.proofs.iter().map(|p| p.fri_proof_bytes.len()).sum();

    // ── TIMED: the cryptographic verification only ──
    let t = Instant::now();
    let honest = verify_stranded_g(
        &proof, &cut, &layout, &case.pub_inputs, n_trace, job.blowup, case.pi_hash, params,
    );
    let verify_ms = t.elapsed().as_secs_f64() * 1000.0;
    let honest_ok = honest.is_ok();

    println!("  verified public statement:");
    println!("     h(m)=e : {}", hx(&case.e_bytes));
    println!("     PK  Qx : {}", hx(&case.qx_bytes));
    println!("     PK  Qy : {}", hx(&case.qy_bytes));
    println!(
        "  verify : {}   ({verify_ms:.1} ms, FRI total {} KiB across {} strands)",
        if honest_ok { "PASS ✓" } else { "FAIL ✗" },
        fri_total / 1024,
        job.g,
    );
    if !honest_ok {
        println!("  ERROR: {:?}", honest.err());
        std::process::exit(1);
    }
    // machine-readable line for the orchestrator report.
    println!("VERIFY verify_ms={verify_ms:.1}");

    // ── NEGATIVE CHECK: corrupt the spliced proof.bin → must REJECT.
    //    Proves the splice cryptographically binds the INDEPENDENTLY-produced
    //    strands: no strand's data can be altered without detection.  We
    //    corrupt the strand's `trace_root` (feeds `augment_pi_hash` → shifts
    //    every FRI/seam FS challenge AND every per-query Merkle path). ──
    let victim = 0usize;
    let helper = |mutate: &dyn Fn(&mut SubAirProofWithTrace)| -> bool {
        let mut p = deserialize_stranded(&raw).unwrap();
        mutate(&mut p.proofs[victim]);
        verify_stranded_g(
            &p, &cut, &layout, &case.pub_inputs, n_trace, job.blowup, case.pi_hash, params,
        )
        .is_err()
    };
    let rej_root = helper(&|p: &mut SubAirProofWithTrace| p.trace_root[0] ^= 0x01);
    // Independent tamper: alter one opened trace CELL value — its committed
    // leaf hash no longer matches → per-query trace-opening check rejects.
    let rej_cell = helper(&|p: &mut SubAirProofWithTrace| {
        p.openings_cur[0].cells[0] += F::from(1u64);
    });
    // Raw on-disk corruption of proof.bin (truncate to half) — the
    // deserializer / verifier must refuse it.
    let raw_rej = deserialize_stranded(&raw[..raw.len() / 2]).is_err();

    println!(
        "  tamper proof.bin (flip strand {victim} trace_root)  : {}",
        if rej_root { "REJECT ✓" } else { "ACCEPTED ✗ (BUG!)" }
    );
    println!(
        "  tamper proof.bin (alter strand {victim} trace cell) : {}",
        if rej_cell { "REJECT ✓" } else { "ACCEPTED ✗ (BUG!)" }
    );
    println!(
        "  tamper proof.bin (truncate artifact)          : {}",
        if raw_rej { "REJECT ✓" } else { "ACCEPTED ✗ (BUG!)" }
    );

    let pass = case.native_ok && honest_ok && rej_root && rej_cell && raw_rej;
    println!();
    if pass {
        println!("=> SWARM PROVED A REAL ECDSA SIGNATURE: honest proof ACCEPTS; tamper REJECTS");
        let _ = std::io::stdout().flush();
    } else {
        println!("=> FAILED");
        std::process::exit(1);
    }
}

fn main() {
    match std::env::var("SWARM_ROLE").as_deref() {
        Ok("coordinator") => role_coordinator(),
        Ok("worker") => role_worker(),
        Ok("splice") => role_splice(),
        Ok("verify") => role_verify(),
        other => {
            eprintln!("SWARM_ROLE must be coordinator|worker|splice|verify (got {other:?})");
            std::process::exit(2);
        }
    }
}

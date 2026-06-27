//! NI-gated update authorization demo (implemented + measured).
//!
//! Source-authenticated, post-quantum DNS record updates with a temporal
//! validity gate and a **proof of time**: a registrar accepts an update only
//! if it carries a STARK proof bound to the owner's registered ML-DSA key, the
//! owner's ML-DSA signature, an append-only chain link (anti-backdating), and
//! an authority-attested creation time provably before the CRQC cutoff.
//!
//! Flagship framing: ACME DNS-01 domain control (`_acme-challenge` TXT).
//!
//! Run:
//!   cargo run --release -p swarm-dns --example ni_gated_update_demo
//!
//! Shows: enrolment, a chain of two accepted (time-attested) updates, then
//! nine rejected attacks — forged record, substituted key, proof lifted onto
//! another key, unregistered name, replay, post-CRQC-cutoff date, broken chain
//! link, backdated timestamp, and a self-claimed (unattested) time.

use std::time::Instant;

use swarm_dns::dns::DnsRecord;
use swarm_dns::dns_authority::{AuthorityKeypair, NistLevel};
use swarm_dns::ni_gate::{
    accept_ni_update, build_ni_update, ni_fs_binding, NameKeyRegistry, NiChainState, NiReject,
    NiUpdate,
};
use swarm_dns::prover::LdtMode;

const T_GENESIS: u64 = 1_700_000_000; // ~2023-11
const T_CRQC_CUTOFF: u64 = 2_000_000_000; // ~2033-05 estimated CRQC emergence

fn main() {
    let ldt = LdtMode::Stir;
    let salt = *b"ni-gate-demo-slt";
    let name = "example.com";

    println!("\n┌─ NI-gated updates: triple binding + temporal + proof-of-time ─");
    println!("│  gate: name<->pk, proof<->pk, sig<->pk, STARK valid, fresh");
    println!("│        serial, chain-linked, created_at < CRQC cutoff, AND");
    println!("│        created_at attested by a trusted time authority (ML-DSA");
    println!("│        proof-of-time, verified in-circuit by the ML-DSA AIR)");
    println!("│  cutoff: {T_CRQC_CUTOFF}   time authority: ML-DSA (PQ)");
    println!("└────────────────────────────────────────────────────────────\n");

    let owner = AuthorityKeypair::keygen(NistLevel::L1, [7u8; 32]);
    let attacker = AuthorityKeypair::keygen(NistLevel::L1, [42u8; 32]);
    let time_authority = AuthorityKeypair::keygen(NistLevel::L1, [99u8; 32]); // PQ time service
    let ta_pk = time_authority.pk_bytes();
    let ta = Some(ta_pk.as_slice());

    let mut registry = NameKeyRegistry::new();
    registry.register(name, &owner.pk_bytes());
    registry.register("attacker.com", &attacker.pk_bytes());
    println!("[1] enrolled owner pk for {name}; trusted ML-DSA time authority configured");

    let token = "3xQ7-acme-challenge-token";
    let mk_records = |ip: [u8; 4]| {
        vec![
            DnsRecord::txt(&format!("_acme-challenge.{name}"), 60, token),
            DnsRecord::a(name, 300, ip),
        ]
    };

    // ── 2. Chain of two accepted, time-attested updates ───────────────────
    let mut chain = NiChainState::genesis();

    let t0 = Instant::now();
    let mut u1 = build_ni_update(&owner, name, &mk_records([93, 184, 216, 34]), 1, T_GENESIS, chain.head_hash, salt, ldt);
    u1.attach_time_attestation(&time_authority); // proof of time
    let prove_ms = t0.elapsed().as_secs_f64() * 1e3;

    let t1 = Instant::now();
    let v1 = accept_ni_update(&registry, &chain, T_CRQC_CUTOFF, ta, &u1, ldt);
    let verify_ms = t1.elapsed().as_secs_f64() * 1e3;
    assert_eq!(v1, Ok(()));
    chain.advance(&u1);
    println!(
        "[2] update #1 ACCEPT (attested {T_GENESIS}); bundle {} KiB, prove+attest {prove_ms:.1} ms, verify {verify_ms:.2} ms",
        u1.proof_sig_bytes() / 1024
    );

    let mut u2 = build_ni_update(&owner, name, &mk_records([93, 184, 216, 35]), 2, T_GENESIS + 86_400, chain.head_hash, salt, ldt);
    u2.attach_time_attestation(&time_authority);
    assert_eq!(accept_ni_update(&registry, &chain, T_CRQC_CUTOFF, ta, &u2, ldt), Ok(()));
    chain.advance(&u2);
    println!("[3] update #2 ACCEPT (attested {}, chained on #1)\n", T_GENESIS + 86_400);

    // ── 4. Attacks, each rejected ─────────────────────────────────────────
    println!("    Attacks (each must be rejected):");
    let head = chain.head_hash;
    let s = 3;
    let d = T_GENESIS + 2 * 86_400;
    let mk = |ip| mk_records(ip);

    let mut forged = build_ni_update(&owner, name, &mk([1, 1, 1, 1]), s, d, head, salt, ldt);
    forged.attach_time_attestation(&time_authority);
    forged.records[1] = DnsRecord::a(name, 300, [6, 6, 6, 6]);
    reject("forged record (tampered A)", &registry, &chain, ta, &forged, ldt);

    let mut swapped = build_ni_update(&owner, name, &mk([1, 1, 1, 1]), s, d, head, salt, ldt);
    swapped.owner_pk = attacker.pk_bytes();
    swapped.owner_sig = attacker.sign(&ni_fs_binding(&attacker.pk_bytes(), name, &swapped.merkle_root, swapped.serial, swapped.created_at, &swapped.prev_proof_hash));
    reject("substituted owner key (same name)", &registry, &chain, ta, &swapped, ldt);

    let att_chain = NiChainState::genesis();
    let mut lifted = build_ni_update(&owner, name, &mk([1, 1, 1, 1]), s, d, att_chain.head_hash, salt, ldt);
    lifted.name = "attacker.com".to_string();
    lifted.owner_pk = attacker.pk_bytes();
    lifted.owner_sig = attacker.sign(&ni_fs_binding(&attacker.pk_bytes(), "attacker.com", &lifted.merkle_root, lifted.serial, lifted.created_at, &lifted.prev_proof_hash));
    reject("proof lifted onto attacker's key/name", &registry, &att_chain, ta, &lifted, ldt);

    let mut unreg = build_ni_update(&owner, name, &mk([1, 1, 1, 1]), s, d, head, salt, ldt);
    unreg.name = "not-enrolled.com".to_string();
    reject("unregistered name", &registry, &chain, ta, &unreg, ldt);

    report("replay (re-sent #2)", accept_ni_update(&registry, &chain, T_CRQC_CUTOFF, ta, &u2, ldt));

    let mut post = build_ni_update(&owner, name, &mk([1, 1, 1, 1]), s, T_CRQC_CUTOFF + 86_400, head, salt, ldt);
    post.attach_time_attestation(&time_authority);
    reject("post-CRQC-cutoff creation date", &registry, &chain, ta, &post, ldt);

    let badlink = build_ni_update(&owner, name, &mk([1, 1, 1, 1]), s, d, [9u8; 32], salt, ldt);
    reject("broken chain link (wrong prev hash)", &registry, &chain, ta, &badlink, ldt);

    let back = build_ni_update(&owner, name, &mk([1, 1, 1, 1]), s, T_GENESIS - 1, head, salt, ldt);
    reject("backdated timestamp (< chain head)", &registry, &chain, ta, &back, ldt);

    // self-claimed time: a fully valid update with NO time attestation.
    let unattested = build_ni_update(&owner, name, &mk([1, 1, 1, 1]), s, d, head, salt, ldt);
    reject("self-claimed time (unattested)", &registry, &chain, ta, &unattested, ldt);

    println!("\n✓ Demo complete: 2 chained time-attested accepts, 9 rejects.\n");
}

fn reject(label: &str, reg: &NameKeyRegistry, chain: &NiChainState, ta: Option<&[u8]>, u: &NiUpdate, ldt: LdtMode) {
    let r = accept_ni_update(reg, chain, T_CRQC_CUTOFF, ta, u, ldt);
    report(label, r);
    assert!(r.is_err(), "attack '{label}' must be rejected, got {r:?}");
}
fn report(label: &str, r: Result<(), NiReject>) {
    match r {
        Ok(()) => println!("      {label:42}  ACCEPT  (!!! unexpected)"),
        Err(e) => println!("      {label:42}  REJECT  ({e:?})"),
    }
}

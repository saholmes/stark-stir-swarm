//! NI-gated update authorization demo (implemented + measured).
//!
//! Source-authenticated, post-quantum DNS record updates with a **temporal
//! validity gate**: a registrar accepts an update only if it carries a STARK
//! proof bound to the owner's registered ML-DSA key, the owner's ML-DSA
//! signature, AND a creation timestamp provably before the CRQC cutoff,
//! extending an append-only per-name chain (anti-backdating).
//!
//! Flagship framing: ACME DNS-01 domain control (`_acme-challenge` TXT).
//!
//! Run:
//!   cargo run --release -p swarm-dns --example ni_gated_update_demo
//!
//! Shows: enrolment, a chain of two accepted updates, then eight rejected
//! attacks (forged record, substituted key, proof lifted onto another key,
//! unregistered name, replay, **post-CRQC-cutoff proof, broken chain link,
//! and a backdated timestamp**), with prove/verify timing and bundle size.

use std::time::Instant;

use swarm_dns::dns::DnsRecord;
use swarm_dns::dns_authority::{AuthorityKeypair, NistLevel};
use swarm_dns::ni_gate::{
    accept_ni_update, build_ni_update, ni_fs_binding, NameKeyRegistry, NiChainState, NiReject,
    NiUpdate,
};
use swarm_dns::prover::LdtMode;

// Illustrative wall-clock anchors (unix seconds).
const T_GENESIS: u64 = 1_700_000_000; // ~2023-11
const T_CRQC_CUTOFF: u64 = 2_000_000_000; // ~2033-05 estimated CRQC emergence

fn main() {
    let ldt = LdtMode::Stir;
    let salt = *b"ni-gate-demo-slt";
    let name = "example.com";

    println!("\n┌─ NI-gated update authorization + temporal validity ───────");
    println!("│  trust root : owner registers H(ML-DSA pk) for the name");
    println!("│  binding    : proof FS-anchor folds owner pk, creation date,");
    println!("│               and prev-proof hash (chain); owner ML-DSA-signs it");
    println!("│  gate       : accept iff name<->pk, proof<->pk, sig<->pk,");
    println!("│               STARK valid, fresh serial, chain-linked,");
    println!("│               created_at < CRQC cutoff (provably pre-CRQC)");
    println!("│  cutoff     : {T_CRQC_CUTOFF} (estimated CRQC emergence)");
    println!("└────────────────────────────────────────────────────────────\n");

    let owner = AuthorityKeypair::keygen(NistLevel::L1, [7u8; 32]);
    let attacker = AuthorityKeypair::keygen(NistLevel::L1, [42u8; 32]);

    let mut registry = NameKeyRegistry::new();
    registry.register(name, &owner.pk_bytes());
    registry.register("attacker.com", &attacker.pk_bytes());
    println!("[1] enrolled owner pk for {name} (+ attacker pk for attacker.com)");

    let token = "3xQ7-acme-challenge-token";
    let mk_records = |ip: [u8; 4]| {
        vec![
            DnsRecord::txt(&format!("_acme-challenge.{name}"), 60, token),
            DnsRecord::a(name, 300, ip),
        ]
    };

    // ── 2. Chain of two accepted updates (genesis -> u1 -> u2) ────────────
    let mut chain = NiChainState::genesis();

    let t0 = Instant::now();
    let u1 = build_ni_update(&owner, name, &mk_records([93, 184, 216, 34]), 1, T_GENESIS, chain.head_hash, salt, ldt);
    let prove_ms = t0.elapsed().as_secs_f64() * 1e3;

    let t1 = Instant::now();
    let v1 = accept_ni_update(&registry, &chain, T_CRQC_CUTOFF, &u1, ldt);
    let verify_ms = t1.elapsed().as_secs_f64() * 1e3;
    assert_eq!(v1, Ok(()));
    chain.advance(&u1);
    println!(
        "[2] update #1 ACCEPT (date {T_GENESIS}); proof+sig {} KiB, prove {prove_ms:.1} ms, verify {verify_ms:.2} ms",
        u1.proof_sig_bytes() / 1024
    );

    let u2 = build_ni_update(&owner, name, &mk_records([93, 184, 216, 35]), 2, T_GENESIS + 86_400, chain.head_hash, salt, ldt);
    assert_eq!(accept_ni_update(&registry, &chain, T_CRQC_CUTOFF, &u2, ldt), Ok(()));
    chain.advance(&u2);
    println!("[3] update #2 ACCEPT (date {}, chained on #1)\n", T_GENESIS + 86_400);

    // ── 4. Attacks against the chain head, each rejected ──────────────────
    println!("    Attacks (each must be rejected):");
    let head = chain.head_hash;
    let next_serial = 3;
    let valid_date = T_GENESIS + 2 * 86_400;

    // (a) forged record: tamper after proving.
    let mut forged = build_ni_update(&owner, name, &mk_records([1, 1, 1, 1]), next_serial, valid_date, head, salt, ldt);
    forged.records[1] = DnsRecord::a(name, 300, [6, 6, 6, 6]);
    expect_reject("forged record (tampered A)", &registry, &chain, &forged, ldt);

    // (b) substituted key, same name.
    let mut swapped = build_ni_update(&owner, name, &mk_records([1, 1, 1, 1]), next_serial, valid_date, head, salt, ldt);
    swapped.owner_pk = attacker.pk_bytes();
    swapped.owner_sig = attacker.sign(&ni_fs_binding(&attacker.pk_bytes(), name, &swapped.merkle_root, swapped.serial, swapped.created_at, &swapped.prev_proof_hash));
    expect_reject("substituted owner key (same name)", &registry, &chain, &swapped, ldt);

    // (c) proof lifted onto attacker's own registered name+key.
    let mut lifted = build_ni_update(&owner, name, &mk_records([1, 1, 1, 1]), next_serial, valid_date, head, salt, ldt);
    lifted.name = "attacker.com".to_string();
    lifted.owner_pk = attacker.pk_bytes();
    lifted.owner_sig = attacker.sign(&ni_fs_binding(&attacker.pk_bytes(), "attacker.com", &lifted.merkle_root, lifted.serial, lifted.created_at, &lifted.prev_proof_hash));
    // attacker.com chain is still genesis; its prev must be [0;32], so this also breaks the link — use attacker.com genesis to isolate the StarkInvalid:
    let att_chain = NiChainState::genesis();
    lifted.prev_proof_hash = att_chain.head_hash;
    lifted.owner_sig = attacker.sign(&ni_fs_binding(&attacker.pk_bytes(), "attacker.com", &lifted.merkle_root, lifted.serial, lifted.created_at, &lifted.prev_proof_hash));
    expect_reject_chain("proof lifted onto attacker's key/name", &registry, &att_chain, &lifted, ldt);

    // (d) unregistered name.
    let mut unreg = build_ni_update(&owner, name, &mk_records([1, 1, 1, 1]), next_serial, valid_date, head, salt, ldt);
    unreg.name = "not-enrolled.com".to_string();
    expect_reject("unregistered name", &registry, &chain, &unreg, ldt);

    // (e) replay: re-present an already-accepted update (#2).
    report("replay (stale serial / re-sent #2)", accept_ni_update(&registry, &chain, T_CRQC_CUTOFF, &u2, ldt));

    // (f) post-CRQC-cutoff proof: created after the cutoff date.
    let post = build_ni_update(&owner, name, &mk_records([1, 1, 1, 1]), next_serial, T_CRQC_CUTOFF + 86_400, head, salt, ldt);
    expect_reject("post-CRQC-cutoff creation date", &registry, &chain, &post, ldt);

    // (g) broken chain link: prev_proof_hash does not extend the head.
    let mut badlink = build_ni_update(&owner, name, &mk_records([1, 1, 1, 1]), next_serial, valid_date, [9u8; 32], salt, ldt);
    let _ = &mut badlink;
    expect_reject("broken chain link (wrong prev hash)", &registry, &chain, &badlink, ldt);

    // (h) backdated: timestamp earlier than the chain head, but correctly linked.
    let back = build_ni_update(&owner, name, &mk_records([1, 1, 1, 1]), next_serial, T_GENESIS - 1, head, salt, ldt);
    expect_reject("backdated timestamp (< chain head)", &registry, &chain, &back, ldt);

    println!("\n✓ NI-gated + temporal demo complete: 2 chained accepts, 8 rejects.\n");
}

fn expect_reject(label: &str, reg: &NameKeyRegistry, chain: &NiChainState, u: &NiUpdate, ldt: LdtMode) {
    expect_reject_chain(label, reg, chain, u, ldt)
}
fn expect_reject_chain(label: &str, reg: &NameKeyRegistry, chain: &NiChainState, u: &NiUpdate, ldt: LdtMode) {
    let r = accept_ni_update(reg, chain, T_CRQC_CUTOFF, u, ldt);
    report(label, r);
    assert!(r.is_err(), "attack '{label}' must be rejected, got {r:?}");
}
fn report(label: &str, r: Result<(), NiReject>) {
    match r {
        Ok(()) => println!("      {label:42}  ACCEPT  (!!! unexpected)"),
        Err(e) => println!("      {label:42}  REJECT  ({e:?})"),
    }
}

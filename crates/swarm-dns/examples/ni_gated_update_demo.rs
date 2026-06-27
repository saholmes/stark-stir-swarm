//! NI-gated update authorization demo (implemented + measured).
//!
//! Demonstrates source-authenticated, post-quantum DNS record updates: a
//! registrar accepts an update only if it carries a STARK proof bound to the
//! owner's registered ML-DSA key plus the owner's ML-DSA signature.  This is
//! the running-code answer to the capture-window MitM: a forged or substituted
//! update is rejected at ingress.
//!
//! Flagship framing: ACME DNS-01 domain control (`_acme-challenge` TXT).
//!
//! Run:
//!   cargo run --release -p swarm-dns --example ni_gated_update_demo \
//!       --features "<your sha3/mldsa feature set>"
//!
//! Shows: (1) one-time owner key enrolment, (2) a valid NI-gated update
//! accepted, and (3) five attacks rejected — forged record, substituted key,
//! proof lifted onto another key, unregistered name, and replay — with
//! prove/verify timing and proof+signature size.

use std::time::Instant;

use swarm_dns::dns::DnsRecord;
use swarm_dns::dns_authority::{AuthorityKeypair, NistLevel};
use swarm_dns::ni_gate::{accept_ni_update, build_ni_update, NameKeyRegistry, NiReject};
use swarm_dns::prover::LdtMode;

fn main() {
    let ldt = LdtMode::Stir;
    let salt = *b"ni-gate-demo-slt";
    let name = "example.com";

    println!("\n┌─ NI-gated update authorization (implemented + measured) ───");
    println!("│  trust root : owner registers H(ML-DSA pk) for the name");
    println!("│  binding    : proof FS-anchor folds owner pk (proof<->pk);");
    println!("│               owner ML-DSA-signs the same anchor (sig<->pk)");
    println!("│  gate       : registrar accepts iff name<->pk, proof<->pk,");
    println!("│               sig<->pk, STARK valid, fresh serial");
    println!("└────────────────────────────────────────────────────────────\n");

    // ── 0. Owner and an unrelated attacker each hold an ML-DSA key ────────
    let owner = AuthorityKeypair::keygen(NistLevel::L1, [7u8; 32]);
    let attacker = AuthorityKeypair::keygen(NistLevel::L1, [42u8; 32]);

    // ── 1. One-time enrolment (the trust root) ────────────────────────────
    let mut registry = NameKeyRegistry::new();
    registry.register(name, &owner.pk_bytes());
    registry.register("attacker.com", &attacker.pk_bytes()); // attacker owns a different name
    println!("[1] enrolled owner pk for {name} (and attacker pk for attacker.com)");

    // ── 2. Owner builds an NI-gated update (ACME _acme-challenge + A) ──────
    let token = b"3xQ7...acme-challenge-token...";
    let records = vec![
        DnsRecord::txt(&format!("_acme-challenge.{name}"), 60, std::str::from_utf8(token).unwrap()),
        DnsRecord::a(name, 300, [93, 184, 216, 34]),
    ];
    let serial = 1u64;

    let t0 = Instant::now();
    let update = build_ni_update(&owner, name, &records, serial, salt, ldt);
    let prove_ms = t0.elapsed().as_secs_f64() * 1e3;
    println!(
        "[2] owner built NI update: {} records, proof+sig {} bytes ({} KiB), prove {:.1} ms",
        update.records.len(),
        update.proof_sig_bytes(),
        update.proof_sig_bytes() / 1024,
        prove_ms,
    );

    // ── 3. Registrar accepts the honest update ────────────────────────────
    let last_serial = 0u64;
    let t1 = Instant::now();
    let verdict = accept_ni_update(&registry, last_serial, &update, ldt);
    let verify_ms = t1.elapsed().as_secs_f64() * 1e3;
    assert_eq!(verdict, Ok(()), "honest update must be accepted");
    println!("[3] registrar ACCEPT (honest update), verify {verify_ms:.2} ms\n");

    // ── 4. Attacks, each rejected ─────────────────────────────────────────
    println!("    Attacks (each must be rejected):");

    // (a) forged record: tamper a record after proving.
    let mut forged = update.clone();
    forged.records[1] = DnsRecord::a(name, 300, [6, 6, 6, 6]); // redirect example.com
    expect_reject("forged record (tampered A)", &registry, &forged, ldt, last_serial);

    // (b) substituted key: present the proof under the attacker's pk, same name.
    let mut swapped = update.clone();
    swapped.owner_pk = attacker.pk_bytes();
    swapped.owner_sig = attacker.sign(&swarm_dns::ni_gate::ni_fs_binding(
        &attacker.pk_bytes(), name, &swapped.merkle_root, swapped.serial,
    ));
    expect_reject("substituted owner key (same name)", &registry, &swapped, ldt, last_serial);

    // (c) proof lifted onto attacker's own registered name+key.
    let mut lifted = update.clone();
    lifted.name = "attacker.com".to_string();
    lifted.owner_pk = attacker.pk_bytes();
    lifted.owner_sig = attacker.sign(&swarm_dns::ni_gate::ni_fs_binding(
        &attacker.pk_bytes(), "attacker.com", &lifted.merkle_root, lifted.serial,
    ));
    expect_reject("proof lifted onto attacker's key/name", &registry, &lifted, ldt, last_serial);

    // (d) unregistered name.
    let mut unreg = update.clone();
    unreg.name = "not-enrolled.com".to_string();
    expect_reject("unregistered name", &registry, &unreg, ldt, last_serial);

    // (e) replay: re-present an already-accepted serial.
    let replay = accept_ni_update(&registry, update.serial, &update, ldt);
    report("replay (stale serial)", replay);

    println!("\n✓ NI-gated demo complete: 1 accept, 5 rejects, all as expected.\n");
}

fn expect_reject(
    label: &str,
    registry: &NameKeyRegistry,
    update: &swarm_dns::ni_gate::NiUpdate,
    ldt: LdtMode,
    last_serial: u64,
) {
    let r = accept_ni_update(registry, last_serial, update, ldt);
    report(label, r);
    assert!(r.is_err(), "attack '{label}' must be rejected, got {r:?}");
}

fn report(label: &str, r: Result<(), NiReject>) {
    match r {
        Ok(()) => println!("      {label:42}  ACCEPT  (!!! unexpected)"),
        Err(e) => println!("      {label:42}  REJECT  ({e:?})"),
    }
}

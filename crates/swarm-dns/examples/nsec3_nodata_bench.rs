//! NSEC3 NODATA non-coverage benchmark (N2 gadget).
//!
//! Companion to `nsec3_completeness_bench`.  Where the completeness proof
//! gives the NXDOMAIN side of authenticated denial-of-existence (no gaps
//! in namespace coverage), this proves the NODATA side: a name that
//! EXISTS has a queried RR type ABSENT from its RFC 4034 §4.1.2 type
//! bitmap.
//!
//! The AIR is fixed-size (one row per window-0 type code, n_trace = 256),
//! so prove/verify/size are constant — independent of zone size.  We
//! report STIR and FRI for a representative NODATA query (name has
//! A/RRSIG/NSEC3 but not AAAA; query AAAA).
//!
//! Run:
//!     cargo run --release -p swarm-dns --example nsec3_nodata_bench

use swarm_dns::prover::{
    prove_nsec3_nodata, verify_nsec3_nodata, LdtMode, Nsec3TypedRecord,
};

const SALT: [u8; 16] = *b"swarm-test-zone1";
const FS_BINDING: [u8; 32] = [0xC3; 32];

fn bitmap_with(types: &[u8]) -> [u8; 32] {
    let mut bm = [0u8; 32];
    for &t in types {
        bm[(t >> 3) as usize] |= 1 << (7 - (t & 7));
    }
    bm
}

fn run_one(ldt: LdtMode, label: &str) {
    // A name that exists with A(1), RRSIG(46), NSEC3(50) but no AAAA(28).
    let rec = Nsec3TypedRecord {
        owner_hash:  [0x11u8; 32],
        next_hash:   [0x22u8; 32],
        type_bitmap: bitmap_with(&[1, 46, 50]),
    };
    let qname = rec.owner_hash;
    let qtype = 28u16; // AAAA — absent ⇒ NODATA

    let out = prove_nsec3_nodata(&rec, &qname, qtype, &SALT, &FS_BINDING, ldt);
    verify_nsec3_nodata(&out, &rec, &qname, qtype, &SALT, &FS_BINDING, ldt)
        .expect("honest NODATA proof must verify");

    println!(
        "    {label:>12}  prove_ms={:>6.1}  verify_ms={:>5.2}  proof_bytes={:>7}  ({} KiB)",
        out.prove_ms, out.local_verify_ms, out.proof_bytes,
        out.proof_bytes / 1024,
    );
}

fn main() {
    println!("\n┌─ NSEC3 NODATA non-coverage — N2 type-bitmap gadget ───────");
    println!("│  AIR    : Nsec3NoData  (w=3, 4 Boolean/non-coverage constraints)");
    println!("│  field  : Goldilocks  Fp⁶ (sextic ext)");
    println!("│  blowup : 32          NIST L1 calibration");
    println!("│  trace  : 256 rows    (one per window-0 RR type code)");
    println!("│  proves : name exists ∧ queried type absent ⇒ NODATA");
    println!("└───────────────────────────────────────────────────────────\n");

    println!("  Query: AAAA (28) at a name holding {{A, RRSIG, NSEC3}} → NODATA\n");
    run_one(LdtMode::Stir, "STARK STIR");
    run_one(LdtMode::Fri, "STARK FRI");

    println!("\n  Cost is constant in zone size N (fixed 256-row trace): the");
    println!("  NODATA non-coverage is bound per-record into pi_hash and");
    println!("  verified once.  The chain-completeness proof (NXDOMAIN side)");
    println!("  supplies the no-gaps soundness a signed Merkle tree cannot;");
    println!("  this gadget folds the NODATA type-bitmap check into the same");
    println!("  transcript-bound proof object as the completeness proof.\n");
}

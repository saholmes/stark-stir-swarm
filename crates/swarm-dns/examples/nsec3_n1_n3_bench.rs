//! N1 (wildcard-synthesis closure) + N3 (NSEC3 Opt-Out) benchmark.
//!
//! Completes the in-circuit NSEC/NSEC3 denial-of-existence gadget set:
//!   * N3 — `Nsec3OptOut` AIR (8-row Flags octet): proves an insecure
//!     delegation is legitimately elided (covering record's Opt-Out bit set).
//!   * N1 — wildcard-synthesis closure: proves the wildcard `*.CE` does not
//!     cover the queried type (reuses the N2 non-coverage AIR, 256-row),
//!     binding the closest-encloser; the wildcard-absent case is bracketing.
//!
//! Both are constant-cost (fixed trace heights), independent of zone size.
//!
//! Run:
//!     cargo run --release -p swarm-dns --example nsec3_n1_n3_bench

use swarm_dns::prover::{
    prove_nsec3_optout, verify_nsec3_optout,
    prove_nsec3_wildcard_closure, verify_nsec3_wildcard_closure,
    LdtMode, Nsec3TypedRecord,
};

const SALT: [u8; 16] = *b"swarm-test-zone1";
const FS:   [u8; 32]  = [0xD4; 32];

fn bitmap_with(types: &[u8]) -> [u8; 32] {
    let mut bm = [0u8; 32];
    for &t in types { bm[(t >> 3) as usize] |= 1 << (7 - (t & 7)); }
    bm
}

fn bench_optout(ldt: LdtMode, label: &str) {
    let mut owner = [0u8; 32]; owner[0] = 0x10;
    let mut deleg = [0u8; 32]; deleg[0] = 0x40;
    let mut next  = [0u8; 32]; next[0]  = 0x80;
    let out = prove_nsec3_optout(&owner, &next, 0x01, &deleg, &SALT, &FS, ldt);
    verify_nsec3_optout(&out, &owner, &next, 0x01, &deleg, &SALT, &FS, ldt).unwrap();
    println!("    N3 Opt-Out  {label:>4}  prove_ms={:>6.1}  verify_ms={:>5.2}  proof={:>6} B ({} KiB)",
        out.prove_ms, out.local_verify_ms, out.proof_bytes, out.proof_bytes / 1024);
}

fn bench_wildcard(ldt: LdtMode, label: &str) {
    let wc = Nsec3TypedRecord {
        owner_hash:  [0x55u8; 32],
        next_hash:   [0x66u8; 32],
        type_bitmap: bitmap_with(&[1, 46]), // A + RRSIG, no AAAA
    };
    let ce = [0x77u8; 32];
    let qname = [0x12u8; 32];
    let out = prove_nsec3_wildcard_closure(&ce, &wc, &qname, 28, &SALT, &FS, ldt);
    verify_nsec3_wildcard_closure(&out, &ce, &wc, &wc.owner_hash, &qname, 28, &SALT, &FS, ldt).unwrap();
    println!("    N1 Wildcard {label:>4}  prove_ms={:>6.1}  verify_ms={:>5.2}  proof={:>6} B ({} KiB)",
        out.prove_ms, out.local_verify_ms, out.proof_bytes, out.proof_bytes / 1024);
}

fn main() {
    println!("\n┌─ N1 wildcard-closure + N3 Opt-Out — denial-of-existence gadgets ─");
    println!("│  N3 : Nsec3OptOut AIR (w=3, 8-row Flags octet, Opt-Out bit SET)");
    println!("│  N1 : wildcard type non-coverage (reuses N2 AIR, 256-row) + CE binding");
    println!("│  both constant-cost, independent of zone size");
    println!("└──────────────────────────────────────────────────────────────────\n");

    bench_optout(LdtMode::Stir, "STIR");
    bench_optout(LdtMode::Fri, "FRI");
    println!();
    bench_wildcard(LdtMode::Stir, "STIR");
    bench_wildcard(LdtMode::Fri, "FRI");

    println!("\n  N3 proves an unsigned delegation is legitimately elided (covering");
    println!("  NSEC3 record's Opt-Out flag set, RFC 5155 §3.1.2.1).  N1 proves a");
    println!("  wildcard would not synthesise the queried type.  Together with the");
    println!("  completeness (NXDOMAIN) and N2 (NODATA) gadgets, this completes the");
    println!("  in-circuit NSEC/NSEC3 denial-of-existence semantics.\n");
}

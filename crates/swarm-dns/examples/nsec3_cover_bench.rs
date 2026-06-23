//! F1 in-circuit lexicographic cover benchmark.
//!
//! Closes the last native-trust component of the denial-of-existence path:
//! the lexicographic interval cover `owner < q < next` is proved
//! in-circuit (LexLt AIR, subtraction-with-borrow) instead of computed by
//! a trusted native byte comparison.  A cover proof is two LexLt
//! sub-proofs (one per cyclic-cover mode); the verifier performs NO byte
//! comparison.
//!
//! Run:
//!     cargo run --release -p swarm-dns --example nsec3_cover_bench

use std::time::Instant;

use swarm_dns::prover::{
    prove_lex_lt, verify_lex_lt, prove_nsec3_cover, verify_nsec3_cover,
    CoverMode, LdtMode,
};

const FS: [u8; 32] = [0xF6; 32];

fn h(msb0: u8) -> [u8; 32] { let mut x = [0u8; 32]; x[0] = msb0; x }

fn bench_lexlt(ldt: LdtMode, label: &str) {
    let a = h(0x10); let b = h(0x20);
    let t = Instant::now();
    let out = prove_lex_lt(&a, &b, &FS, ldt);
    let prove_ms = t.elapsed().as_secs_f64() * 1e3;
    let t2 = Instant::now();
    assert!(verify_lex_lt(&out, &a, &b, &FS, ldt));
    let verify_ms = t2.elapsed().as_secs_f64() * 1e3;
    println!("    LexLt (a<b)  {label:>4}  prove_ms={prove_ms:>6.1}  verify_ms={verify_ms:>5.2}  proof={:>6} B ({} KiB)",
        out.proof_bytes, out.proof_bytes / 1024);
}

fn bench_cover(ldt: LdtMode, label: &str) {
    let owner = h(0x10); let q = h(0x40); let next = h(0x80);
    let t = Instant::now();
    let p = prove_nsec3_cover(&owner, &q, &next, &FS, ldt);
    let prove_ms = t.elapsed().as_secs_f64() * 1e3;
    let t2 = Instant::now();
    verify_nsec3_cover(&p, &owner, &q, &next, &FS, ldt).unwrap();
    let verify_ms = t2.elapsed().as_secs_f64() * 1e3;
    let bytes = p.lt1.proof_bytes + p.lt2.proof_bytes;
    assert_eq!(p.mode, CoverMode::Interior);
    println!("    Cover (2 LT) {label:>4}  prove_ms={prove_ms:>6.1}  verify_ms={verify_ms:>5.2}  proof={:>6} B ({} KiB)",
        bytes, bytes / 1024);
}

fn main() {
    println!("\n┌─ F1 in-circuit lexicographic cover ───────────────────────");
    println!("│  LexLt AIR : w=776, subtraction-with-borrow (a+1+δ=b, no final carry)");
    println!("│  cover     : 2 LexLt sub-proofs (Interior / WrapUpper / WrapLower)");
    println!("│  verifier  : NO native byte comparison (was nsec3_covers)");
    println!("└────────────────────────────────────────────────────────────\n");

    bench_lexlt(LdtMode::Stir, "STIR");
    bench_lexlt(LdtMode::Fri, "FRI");
    println!();
    bench_cover(LdtMode::Stir, "STIR");
    bench_cover(LdtMode::Fri, "FRI");

    println!("\n  The lexicographic `owner < q < next` decision is now enforced");
    println!("  by the low-degree test on the comparison AIR, not by trusted");
    println!("  native code — removing the last native step from the in-circuit");
    println!("  NSEC/NSEC3 denial-of-existence path.  Operand identity is bound");
    println!("  via the FS public input, as for every other gadget.\n");
}

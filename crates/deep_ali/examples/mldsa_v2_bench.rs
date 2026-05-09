//! **NOTE**: this example was superseded by the `v2_bench` `#[test]
//! #[ignore]` in `ml_dsa_verify_air_v2_orchestration.rs::tests`.  The
//! test has full access to the test-helper `synthesize_witness` and
//! produces the same CSV-friendly output expected by
//! `aws-bench/bench-mldsa-l{1,3,5}.sh`.
//!
//! Run with:
//!     cargo test --release -p deep_ali \
//!         --features "parallel sha3-256 mldsa-44" --no-default-features \
//!         v2_bench -- --ignored --nocapture
//!
//! See `aws-bench/bench-mldsa-l1.sh` for the canonical wrapper.

fn main() {
    eprintln!(
        "This example is a placeholder.  Use the `v2_bench` test instead:\n\
         \n\
         cargo test --release -p deep_ali \\\n\
             --features \"parallel sha3-N mldsa-N\" --no-default-features \\\n\
             v2_bench -- --ignored --nocapture\n\
         \n\
         where (sha3-N, mldsa-N) ∈ {{(sha3-256, mldsa-44), (sha3-384, mldsa-65), (sha3-512, mldsa-87)}}\n\
         for NIST PQ Levels 1, 3, 5 respectively.\n\
         \n\
         Or use the wrapper scripts in scripts/aws-bench/."
    );
    std::process::exit(1);
}

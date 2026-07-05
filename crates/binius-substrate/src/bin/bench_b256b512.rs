// bench_b256b512 — PART 1 RSS baseline. Proves N raw Keccak-f[1600] permutations
// over the NIST tower fields B256 (L1) / B512 (L5) under the FIPS SHA-256
// commitment + SHA-256 Fiat-Shamir transcript, and prints ONE structured RESULT
// line so `scripts/bench-b256b512.sh` (which wraps this binary in
// `/usr/bin/time -l`) can parse prove_ms/proof_bytes and pair them with the peak
// resident set size of the whole process.
//
// Usage:  bench_b256b512 <field> [N] [security_bits]
//   field         b256 | b512  (which NIST tower field / challenge field)
//   N             batch size = number of in-circuit Keccak-f[1600] permutations
//                 (rounded up to a power of two by the m3 table; default 8)
//   security_bits Fiat-Shamir soundness target; default 128 for b256 (NIST L1),
//                 256 for b512 (NIST L5)
//
// log_inv_rate is fixed at 1 (blowup = 2), matching the b256_keccak / b512_keccak
// gates. This is the SAME FIPS prove wiring those gates already verify; here we
// only time prove/verify separately and let the shell wrapper capture peak RSS.
//
// IMPORTANT (peak RSS): run the BUILT binary directly under `/usr/bin/time -l`,
// e.g. `./target/release/bench_b256b512 b256 64 128`. Do NOT wrap `cargo run` —
// cargo's own RSS masks the prover's, defeating the measurement.

use std::env;

use binius_substrate::bench::{bench_keccak_b256, bench_keccak_b512, BenchKeccakResult};

/// blowup = 2^LOG_INV_RATE = 2, matching the b256/b512 Keccak gates.
const LOG_INV_RATE: usize = 1;

fn main() {
	let mut args = env::args().skip(1);

	let field = args
		.next()
		.unwrap_or_else(|| "b256".to_string())
		.to_lowercase();

	let n: usize = args
		.next()
		.map(|s| s.parse().expect("N must be a positive integer"))
		.unwrap_or(8);

	// Default security_bits depends on the level: L1 for b256, L5 for b512.
	let default_sec = if field == "b512" { 256 } else { 128 };
	let security_bits: usize = args
		.next()
		.map(|s| s.parse().expect("security_bits must be a positive integer"))
		.unwrap_or(default_sec);

	let r: BenchKeccakResult = match field.as_str() {
		"b256" => bench_keccak_b256(n, LOG_INV_RATE, security_bits)
			.expect("Keccak-f batch must prove AND verify over B256"),
		"b512" => bench_keccak_b512(n, LOG_INV_RATE, security_bits)
			.expect("Keccak-f batch must prove AND verify over B512"),
		other => panic!("unknown field '{other}': expected b256 or b512"),
	};

	// Single structured line — stable key=value fields for the shell parser.
	println!(
		"RESULT field={} N={} sec={} log_inv_rate={} prove_ms={} verify_ms={} proof_bytes={}",
		field, r.n, r.security_bits, r.log_inv_rate, r.prove_ms, r.verify_ms, r.proof_bytes,
	);
}

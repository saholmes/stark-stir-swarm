// bench_sha3 — CLI entry for the M2a in-circuit SHA3-256 prove/verify scaling
// bench. Prints ONE structured RESULT line so `scripts/bench-sha3.sh` (which
// wraps this binary in `/usr/bin/time -l` for peak RSS) can parse it.
//
// Usage:  bench_sha3 [N] [log_inv_rate]
//   N            batch size = number of in-circuit SHA3-256 single-block hashes
//                (default 256)
//   log_inv_rate FRI inverse-rate exponent; blowup = 2^log_inv_rate
//                (default 2, i.e. blowup=4, matching the paper's smoke L1 config)
//
// security_bits is fixed at 100 to match the paper's smoke L1 baseline.
//
// IMPORTANT (peak RSS): run the built binary directly under `/usr/bin/time -l`,
// e.g. `./target/release/bench_sha3 4096 2`. Do NOT wrap `cargo run` — cargo's
// own RSS masks the prover's, defeating the measurement.

use std::env;

use binius_substrate::bench::bench_sha3_256;

const SECURITY_BITS: usize = 100;

fn main() {
	let mut args = env::args().skip(1);

	let n: usize = args
		.next()
		.map(|s| s.parse().expect("N must be a positive integer"))
		.unwrap_or(256);
	let log_inv_rate: usize = args
		.next()
		.map(|s| s.parse().expect("log_inv_rate must be a non-negative integer"))
		.unwrap_or(2);

	let r = bench_sha3_256(n, log_inv_rate, SECURITY_BITS)
		.expect("in-circuit SHA3-256 bench must prove and verify");

	// ms/hash as a float with 3 decimals; guard n>0 (bench_sha3_256 asserts it).
	let ms_per_hash = r.prove_ms as f64 / r.n as f64;

	// Single structured line — stable key=value fields for the shell parser.
	println!(
		"RESULT n={} blowup={} log_inv_rate={} prove_ms={} verify_ms={} proof_bytes={} ms_per_hash={:.3}",
		r.n,
		1usize << r.log_inv_rate,
		r.log_inv_rate,
		r.prove_ms,
		r.verify_ms,
		r.proof_bytes,
		ms_per_hash,
	);
}

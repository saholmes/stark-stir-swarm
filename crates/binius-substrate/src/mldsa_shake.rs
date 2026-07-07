// S1b (ML-DSA / FIPS 204 verify port) — the SHAKE-XOF + ExpandA layer over the
// 256-bit tower field `B256TowerFamily` at NIST L1 (128) with a SHA-256 Merkle
// commitment + SHA-256 Fiat–Shamir challenger.
//
// ML-DSA verify needs, before the R_q arithmetic of S1a can run:
//   * μ         = H(BytesToBits(tr) ‖ M)            (SHAKE-256, absorbed multi-block)
//   * c         = SampleInBall(c̃)                   (SHAKE-256 XOF, S1c)
//   * A_hat     = ExpandA(ρ)                         (SHAKE-128 XOF + rejection → Ŕ_q^{k×l})
//   * c̃'        = H(μ ‖ w1Encode(w1))  and  c̃' == c̃  (SHAKE-256, S1c/S1d)
// This module delivers the SHAKE **extendable-output function (XOF)** and **ExpandA**
// (matrix generation by rejection sampling), which are the parts S1a does not cover.
//
// ── WHAT IS NEW vs. b256_sha3 / b256_keccak ───────────────────────────────────────
// `b256_sha3.rs` proves a SINGLE-BLOCK, FIXED-length SHA3-256/384/512 digest over
// B256 (one Keccak-f permutation; squeeze once). ExpandA/SampleInBall instead need:
//   (1) a SHAKE variant  — rate 168 (SHAKE-128) / 136 (SHAKE-256); domain-pad 0x1F
//       (vs SHA3's 0x06) in the pad10*1 first byte.
//   (2) a MULTI-BLOCK squeeze — the XOF emits `rate` bytes, re-applies Keccak-f, emits
//       the next `rate`, … . In-circuit this is a CHAIN of Keccak-f tables where
//       block b+1's `state_in` is bound to block b's `state_out` by the `sha3_join`
//       push/pull channel primitive (same mechanism M2b-4 uses to bind a parent
//       gadget's input lanes to a child gadget's output digest — see sha3_join.rs).
//   (3) REJECTION SAMPLING — the squeezed byte-stream is chunked into 3-byte triples;
//       each triple → a 23-bit value z = CoeffFromThreeBytes(b0,b1,b2); z is ACCEPTED
//       iff z < q. The first 256 accepted z's are the polynomial â. This is the
//       genuinely new soundness object; its `z < q` decision reuses S0's carry-out
//       trick verbatim (`crate::nonnative`), and its variable-rate consumption is
//       bound by a hint-and-verify layout (see the SOUNDNESS BOUNDARY below).
//
// ── REUSE (no reinvented primitives) ──────────────────────────────────────────────
//   * `binius_m3 ...::keccak::Keccakf`   — the permutation, already proven over B256.
//   * `crate::sha3_variants`             — field-agnostic u64-lane sponge helpers;
//                                          extended here by `ShakeVariant`.
//   * `crate::sha3_join`                 — the push/pull channel that binds
//                                          state_out(block b) == state_in(block b+1).
//   * `crate::nonnative`                 — S0's `z < q` carry decision for rejection.
//
// ── SOUNDNESS BOUNDARY (READ THIS) ────────────────────────────────────────────────
// This module is developed in slices; each in-circuit binding is stated explicitly.
//
//   IN-CIRCUIT (constrained), delivered here / next:
//     * state_out = Keccak-f(state_in) for every squeeze block  — from Keccakf (done).
//     * state_in(block b+1) == state_out(block b)               — from sha3_join push/
//       pull (the XOF chain binding; S1b prove-path).
//     * For each 3-byte triple: z is the correct CoeffFromThreeBytes of the three
//       squeezed bytes (top bit of b2 masked), and accept_bit == (z < q)  — via S0's
//       carry-out of `z + (2^W − q)` (S1b rejection gadget).
//     * The accepted z's, IN ORDER, equal â[0..256]; exactly 256 are taken; the block
//       count is the minimum that yields 256 accepts (no early stop / padding)  —
//       hint-and-verify ordering layer (S1b rejection gadget).
//
//   WITNESS-SIDE (gated vs the `sha3` crate + NIST KATs, not yet an in-circuit
//   boundary): that the FIRST block's `state_in` is the FIPS-202/SHAKE padding of the
//   specific seed ρ‖s‖r. Binding the absorbed message in-circuit is the padding-
//   binding work (sha3_join's msg_bind path, reused from M2b) — wired in S1d when the
//   whole verify is assembled and ρ becomes a public boundary column.
//
//   OUTER COMMITMENT IS STILL SHA-256 (FIPS 180-4); the 2^256 challenge field carries
//   the FS/sumcheck/FRI soundness at NIST L1/L3, exactly as in b256_sha3.
// ============================================================================
//
// DRAFT STATUS (S1b, in progress): the NATIVE reference (SHAKE XOF, CoeffFromThreeBytes,
// RejNTTPoly, ExpandA) and the witness-generation helpers (squeeze-block chain, the
// rejection stream) are COMPLETE and gated against the `sha3` crate + NIST SHAKE KATs.
// The in-circuit prove path (multi-block squeeze over B256 via `sha3_join`, then the
// rejection gadget over S0) is specified below and wired next, once the S1a `full_256`
// proof frees the shared build target. The heavy prove gates are `#[ignore]` until then.

use sha3::digest::{ExtendableOutput, Update, XofReader};
use sha3::{Shake128, Shake256};

/// ML-DSA / Dilithium prime.  q = 2^23 − 2^13 + 1.
pub const Q: u32 = 8_380_417;

/// The two ML-DSA SHAKE XOFs. Both are FIPS-202 sponges with domain-pad byte 0x1F
/// (vs 0x06 for the fixed SHA3 digests); they differ only in the sponge rate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ShakeVariant {
	/// SHAKE-128: rate r = 1344 bits = 168 bytes = 21 lanes. Used by ExpandA.
	Shake128,
	/// SHAKE-256: rate r = 1088 bits = 136 bytes = 17 lanes. Used by ExpandS/Mask,
	/// SampleInBall, and the μ / c̃' message hashes.
	Shake256,
}

impl ShakeVariant {
	/// Sponge rate in bytes (r/8).
	pub const fn rate_bytes(self) -> usize {
		match self {
			ShakeVariant::Shake128 => 168,
			ShakeVariant::Shake256 => 136,
		}
	}

	/// Sponge rate in 64-bit lanes (rate_bytes / 8): 21 for SHAKE-128, 17 for SHAKE-256.
	pub const fn rate_lanes(self) -> usize {
		self.rate_bytes() / 8
	}

	/// FIPS-202 domain-separation + pad10*1 first byte for a SHAKE XOF.
	pub const fn pad_byte(self) -> u8 {
		0x1F
	}

	pub const fn name(self) -> &'static str {
		match self {
			ShakeVariant::Shake128 => "SHAKE-128",
			ShakeVariant::Shake256 => "SHAKE-256",
		}
	}
}

// ──────────────────────────────────────────────────────────────────────────────────
//  NATIVE REFERENCE (independent of any circuit)
// ──────────────────────────────────────────────────────────────────────────────────

/// SHAKE-128 XOF of `input`, `outlen` output bytes, via the `sha3` crate. This is the
/// independent oracle the in-circuit multi-block squeeze is gated against.
pub fn shake128_xof(input: &[u8], outlen: usize) -> Vec<u8> {
	let mut h = Shake128::default();
	h.update(input);
	let mut reader = h.finalize_xof();
	let mut out = vec![0u8; outlen];
	reader.read(&mut out);
	out
}

/// SHAKE-256 XOF of `input`, `outlen` output bytes, via the `sha3` crate.
pub fn shake256_xof(input: &[u8], outlen: usize) -> Vec<u8> {
	let mut h = Shake256::default();
	h.update(input);
	let mut reader = h.finalize_xof();
	let mut out = vec![0u8; outlen];
	reader.read(&mut out);
	out
}

/// FIPS 204 Algorithm 14 — CoeffFromThreeBytes. Interpret three squeezed bytes as a
/// little-endian 23-bit integer (the top bit of b2 is masked to 0). Returns `Some(z)`
/// iff z < q (ACCEPT), else `None` (REJECT). This IS the rejection predicate ExpandA
/// applies; in-circuit the `z < q` half reuses S0's carry-out decision.
pub fn coeff_from_three_bytes(b0: u8, b1: u8, b2: u8) -> Option<u32> {
	let z = (b0 as u32) | ((b1 as u32) << 8) | (((b2 & 0x7F) as u32) << 16);
	if z < Q {
		Some(z)
	} else {
		None
	}
}

/// The number of squeeze blocks a SHAKE-128 rejection sample consumes to reach `n`
/// accepted coefficients from `seed`. This is what the in-circuit block-count binding
/// must reproduce (the chain length is data-dependent but publicly recomputable from
/// the accept pattern, so it is bindable). Deterministic in the seed.
pub fn rej_ntt_poly_block_count(seed: &[u8], n: usize) -> usize {
	let rate = ShakeVariant::Shake128.rate_bytes();
	let mut h = Shake128::default();
	h.update(seed);
	let mut reader = h.finalize_xof();

	let mut got = 0usize;
	let mut blocks = 0usize;
	let mut buf = vec![0u8; rate];
	let mut off = rate; // force a block read on first iteration
	while got < n {
		if off + 3 > rate {
			// Refill: SHAKE consumes whole rate-blocks; a triple never straddles a
			// block boundary because rate (168) is a multiple of 3? 168 = 56*3, yes —
			// so SHAKE-128 triples align to blocks. (SHAKE-256 rate 136 is NOT a
			// multiple of 3; ExpandA only uses SHAKE-128, so alignment holds here.)
			reader.read(&mut buf);
			blocks += 1;
			off = 0;
		}
		let z = coeff_from_three_bytes(buf[off], buf[off + 1], buf[off + 2]);
		off += 3;
		if z.is_some() {
			got += 1;
		}
	}
	blocks
}

/// FIPS 204 Algorithm 30 — RejNTTPoly. Absorb `seed` into SHAKE-128 and rejection-
/// sample 256 coefficients in [0, q). Output is already in the NTT domain (â). This is
/// the reference the ExpandA circuit's per-cell output is gated against.
pub fn rej_ntt_poly(seed: &[u8]) -> [u32; 256] {
	let rate = ShakeVariant::Shake128.rate_bytes();
	let mut h = Shake128::default();
	h.update(seed);
	let mut reader = h.finalize_xof();

	let mut a = [0u32; 256];
	let mut j = 0usize;
	let mut buf = vec![0u8; rate];
	let mut off = rate;
	while j < 256 {
		if off + 3 > rate {
			reader.read(&mut buf);
			off = 0;
		}
		if let Some(z) = coeff_from_three_bytes(buf[off], buf[off + 1], buf[off + 2]) {
			a[j] = z;
			j += 1;
		}
		off += 3;
	}
	a
}

/// FIPS 204 Algorithm 32 — ExpandA. Build the public matrix Â ∈ (T_q)^{k×l} from the
/// 32-byte seed ρ. Cell (r, s) is `RejNTTPoly(ρ ‖ IntegerToBytes(s,1) ‖ IntegerToBytes(r,1))`.
/// Row-major: `a[r][s]`. (k,l) are the ML-DSA parameter-set dimensions.
pub fn expand_a_ref(rho: &[u8; 32], k: usize, l: usize) -> Vec<Vec<[u32; 256]>> {
	let mut a = Vec::with_capacity(k);
	for r in 0..k {
		let mut row = Vec::with_capacity(l);
		for s in 0..l {
			let mut seed = Vec::with_capacity(34);
			seed.extend_from_slice(rho);
			seed.push(s as u8); // column index first (low byte)
			seed.push(r as u8); // row index second
			row.push(rej_ntt_poly(&seed));
		}
		a.push(row);
	}
	a
}

/// ML-DSA parameter-set matrix dimensions (k rows, l cols).
pub const fn dims(param: MlDsaParam) -> (usize, usize) {
	match param {
		MlDsaParam::MlDsa44 => (4, 4),
		MlDsaParam::MlDsa65 => (6, 5),
		MlDsaParam::MlDsa87 => (8, 7),
	}
}

/// Number of ±1 coefficients in the SampleInBall challenge c (its Hamming weight).
/// FIPS 204 Table 1: ML-DSA-44 τ=39, ML-DSA-65 τ=49, ML-DSA-87 τ=60.
pub const fn tau(param: MlDsaParam) -> usize {
	match param {
		MlDsaParam::MlDsa44 => 39,
		MlDsaParam::MlDsa65 => 49,
		MlDsaParam::MlDsa87 => 60,
	}
}

/// Length in bytes of the challenge seed c̃ = λ/4 bytes (2λ bits).
/// ML-DSA-44 λ=128 → 32 B; ML-DSA-65 λ=192 → 48 B; ML-DSA-87 λ=256 → 64 B.
pub const fn c_tilde_bytes(param: MlDsaParam) -> usize {
	match param {
		MlDsaParam::MlDsa44 => 32,
		MlDsaParam::MlDsa65 => 48,
		MlDsaParam::MlDsa87 => 64,
	}
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MlDsaParam {
	MlDsa44,
	MlDsa65,
	MlDsa87,
}

// ──────────────────────────────────────────────────────────────────────────────────
//  S1c — SampleInBall (FIPS 204 Algorithm 29), native reference
// ──────────────────────────────────────────────────────────────────────────────────

/// FIPS 204 Algorithm 29 — SampleInBall. Absorb the challenge seed c̃ into SHAKE-256,
/// take the first 8 squeezed bytes as 64 sign bits, then run a rejection-sampled
/// Fisher–Yates placement over i ∈ [256−τ, 256): for each i, squeeze bytes until one is
/// `j ≤ i`, set c[i] ← c[j] and c[j] ← (−1)^{sign_bit[i+τ−256]}. The result has EXACTLY
/// τ nonzero coefficients, each ±1. Coefficients are returned as `i8` in {−1,0,1}.
///
/// This is the reference the SampleInBall circuit's output is gated against; in-circuit,
/// the `j ≤ i` acceptance reuses a carry-out decision (S0's `< m` trick, bound = i+1),
/// and the array evolution is a read/write-consistent permutation trace (S1c gadget).
pub fn sample_in_ball(c_tilde: &[u8], tau: usize) -> [i8; 256] {
	assert!(tau <= 64, "τ must be ≤ 64 (only the first 8 squeeze bytes carry sign bits)");
	let mut c = [0i8; 256];

	let mut h = Shake256::default();
	h.update(c_tilde);
	let mut reader = h.finalize_xof();

	// First 8 bytes → 64 sign bits (LSB-first within each byte, FIPS 202 BytesToBits).
	let mut sign = [0u8; 8];
	reader.read(&mut sign);
	let sign_bit = |k: usize| -> i8 {
		let bit = (sign[k / 8] >> (k % 8)) & 1;
		if bit == 1 {
			-1
		} else {
			1
		}
	};

	// Fisher–Yates with rejection: place τ signs at shuffled positions.
	let mut one = [0u8; 1];
	for i in (256 - tau)..256 {
		// squeeze bytes until j ≤ i
		let j = loop {
			reader.read(&mut one);
			let j = one[0] as usize;
			if j <= i {
				break j;
			}
		};
		c[i] = c[j];
		c[j] = sign_bit(i + tau - 256);
	}
	c
}

/// The number of single-byte squeezes SampleInBall consumes AFTER the initial 8 sign
/// bytes (i.e. the count of Fisher–Yates draws incl. rejected ones). The in-circuit
/// squeeze-chain length binding must reproduce this; deterministic in (c̃, τ).
pub fn sample_in_ball_draw_count(c_tilde: &[u8], tau: usize) -> usize {
	let mut h = Shake256::default();
	h.update(c_tilde);
	let mut reader = h.finalize_xof();
	let mut sign = [0u8; 8];
	reader.read(&mut sign);

	let mut draws = 0usize;
	let mut one = [0u8; 1];
	for i in (256 - tau)..256 {
		loop {
			reader.read(&mut one);
			draws += 1;
			if (one[0] as usize) <= i {
				break;
			}
		}
	}
	draws
}

// ──────────────────────────────────────────────────────────────────────────────────
//  IN-CIRCUIT PROVE PATH  (design; wired next — see DRAFT STATUS)
// ──────────────────────────────────────────────────────────────────────────────────
//
// prove_verify_shake_xof_b256(variant, input, outlen, log_inv_rate, security_bits)
//   1. Absorb: one Keccakf table; state_in = shake_padded(variant, input) (single
//      block for |input| < rate; ExpandA seeds are 34 B < 168). Squeeze block 0 =
//      first `rate_lanes` lanes of that table's state (per FIPS-202, the absorb output
//      state's rate lanes ARE the first squeeze block — no extra permutation before
//      the first read).  state_out = Keccak-f(state_in) feeds block 1.
//   2. Chain: for b = 1 .. ceil(outlen/rate): a Keccakf table whose state_in is bound
//      to the previous table's state_out by a per-chain `join` channel — push
//      state_out(b-1) lanes 0..24, pull them as state_in(b). Squeeze block b = state
//      lanes 0..rate_lanes of table b.  (Reuses sha3_join::{push,pull} lane groups.)
//   3. Serialize the squeezed lanes little-endian → outlen bytes; gate == shake_xof.
//
// prove_verify_expand_a_cell_b256(seed, log_inv_rate, security_bits)
//   = the squeeze chain above (SHAKE-128) + a REJECTION table:
//     • triples[t] = (b0,b1,b2) read from the squeeze byte-stream (bound to the chain
//       lanes by column equality, same as digest read-back in b256_sha3);
//     • z[t] = b0 + (b1<<8) + ((b2 & 0x7F)<<16)   — a linear B1 recombination; masking
//       b2's top bit is FREE (that bit's column is simply not wired into z);
//     • accept[t] ∈ {0,1} = 1 − carry_out(z[t] + (2^32 − q))   — S0's `r < m` carry, W=32
//       (z is 24-bit); accept is a B1 column, the complement of the sound carry-out (NOT an
//       m3 borrow, which is unconstrained). This is the load-bearing rejection predicate;
//     • idx[t] = idx[t−1] + accept[t]   — a running prefix-sum (≤ 256, a 9-bit adder), and
//       on accept the pair (idx[t]−1, z[t]) is EMITTED;
//     • PERMUTATION ARGUMENT (permutation_argument.rs, γ,α in F_ext): the emitted multiset
//       {(idx[t]−1, z[t]) : accept[t]=1} equals {(j, â[j]) : j∈[0,256)} — this binds the
//       accepted z's, in order, to â[0..256] with no drop/insert;
//     • termination: idx[T−1] == 256 (a boundary) and the last triple is an accept, so T is
//       exactly rej_ntt_poly_block_count worth of triples (no early stop, no padding).
//   â is then handed to S1a's NTT-domain arithmetic unchanged. (The native model
//   `rejection_gadget_ref` in tests computes exactly this and is gated == rej_ntt_poly.)
//
// SOUNDNESS of rejection: the accept bits are the sound carry decisions (accept ⟺ z<q);
// the prefix-sum is a constrained adder; the permutation argument (grand-product over
// F_ext) forces the emitted (rank, value) pairs to be exactly (0,â0)…(255,â255), so a
// prover cannot drop an accepted triple, smuggle a rejected one (z≥q ⇒ accept=0 ⇒ not
// emitted), or reorder. The block count binds the stream length. Union-bound over the ≤
// ~260 triples is ≤ 2^−λ at the B256 challenge field. (Full write-up in report.)
//
// prove_verify_sample_in_ball_b256(c_tilde, tau, log_inv_rate, security_bits)  [S1c]
//   = SHAKE-256 absorb(c̃) (single block, |c̃| ≤ 64 < 136) + the S1b squeeze chain, then
//     a FISHER–YATES table:
//     • the first 8 squeezed bytes → 64 sign bits (bit-decomposed B1 columns, free);
//     • for each i ∈ [256−τ, 256): the accepted draw byte j is bound to the squeeze
//       stream; `j ≤ i` is the accept decision — S0's carry-out of `j + (2^W − (i+1))`,
//       W=8, with i a PUBLIC per-row constant — and every rejected draw before it also
//       carries `j' > i` (so the prover cannot skip a valid-earlier byte);
//     • the array evolution c[i]←c[j], c[j]←±1 is a READ/WRITE-consistent trace bound by
//       OFFLINE MEMORY CHECKING (Spice/permutation style): the 256-slot array is a memory;
//       each op is a tuple (addr, value, timestamp). init write-set = {(a,0,0) : a<256};
//       per step i: READ c[j] (emit read-tuple with its last timestamp, re-emit a write
//       with a fresh timestamp), WRITE c[i]=that value, WRITE c[j]=(−1)^{sign[i+τ−256]}. A
//       grand-product permutation argument (γ,α in F_ext) forces read-set ∪ final-reads ==
//       write-set, so every read returns the last-written value — the array evolution is a
//       single consistent history and the final memory state IS the output c. A tampered
//       swap (wrong j, mis-placed sign, or an out-of-history read) breaks the multiset
//       equality. Weight-τ and coeffs∈{−1,0,1} fall out of the construction (τ ±1 writes).
//       (The native model `sample_in_ball_gadget_ref` in tests computes exactly this trace
//       and is gated == sample_in_ball across all three parameter sets.)
//   GATES: in-circuit c == sample_in_ball(c̃,τ); Hamming weight == τ and coeffs ∈{−1,0,1}
//   fall out of the trace; a tampered draw (a j>i smuggled as accepted, or a mis-placed
//   sign) is REJECTED (the carry decision / perm-argument fails). Union-bound over the
//   ≤ ~τ+O(1) draws ≤ 2^−λ at B256.
//
// SampleInBall feeds S1a: c is lifted to the NTT domain (ĉ = NTT(c)) and multiplied by
// t1·2^d there; and c̃' = H(μ ‖ w1Encode(w1)) is a SHAKE-256 hash whose equality to c̃
// closes the verify (S1d).

#[cfg(test)]
mod tests {
	use super::*;

	// ── NIST FIPS-202 SHAKE known-answer vectors (empty message). ──
	// SHAKE128("", 32 bytes) and SHAKE256("", 32 bytes), from the NIST XOF KATs.
	const SHAKE128_EMPTY_32: &str =
		"7f9c2ba4e88f827d616045507605853ed73b8093f6efbc88eb1a6eacfa66ef26";
	const SHAKE256_EMPTY_32: &str =
		"46b9dd2b0ba88d13233b3feb743eeb243fcd52ea62b81b82b50c27646ed5762f";

	fn hex(s: &str) -> Vec<u8> {
		(0..s.len())
			.step_by(2)
			.map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
			.collect()
	}

	/// Build the padded single-block absorb state for a SHAKE XOF over a short seed
	/// (|seed| ≤ rate−1; ExpandA/SampleInBall seeds are ≤ 64 B < both rates). Lane i =
	/// bytes[8i..8i+8] little-endian; domain-pad `0x1F` at byte |seed|, `0x80` at byte
	/// rate−1, capacity zero. This is the state fed to the FIRST Keccak-f (absorb).
	fn shake_padded_state(variant: ShakeVariant, seed: &[u8]) -> [u64; 25] {
		let rate = variant.rate_bytes();
		assert!(seed.len() <= rate - 1, "single-block absorb only");
		let mut buf = [0u8; 200];
		buf[..seed.len()].copy_from_slice(seed);
		buf[seed.len()] ^= variant.pad_byte(); // 0x1F
		buf[rate - 1] ^= 0x80; // pad10*1 closing bit
		let mut lanes = [0u64; 25];
		for (i, lane) in lanes.iter_mut().enumerate() {
			*lane = u64::from_le_bytes(buf[i * 8..i * 8 + 8].try_into().unwrap());
		}
		lanes
	}

	/// The EXACT witness the in-circuit multi-block squeeze reproduces: absorb-permute, then
	/// per block emit the first `rate_lanes` lanes (little-endian) and apply Keccak-f for the
	/// next block. In-circuit this is one `Keccakf` table per block with state_out(b) bound
	/// to state_in(b+1) by the sha3_join channel; here `tiny_keccak::keccakf` is the
	/// permutation oracle (the same one b256_keccak gates the gadget against).
	fn shake_squeeze_blocks(variant: ShakeVariant, seed: &[u8], n_blocks: usize) -> Vec<u8> {
		let rate_lanes = variant.rate_lanes();
		let mut state = shake_padded_state(variant, seed);
		tiny_keccak::keccakf(&mut state); // absorb permutation → state_0
		let mut out = Vec::with_capacity(n_blocks * variant.rate_bytes());
		for b in 0..n_blocks {
			if b > 0 {
				tiny_keccak::keccakf(&mut state);
			}
			for lane in state.iter().take(rate_lanes) {
				out.extend_from_slice(&lane.to_le_bytes());
			}
		}
		out
	}

	/// GATE ref-6 (S1b squeeze chain) — the explicit padded-state → Keccak-f → lane-extract
	/// block chain equals the `sha3`-crate XOF byte-for-byte (SHAKE-128 AND SHAKE-256, 5
	/// blocks), AND end-to-end: rejection-sampling the chain stream yields exactly the same
	/// â as `rej_ntt_poly` (the whole S1b native pipeline: squeeze → reject → 256 coeffs).
	#[test]
	fn shake_squeeze_chain_matches_xof_and_feeds_expand_a() {
		let seed = [7u8; 34]; // ExpandA-sized seed
		for variant in [ShakeVariant::Shake128, ShakeVariant::Shake256] {
			let nb = 5;
			let chain = shake_squeeze_blocks(variant, &seed, nb);
			let xof = match variant {
				ShakeVariant::Shake128 => shake128_xof(&seed, nb * variant.rate_bytes()),
				ShakeVariant::Shake256 => shake256_xof(&seed, nb * variant.rate_bytes()),
			};
			assert_eq!(chain, xof, "{} squeeze chain != sha3 XOF", variant.name());
		}

		// End-to-end: the chain feeds ExpandA's rejection sampler. rate 168 = 56·3 so
		// SHAKE-128 triples align to blocks; consume exactly the block count RejNTTPoly needs.
		let seed = b"S1b-expandA-cell-seed-example-01";
		let nb = rej_ntt_poly_block_count(seed, 256);
		let stream = shake_squeeze_blocks(ShakeVariant::Shake128, seed, nb);
		let mut a = [0u32; 256];
		let mut j = 0usize;
		let mut off = 0usize;
		while j < 256 {
			if let Some(z) = coeff_from_three_bytes(stream[off], stream[off + 1], stream[off + 2]) {
				a[j] = z;
				j += 1;
			}
			off += 3;
		}
		assert_eq!(a, rej_ntt_poly(seed), "chain → rejection sample != rej_ntt_poly");
		println!("GATE ref-6: SHAKE-128/256 squeeze chain == sha3 XOF; chain→rejection == rej_ntt_poly");
	}

	/// The circuit's ACCEPT decision, computed the S0 way: z < q iff the carry-out of the
	/// W=32 addition `z + (2^32 − q)` is 0 (S0's `r < m` trick — the carry, NOT an
	/// unconstrained borrow, is the sound decision). z is a 24-bit value so no u64 overflow.
	fn rej_accept_via_carry(z: u32) -> bool {
		let two_pow_w_minus_q = (1u64 << 32) - Q as u64;
		((z as u64 + two_pow_w_minus_q) >> 32) == 0
	}

	/// Native model of the in-circuit ExpandA REJECTION gadget, mirroring it lane-for-lane:
	///   • z[t] = b0 ∣ b1<<8 ∣ (b2 & 0x7F)<<16   — linear B1 reconstruction; masking b2's top
	///     bit is FREE (that bit's column is simply not wired into z).
	///   • accept[t] = (carry-out of z[t] + (2^32 − q)) == 0   — S0's carry decision.
	///   • idx[t] = idx[t−1] + accept[t]   — a running prefix-sum (≤ 256, a 9-bit adder);
	///     on accept, â[idx−1] = z[t]  (the placement bound in-circuit by a permutation
	///     argument: {(idx[t]−1, z[t]) : accept[t]} == {(j, â[j]) : j∈[0,256)}).
	///   • termination: idx reaches 256 exactly at the last consumed triple.
	/// Validated against `rej_ntt_poly` (which uses the sha3 crate) so the AIR's witness
	/// generation and the carry/prefix-sum arithmetic are proven correct.
	fn rejection_gadget_ref(stream: &[u8]) -> [u32; 256] {
		let mut a = [0u32; 256];
		let mut idx = 0usize; // prefix sum of accept bits
		let mut off = 0usize;
		while idx < 256 {
			let z = (stream[off] as u32)
				| ((stream[off + 1] as u32) << 8)
				| (((stream[off + 2] & 0x7F) as u32) << 16);
			if rej_accept_via_carry(z) {
				a[idx] = z; // placement â[idx] = z
				idx += 1;
			}
			off += 3;
		}
		a
	}

	/// GATE ref-7 (S1b rejection gadget over S0) — (a) the S0 carry-out accept decision
	/// equals `z < q` across the boundary and the full 23-bit span; (b) the rejection
	/// gadget (carry accept + prefix-sum placement) over the real squeeze stream reproduces
	/// `rej_ntt_poly` exactly, for a plain seed AND a real ExpandA seed ρ‖s‖r.
	#[test]
	fn expand_a_rejection_gadget_over_s0() {
		// (a) accept-via-carry == (z < q)
		assert!(rej_accept_via_carry(0), "0 must accept");
		assert!(rej_accept_via_carry(Q - 1), "q−1 must accept");
		assert!(!rej_accept_via_carry(Q), "q must reject");
		assert!(!rej_accept_via_carry((1 << 23) - 1), "max 23-bit (≥q) must reject");
		for z in (0..(1u32 << 23)).step_by(9973) {
			assert_eq!(rej_accept_via_carry(z), z < Q, "carry accept != (z<q) at z={z}");
		}

		// (b) gadget over the real chain == rej_ntt_poly, plain seed
		let seed = b"S1b-expandA-cell-seed-example-01";
		let nb = rej_ntt_poly_block_count(seed, 256);
		let stream = shake_squeeze_blocks(ShakeVariant::Shake128, seed, nb);
		assert_eq!(rejection_gadget_ref(&stream), rej_ntt_poly(seed), "gadget != rej_ntt_poly");

		// (b') a real ExpandA cell ρ‖s‖r (ρ=[3;32], s=2, r=1)
		let mut a_seed = vec![3u8; 32];
		a_seed.push(2); // column s
		a_seed.push(1); // row r
		let nb2 = rej_ntt_poly_block_count(&a_seed, 256);
		let stream2 = shake_squeeze_blocks(ShakeVariant::Shake128, &a_seed, nb2);
		let cell = rejection_gadget_ref(&stream2);
		assert_eq!(cell, rej_ntt_poly(&a_seed), "ExpandA cell gadget != rej_ntt_poly");
		assert_eq!(cell, expand_a_ref(&[3u8; 32], 4, 4)[1][2], "cell != ExpandA(ρ)[r=1][s=2]");
		assert!(cell.iter().all(|&c| c < Q), "gadget produced a coeff ≥ q");
		println!("GATE ref-7: S0 carry accept == z<q; rejection gadget == rej_ntt_poly == ExpandA cell");
	}

	/// GATE ref-1 — the native SHAKE reference matches the NIST XOF KATs and is
	/// self-consistent with the `sha3` crate at several output lengths.
	#[test]
	fn shake_reference_matches_nist_kat() {
		assert_eq!(shake128_xof(b"", 32), hex(SHAKE128_EMPTY_32), "SHAKE128(\"\") != NIST KAT");
		assert_eq!(shake256_xof(b"", 32), hex(SHAKE256_EMPTY_32), "SHAKE256(\"\") != NIST KAT");
		// A longer squeeze must be a prefix-extension of a shorter one (XOF property).
		let long = shake128_xof(b"abc", 200);
		let short = shake128_xof(b"abc", 64);
		assert_eq!(&long[..64], &short[..], "SHAKE128 is not prefix-consistent across outlen");
		println!("GATE ref-1: SHAKE-128/256 reference == NIST XOF KATs and prefix-consistent");
	}

	/// GATE ref-2 — CoeffFromThreeBytes: the accept predicate is exactly `z < q`, the
	/// top bit of b2 is masked, and the boundary values are classified correctly.
	#[test]
	fn coeff_from_three_bytes_boundary() {
		// z = 0 accepted.
		assert_eq!(coeff_from_three_bytes(0, 0, 0), Some(0));
		// q-1 accepted, q rejected. q = 0x7FE001.
		let qm1 = Q - 1;
		let (a0, a1, a2) = ((qm1 & 0xFF) as u8, ((qm1 >> 8) & 0xFF) as u8, ((qm1 >> 16) & 0xFF) as u8);
		assert_eq!(coeff_from_three_bytes(a0, a1, a2), Some(qm1), "q-1 must be accepted");
		let (b0, b1, b2) = ((Q & 0xFF) as u8, ((Q >> 8) & 0xFF) as u8, ((Q >> 16) & 0xFF) as u8);
		assert_eq!(coeff_from_three_bytes(b0, b1, b2), None, "q must be rejected");
		// Top bit of b2 is masked: 0xFF -> 0x7F, so max z = 0x7FFFFF = 8388607 >= q -> reject.
		assert_eq!(coeff_from_three_bytes(0xFF, 0xFF, 0xFF), None);
		// but 0xFF,0xFF,0x80 masks to 0x00FFFF < q -> accept.
		assert_eq!(coeff_from_three_bytes(0xFF, 0xFF, 0x80), Some(0x00FFFF));
		println!("GATE ref-2: CoeffFromThreeBytes accept ⟺ z<q, top-bit masked, boundaries correct");
	}

	/// GATE ref-3 — RejNTTPoly produces 256 coefficients all in [0,q), deterministic in
	/// the seed, and the block-count helper agrees with the actual squeeze consumption.
	#[test]
	fn rej_ntt_poly_wellformed_and_deterministic() {
		let seed = b"S1b-expandA-cell-seed-example-01";
		let a = rej_ntt_poly(seed);
		assert!(a.iter().all(|&c| c < Q), "RejNTTPoly produced a coeff >= q");
		let a2 = rej_ntt_poly(seed);
		assert_eq!(a, a2, "RejNTTPoly must be deterministic in the seed");
		let blocks = rej_ntt_poly_block_count(seed, 256);
		assert!(blocks >= 5, "expected >= 5 SHAKE-128 blocks to fill 256 coeffs (got {blocks})");
		println!("GATE ref-3: RejNTTPoly → 256 coeffs < q, deterministic; block-count = {blocks}");
	}

	/// GATE ref-4 — ExpandA: the matrix is k×l, every coefficient < q, every cell equals
	/// its own RejNTTPoly(ρ‖s‖r), and distinct cells differ (distinct seeds).
	#[test]
	fn expand_a_wellformed() {
		let rho = [7u8; 32];
		let (k, l) = dims(MlDsaParam::MlDsa44);
		let a = expand_a_ref(&rho, k, l);
		assert_eq!(a.len(), k);
		for (r, row) in a.iter().enumerate() {
			assert_eq!(row.len(), l);
			for (s, cell) in row.iter().enumerate() {
				assert!(cell.iter().all(|&c| c < Q), "A[{r}][{s}] has a coeff >= q");
				let mut seed = rho.to_vec();
				seed.push(s as u8);
				seed.push(r as u8);
				assert_eq!(*cell, rej_ntt_poly(&seed), "A[{r}][{s}] != RejNTTPoly(ρ‖s‖r)");
			}
		}
		// Two different cells should (whp) differ.
		assert_ne!(a[0][0], a[1][0], "distinct ExpandA cells collided");
		println!("GATE ref-4: ExpandA(ρ) is {k}×{l}, all coeffs < q, each cell == RejNTTPoly(ρ‖s‖r)");
	}

	/// GATE ref-5 (S1c) — SampleInBall: the challenge has EXACTLY τ nonzero coefficients,
	/// each ∈ {−1,+1}, the rest 0; it is deterministic in c̃; and distinct seeds differ.
	/// Checked across all three parameter sets' (τ, |c̃|).
	#[test]
	fn sample_in_ball_wellformed() {
		for param in [MlDsaParam::MlDsa44, MlDsaParam::MlDsa65, MlDsaParam::MlDsa87] {
			let t = tau(param);
			let clen = c_tilde_bytes(param);
			let c_tilde: Vec<u8> = (0..clen).map(|i| (i as u8).wrapping_mul(31).wrapping_add(1)).collect();
			let c = sample_in_ball(&c_tilde, t);

			assert!(c.iter().all(|&x| x == -1 || x == 0 || x == 1), "{param:?}: coeff not in {{-1,0,1}}");
			let weight = c.iter().filter(|&&x| x != 0).count();
			assert_eq!(weight, t, "{param:?}: Hamming weight {weight} != τ {t}");

			let c2 = sample_in_ball(&c_tilde, t);
			assert_eq!(c, c2, "{param:?}: SampleInBall not deterministic in c̃");

			// A one-byte change in c̃ should (whp) change the challenge.
			let mut c_tilde_b = c_tilde.clone();
			c_tilde_b[0] ^= 0xFF;
			assert_ne!(c, sample_in_ball(&c_tilde_b, t), "{param:?}: distinct c̃ collided");

			let draws = sample_in_ball_draw_count(&c_tilde, t);
			assert!(draws >= t, "{param:?}: draw count {draws} < τ {t} (impossible)");
			println!("GATE ref-5: {param:?} SampleInBall weight=={t}, coeffs∈{{-1,0,1}}, draws={draws}");
		}
	}

	/// The Fisher–Yates ACCEPT decision computed the S0 way: `j ≤ i` iff the carry-out of
	/// the W=8 addition `j + (2^8 − (i+1))` is 0. `i` is a PUBLIC per-step bound (256−τ…255),
	/// so `2^8 − (i+1)` is a constant column; j is the drawn byte. u16 avoids the u8 overflow.
	fn sib_accept_via_carry(j: u8, i: usize) -> bool {
		let tpwm = 256u16 - (i as u16 + 1); // 2^8 − (i+1)
		((j as u16 + tpwm) >> 8) == 0
	}

	/// Native model of the in-circuit SampleInBall FISHER–YATES gadget, mirroring it
	/// lane-for-lane: the first 8 stream bytes give 64 sign bits; for each i ∈ [256−τ, 256)
	/// the accepted draw j is the first stream byte with `sib_accept_via_carry(j, i)` (every
	/// rejected draw before it carries j>i), then c[i] ← c[j] and c[j] ← (−1)^{sign[i+τ−256]}.
	/// The array evolution is a read/write memory trace bound in-circuit by a permutation
	/// argument. Validated == `sample_in_ball`.
	fn sample_in_ball_gadget_ref(stream: &[u8], tau: usize) -> [i8; 256] {
		let mut c = [0i8; 256];
		let sign = &stream[0..8];
		let sign_bit = |k: usize| -> i8 {
			if (sign[k / 8] >> (k % 8)) & 1 == 1 {
				-1
			} else {
				1
			}
		};
		let mut pos = 8usize;
		for i in (256 - tau)..256 {
			let j = loop {
				let jb = stream[pos];
				pos += 1;
				if sib_accept_via_carry(jb, i) {
					break jb as usize;
				}
			};
			c[i] = c[j];
			c[j] = sign_bit(i + tau - 256);
		}
		c
	}

	/// GATE ref-8 (S1c Fisher–Yates gadget over S0) — (a) the S0 carry accept equals `j ≤ i`
	/// for ALL (i, j) ∈ [0,256)²; (b) the gadget (carry accept + array-swap trace) over the
	/// real SHAKE-256 stream reproduces `sample_in_ball` for all three parameter sets, with
	/// Hamming weight exactly τ.
	#[test]
	fn sample_in_ball_fisher_yates_over_s0() {
		// (a) carry accept == (j ≤ i) exhaustively
		for i in 0..256usize {
			for j in 0..256usize {
				assert_eq!(sib_accept_via_carry(j as u8, i), j <= i, "carry != (j≤i) at i={i} j={j}");
			}
		}

		// (b) gadget over the real SHAKE-256 squeeze stream == sample_in_ball, all param sets
		let rate = ShakeVariant::Shake256.rate_bytes();
		for param in [MlDsaParam::MlDsa44, MlDsaParam::MlDsa65, MlDsaParam::MlDsa87] {
			let t = tau(param);
			let clen = c_tilde_bytes(param);
			let c_tilde: Vec<u8> =
				(0..clen).map(|i| (i as u8).wrapping_mul(31).wrapping_add(1)).collect();
			let draws = sample_in_ball_draw_count(&c_tilde, t);
			let nblocks = (8 + draws).div_ceil(rate) + 1; // enough bytes (+margin)
			let stream = shake_squeeze_blocks(ShakeVariant::Shake256, &c_tilde, nblocks);
			let c = sample_in_ball_gadget_ref(&stream, t);
			assert_eq!(c, sample_in_ball(&c_tilde, t), "{param:?}: gadget != sample_in_ball");
			assert_eq!(c.iter().filter(|&&x| x != 0).count(), t, "{param:?}: weight != τ");
		}
		println!("GATE ref-8: j≤i carry accept exhaustive; Fisher–Yates gadget == sample_in_ball, weight τ");
	}

	/// The witness the in-circuit ML-DSA MESSAGE hashes reproduce: SHAKE-256 as a hash with
	/// MULTI-BLOCK ABSORB (μ = SHAKE-256(tr ‖ M') and c̃' = SHAKE-256(μ ‖ w1Encode) — the
	/// message can span many rate-blocks, unlike ExpandA's single-block seed). Each absorb
	/// block XORs the message rate-lanes into the state and permutes; then the fixed-length
	/// output is squeezed. In-circuit this is a chain of Keccakf tables where block b's input
	/// state = (block b−1's output state) ⊕ (message block b), bound by the sha3_join seam.
	fn shake256_hash_ref(input: &[u8], out_len: usize) -> Vec<u8> {
		let rate = ShakeVariant::Shake256.rate_bytes(); // 136
		let rate_lanes = rate / 8; // 17
		let mut padded = input.to_vec();
		padded.push(0x1F);
		while padded.len() % rate != 0 {
			padded.push(0);
		}
		let last = padded.len() - 1;
		padded[last] |= 0x80;

		let mut state = [0u64; 25];
		for block in padded.chunks(rate) {
			for i in 0..rate_lanes {
				state[i] ^= u64::from_le_bytes(block[i * 8..i * 8 + 8].try_into().unwrap());
			}
			tiny_keccak::keccakf(&mut state);
		}
		let mut out = Vec::with_capacity(out_len + 8);
		while out.len() < out_len {
			for lane in state.iter().take(rate_lanes) {
				out.extend_from_slice(&lane.to_le_bytes());
			}
			if out.len() < out_len {
				tiny_keccak::keccakf(&mut state);
			}
		}
		out.truncate(out_len);
		out
	}

	/// GATE ref-9 (S1 SHAKE-256 message hash) — the multi-block-absorb SHAKE-256 (the witness
	/// for μ and c̃') equals the sha3-crate XOF for a MULTI-BLOCK μ input (tr‖M', 3 rate-blocks)
	/// and for the three c̃' output lengths (32/48/64), and still matches on a short single-block
	/// input.
	#[test]
	fn shake256_message_hash_multiblock() {
		// μ = SHAKE-256(tr ‖ M', 64) — 64 + 300 = 364 B = 3 rate-blocks (multi-block absorb)
		let mut input: Vec<u8> = (0..64u8).collect();
		input.extend(std::iter::repeat(0x5Au8).take(300));
		assert_eq!(shake256_hash_ref(&input, 64), shake256_xof(&input, 64), "μ multi-block absorb != XOF");
		// c̃' = SHAKE-256(μ ‖ w1Encode, {32,48,64}) for L1/L3/L5
		let x: Vec<u8> = (0..200u32).map(|i| i as u8).collect();
		for out_len in [32usize, 48, 64] {
			assert_eq!(shake256_hash_ref(&x, out_len), shake256_xof(&x, out_len), "c̃' len {out_len} != XOF");
		}
		// short single-block input still correct
		assert_eq!(shake256_hash_ref(b"abc", 32), shake256_xof(b"abc", 32), "single-block != XOF");
		println!("GATE ref-9: SHAKE-256 message hash (multi-block absorb + squeeze) == sha3 XOF for μ (tr‖M') and c̃' (32/48/64)");
	}

	// ── IN-CIRCUIT PROVE GATES (heavy; wired + un-ignored after S1a full_256 frees the
	//    shared target). Placeholders assert the design contract so the module's intent
	//    is documented as executable stubs until the prove path lands. ──

	// ── S1b PROVE PATH (Phase-3): SHAKE multi-block squeeze over B256, Keccak-f channel chain ──
	// The multi-block squeeze binds state_out(b) == state_in(b+1) across permutations. Rather
	// than an in-table `add_shifted` seam (wrong primitive for full-state cross-permutation
	// chaining), we use the sha3_join CHANNEL — the NIST-validated M2b mechanism: each block is
	// its OWN table that PUSHES its 25-lane output state (track-7) and PULLS its 25-lane input
	// state (track-0) on ONE shared channel. The channel balances as a multiset iff every pulled
	// input equals a pushed output, i.e. iff the chain state_out(b)==state_in(b+1) holds.
	use crate::b256_field::{B256TowerFamily, B256 as OurB256, U256};
	use binius_core::fiat_shamir::HasherChallenger;
	use binius_hash::sha2::Sha256Compression;
	use binius_m3::builder::{Col, ConstraintSystem, Statement, TableId, WitnessIndex, B1, B64};
	use binius_m3::gadgets::hash::keccak::{Keccakf, StateMatrix};
	use bumpalo::Bump;
	use sha2::Sha256;

	const SHAKE_LANE_BITS: usize = 512; // PackedLane8 = 8 tracks × 64 bits
	const SHAKE_LANE64_BITS: usize = 64; // one lane's track = 64 bits
	const SHAKE_IN_TRACK: usize = 0; // permutation input lives on track 0
	const SHAKE_OUT_TRACK: usize = 7; // permutation output lives on track 7

	type ShakeTbl<'a> = binius_m3::builder::TableBuilder<'a, OurB256>;
	type ShakeSeg<'a> = binius_m3::builder::TableWitnessSegment<'a, OurB256>;

	/// The full witness of the multi-block squeeze: the padded absorb state, then the running
	/// 25-lane state after each Keccak-f (block b's output). Mirrors `shake_squeeze_blocks`.
	fn shake_chain_states(variant: ShakeVariant, seed: &[u8], n_blocks: usize) -> Vec<StateMatrix<u64>> {
		let rate = variant.rate_bytes();
		let mut bytes = [0u8; 200];
		bytes[..seed.len()].copy_from_slice(seed);
		bytes[seed.len()] ^= variant.pad_byte();
		bytes[rate - 1] ^= 0x80;
		let mut lanes: [u64; 25] =
			std::array::from_fn(|i| u64::from_le_bytes(bytes[i * 8..i * 8 + 8].try_into().unwrap()));
		let mut states = Vec::with_capacity(n_blocks);
		for _ in 0..n_blocks {
			tiny_keccak::keccakf(&mut lanes); // state_b = Keccak-f(state_{b-1})
			states.push(StateMatrix::from_values(lanes));
		}
		states
	}

	/// Extract the 64-bit `track` block of all 25 lanes as `Col<B1,64>` projected virtual
	/// oracles, then pack each to a `Col<B64,1>` aliasing the same bits — the 25-tuple form
	/// pushed to / pulled from a channel. (25-lane analogue of b256_recursion's 4-lane helper.)
	fn track25_to_b64(
		table: &mut ShakeTbl<'_>,
		name: &str,
		lanes: &[Col<B1, SHAKE_LANE_BITS>],
		track: usize,
	) -> ([Col<B1, SHAKE_LANE64_BITS>; 25], [Col<B64, 1>; 25]) {
		let sel: [Col<B1, SHAKE_LANE64_BITS>; 25] = std::array::from_fn(|i| {
			table.add_selected_block::<B1, SHAKE_LANE_BITS, SHAKE_LANE64_BITS>(
				format!("{name}_sel[{i}]"),
				lanes[i],
				track,
			)
		});
		let b64: [Col<B64, 1>; 25] = std::array::from_fn(|i| {
			table.add_packed::<B1, SHAKE_LANE64_BITS, B64, 1>(format!("{name}_b64[{i}]"), sel[i])
		});
		(sel, b64)
	}

	/// Write the genuine per-row lane values into a 25-lane projected selected-block column set.
	fn fill_selected25(
		seg: &mut ShakeSeg<'_>,
		cols: &[Col<B1, SHAKE_LANE64_BITS>; 25],
		states: &[StateMatrix<u64>],
	) -> anyhow::Result<()> {
		for (i, &col) in cols.iter().enumerate() {
			let mut d: std::cell::RefMut<'_, [u64]> = seg.get_mut_as(col)?;
			for (k, cell) in d.iter_mut().take(states.len()).enumerate() {
				*cell = states[k].as_inner()[i];
			}
		}
		Ok(())
	}

	/// One squeeze block = one table with a Keccak-f gadget. Block b (b>0) PULLS its 25-lane
	/// input state from the chain channel; block b (b<n-1) PUSHES its 25-lane output state.
	struct ShakeBlockTable {
		table_id: TableId,
		g: Keccakf,
		pull_sel: Option<[Col<B1, SHAKE_LANE64_BITS>; 25]>, // input track-0 lanes (pulled) if b>0
		push_sel: Option<[Col<B1, SHAKE_LANE64_BITS>; 25]>, // output track-7 lanes (pushed) if b<n-1
	}

	/// Prove AND verify the `n_blocks`-block SHAKE squeeze over B256TowerFamily (SHA-256 commit +
	/// challenger): N Keccak-f tables joined by ONE channel so state_out(b)==state_in(b+1).
	/// Returns (proof_size, all squeezed blocks concatenated). For n=1 there is no channel
	/// traffic (a single self-contained permutation).
	fn prove_shake_chain_b256(
		variant: ShakeVariant,
		seed: &[u8],
		n_blocks: usize,
		log_inv_rate: usize,
		security_bits: usize,
	) -> anyhow::Result<(usize, Vec<u8>)> {
		let allocator = Bump::new();
		let mut cs = ConstraintSystem::<OurB256>::new();
		let chain = cs.add_channel("squeeze_chain");

		// Witness: gadget b's INPUT is state_{b-1} (state_{-1} = padded absorb); its OUTPUT is
		// state_b. `states[b]` = state_b = Keccak-f(state_{b-1}).
		let states = shake_chain_states(variant, seed, n_blocks);
		let mut inputs = Vec::with_capacity(n_blocks);
		{
			let rate = variant.rate_bytes();
			let mut bytes = [0u8; 200];
			bytes[..seed.len()].copy_from_slice(seed);
			bytes[seed.len()] ^= variant.pad_byte();
			bytes[rate - 1] ^= 0x80;
			let padded: [u64; 25] =
				std::array::from_fn(|i| u64::from_le_bytes(bytes[i * 8..i * 8 + 8].try_into().unwrap()));
			inputs.push(StateMatrix::from_values(padded)); // input of gadget 0 = padded absorb
			for st in states.iter().take(n_blocks - 1) {
				inputs.push(st.clone()); // input of gadget b (b≥1) = state_{b-1}
			}
		}

		// Build N single-gadget tables, wiring the channel chain.
		let mut blocks = Vec::with_capacity(n_blocks);
		for b in 0..n_blocks {
			let mut table = cs.add_table(format!("SHAKE squeeze block {b} over B256"));
			let state_in: StateMatrix<Col<B1, SHAKE_LANE_BITS>> =
				StateMatrix::from_fn(|(x, y)| table.add_committed(format!("in{b}[{x},{y}]")));
			let g = Keccakf::new(&mut table, state_in.clone());
			// PULL this block's input (track-0 of the permutation input) if it continues a chain.
			let pull_sel = if b > 0 {
				let g_in = g.packed_state_in();
				let (sel, b64) = track25_to_b64(&mut table, &format!("in{b}"), g_in.as_inner(), SHAKE_IN_TRACK);
				table.pull(chain, b64);
				Some(sel)
			} else {
				None
			};
			// PUSH this block's output (track-7 of the permutation output) if a next block consumes it.
			let push_sel = if b + 1 < n_blocks {
				let g_out = g.packed_state_out();
				let (sel, b64) = track25_to_b64(&mut table, &format!("out{b}"), g_out.as_inner(), SHAKE_OUT_TRACK);
				table.push(chain, b64);
				Some(sel)
			} else {
				None
			};
			blocks.push(ShakeBlockTable { table_id: table.id(), g, pull_sel, push_sel });
		}

		let statement = Statement { boundaries: vec![], table_sizes: vec![1; n_blocks] };
		let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
		let mut out = Vec::with_capacity(n_blocks * variant.rate_bytes());
		for (b, blk) in blocks.iter().enumerate() {
			let tw = witness.init_table(blk.table_id, 1)?;
			let mut segment = tw.full_segment();
			blk.g.populate_state_in(&mut segment, std::iter::once(&inputs[b]))?;
			blk.g.populate(&mut segment)?;
			let out_states: Vec<StateMatrix<u64>> = blk.g.read_state_outs(&segment)?.collect();
			for lane in out_states[0].as_inner().iter().take(variant.rate_lanes()) {
				out.extend_from_slice(&lane.to_le_bytes());
			}
			// Fill the pulled input lanes (= this block's input state) and pushed output lanes
			// (= this block's output state) so the channel tuples carry the genuine values.
			if let Some(sel) = &blk.pull_sel {
				fill_selected25(&mut segment, sel, std::slice::from_ref(&inputs[b]))?;
			}
			if let Some(sel) = &blk.push_sel {
				fill_selected25(&mut segment, sel, &out_states)?;
			}
		}

		let ccs = cs.compile(&statement).unwrap();
		let witness = witness.into_multilinear_extension_index();
		let proof = binius_core::constraint_system::prove::<
			U256,
			B256TowerFamily,
			Sha256,
			Sha256Compression,
			HasherChallenger<Sha256>,
			_,
		>(
			&ccs,
			log_inv_rate,
			security_bits,
			&statement.boundaries,
			witness,
			&binius_hal::make_portable_backend(),
		)?;
		let sz = proof.get_proof_size();
		binius_core::constraint_system::verify::<
			U256,
			B256TowerFamily,
			Sha256,
			Sha256Compression,
			HasherChallenger<Sha256>,
		>(&ccs, log_inv_rate, security_bits, &statement.boundaries, proof.clone())?;
		Ok((sz, out))
	}

	/// GATE prove-1 (Phase-3) — the SHAKE-128 squeeze PROVES AND VERIFIES over B256TowerFamily
	/// at NIST L1 (128), and the in-circuit squeeze equals the sha3-crate XOF byte-for-byte.
	/// Tested single-block (n=1, self-contained permutation) AND multi-block (n=3, Keccak-f
	/// tables joined by the sha3_join channel so state_out(b)==state_in(b+1)). Reuses the
	/// committed Keccak-f/b256 + M2b channel infrastructure with zero fork change.
	#[test]
	fn shake_xof_proves_over_b256() {
		let seed = [7u8; 34]; // ExpandA-sized seed
		let rate = ShakeVariant::Shake128.rate_bytes();
		for n in [1usize, 3] {
			let (sz, out) = prove_shake_chain_b256(ShakeVariant::Shake128, &seed, n, 1, 128)
				.unwrap_or_else(|e| panic!("SHAKE-128 {n}-block squeeze must PROVE+VERIFY over B256: {e}"));
			assert_eq!(out, shake128_xof(&seed, n * rate), "in-circuit {n}-block squeeze != sha3 XOF");
			assert!(sz > 0);
			println!("GATE prove-1: SHAKE-128 {n}-block squeeze PROVEN+VERIFIED over B256 @L1(128); {sz} B; == sha3 XOF");
		}
	}

	/// GATE prove-2 (Phase-3) — the ExpandA ACCEPT-DECISION gadget over B256, the load-bearing
	/// rejection-sampling soundness object. For each candidate 24-bit z (raw ExpandA triple
	/// `b0 | b1<<8 | (b2&0x7f)<<16` from a real SHAKE-128 stream), accept = (z<q) is decided by
	/// S0's carry trick: accept = NOT carry_out(z + (2^32 − q)) (W=32). `accept` is a COMMITTED
	/// bit BOUND to the carry via `accept + final_carry + 1 == 0`. Honest accepts PROVE+VERIFY
	/// and match z<q; a tampered accept bit (either direction) is REJECTED, isolated by
	/// `validate_witness` to `accept_bind`. Naive rejection sampling is unsound precisely because
	/// the accept bit is unconstrained — this is the fix, the same r_lt_m carry S0 proves.
	/// (The ordered placement of accepted z into â — prefix-sum index + channel permutation —
	/// is the next increment, prove-2b.)
	#[test]
	fn expand_a_accept_decision_proves_and_tamper_rejected() {
		use crate::nonnative::{ripple_add, shl, two_pow_w_minus, write_bit, write_col};
		use binius_core::oracle::ShiftVariant;
		use binius_field::Field;

		const ACC_W: usize = 32;
		const ACC_LOGW: usize = 5;
		const MLDSA_Q: u32 = 8380417;
		fn u32_bits(x: u32) -> Vec<bool> {
			(0..ACC_W).map(|k| (x >> k) & 1 == 1).collect()
		}

		// 16 candidate z's from a real SHAKE-128 ExpandA stream (seed ρ‖s‖r), each the raw
		// 24-bit ExpandA triple before the <q rejection test.
		let mut seed = vec![0u8; 34];
		seed[32] = 2; // s = 2
		seed[33] = 1; // r = 1  (one Â cell)
		let stream = shake128_xof(&seed, 3 * 64);
		let mut zs: Vec<u32> = (0..16)
			.map(|t| {
				let (b0, b1, b2) = (stream[3 * t], stream[3 * t + 1], stream[3 * t + 2]);
				(b0 as u32) | ((b1 as u32) << 8) | (((b2 & 0x7f) as u32) << 16)
			})
			.collect();
		// Force boundary coverage: q−1 (accept), q (reject), 0 (accept), 2^24−1 (reject).
		zs[0] = MLDSA_Q - 1;
		zs[1] = MLDSA_Q;
		zs[2] = 0;
		zs[3] = (1 << 24) - 1;
		let n_rows = zs.len(); // 16 (power of two)
		let native_accept: Vec<bool> = zs.iter().map(|&z| z < MLDSA_Q).collect();

		let c_bits = two_pow_w_minus(&u32_bits(MLDSA_Q)); // 2^32 − q
		let c_arr: [B1; ACC_W] =
			std::array::from_fn(|k| if c_bits[k] { B1::ONE } else { B1::ZERO });

		// Build + populate the reject table; `reject_override` forces one row's reject bit.
		// The committed `reject` bit is BOUND to the carry-out: reject == final_carry (z≥q). The
		// accept decision is its complement, accept = NOT reject. `full` runs the full B256
		// prove/verify; otherwise only the deterministic `validate_witness` (which names the
		// violated constraint) is run. Returns (validate_ok, validate_err, verify_ok).
		let run = |reject_override: Option<(usize, bool)>, full: bool| -> (bool, String, bool) {
			let allocator = Bump::new();
			let mut cs = ConstraintSystem::<OurB256>::new();
			let mut table = cs.add_table("ExpandA accept-decision (z<q via carry) over B256");
			let z = table.add_committed::<B1, ACC_W>("z");
			let c_col = table.add_constant("two_pow32_minus_q", c_arr);
			let cout = table.add_committed::<B1, ACC_W>("cout");
			let cin = table.add_shifted("cin", cout, ACC_LOGW, 1, ShiftVariant::LogicalLeft);
			// per-lane carry: cout = maj(z, c, cin).
			table.assert_zero("acc_carry", (z + cin) * (c_col + cin) + cin - cout);
			let final_carry = table.add_selected("final_carry", cout, ACC_W - 1);
			let reject = table.add_committed::<B1, 1>("reject");
			// reject == final_carry (= carry-out of z + (2^32−q)) == (z ≥ q). accept = NOT reject.
			table.assert_zero("reject_bind", reject - final_carry);
			let table_id = table.id();

			let statement = Statement { boundaries: vec![], table_sizes: vec![n_rows] };
			let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
			{
				let tw = witness.init_table(table_id, n_rows).unwrap();
				let mut seg = tw.full_segment();
				for (row, &zv) in zs.iter().enumerate() {
					write_col::<ACC_W>(&mut seg, z, row, &u32_bits(zv)).unwrap();
					write_col::<ACC_W>(&mut seg, c_col, row, &c_bits).unwrap();
					let (_s, co) = ripple_add(&u32_bits(zv), &c_bits);
					write_col::<ACC_W>(&mut seg, cout, row, &co).unwrap();
					// cin (add_shifted) and final_carry (add_selected) are NOT auto-derived here
					// — populate them explicitly (cin[k]=cout[k-1], cin[0]=0).
					write_col::<ACC_W>(&mut seg, cin, row, &shl(&co, 1)).unwrap();
					write_bit(&mut seg, final_carry, row, co[ACC_W - 1]).unwrap();
					let rej = match reject_override {
						Some((r, v)) if r == row => v,
						_ => zv >= MLDSA_Q,
					};
					write_bit(&mut seg, reject, row, rej).unwrap();
				}
			}
			let ccs = cs.compile(&statement).unwrap();
			let witness = witness.into_multilinear_extension_index();
			let v = binius_core::constraint_system::validate::validate_witness(
				&ccs,
				&statement.boundaries,
				&witness,
			);
			let vok = v.is_ok();
			let verr = v.err().map(|e| e.to_string()).unwrap_or_default();
			if !full {
				return (vok, verr, false);
			}
			let proof = binius_core::constraint_system::prove::<
				U256,
				B256TowerFamily,
				Sha256,
				Sha256Compression,
				HasherChallenger<Sha256>,
				_,
			>(&ccs, 1, 128, &statement.boundaries, witness, &binius_hal::make_portable_backend());
			let verify_ok = match proof {
				Err(_) => false,
				Ok(pf) => binius_core::constraint_system::verify::<
					U256,
					B256TowerFamily,
					Sha256,
					Sha256Compression,
					HasherChallenger<Sha256>,
				>(&ccs, 1, 128, &statement.boundaries, pf)
				.is_ok(),
			};
			(vok, verr, verify_ok)
		};

		// (a) Honest: validate + full B256 prove/verify must ACCEPT.
		let (vok, verr, verify_ok) = run(None, true);
		assert!(vok, "honest accept-decision failed validate_witness: {verr}");
		assert!(verify_ok, "honest accept-decision must PROVE+VERIFY over B256");

		// (b) LOAD-BEARING: on an ACCEPTED row (z<q, reject=0) force reject=1 ("smuggle z≥q as
		// out-of-range") — must reject at reject_bind.
		let acc_row = native_accept.iter().position(|&a| a).unwrap();
		let (vok2, verr2, _) = run(Some((acc_row, true)), false);
		assert!(!vok2, "SOUNDNESS FAILURE: forged reject bit on z<q was ACCEPTED");
		assert!(
			verr2.contains("reject_bind"),
			"tampered reject (z<q) not isolated to reject_bind (got: {verr2})"
		);

		// (c) LOAD-BEARING: on a REJECTED row (z≥q, reject=1) force reject=0 ("accept an
		// out-of-range coefficient") — must reject at reject_bind.
		let rej_row = native_accept.iter().position(|&a| !a).unwrap();
		let (vok3, verr3, _) = run(Some((rej_row, false)), false);
		assert!(!vok3, "SOUNDNESS FAILURE: forged accept on z≥q was ACCEPTED");
		assert!(
			verr3.contains("reject_bind"),
			"tampered accept (z≥q) not isolated to reject_bind (got: {verr3})"
		);

		let n_acc = native_accept.iter().filter(|&&a| a).count();
		println!(
			"GATE prove-2: ExpandA accept-decision PROVEN+VERIFIED over B256 @L1(128); {n_rows} candidates, {n_acc} accepted (z<q); tampered decision bit BOTH directions REJECTED, isolated to reject_bind"
		);
	}

	/// GATE prove-2b (Phase-3) — the ExpandA ORDERED-PLACEMENT binding over B256: the output
	/// polynomial â is bound to EXACTLY the accepted z's, positioned by rank, via a selector-gated
	/// sha3_join channel. A candidate table runs the prove-2 carry-accept gadget and PUSHES
	/// `(rank, z)` gated by the accept bit (`push_with_opts` selector); an output table PULLS
	/// `(j, â[j])` for each position j. The channel balances as a multiset iff
	/// `{(rank,z) : accept} == {(j, â[j])}` — so no coefficient can be dropped, inserted,
	/// duplicated, or altered. Honest placement PROVES+VERIFIES; a tampered â value or a duplicated
	/// rank UNBALANCES the channel and is REJECTED. (Pinning rank == scan-order prefix-sum — vs the
	/// committed rank here — is the final refinement, prove-2c.)
	#[test]
	fn expand_a_placement_binds_ahat_and_tamper_rejected() {
		use crate::nonnative::{ripple_add, shl, two_pow_w_minus, write_bit, write_col};
		use binius_core::oracle::ShiftVariant;
		use binius_field::Field;
		use binius_m3::builder::{FlushOpts, B32};

		const W: usize = 32;
		const LOGW: usize = 5;
		const Q: u32 = 8380417;
		fn bits(x: u32) -> Vec<bool> {
			(0..W).map(|k| (x >> k) & 1 == 1).collect()
		}

		// 16 candidates: 8 ACCEPT (z<q, distinct) at scan rows 0..7, then 8 REJECT (z≥q) at
		// rows 8..15. K = 8 accepted → â has 8 coefficients. rank(accept row t) = t.
		let accepted_z: [u32; 8] = [0, 1, 100, 12345, Q - 1, 777, 40000, 8000000];
		let rejected_z: [u32; 8] = [Q, Q + 1, Q + 50, (1 << 24) - 1, Q + 9, Q + 3, Q + 100, Q + 7];
		let cand: Vec<(u32, bool)> = accepted_z
			.iter()
			.map(|&z| (z, true))
			.chain(rejected_z.iter().map(|&z| (z, false)))
			.collect();
		let n = cand.len(); // 16
		let k = 8usize; // accepted count (power of two)
		let mut ranks = vec![0u32; n];
		{
			let mut r = 0u32;
			for t in 0..n {
				if cand[t].1 {
					ranks[t] = r;
					r += 1;
				}
			}
		}
		let ahat: Vec<u32> = (0..k).map(|j| accepted_z[j]).collect(); // â[j] = accepted z at rank j

		let c_bits = two_pow_w_minus(&bits(Q)); // 2^32 − q
		let c_arr: [B1; W] = std::array::from_fn(|kk| if c_bits[kk] { B1::ONE } else { B1::ZERO });

		// Build the two-table one-channel placement; overrides tamper one output value / one rank.
		// Returns (validate_ok, validate_err, verify_ok).
		let run = |ahat_override: Option<(usize, u32)>,
		           rank_override: Option<(usize, u32)>,
		           full: bool|
		 -> (bool, String, bool) {
			let allocator = Bump::new();
			let mut cs = ConstraintSystem::<OurB256>::new();
			let place = cs.add_channel("placement");

			// candidate table: carry-accept gadget + selector-gated push (rank, z).
			// A custom flush selector requires the table to be power-of-two sized (else the
			// framework's implicit step-down selector would collide — "multiple selectors").
			let mut ct = cs.add_table("ExpandA candidate placement over B256");
			ct.require_power_of_two_size();
			let z = ct.add_committed::<B1, W>("z");
			let c_col = ct.add_constant("two_pow32_minus_q", c_arr);
			let cout = ct.add_committed::<B1, W>("cout");
			let cin = ct.add_shifted("cin", cout, LOGW, 1, ShiftVariant::LogicalLeft);
			ct.assert_zero("acc_carry", (z + cin) * (c_col + cin) + cin - cout);
			let final_carry = ct.add_selected("final_carry", cout, W - 1);
			let accept = ct.add_committed::<B1, 1>("accept");
			let one_col = ct.add_constant("one", [B1::ONE]);
			ct.assert_zero("accept_bind", accept + final_carry + one_col); // accept = NOT final_carry
			let rank = ct.add_committed::<B1, W>("rank");
			let z_b32 = ct.add_packed::<B1, W, B32, 1>("z_b32", z);
			let rank_b32 = ct.add_packed::<B1, W, B32, 1>("rank_b32", rank);
			ct.push_with_opts(
				place,
				[rank_b32, z_b32],
				FlushOpts { multiplicity: 1, selector: Some(accept) },
			);
			let ct_id = ct.id();

			// output table: pull (j, â[j]) for each position.
			let mut ot = cs.add_table("ExpandA ahat output over B256");
			let jcol = ot.add_committed::<B1, W>("j");
			let ahatcol = ot.add_committed::<B1, W>("ahat");
			let j_b32 = ot.add_packed::<B1, W, B32, 1>("j_b32", jcol);
			let ahat_b32 = ot.add_packed::<B1, W, B32, 1>("ahat_b32", ahatcol);
			ot.pull(place, [j_b32, ahat_b32]);
			let ot_id = ot.id();

			let statement = Statement { boundaries: vec![], table_sizes: vec![n, k] };
			let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
			{
				let tw = witness.init_table(ct_id, n).unwrap();
				let mut seg = tw.full_segment();
				for t in 0..n {
					let (zv, acc) = cand[t];
					write_col::<W>(&mut seg, z, t, &bits(zv)).unwrap();
					write_col::<W>(&mut seg, c_col, t, &c_bits).unwrap();
					let (_s, co) = ripple_add(&bits(zv), &c_bits);
					write_col::<W>(&mut seg, cout, t, &co).unwrap();
					write_col::<W>(&mut seg, cin, t, &shl(&co, 1)).unwrap();
					write_bit(&mut seg, final_carry, t, co[W - 1]).unwrap();
					write_bit(&mut seg, accept, t, acc).unwrap();
					write_bit(&mut seg, one_col, t, true).unwrap();
					let rv = match rank_override {
						Some((r, v)) if r == t => v,
						_ => ranks[t],
					};
					write_col::<W>(&mut seg, rank, t, &bits(rv)).unwrap();
				}
			}
			{
				let tw = witness.init_table(ot_id, k).unwrap();
				let mut seg = tw.full_segment();
				for j in 0..k {
					write_col::<W>(&mut seg, jcol, j, &bits(j as u32)).unwrap();
					let av = match ahat_override {
						Some((jj, v)) if jj == j => v,
						_ => ahat[j],
					};
					write_col::<W>(&mut seg, ahatcol, j, &bits(av)).unwrap();
				}
			}

			let ccs = cs.compile(&statement).unwrap();
			let witness = witness.into_multilinear_extension_index();
			let v = binius_core::constraint_system::validate::validate_witness(
				&ccs,
				&statement.boundaries,
				&witness,
			);
			let vok = v.is_ok();
			let verr = v.err().map(|e| e.to_string()).unwrap_or_default();
			if !full {
				return (vok, verr, false);
			}
			let proof = binius_core::constraint_system::prove::<
				U256,
				B256TowerFamily,
				Sha256,
				Sha256Compression,
				HasherChallenger<Sha256>,
				_,
			>(&ccs, 1, 128, &statement.boundaries, witness, &binius_hal::make_portable_backend());
			let verify_ok = match proof {
				Err(_) => false,
				Ok(pf) => binius_core::constraint_system::verify::<
					U256,
					B256TowerFamily,
					Sha256,
					Sha256Compression,
					HasherChallenger<Sha256>,
				>(&ccs, 1, 128, &statement.boundaries, pf)
				.is_ok(),
			};
			(vok, verr, verify_ok)
		};

		// (a) Honest: â = accepted z's by rank — validate + full B256 prove/verify ACCEPT.
		let (vok, verr, verify_ok) = run(None, None, true);
		assert!(vok, "honest placement failed validate_witness: {verr}");
		assert!(verify_ok, "honest placement must PROVE+VERIFY over B256");

		// (b) Tamper an OUTPUT value: â[0] := a value no accepted z has → channel UNBALANCED.
		let (vok2, _e2, _) = run(Some((0, 9_999_999)), None, false);
		assert!(!vok2, "SOUNDNESS FAILURE: a forged â coefficient was ACCEPTED (placement not bound)");

		// (c) Tamper a RANK: duplicate rank 0 (rows 0 and 1 both rank 0) → position 1 unmatched,
		// channel UNBALANCED.
		let (vok3, _e3, _) = run(None, Some((1, 0)), false);
		assert!(!vok3, "SOUNDNESS FAILURE: a duplicated placement rank was ACCEPTED");

		println!(
			"GATE prove-2b: ExpandA ordered placement PROVEN+VERIFIED over B256 @L1(128); {n}→{k} accepted, â bound to accepted z's by rank via selector-gated channel; forged â value + duplicated rank REJECTED (channel unbalanced)"
		);
	}

	/// GATE prove-2c (Phase-3) — pin `rank == scan-order prefix-sum` via a counter channel, the
	/// ordering refinement that makes the prove-2b placement pin â to the accepted z's in EXACT
	/// scan order (not just as a set). A single `count` channel carries `(pos, count)` tuples:
	/// each candidate row PULLS `(pos_in, rank_in)` and PUSHES `(pos_in+1, rank_in+accept)`, with
	/// the increments enforced by the nonnative ripple adder (`rank_out = rank_in + accept`,
	/// `pos_out = pos_in + 1`). Statement boundaries seed `(0,0)` and drain `(N, total)`. The
	/// channel balances iff the positions chain 0→N and each `rank` is the running accept count —
	/// so `rank_in[t]` is forced to equal the number of accepts strictly before row t. An
	/// inconsistent (non-prefix-sum) rank UNBALANCES the channel and is REJECTED.
	#[test]
	fn expand_a_rank_is_prefix_sum_over_b256() {
		use crate::nonnative::{write_col, Adder};
		use binius_field::Field;
		use binius_m3::builder::{Boundary, FlushDirection, B32};

		const W: usize = 32;
		fn bits(x: u32) -> Vec<bool> {
			(0..W).map(|k| (x >> k) & 1 == 1).collect()
		}

		// A mixed accept pattern over N=16 rows (interspersed accepts/rejects → non-trivial
		// prefix sum). accept[t] ∈ {0,1}; rank_in[t] = #accepts in rows 0..t-1.
		let accept: [bool; 16] = [
			true, false, true, true, false, false, true, false, true, true, true, false, false,
			true, false, true,
		];
		let n = accept.len();
		let mut rank_in = vec![0u32; n];
		let mut running = 0u32;
		for t in 0..n {
			rank_in[t] = running;
			if accept[t] {
				running += 1;
			}
		}
		let total = running; // = 9

		// mask with bits 1..31 set (bit0 = 0): forces accept_ext ∈ {0,1}.
		let mask_hi_bits: Vec<bool> = (0..W).map(|k| k != 0).collect();
		let mask_hi_arr: [B1; W] =
			std::array::from_fn(|k| if mask_hi_bits[k] { B1::ONE } else { B1::ZERO });
		let one_bits = bits(1);
		let one_arr: [B1; W] = std::array::from_fn(|k| if one_bits[k] { B1::ONE } else { B1::ZERO });

		let b32 = |v: u32| OurB256::from(B32::new(v));

		// `rank_override` tampers one row's committed rank_in (breaking the prefix-sum chain).
		let run = |rank_override: Option<(usize, u32)>, full: bool| -> (bool, String, bool) {
			let allocator = Bump::new();
			let mut cs = ConstraintSystem::<OurB256>::new();
			let cnt = cs.add_channel("count");

			let mut ct = cs.add_table("ExpandA prefix-sum counter over B256");
			let rank_in_c = ct.add_committed::<B1, W>("rank_in");
			let accept_ext = ct.add_committed::<B1, W>("accept_ext"); // 0/1 in bit 0
			let pos_in = ct.add_committed::<B1, W>("pos_in");
			let one_col = ct.add_constant("one", one_arr);
			let mask_hi = ct.add_constant("mask_hi", mask_hi_arr);
			// accept_ext ∈ {0,1}: all bits above bit 0 are zero.
			ct.assert_zero("accept_is_bit", accept_ext * mask_hi);
			// rank_out = rank_in + accept ; pos_out = pos_in + 1.
			let rank_add = Adder::<W>::build(&mut ct, rank_in_c, accept_ext, "radd");
			let pos_add = Adder::<W>::build(&mut ct, pos_in, one_col, "padd");
			let rank_in_b32 = ct.add_packed::<B1, W, B32, 1>("rank_in_b32", rank_in_c);
			let rank_out_b32 = ct.add_packed::<B1, W, B32, 1>("rank_out_b32", rank_add.sum);
			let pos_in_b32 = ct.add_packed::<B1, W, B32, 1>("pos_in_b32", pos_in);
			let pos_out_b32 = ct.add_packed::<B1, W, B32, 1>("pos_out_b32", pos_add.sum);
			ct.pull(cnt, [pos_in_b32, rank_in_b32]);
			ct.push(cnt, [pos_out_b32, rank_out_b32]);
			let ct_id = ct.id();

			// Boundaries: PUSH (0,0) seeds the chain (matches row 0's pull at pos 0 → rank_in[0]=0);
			// PULL (N,total) drains it (matches row N-1's push at pos N → rank_out[N-1]=total).
			let statement = Statement {
				boundaries: vec![
					Boundary {
						values: vec![b32(0), b32(0)],
						channel_id: cnt,
						direction: FlushDirection::Push,
						multiplicity: 1,
					},
					Boundary {
						values: vec![b32(n as u32), b32(total)],
						channel_id: cnt,
						direction: FlushDirection::Pull,
						multiplicity: 1,
					},
				],
				table_sizes: vec![n],
			};
			let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
			{
				let tw = witness.init_table(ct_id, n).unwrap();
				let mut seg = tw.full_segment();
				for t in 0..n {
					let riv = match rank_override {
						Some((r, v)) if r == t => v,
						_ => rank_in[t],
					};
					let acc_bits: Vec<bool> = (0..W).map(|k| k == 0 && accept[t]).collect();
					write_col::<W>(&mut seg, rank_in_c, t, &bits(riv)).unwrap();
					write_col::<W>(&mut seg, accept_ext, t, &acc_bits).unwrap();
					write_col::<W>(&mut seg, pos_in, t, &bits(t as u32)).unwrap();
					write_col::<W>(&mut seg, one_col, t, &one_bits).unwrap();
					write_col::<W>(&mut seg, mask_hi, t, &mask_hi_bits).unwrap();
					// adder columns (cout/cin/sum) — the inputs rank_in/accept_ext/pos_in/one are
					// already written above.
					// Adder::populate fills each adder's cout/cin/sum from the operand bit-vectors.
					let _ = rank_add.populate(&mut seg, t, &bits(riv), &acc_bits).unwrap();
					let _ = pos_add.populate(&mut seg, t, &bits(t as u32), &one_bits).unwrap();
				}
			}

			let ccs = cs.compile(&statement).unwrap();
			let witness = witness.into_multilinear_extension_index();
			let v = binius_core::constraint_system::validate::validate_witness(
				&ccs,
				&statement.boundaries,
				&witness,
			);
			let vok = v.is_ok();
			let verr = v.err().map(|e| e.to_string()).unwrap_or_default();
			if !full {
				return (vok, verr, false);
			}
			let proof = binius_core::constraint_system::prove::<
				U256,
				B256TowerFamily,
				Sha256,
				Sha256Compression,
				HasherChallenger<Sha256>,
				_,
			>(&ccs, 1, 128, &statement.boundaries, witness, &binius_hal::make_portable_backend());
			let verify_ok = match proof {
				Err(_) => false,
				Ok(pf) => binius_core::constraint_system::verify::<
					U256,
					B256TowerFamily,
					Sha256,
					Sha256Compression,
					HasherChallenger<Sha256>,
				>(&ccs, 1, 128, &statement.boundaries, pf)
				.is_ok(),
			};
			(vok, verr, verify_ok)
		};

		// (a) Honest prefix-sum: validate + full B256 prove/verify ACCEPT.
		let (vok, verr, verify_ok) = run(None, true);
		assert!(vok, "honest prefix-sum failed validate_witness: {verr}");
		assert!(verify_ok, "honest prefix-sum counter must PROVE+VERIFY over B256");

		// (b) Tamper: set rank_in[6] to a wrong (non-prefix-sum) value → the pos-6 pull no longer
		// matches the pos-6 push from row 5 → channel UNBALANCED → REJECT.
		let bad = rank_in[6] + 1;
		let (vok2, _e2, _) = run(Some((6, bad)), false);
		assert!(!vok2, "SOUNDNESS FAILURE: an inconsistent (non-prefix-sum) rank was ACCEPTED");

		println!(
			"GATE prove-2c: ExpandA rank==prefix-sum PROVEN+VERIFIED over B256 @L1(128); N={n}, total={total} accepts, counter channel pins each rank to the running accept count; inconsistent rank REJECTED (channel unbalanced)"
		);
	}

	/// GATE prove-3 (PENDING, S1c) — SampleInBall proves over B256; the in-circuit c
	/// equals sample_in_ball(c̃,τ) with weight τ; a smuggled j>i draw or a mis-placed
	/// sign is REJECTED (Fisher–Yates carry + permutation-argument soundness gate).
	#[test]
	#[ignore = "S1c Fisher–Yates gadget not wired yet — enable after S1a full_256 frees the target"]
	fn sample_in_ball_proves_and_tamper_rejected() {
		unimplemented!("Fisher–Yates over S0's j≤i carry + permutation_argument memory trace — next wiring step");
	}
}

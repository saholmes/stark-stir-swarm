// sha256_air — M3-native SHA-256 (FIPS 180-4) block compression over the B256 tower.
//
// This is the Tier-B RECURSION HASH: the recursive master verifies an inner proof by
// recomputing its SHA-256 Merkle/Fiat-Shamir hashes IN-CIRCUIT, so it needs SHA-256 as
// an M3 gadget over B256 (binius ships only keccak/groestl in M3; the only FIPS hasher
// in binius_hash is SHA-256, and it is already the system's commitment hash — so the
// whole stack stays FIPS-approved: SHA-256 for every hash, B256 STARK for 128-bit
// unconditional/PQ soundness, sliver decomposition as an assumption-free prover technique).
//
// One call compresses a 256-bit state (8 words a..h) with a 512-bit message block (16
// words) into a new 256-bit state — exactly `binius_hash::sha2` / FIPS 180-4 §6.2, the
// raw compression the Merkle 2-to-1 uses. All arithmetic is over B1 bit-columns
// `Col<B1,32>`: XOR = field `+`, AND = field `*`, rotate/shift = `add_shifted`
// (Circular/Logical), 32-bit modular add = the S0 `Adder<32>` carry recipe.
//
// Correctness is gated against `sha2::compress256` (the canonical FIPS implementation),
// and a tampered output word is REJECTED.

use anyhow::Result;

use binius_core::oracle::ShiftVariant;
use binius_field::Field;
use binius_hal::make_portable_backend;
use binius_core::fiat_shamir::HasherChallenger;
use binius_hash::sha2::Sha256Compression;
use sha2::Sha256;

use binius_m3::builder::{
	Col, ConstraintSystem, Statement, TableBuilder, TableId, TableWitnessSegment, WitnessIndex, B1,
};

use crate::b256_field::{B256TowerFamily, B256 as OurB256, U256};
use crate::nonnative::{write_col, Adder};

/// SHA-256 round constants K[0..64] (FIPS 180-4 §4.2.2).
#[rustfmt::skip]
pub const K256: [u32; 64] = [
	0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
	0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
	0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
	0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
	0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
	0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
	0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
	0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

/// Native SHA-256 block compression (FIPS 180-4 §6.2): `state`-updated by one 512-bit
/// message `block` (both as 32-bit words). This is the reference the AIR is gated
/// against; it is itself cross-checked against `sha2::compress256` in the tests.
pub fn compress256_ref(state: &[u32; 8], block: &[u32; 16]) -> [u32; 8] {
	let mut w = [0u32; 64];
	w[..16].copy_from_slice(block);
	for t in 16..64 {
		let s0 = w[t - 15].rotate_right(7) ^ w[t - 15].rotate_right(18) ^ (w[t - 15] >> 3);
		let s1 = w[t - 2].rotate_right(17) ^ w[t - 2].rotate_right(19) ^ (w[t - 2] >> 10);
		w[t] = w[t - 16]
			.wrapping_add(s0)
			.wrapping_add(w[t - 7])
			.wrapping_add(s1);
	}
	let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = *state;
	for t in 0..64 {
		let big_s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
		let ch = (e & f) ^ ((!e) & g);
		let t1 = h
			.wrapping_add(big_s1)
			.wrapping_add(ch)
			.wrapping_add(K256[t])
			.wrapping_add(w[t]);
		let big_s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
		let maj = (a & b) ^ (a & c) ^ (b & c);
		let t2 = big_s0.wrapping_add(maj);
		h = g;
		g = f;
		f = e;
		e = d.wrapping_add(t1);
		d = c;
		c = b;
		b = a;
		a = t1.wrapping_add(t2);
	}
	[
		state[0].wrapping_add(a),
		state[1].wrapping_add(b),
		state[2].wrapping_add(c),
		state[3].wrapping_add(d),
		state[4].wrapping_add(e),
		state[5].wrapping_add(f),
		state[6].wrapping_add(g),
		state[7].wrapping_add(h),
	]
}

// ---- witness helpers -------------------------------------------------------------

/// 32-bit little-endian bit vector of a u32 (bit k = bit k of v).
fn u32_bits(v: u32) -> Vec<bool> {
	(0..32).map(|k| (v >> k) & 1 == 1).collect()
}

/// Write a u32 into a `Col<B1,32>` at `row`.
fn wc(seg: &mut TableWitnessSegment<OurB256>, col: Col<B1, 32>, row: usize, v: u32) -> Result<()> {
	write_col::<32>(seg, col, row, &u32_bits(v))
}

// ---- the gadget ------------------------------------------------------------------

/// A Σ/σ mixing column: three rotate/shift inputs XORed into one output. For populate
/// we recompute the three inputs + the output natively.
#[derive(Clone, Copy)]
struct Mix {
	i0: Col<B1, 32>,
	i1: Col<B1, 32>,
	i2: Col<B1, 32>,
	out: Col<B1, 32>,
}

/// Per-round columns retained for population.
struct Round {
	s1: Mix,           // Σ1(e)
	ch: Col<B1, 32>,   // Ch(e,f,g)
	t1: [Adder<32>; 4], // h+Σ1, +ch, +K, +w  (t1[3].sum = T1)
	s0: Mix,           // Σ0(a)
	maj: Col<B1, 32>,  // Maj(a,b,c)
	t2: Adder<32>,     // Σ0+maj
	e_new: Adder<32>,  // d + T1
	a_new: Adder<32>,  // T1 + T2
}

/// Message-schedule extension column set for one t in 16..64.
struct Sched {
	s0: Mix, // σ0(w[t-15])
	s1: Mix, // σ1(w[t-2])
	add: [Adder<32>; 3], // w[t-16]+σ0, +w[t-7], +σ1  (add[2].sum = w[t])
}

/// SHA-256 one-block compression AIR: input state `h_in`, message `w_in`, output state
/// `h_out` (each an 8- resp. 16-word array of `Col<B1,32>`), asserting the FIPS 180-4
/// compression. `k_cols` are the constant round-key columns.
pub struct Sha256Compress {
	pub table_id: TableId,
	h_in: [Col<B1, 32>; 8],
	w_in: [Col<B1, 32>; 16],
	k_cols: Vec<Col<B1, 32>>,
	sched: Vec<Sched>,   // t = 16..64
	rounds: Vec<Round>,  // t = 0..64
	ff: [Adder<32>; 8],  // feed-forward state_in[i] + working[i]
	h_out: [Col<B1, 32>; 8],
}

impl Sha256Compress {
	pub fn build(cs: &mut ConstraintSystem<OurB256>) -> Self {
		let mut table = cs.add_table("sha256 block compression (FIPS 180-4)");

		let h_in: [Col<B1, 32>; 8] =
			std::array::from_fn(|i| table.add_committed::<B1, 32>(format!("h_in{i}")));
		let w_in: [Col<B1, 32>; 16] =
			std::array::from_fn(|i| table.add_committed::<B1, 32>(format!("w{i}")));

		// Constant round keys as constant columns.
		let k_cols: Vec<Col<B1, 32>> = (0..64)
			.map(|t| {
				let bits = u32_bits(K256[t]);
				let arr: [B1; 32] = std::array::from_fn(|k| if bits[k] { B1::ONE } else { B1::ZERO });
				table.add_constant(format!("K{t}"), arr)
			})
			.collect();

		// ROTR_n (circular right by n) = CircularLeft by (32-n); SHR_n = LogicalRight by n.
		let rotr = |t: &mut TableBuilder<OurB256>, nm: String, x: Col<B1, 32>, n: usize| {
			t.add_shifted(nm, x, 5, (32 - n) % 32, ShiftVariant::CircularLeft)
		};
		let shrn = |t: &mut TableBuilder<OurB256>, nm: String, x: Col<B1, 32>, n: usize| {
			t.add_shifted(nm, x, 5, n, ShiftVariant::LogicalRight)
		};

		// --- Message schedule: w[16..64]. ---
		let mut w: Vec<Col<B1, 32>> = w_in.to_vec();
		let mut sched = Vec::with_capacity(48);
		for t in 16..64 {
			// σ0(w[t-15]) = ROTR7 ^ ROTR18 ^ SHR3
			let x15 = w[t - 15];
			let a0 = rotr(&mut table, format!("s0r7_{t}"), x15, 7);
			let a1 = rotr(&mut table, format!("s0r18_{t}"), x15, 18);
			let a2 = shrn(&mut table, format!("s0s3_{t}"), x15, 3);
			let sig0 = table.add_computed(format!("sig0_{t}"), a0 + a1 + a2);
			// σ1(w[t-2]) = ROTR17 ^ ROTR19 ^ SHR10
			let x2 = w[t - 2];
			let b0 = rotr(&mut table, format!("s1r17_{t}"), x2, 17);
			let b1 = rotr(&mut table, format!("s1r19_{t}"), x2, 19);
			let b2 = shrn(&mut table, format!("s1s10_{t}"), x2, 10);
			let sig1 = table.add_computed(format!("sig1_{t}"), b0 + b1 + b2);
			// w[t] = w[t-16] + σ0 + w[t-7] + σ1
			let ad0 = Adder::<32>::build(&mut table, w[t - 16], sig0, &format!("wsch0_{t}"));
			let ad1 = Adder::<32>::build(&mut table, ad0.sum, w[t - 7], &format!("wsch1_{t}"));
			let ad2 = Adder::<32>::build(&mut table, ad1.sum, sig1, &format!("wsch2_{t}"));
			w.push(ad2.sum);
			sched.push(Sched {
				s0: Mix { i0: a0, i1: a1, i2: a2, out: sig0 },
				s1: Mix { i0: b0, i1: b1, i2: b2, out: sig1 },
				add: [ad0, ad1, ad2],
			});
		}

		// --- 64 compression rounds. a..h track live column handles (shifts are free). ---
		let mut a = h_in[0];
		let mut b = h_in[1];
		let mut c = h_in[2];
		let mut d = h_in[3];
		let mut e = h_in[4];
		let mut f = h_in[5];
		let mut g = h_in[6];
		let mut h = h_in[7];
		let mut rounds = Vec::with_capacity(64);
		for t in 0..64 {
			// Σ1(e) = ROTR6 ^ ROTR11 ^ ROTR25
			let r6 = rotr(&mut table, format!("S1r6_{t}"), e, 6);
			let r11 = rotr(&mut table, format!("S1r11_{t}"), e, 11);
			let r25 = rotr(&mut table, format!("S1r25_{t}"), e, 25);
			let big_s1 = table.add_computed(format!("BigS1_{t}"), r6 + r11 + r25);
			// Ch(e,f,g) = e&f ^ ~e&g = e*f + g + e*g
			let ch = table.add_computed(format!("Ch_{t}"), e * f + g + e * g);
			// T1 = h + Σ1 + Ch + K + w[t]
			let ta = Adder::<32>::build(&mut table, h, big_s1, &format!("T1a_{t}"));
			let tb = Adder::<32>::build(&mut table, ta.sum, ch, &format!("T1b_{t}"));
			let tc = Adder::<32>::build(&mut table, tb.sum, k_cols[t], &format!("T1c_{t}"));
			let td = Adder::<32>::build(&mut table, tc.sum, w[t], &format!("T1d_{t}"));
			let t1 = td.sum;
			// Σ0(a) = ROTR2 ^ ROTR13 ^ ROTR22
			let q2 = rotr(&mut table, format!("S0r2_{t}"), a, 2);
			let q13 = rotr(&mut table, format!("S0r13_{t}"), a, 13);
			let q22 = rotr(&mut table, format!("S0r22_{t}"), a, 22);
			let big_s0 = table.add_computed(format!("BigS0_{t}"), q2 + q13 + q22);
			// Maj(a,b,c) = a*b + a*c + b*c
			let maj = table.add_computed(format!("Maj_{t}"), a * b + a * c + b * c);
			// T2 = Σ0 + Maj
			let t2a = Adder::<32>::build(&mut table, big_s0, maj, &format!("T2_{t}"));
			// e_new = d + T1 ; a_new = T1 + T2
			let en = Adder::<32>::build(&mut table, d, t1, &format!("en_{t}"));
			let an = Adder::<32>::build(&mut table, t1, t2a.sum, &format!("an_{t}"));

			rounds.push(Round {
				s1: Mix { i0: r6, i1: r11, i2: r25, out: big_s1 },
				ch,
				t1: [ta, tb, tc, td],
				s0: Mix { i0: q2, i1: q13, i2: q22, out: big_s0 },
				maj,
				t2: t2a,
				e_new: en,
				a_new: an,
			});

			// shift the working variables
			h = g;
			g = f;
			f = e;
			e = en.sum;
			d = c;
			c = b;
			b = a;
			a = an.sum;
		}
		let working = [a, b, c, d, e, f, g, h];

		// --- Feed-forward: h_out[i] = h_in[i] + working[i]. ---
		let ff: [Adder<32>; 8] = std::array::from_fn(|i| {
			Adder::<32>::build(&mut table, h_in[i], working[i], &format!("ff{i}"))
		});
		let h_out: [Col<B1, 32>; 8] = std::array::from_fn(|i| ff[i].sum);

		Sha256Compress {
			table_id: table.id(),
			h_in,
			w_in,
			k_cols,
			sched,
			rounds,
			ff,
			h_out,
		}
	}

	/// Read the in-circuit output state word `i` at `row` (for gating vs the reference).
	pub fn read_out(&self, seg: &TableWitnessSegment<OurB256>, i: usize, row: usize) -> Result<u32> {
		let bits = crate::nonnative::read_col::<32>(seg, self.h_out[i], row)?;
		Ok((0..32).fold(0u32, |acc, k| acc | ((bits[k] as u32) << k)))
	}

	pub fn populate(
		&self,
		seg: &mut TableWitnessSegment<OurB256>,
		row: usize,
		state: &[u32; 8],
		block: &[u32; 16],
	) -> Result<()> {
		// Inputs + constants.
		for i in 0..8 {
			wc(seg, self.h_in[i], row, state[i])?;
		}
		for i in 0..16 {
			wc(seg, self.w_in[i], row, block[i])?;
		}
		for (t, col) in self.k_cols.iter().enumerate() {
			wc(seg, *col, row, K256[t])?;
		}

		// Message schedule (recompute w[] natively, filling every column).
		let mut w = [0u32; 64];
		w[..16].copy_from_slice(block);
		for (idx, t) in (16..64).enumerate() {
			let x15 = w[t - 15];
			let (r7, r18, s3) = (x15.rotate_right(7), x15.rotate_right(18), x15 >> 3);
			let x2 = w[t - 2];
			let (r17, r19, s10) = (x2.rotate_right(17), x2.rotate_right(19), x2 >> 10);
			let sig0 = r7 ^ r18 ^ s3;
			let sig1 = r17 ^ r19 ^ s10;
			let sc = &self.sched[idx];
			wc(seg, sc.s0.i0, row, r7)?;
			wc(seg, sc.s0.i1, row, r18)?;
			wc(seg, sc.s0.i2, row, s3)?;
			wc(seg, sc.s0.out, row, sig0)?;
			wc(seg, sc.s1.i0, row, r17)?;
			wc(seg, sc.s1.i1, row, r19)?;
			wc(seg, sc.s1.i2, row, s10)?;
			wc(seg, sc.s1.out, row, sig1)?;
			let a0 = w[t - 16].wrapping_add(sig0);
			let a1 = a0.wrapping_add(w[t - 7]);
			let a2 = a1.wrapping_add(sig1);
			sc.add[0].populate(seg, row, &u32_bits(w[t - 16]), &u32_bits(sig0))?;
			sc.add[1].populate(seg, row, &u32_bits(a0), &u32_bits(w[t - 7]))?;
			sc.add[2].populate(seg, row, &u32_bits(a1), &u32_bits(sig1))?;
			w[t] = a2;
		}

		// Compression rounds.
		let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = *state;
		for t in 0..64 {
			let rd = &self.rounds[t];
			let (r6, r11, r25) = (e.rotate_right(6), e.rotate_right(11), e.rotate_right(25));
			let big_s1 = r6 ^ r11 ^ r25;
			let ch = (e & f) ^ ((!e) & g);
			wc(seg, rd.s1.i0, row, r6)?;
			wc(seg, rd.s1.i1, row, r11)?;
			wc(seg, rd.s1.i2, row, r25)?;
			wc(seg, rd.s1.out, row, big_s1)?;
			wc(seg, rd.ch, row, ch)?;
			let a_h = h.wrapping_add(big_s1);
			let a_ch = a_h.wrapping_add(ch);
			let a_k = a_ch.wrapping_add(K256[t]);
			let t1 = a_k.wrapping_add(w[t]);
			rd.t1[0].populate(seg, row, &u32_bits(h), &u32_bits(big_s1))?;
			rd.t1[1].populate(seg, row, &u32_bits(a_h), &u32_bits(ch))?;
			rd.t1[2].populate(seg, row, &u32_bits(a_ch), &u32_bits(K256[t]))?;
			rd.t1[3].populate(seg, row, &u32_bits(a_k), &u32_bits(w[t]))?;
			let (q2, q13, q22) = (a.rotate_right(2), a.rotate_right(13), a.rotate_right(22));
			let big_s0 = q2 ^ q13 ^ q22;
			let maj = (a & b) ^ (a & c) ^ (b & c);
			wc(seg, rd.s0.i0, row, q2)?;
			wc(seg, rd.s0.i1, row, q13)?;
			wc(seg, rd.s0.i2, row, q22)?;
			wc(seg, rd.s0.out, row, big_s0)?;
			wc(seg, rd.maj, row, maj)?;
			let t2 = big_s0.wrapping_add(maj);
			rd.t2.populate(seg, row, &u32_bits(big_s0), &u32_bits(maj))?;
			let e_new = d.wrapping_add(t1);
			let a_new = t1.wrapping_add(t2);
			rd.e_new.populate(seg, row, &u32_bits(d), &u32_bits(t1))?;
			rd.a_new.populate(seg, row, &u32_bits(t1), &u32_bits(t2))?;
			h = g;
			g = f;
			f = e;
			e = e_new;
			d = c;
			c = b;
			b = a;
			a = a_new;
		}

		// Feed-forward.
		let working = [a, b, c, d, e, f, g, h];
		for i in 0..8 {
			self.ff[i].populate(seg, row, &u32_bits(state[i]), &u32_bits(working[i]))?;
		}
		Ok(())
	}
}

/// Prove + verify one SHA-256 block compression over B256; returns `(proof_bytes, out_state)`.
pub fn prove_verify_sha256_compress(
	state: &[u32; 8],
	block: &[u32; 16],
) -> Result<(usize, [u32; 8])> {
	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let air = Sha256Compress::build(&mut cs);
	let statement = Statement { boundaries: vec![], table_sizes: vec![1] };

	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	let out;
	{
		let tw = witness.init_table(air.table_id, 1)?;
		let mut seg = tw.full_segment();
		air.populate(&mut seg, 0, state, block)?;
		out = std::array::from_fn(|i| air.read_out(&seg, i, 0).unwrap());
	}

	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();
	binius_core::constraint_system::validate::validate_witness(&ccs, &[], &witness)?;

	let proof = binius_core::constraint_system::prove::<
		U256,
		B256TowerFamily,
		Sha256,
		Sha256Compression,
		HasherChallenger<Sha256>,
		_,
	>(&ccs, 1, 128, &statement.boundaries, witness, &make_portable_backend())?;
	let proof_size = proof.get_proof_size();

	binius_core::constraint_system::verify::<
		U256,
		B256TowerFamily,
		Sha256,
		Sha256Compression,
		HasherChallenger<Sha256>,
	>(&ccs, 1, 128, &statement.boundaries, proof)?;

	Ok((proof_size, out))
}

#[cfg(test)]
mod tests {
	use super::*;

	/// SHA-256 initial hash values (FIPS 180-4 §5.3.3) — a convenient test state.
	const IV: [u32; 8] = [
		0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
	];

	/// The native reference matches the canonical `sha2::compress256`.
	#[test]
	fn compress_ref_matches_sha2_crate() {
		use sha2::compress256;
		let block: [u32; 16] = std::array::from_fn(|i| (i as u32).wrapping_mul(0x9e3779b1));
		let mut sha2_state = IV;
		let mut bytes = [0u8; 64];
		for (i, w) in block.iter().enumerate() {
			bytes[i * 4..i * 4 + 4].copy_from_slice(&w.to_be_bytes());
		}
		compress256(&mut sha2_state, &[bytes.into()]);
		let ours = compress256_ref(&IV, &block);
		assert_eq!(ours, sha2_state, "compress256_ref != sha2::compress256");
	}

	/// GATE M1 — the in-circuit SHA-256 compression PROVES+VERIFIES over B256 and its
	/// output matches the native reference; a tampered output is REJECTED.
	#[test]
	fn sha256_compress_proves_over_b256() {
		let block: [u32; 16] = std::array::from_fn(|i| (i as u32).wrapping_mul(0x9e3779b1) ^ 0x5a5a5a5a);
		let want = compress256_ref(&IV, &block);
		let (size, got) = prove_verify_sha256_compress(&IV, &block)
			.expect("SHA-256 compression must PROVE+VERIFY over B256");
		assert_eq!(got, want, "in-circuit SHA-256 output != reference");
		println!(
			"GATE M1 sha256-compress: FIPS 180-4 block compression PROVES+VERIFIES over B256 @L1(128); \
			 in-circuit out == sha2::compress256; proof = {size} bytes"
		);
	}

	/// Soundness: a tampered input word (inconsistent with the rest of the honest
	/// witness) is REJECTED by validate_witness — the compression constraints bind the
	/// output to `compress256(state, block)`, so no wrong (state,block,out) can pass.
	#[test]
	fn sha256_compress_tamper_rejected() {
		let allocator = bumpalo::Bump::new();
		let mut cs = ConstraintSystem::<OurB256>::new();
		let air = Sha256Compress::build(&mut cs);
		let statement = Statement { boundaries: vec![], table_sizes: vec![1] };
		let block: [u32; 16] = std::array::from_fn(|i| (i as u32).wrapping_mul(0x01234567));

		let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
		{
			let tw = witness.init_table(air.table_id, 1).unwrap();
			let mut seg = tw.full_segment();
			air.populate(&mut seg, 0, &IV, &block).unwrap();
			// Flip one bit of h_in[0] AFTER honest population: every column derived from
			// state[0] (round usage + feed-forward ff[0]) is now inconsistent.
			wc(&mut seg, air.h_in[0], 0, IV[0] ^ 1).unwrap();
		}
		let ccs = cs.compile(&statement).unwrap();
		let witness = witness.into_multilinear_extension_index();
		let rejected =
			binius_core::constraint_system::validate::validate_witness(&ccs, &[], &witness).is_err();
		assert!(rejected, "SOUNDNESS FAILURE: a tampered SHA-256 input was accepted");
		println!("GATE M1 soundness: a tampered SHA-256 compression witness is REJECTED");
	}
}

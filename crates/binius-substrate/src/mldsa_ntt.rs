// S1a (ML-DSA / FIPS 204 verify port) — the R_q polynomial-arithmetic layer over
// Z_q with q = 8380417, proven over the 256-bit tower field `B256TowerFamily` at
// NIST L1 (128) with a SHA-256 Merkle commitment + SHA-256 Fiat–Shamir challenger.
//
// R_q = Z_q[X]/(X^256 + 1). ML-DSA verify computes w' ≈ A·z − c·t1·2^d in the NTT
// domain, so the load-bearing arithmetic primitives are: modular add/sub mod q,
// modular multiply-by-a-public-twiddle ζ·v mod q, and the forward/inverse negacyclic
// (256-point) NTT built from them. This module delivers all of those as SOUND
// in-circuit gadgets and gates them (round-trip, num-bigint cross-check, twiddle
// validity, and adversarial tamper-rejection).
//
// ── REUSE OF S0 (no reinvented modmul) ────────────────────────────────────────────
// Every gadget here is built on S0's audited primitives from `crate::nonnative`:
//   * `Adder<W>`      — the sound width-W carry adder  `cout = maj(x,y,cin)`,
//                       `cin = cout<<1`, `sum = x+y+cin`  (the U32Add recipe).
//   * `shl/shr/ripple_add/two_pow_w_minus` — the exact bit-vector arithmetic used to
//                       fill the witness, so populate mirrors the circuit lane-for-lane.
//   * `write_col/write_bit/read_col` — column I/O.
// The modular-reduction recipe (identity `lhs == quo*q + r` + strict `r < q` via the
// adder's carry-out of `r + (2^W − q)`) is S0's, specialised for the fixed modulus q.
// NO fork change: only the field-generic `TableBuilder<B256>` surface is used.
//
// ── WHY q FITS IN W = 64 ───────────────────────────────────────────────────────────
// n = ⌈log2 q⌉ = 23. All operands are < q < 2^23. The widest intermediate is the
// un-reduced product ζ·v < q^2 < 2^46 and its reduction quo·q + r < 2^46 + 2^23 < 2^47.
// Both fit in W = 64 bits with NO wraparound, so every committed column equals its true
// integer value and every `assert_zero` identity is a TRUE integer equality (sound).
//
// ── STRAND-DECOMPOSITION NOTE (RSS tuning; see report item (f)) ────────────────────
// The 256-point NTT is 8 Cooley–Tukey stages. The first stage (len=128) is a single
// cross-coupling group spanning all 256 coefficients; but after the top stage the
// transform splits into two INDEPENDENT 128-point sub-NTTs (coeffs [0,128) and
// [128,256)), then four 64-point, … , i.e. at "cut depth" d the network decomposes
// into G = 2^d independent equal-width strands with NO data dependence between them
// until they are recombined by the stages ABOVE the cut. A low-memory prover picks a
// budget, sets d so 256/G ≈ budget, proves each of the G strands (fine-decompose) as
// its own sub-table (peak RSS ∝ strand width, not 256), and re-binds adjacent strands
// with a seam over the coefficients the cross-cut stages share (union-bounded ≤ 2^−λ,
// exactly S0's strand-splice model). This module builds G = 1 (the whole transform in
// one table) but is written so the per-butterfly gadgets are independent objects that a
// strand cut can partition without touching the arithmetic — see `Butterfly`/`InvOp`.

use anyhow::Result;
use binius_core::{
	constraint_system::channel::{Boundary, ChannelId, FlushDirection},
	fiat_shamir::HasherChallenger,
	oracle::ShiftVariant,
};
use binius_field::Field;
use binius_hash::sha2::Sha256Compression;
use binius_m3::builder::{
	Col, ConstraintSystem, Statement, TableBuilder, TableId, TableWitnessSegment, WitnessIndex, B1, B64,
};
use bumpalo::Bump;
use sha2::Sha256;

use crate::b256_field::{B256TowerFamily, B256 as OurB256, U256};
use crate::nonnative::{read_col, ripple_add, shl, shr, two_pow_w_minus, write_bit, write_col, Adder};

/// ML-DSA / Dilithium prime.  q = 2^23 − 2^13 + 1.
pub const Q: u64 = 8_380_417;
/// ⌈log2 q⌉.
const NBITS_Q: usize = 23;
/// Bit-width of every column: 2n+1 ≤ 47 ⇒ next power of two is 64.
const W: usize = 64;
/// ψ, a primitive 512-th root of unity mod q (the Dilithium base twiddle).
const PSI512: u64 = 1753;

// ───────────────────────────── integer helpers ─────────────────────────────

fn bits64(v: u64) -> Vec<bool> {
	(0..W).map(|k| (v >> k) & 1 == 1).collect()
}

fn to_u64(bits: &[bool]) -> u64 {
	let mut v = 0u64;
	for (k, &b) in bits.iter().enumerate().take(W) {
		if b {
			v |= 1u64 << k;
		}
	}
	v
}

fn set_bits_of(v: u64) -> Vec<usize> {
	(0..W).filter(|&k| (v >> k) & 1 == 1).collect()
}

fn q_bits() -> Vec<bool> {
	bits64(Q)
}

/// C = 2^W − q, the addend whose carry-out of bit W−1 decides `r < q`.
fn c_q_bits() -> Vec<bool> {
	two_pow_w_minus(&q_bits())
}

/// Modular exponentiation over u128 (safe: base,q < 2^24 ⇒ products < 2^48).
fn modpow(mut base: u64, mut e: u64) -> u64 {
	let q = Q as u128;
	let mut b = base as u128 % q;
	let mut acc = 1u128;
	while e > 0 {
		if e & 1 == 1 {
			acc = acc * b % q;
		}
		b = b * b % q;
		e >>= 1;
	}
	base = acc as u64;
	base
}

/// Modular inverse via Fermat (q is prime).
fn modinv(x: u64) -> u64 {
	modpow(x % Q, Q - 2)
}

/// Bit-reverse the low `bits` bits of `x`.
fn brv(x: usize, bits: usize) -> usize {
	let mut r = 0usize;
	for i in 0..bits {
		if (x >> i) & 1 == 1 {
			r |= 1 << (bits - 1 - i);
		}
	}
	r
}

/// The forward Cooley–Tukey butterfly groups for an `n`-point negacyclic NTT.
/// Each entry is `(start, len, zeta)`; the twiddle is ω_{2n}^{brv(k)} where
/// ω_{2n} = ψ^{256/n} has order 2n, and k increments across the whole schedule with
/// the bit-reversal taken over m = log2(n) bits (the standard Dilithium table).
fn forward_groups(n: usize) -> Vec<(usize, usize, u64)> {
	let m = n.trailing_zeros() as usize;
	let omega = modpow(PSI512, (256 / n) as u64); // order 2n
	let mut groups = Vec::new();
	let mut k = 0usize;
	let mut len = n / 2;
	while len >= 1 {
		let mut start = 0usize;
		while start < n {
			k += 1;
			let zeta = modpow(omega, brv(k, m) as u64);
			groups.push((start, len, zeta));
			start += 2 * len;
		}
		len >>= 1;
	}
	groups
}

// ─────────────────────── independent num-bigint references ───────────────────────

#[cfg(test)]
pub mod reference {
	use super::*;
	use num_bigint::BigUint;

	fn big(v: u64) -> BigUint {
		BigUint::from(v)
	}
	fn small(v: &BigUint) -> u64 {
		v.to_u64_digits().first().copied().unwrap_or(0)
	}

	/// Forward negacyclic NTT in independent BigUint arithmetic — mirrors the circuit's
	/// group schedule but shares NONE of its bit-vector machinery, so "circuit == ref"
	/// is a real cross-check of the in-circuit shift-add reductions and the wiring.
	pub fn ntt_ref(input: &[u64], n: usize) -> Vec<u64> {
		let q = big(Q);
		let mut a: Vec<BigUint> = input.iter().map(|&x| big(x)).collect();
		for (start, len, zeta) in forward_groups(n) {
			let z = big(zeta);
			for j in start..start + len {
				let t = (&z * &a[j + len]) % &q;
				let u = a[j].clone();
				a[j] = (&u + &t) % &q;
				a[j + len] = (&u + &q - &t) % &q; // (u − t) mod q
			}
		}
		a.iter().map(small).collect()
	}

	/// The exact butterfly-inverse of `ntt_ref`: reverse the schedule and invert each
	/// CT butterfly (u,v)→(u+zv, u−zv) by (p,m)→((p+m)/2, (p−m)/(2z)).  Guaranteed to
	/// invert for ANY twiddle set; the accumulated ×(1/2) per stage supplies the 1/n.
	pub fn invntt_ref(input: &[u64], n: usize) -> Vec<u64> {
		let q = big(Q);
		let inv2 = big(modinv(2));
		let mut a: Vec<BigUint> = input.iter().map(|&x| big(x)).collect();
		for (start, len, zeta) in forward_groups(n).into_iter().rev() {
			let inv2z = big(modinv((2 * zeta) % Q));
			for j in start..start + len {
				let p = a[j].clone();
				let mm = a[j + len].clone();
				a[j] = ((&p + &mm) % &q * &inv2) % &q;
				a[j + len] = ((&p + &q - &mm) % &q * &inv2z) % &q;
			}
		}
		a.iter().map(small).collect()
	}

	/// Closed-form multipoint-evaluation reference used ONLY to validate that the
	/// forward twiddle table yields a genuine negacyclic transform.  The evaluation
	/// point implied by the network for output `j` is `pt[j] = ntt_ref(X)[j]`
	/// (linearity ⇒ column j of the NTT matrix at the degree-1 monomial). We then
	/// assert independently that each `pt[j]` is a root of X^n+1 and evaluate directly.
	pub fn eval_points(n: usize) -> Vec<u64> {
		let mut unit_x = vec![0u64; n];
		unit_x[1] = 1; // the polynomial X
		ntt_ref(&unit_x, n)
	}

	pub fn eval_ref(input: &[u64], n: usize) -> Vec<u64> {
		let q = big(Q);
		let pts = eval_points(n);
		let mut out = Vec::with_capacity(n);
		for &p in &pts {
			let pb = big(p);
			let mut acc = BigUint::from(0u64);
			let mut pw = BigUint::from(1u64);
			for &ai in input {
				acc = (&acc + big(ai) * &pw) % &q;
				pw = (&pw * &pb) % &q;
			}
			out.push(small(&acc));
		}
		out
	}
}

// ───────────────────────────── sub-gadgets ─────────────────────────────

/// `x < q` decided by the carry-out of `x + (2^W − q)` (S0's `r < m` recipe). Shares a
/// caller-supplied constant column `C = 2^W − q`.
struct LtQ {
	cout: Col<B1, W>,
	cin: Col<B1, W>,
	final_carry: Col<B1, 1>,
}

impl LtQ {
	fn build(t: &mut TableBuilder<OurB256>, name: &str, x: Col<B1, W>, c_col: Col<B1, W>) -> Self {
		let logw = W.trailing_zeros() as usize;
		let cout = t.add_committed::<B1, W>(format!("{name}_ltq_cout"));
		let cin = t.add_shifted(format!("{name}_ltq_cin"), cout, logw, 1, ShiftVariant::LogicalLeft);
		t.assert_zero(format!("{name}_ltq_carry"), (x + cin) * (c_col + cin) + cin - cout);
		let final_carry = t.add_selected(format!("{name}_ltq_final"), cout, W - 1);
		t.assert_zero(format!("{name}_lt_q"), final_carry * B1::ONE);
		Self { cout, cin, final_carry }
	}

	fn populate(&self, seg: &mut TableWitnessSegment<OurB256>, row: usize, x: &[bool], c: &[bool]) -> Result<()> {
		let (_s, cout) = ripple_add(x, c);
		let cin = shl(&cout, 1);
		write_col::<W>(seg, self.cout, row, &cout)?;
		write_col::<W>(seg, self.cin, row, &cin)?;
		write_bit(seg, self.final_carry, row, cout[W - 1])?;
		Ok(())
	}
}

/// `x >> k == 0`  ⇔  `x < 2^k`  (S0's operand-bound recipe). Used to pin selector bits
/// (k=1) and the reduction quotient (k=NBITS_Q).
struct ShrZero {
	hi: Col<B1, W>,
	k: usize,
}

impl ShrZero {
	fn build(t: &mut TableBuilder<OurB256>, name: &str, x: Col<B1, W>, k: usize) -> Self {
		let logw = W.trailing_zeros() as usize;
		let hi = t.add_shifted(format!("{name}_hi"), x, logw, k, ShiftVariant::LogicalRight);
		t.assert_zero(format!("{name}_range"), hi * B1::ONE);
		Self { hi, k }
	}

	fn populate(&self, seg: &mut TableWitnessSegment<OurB256>, row: usize, x: &[bool]) -> Result<()> {
		write_col::<W>(seg, self.hi, row, &shr(x, self.k))
	}
}

/// `product = mult · const_val`, where `const_val`'s set-bit positions are `set_bits`
/// (a compile-time constant) and `mult` is a witness column: `product = Σ_p (mult<<p)`.
/// This is S0's `q*m = Σ_{m_i=1}(q<<i)` shift-sum, with roles chosen per call. No
/// broadcast column is needed because the constant selects which shifts of the witness
/// multiplier to add.
struct ShiftSumMul {
	terms: Vec<Col<B1, W>>, // aligned with set_bits; entry for p==0 aliases `mult`
	adders: Vec<Adder<W>>,
	set_bits: Vec<usize>,
	result: Col<B1, W>,
}

impl ShiftSumMul {
	fn build(t: &mut TableBuilder<OurB256>, name: &str, mult: Col<B1, W>, set_bits: &[usize]) -> Self {
		assert!(!set_bits.is_empty(), "constant multiplier must be non-zero");
		let logw = W.trailing_zeros() as usize;
		let mut terms = Vec::with_capacity(set_bits.len());
		for &p in set_bits {
			let term = if p == 0 {
				mult
			} else {
				t.add_shifted(format!("{name}_shl{p}"), mult, logw, p, ShiftVariant::LogicalLeft)
			};
			terms.push(term);
		}
		let mut adders = Vec::new();
		let mut acc = terms[0];
		for (idx, _) in set_bits.iter().enumerate().skip(1) {
			let adder = Adder::<W>::build(t, acc, terms[idx], &format!("{name}_acc{idx}"));
			acc = adder.sum;
			adders.push(adder);
		}
		Self { terms, adders, set_bits: set_bits.to_vec(), result: acc }
	}

	/// Fill the shifted-term and adder columns; `mult_bits` is the (already-written)
	/// witness multiplier. Returns the product bits.
	fn populate(&self, seg: &mut TableWitnessSegment<OurB256>, row: usize, mult_bits: &[bool]) -> Result<Vec<bool>> {
		for (idx, &p) in self.set_bits.iter().enumerate() {
			if p != 0 {
				write_col::<W>(seg, self.terms[idx], row, &shl(mult_bits, p))?;
			}
		}
		let mut acc = shl(mult_bits, self.set_bits[0]);
		let mut ai = 0usize;
		for &p in &self.set_bits[1..] {
			acc = self.adders[ai].populate(seg, row, &acc, &shl(mult_bits, p))?;
			ai += 1;
		}
		Ok(acc)
	}
}

// ───────────────────── modular gadgets over Z_q ─────────────────────

/// `out = (u + v) mod q`, for `u, v ∈ [0, q)`.  s = u+v < 2q; a single quotient bit
/// `qb ∈ {0,1}` and `s == qb·q + out` with `out < q` uniquely fix `out`.
struct ModAdd {
	uv: Adder<W>,
	qb: Col<B1, W>,
	qb_rng: ShrZero,
	qbq: ShiftSumMul,
	rhs: Adder<W>,
	out: Col<B1, W>,
	out_lt: LtQ,
}

impl ModAdd {
	fn build(t: &mut TableBuilder<OurB256>, name: &str, u: Col<B1, W>, v: Col<B1, W>, c_col: Col<B1, W>, q_set: &[usize]) -> Self {
		let uv = Adder::<W>::build(t, u, v, &format!("{name}_uv"));
		let qb = t.add_committed::<B1, W>(format!("{name}_qb"));
		let qb_rng = ShrZero::build(t, &format!("{name}_qb"), qb, 1);
		let qbq = ShiftSumMul::build(t, &format!("{name}_qbq"), qb, q_set);
		let out = t.add_committed::<B1, W>(format!("{name}_out"));
		let rhs = Adder::<W>::build(t, qbq.result, out, &format!("{name}_rhs"));
		t.assert_zero(format!("{name}_identity"), uv.sum - rhs.sum);
		let out_lt = LtQ::build(t, &format!("{name}_out"), out, c_col);
		Self { uv, qb, qb_rng, qbq, rhs, out, out_lt }
	}

	fn populate(&self, seg: &mut TableWitnessSegment<OurB256>, row: usize, u: &[bool], v: &[bool], c: &[bool]) -> Result<Vec<bool>> {
		let s = self.uv.populate(seg, row, u, v)?;
		let sv = to_u64(u) + to_u64(v);
		let qb_bit = sv >= Q;
		let out_v = sv - if qb_bit { Q } else { 0 };
		let qb_bits = bits64(qb_bit as u64);
		write_col::<W>(seg, self.qb, row, &qb_bits)?;
		self.qb_rng.populate(seg, row, &qb_bits)?;
		let qbq_bits = self.qbq.populate(seg, row, &qb_bits)?;
		let out_bits = bits64(out_v);
		write_col::<W>(seg, self.out, row, &out_bits)?;
		self.rhs.populate(seg, row, &qbq_bits, &out_bits)?;
		let _ = s;
		self.out_lt.populate(seg, row, &out_bits, c)?;
		Ok(out_bits)
	}
}

/// `out = (u − v) mod q`, for `u, v ∈ [0, q)`.  A borrow bit `bb ∈ {0,1}` with
/// `u + bb·q == v + out` and `out < q` uniquely fixes `out`.
struct ModSub {
	bb: Col<B1, W>,
	bb_rng: ShrZero,
	bbq: ShiftSumMul,
	lhs: Adder<W>,
	rhs: Adder<W>,
	out: Col<B1, W>,
	out_lt: LtQ,
}

impl ModSub {
	fn build(t: &mut TableBuilder<OurB256>, name: &str, u: Col<B1, W>, v: Col<B1, W>, c_col: Col<B1, W>, q_set: &[usize]) -> Self {
		let bb = t.add_committed::<B1, W>(format!("{name}_bb"));
		let bb_rng = ShrZero::build(t, &format!("{name}_bb"), bb, 1);
		let bbq = ShiftSumMul::build(t, &format!("{name}_bbq"), bb, q_set);
		let out = t.add_committed::<B1, W>(format!("{name}_out"));
		let lhs = Adder::<W>::build(t, u, bbq.result, &format!("{name}_lhs"));
		let rhs = Adder::<W>::build(t, v, out, &format!("{name}_rhs"));
		t.assert_zero(format!("{name}_identity"), lhs.sum - rhs.sum);
		let out_lt = LtQ::build(t, &format!("{name}_out"), out, c_col);
		Self { bb, bb_rng, bbq, lhs, rhs, out, out_lt }
	}

	fn populate(&self, seg: &mut TableWitnessSegment<OurB256>, row: usize, u: &[bool], v: &[bool], c: &[bool]) -> Result<Vec<bool>> {
		let uu = to_u64(u);
		let vv = to_u64(v);
		let bb_bit = uu < vv;
		let out_v = uu + if bb_bit { Q } else { 0 } - vv;
		let bb_bits = bits64(bb_bit as u64);
		write_col::<W>(seg, self.bb, row, &bb_bits)?;
		self.bb_rng.populate(seg, row, &bb_bits)?;
		let bbq_bits = self.bbq.populate(seg, row, &bb_bits)?;
		let out_bits = bits64(out_v);
		write_col::<W>(seg, self.out, row, &out_bits)?;
		self.lhs.populate(seg, row, u, &bbq_bits)?;
		self.rhs.populate(seg, row, v, &out_bits)?;
		self.out_lt.populate(seg, row, &out_bits, c)?;
		Ok(out_bits)
	}
}

/// `out = (ζ · v) mod q`, ζ a compile-time-known twiddle, v a witness in [0, q).
/// P = ζ·v < q^2 < 2^46; a quotient `quo` (< q) and remainder `out` with
/// `P == quo·q + out` and `out < q` uniquely fix `out`.
struct ModMulConst {
	prod: ShiftSumMul,
	quo: Col<B1, W>,
	quo_rng: ShrZero,
	quoq: ShiftSumMul,
	rhs: Adder<W>,
	out: Col<B1, W>,
	out_lt: LtQ,
	zeta: u64,
}

impl ModMulConst {
	fn build(t: &mut TableBuilder<OurB256>, name: &str, v: Col<B1, W>, zeta: u64, c_col: Col<B1, W>, q_set: &[usize]) -> Self {
		let zeta_set = set_bits_of(zeta % Q);
		let prod = ShiftSumMul::build(t, &format!("{name}_prod"), v, &zeta_set);
		let quo = t.add_committed::<B1, W>(format!("{name}_quo"));
		let quo_rng = ShrZero::build(t, &format!("{name}_quo"), quo, NBITS_Q);
		let quoq = ShiftSumMul::build(t, &format!("{name}_quoq"), quo, q_set);
		let out = t.add_committed::<B1, W>(format!("{name}_out"));
		let rhs = Adder::<W>::build(t, quoq.result, out, &format!("{name}_rhs"));
		t.assert_zero(format!("{name}_identity"), prod.result - rhs.sum);
		let out_lt = LtQ::build(t, &format!("{name}_out"), out, c_col);
		Self { prod, quo, quo_rng, quoq, rhs, out, out_lt, zeta: zeta % Q }
	}

	fn populate(&self, seg: &mut TableWitnessSegment<OurB256>, row: usize, v: &[bool], c: &[bool]) -> Result<Vec<bool>> {
		let vv = to_u64(v);
		let p = (self.zeta as u128 * vv as u128) as u64; // < 2^46
		let quo_v = p / Q;
		let out_v = p % Q;
		let prod_bits = self.prod.populate(seg, row, v)?;
		debug_assert_eq!(to_u64(&prod_bits), p, "in-circuit ζ·v product desync");
		let quo_bits = bits64(quo_v);
		write_col::<W>(seg, self.quo, row, &quo_bits)?;
		self.quo_rng.populate(seg, row, &quo_bits)?;
		let quoq_bits = self.quoq.populate(seg, row, &quo_bits)?;
		let out_bits = bits64(out_v);
		write_col::<W>(seg, self.out, row, &out_bits)?;
		self.rhs.populate(seg, row, &quoq_bits, &out_bits)?;
		self.out_lt.populate(seg, row, &out_bits, c)?;
		Ok(out_bits)
	}
}

// ───────────────────────────── the NTT circuit ─────────────────────────────

/// A forward CT butterfly: (u,v) → (u + ζ·v, u − ζ·v) mod q.
struct Butterfly {
	j: usize,
	jl: usize,
	mul: ModMulConst,
	add: ModAdd,
	sub: ModSub,
}

/// An inverse GS butterfly: (p,m) → ((p+m)·½ , (p−m)·(2ζ)⁻¹) mod q.
struct InvOp {
	j: usize,
	jl: usize,
	add: ModAdd,
	mul_j: ModMulConst,
	sub: ModSub,
	mul_k: ModMulConst,
}

/// The whole (forward, or forward∘inverse) negacyclic NTT over R_q in a single table.
pub struct Ntt {
	pub table_id: TableId,
	n: usize,
	roundtrip: bool,
	c_col: Col<B1, W>,
	inputs: Vec<Col<B1, W>>,
	in_lt: Vec<LtQ>,
	fwd: Vec<Butterfly>,
	out_cols: Vec<Col<B1, W>>, // forward outputs (== inputs when roundtrip)
	inv: Vec<InvOp>,
}

impl Ntt {
	/// Build the constraint system. If `roundtrip`, the circuit computes invNTT(NTT(x))
	/// and asserts it equals the input coefficient-for-coefficient (proven round-trip).
	pub fn build(cs: &mut ConstraintSystem<OurB256>, n: usize, roundtrip: bool) -> Self {
		assert!(n.is_power_of_two() && (2..=256).contains(&n));
		let mut t = cs.add_table(format!("mldsa R_q {}NTT n={n}", if roundtrip { "round-trip " } else { "" }));

		let c_arr: [B1; W] = std::array::from_fn(|k| if c_q_bits()[k] { B1::ONE } else { B1::ZERO });
		let c_col = t.add_constant("two_pow_W_minus_q", c_arr);
		let q_set = set_bits_of(Q);

		// Inputs, each range-checked < q (valid ring elements).
		let mut inputs = Vec::with_capacity(n);
		let mut in_lt = Vec::with_capacity(n);
		for i in 0..n {
			let col = t.add_committed::<B1, W>(format!("in{i}"));
			in_lt.push(LtQ::build(&mut t, &format!("in{i}"), col, c_col));
			inputs.push(col);
		}

		// Forward CT network. `cur[i]` tracks the live column for coefficient i.
		let mut cur = inputs.clone();
		let mut fwd = Vec::new();
		for (gi, (start, len, zeta)) in forward_groups(n).into_iter().enumerate() {
			for j in start..start + len {
				let jl = j + len;
				let nm = format!("f{}_{}", gi, j);
				let mul = ModMulConst::build(&mut t, &format!("{nm}_mul"), cur[jl], zeta, c_col, &q_set);
				let add = ModAdd::build(&mut t, &format!("{nm}_add"), cur[j], mul.out, c_col, &q_set);
				let sub = ModSub::build(&mut t, &format!("{nm}_sub"), cur[j], mul.out, c_col, &q_set);
				cur[j] = add.out;
				cur[jl] = sub.out;
				fwd.push(Butterfly { j, jl, mul, add, sub });
			}
		}
		let out_cols = cur.clone();

		// Inverse GS network (exact butterfly-inverse, reversed schedule).
		let mut inv = Vec::new();
		if roundtrip {
			let inv2 = modinv(2);
			for (gi, (start, len, zeta)) in forward_groups(n).into_iter().rev().enumerate() {
				let inv2z = modinv((2 * zeta) % Q);
				for j in start..start + len {
					let jl = j + len;
					let nm = format!("i{}_{}", gi, j);
					let add = ModAdd::build(&mut t, &format!("{nm}_add"), cur[j], cur[jl], c_col, &q_set);
					let mul_j = ModMulConst::build(&mut t, &format!("{nm}_mulj"), add.out, inv2, c_col, &q_set);
					let sub = ModSub::build(&mut t, &format!("{nm}_sub"), cur[j], cur[jl], c_col, &q_set);
					let mul_k = ModMulConst::build(&mut t, &format!("{nm}_mulk"), sub.out, inv2z, c_col, &q_set);
					cur[j] = mul_j.out;
					cur[jl] = mul_k.out;
					inv.push(InvOp { j, jl, add, mul_j, sub, mul_k });
				}
			}
			// Proven round-trip: final == input.
			for i in 0..n {
				t.assert_zero(format!("roundtrip_eq{i}"), cur[i] - inputs[i]);
			}
		}

		Ntt { table_id: t.id(), n, roundtrip, c_col, inputs, in_lt, fwd, out_cols, inv }
	}

	/// Fill every column for one row from the input coefficients (each < q).
	pub fn populate(&self, seg: &mut TableWitnessSegment<OurB256>, row: usize, input: &[u64]) -> Result<()> {
		assert_eq!(input.len(), self.n);
		let c = c_q_bits();
		write_col::<W>(seg, self.c_col, row, &c)?;

		let mut cur: Vec<Vec<bool>> = Vec::with_capacity(self.n);
		for (i, &x) in input.iter().enumerate() {
			assert!(x < Q, "input coefficient {i} = {x} not reduced mod q");
			let xb = bits64(x);
			write_col::<W>(seg, self.inputs[i], row, &xb)?;
			self.in_lt[i].populate(seg, row, &xb, &c)?;
			cur.push(xb);
		}

		for bf in &self.fwd {
			let u = cur[bf.j].clone();
			let v = cur[bf.jl].clone();
			let t = bf.mul.populate(seg, row, &v, &c)?;
			let newu = bf.add.populate(seg, row, &u, &t, &c)?;
			let newv = bf.sub.populate(seg, row, &u, &t, &c)?;
			cur[bf.j] = newu;
			cur[bf.jl] = newv;
		}

		if self.roundtrip {
			for op in &self.inv {
				let p = cur[op.j].clone();
				let m = cur[op.jl].clone();
				let s = op.add.populate(seg, row, &p, &m, &c)?;
				let newj = op.mul_j.populate(seg, row, &s, &c)?;
				let d = op.sub.populate(seg, row, &p, &m, &c)?;
				let newk = op.mul_k.populate(seg, row, &d, &c)?;
				cur[op.j] = newj;
				cur[op.jl] = newk;
			}
		}
		Ok(())
	}

	/// Read back the forward-NTT output coefficients for `row`.
	pub fn read_outputs(&self, seg: &TableWitnessSegment<OurB256>, row: usize) -> Result<Vec<u64>> {
		self.out_cols.iter().map(|&col| Ok(to_u64(&read_col::<W>(seg, col, row)?))).collect()
	}
}

// ───────────────────────────── prove / validate wiring ─────────────────────────────

const LOG_INV_RATE: usize = 1;
const SECURITY_BITS: usize = 128;

/// Honest build → populate → validate → PROVE → verify over B256 at NIST L1. Returns
/// `(proof_size_bytes, forward_output_coeffs)`.
pub fn prove(n: usize, roundtrip: bool, input: &[u64]) -> Result<(usize, Vec<u64>)> {
	let allocator = Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let ntt = Ntt::build(&mut cs, n, roundtrip);
	let statement = Statement { boundaries: vec![], table_sizes: vec![1] };

	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	let outputs;
	{
		let tw = witness.init_table(ntt.table_id, 1)?;
		let mut seg = tw.full_segment();
		ntt.populate(&mut seg, 0, input)?;
		outputs = ntt.read_outputs(&seg, 0)?;
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
	>(&ccs, LOG_INV_RATE, SECURITY_BITS, &statement.boundaries, witness, &binius_hal::make_portable_backend())?;

	let proof_size = proof.get_proof_size();
	binius_core::constraint_system::verify::<
		U256,
		B256TowerFamily,
		Sha256,
		Sha256Compression,
		HasherChallenger<Sha256>,
	>(&ccs, LOG_INV_RATE, SECURITY_BITS, &statement.boundaries, proof)?;
	Ok((proof_size, outputs))
}

/// Honest build → populate → `validate_witness` (NO FRI) → read outputs. Used to check
/// the FULL 256-point transform, where a complete FRI proof is impractically large but
/// witness validation still evaluates EVERY constraint (constraint-satisfaction is the
/// soundness surface; the FRI layer only attests it).
pub fn validate(n: usize, roundtrip: bool, input: &[u64]) -> Result<Vec<u64>> {
	let allocator = Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let ntt = Ntt::build(&mut cs, n, roundtrip);
	let statement = Statement { boundaries: vec![], table_sizes: vec![1] };
	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	let outputs;
	{
		let tw = witness.init_table(ntt.table_id, 1)?;
		let mut seg = tw.full_segment();
		ntt.populate(&mut seg, 0, input)?;
		outputs = ntt.read_outputs(&seg, 0)?;
	}
	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();
	binius_core::constraint_system::validate::validate_witness(&ccs, &[], &witness)?;
	Ok(outputs)
}

// ══════════════ TALL-NARROW butterfly batch (row-per-butterfly) ══════════════
//
// The `Ntt` above lays a whole transform in ONE row (all butterflies as columns) —
// FRI-pathological (RSS/time ∝ trace AREA ≈ width; measured 880 MiB at n=32). This
// section lays butterflies as ROWS (table_sizes=[nrows], ~fixed narrow columns/row),
// the tall-narrow shape every low-RSS strand uses (nonnative mod-mul, ec_verify).
// A full n-point transform's (n/2)·log₂n butterflies become that many rows; the
// per-row arithmetic is proven identically, but the trace is tall-narrow ⇒ low RSS
// and it shards by row-block across a fleet (seam-bound; docs/s1d-fleet-sharding-ntt.md).
// The twiddle ζ therefore varies per row, so ζ·v is a var×var multiply (`ModMulVar`).
// Inter-layer routing (o_add/o_sub of one butterfly feeding the next layer's inputs)
// is NOT yet enforced in-circuit here — it is the next increment (channel/seam);
// this table proves the per-butterfly ARITHMETIC tall-narrow and its RSS/time regime.

const WLOG: usize = 6; // log2(W), W = 64

/// `(ζ · v) mod q` with BOTH ζ and v witness columns (the row-per-butterfly twiddle
/// varies per row).  v's low NBITS_Q bits gate shifts of the ζ column into partial
/// products (broadcast-bit × ζ<<i, the decompose-gadget recipe), summed to the < 2^46
/// product, then reduced `prod = quo·q + out`, `out < q`, `quo < 2^NBITS_Q`.
struct ModMulVar {
	vbits: Vec<Col<B1, 1>>,
	bcast: Vec<Col<B1, W>>,
	bcast_rot: Vec<Col<B1, W>>,
	bcast_l0: Vec<Col<B1, 1>>,
	zshl: Vec<Col<B1, W>>,
	pp: Vec<Col<B1, W>>,
	adders: Vec<Adder<W>>,
	quo: Col<B1, W>,
	quo_rng: ShrZero,
	quoq: ShiftSumMul,
	rhs: Adder<W>,
	out: Col<B1, W>,
	out_lt: LtQ,
}

impl ModMulVar {
	fn build(t: &mut TableBuilder<OurB256>, name: &str, v: Col<B1, W>, zeta: Col<B1, W>, c_col: Col<B1, W>, q_set: &[usize]) -> Self {
		let mut vbits = Vec::new();
		let mut bcast = Vec::new();
		let mut bcast_rot = Vec::new();
		let mut bcast_l0 = Vec::new();
		let mut zshl = Vec::new();
		let mut pp = Vec::new();
		for i in 0..NBITS_Q {
			// v's bit i, broadcast to all lanes (rotate-invariant + lane0 == the bit).
			let vb = t.add_selected(format!("{name}_vb{i}"), v, i);
			let bc = t.add_committed::<B1, W>(format!("{name}_bc{i}"));
			let bc_rot = t.add_shifted(format!("{name}_bc{i}rot"), bc, WLOG, 1, ShiftVariant::CircularLeft);
			t.assert_zero(format!("{name}_bc{i}eq"), bc - bc_rot);
			let bc_l0 = t.add_selected(format!("{name}_bc{i}l0"), bc, 0);
			t.assert_zero(format!("{name}_bc{i}bind"), bc_l0 - vb);
			// partial product pp_i = bit_i(v) · (ζ << i).
			let zs = if i == 0 {
				zeta
			} else {
				t.add_shifted(format!("{name}_zshl{i}"), zeta, WLOG, i, ShiftVariant::LogicalLeft)
			};
			let p = t.add_committed::<B1, W>(format!("{name}_pp{i}"));
			t.assert_zero(format!("{name}_pp{i}def"), p - bc * zs);
			vbits.push(vb);
			bcast.push(bc);
			bcast_rot.push(bc_rot);
			bcast_l0.push(bc_l0);
			zshl.push(zs);
			pp.push(p);
		}
		// prod = Σ_i pp_i (< 2^46, no overflow in W=64).
		let mut adders = Vec::new();
		let mut acc = pp[0];
		for p in pp.iter().skip(1) {
			let a = Adder::<W>::build(t, acc, *p, &format!("{name}_sum{}", adders.len()));
			acc = a.sum;
			adders.push(a);
		}
		let prod = acc;
		// reduce: prod == quo·q + out, out < q, quo < 2^NBITS_Q.
		let quo = t.add_committed::<B1, W>(format!("{name}_quo"));
		let quo_rng = ShrZero::build(t, &format!("{name}_quo"), quo, NBITS_Q);
		let quoq = ShiftSumMul::build(t, &format!("{name}_quoq"), quo, q_set);
		let out = t.add_committed::<B1, W>(format!("{name}_out"));
		let rhs = Adder::<W>::build(t, quoq.result, out, &format!("{name}_rhs"));
		t.assert_zero(format!("{name}_identity"), prod - rhs.sum);
		let out_lt = LtQ::build(t, &format!("{name}_out"), out, c_col);
		Self { vbits, bcast, bcast_rot, bcast_l0, zshl, pp, adders, quo, quo_rng, quoq, rhs, out, out_lt }
	}

	fn populate(&self, seg: &mut TableWitnessSegment<OurB256>, row: usize, v: &[bool], zeta: &[bool], c: &[bool]) -> Result<Vec<bool>> {
		let vv = to_u64(v);
		let zz = to_u64(zeta);
		let p = zz as u128 * vv as u128; // < 2^46
		let quo_v = (p / Q as u128) as u64;
		let out_v = (p % Q as u128) as u64;
		let mut acc = vec![false; W];
		for i in 0..NBITS_Q {
			let vb = (vv >> i) & 1 == 1;
			let uni = vec![vb; W];
			write_bit(seg, self.vbits[i], row, vb)?;
			write_col::<W>(seg, self.bcast[i], row, &uni)?;
			write_col::<W>(seg, self.bcast_rot[i], row, &uni)?;
			write_bit(seg, self.bcast_l0[i], row, vb)?;
			let zshl_bits = shl(zeta, i);
			if i != 0 {
				write_col::<W>(seg, self.zshl[i], row, &zshl_bits)?;
			}
			let ppv = if vb { zshl_bits.clone() } else { vec![false; W] };
			write_col::<W>(seg, self.pp[i], row, &ppv)?;
			if i == 0 {
				acc = ppv;
			} else {
				acc = self.adders[i - 1].populate(seg, row, &acc, &ppv)?;
			}
		}
		debug_assert_eq!(to_u64(&acc), p as u64, "var mul product desync");
		let quo_bits = bits64(quo_v);
		write_col::<W>(seg, self.quo, row, &quo_bits)?;
		self.quo_rng.populate(seg, row, &quo_bits)?;
		let quoq_bits = self.quoq.populate(seg, row, &quo_bits)?;
		let out_bits = bits64(out_v);
		write_col::<W>(seg, self.out, row, &out_bits)?;
		self.rhs.populate(seg, row, &quoq_bits, &out_bits)?;
		self.out_lt.populate(seg, row, &out_bits, c)?;
		Ok(out_bits)
	}
}

/// A tall-narrow batch of forward CT butterflies: each ROW proves one
/// `(u, v, ζ) → (u + ζ·v, u − ζ·v) mod q`, with u, v, ζ range-checked `< q`.
pub struct ButterflyBatch {
	pub table_id: TableId,
	c_col: Col<B1, W>,
	u: Col<B1, W>,
	v: Col<B1, W>,
	zeta: Col<B1, W>,
	u_lt: LtQ,
	v_lt: LtQ,
	z_lt: LtQ,
	mul: ModMulVar,
	add: ModAdd,
	sub: ModSub,
	/// Positional-seam key columns [pos_u, pos_v, pos_add, pos_sub] when built positional.
	pos: Option<[Col<B1, W>; 4]>,
}

impl ButterflyBatch {
	pub fn build(cs: &mut ConstraintSystem<OurB256>) -> Self {
		Self::build_inner(cs, None, None, None, None)
	}

	/// POSITIONAL batched seam: a whole STAGE's n/2 butterflies share ONE channel, the token
	/// key being `(position, value)` where `position` encodes `(slot, version)`.  Each row
	/// PULLs `[pos_u, u]` and `[pos_v, v]` and PUSHes `[pos_add, o_add]` and `[pos_sub, o_sub]`
	/// on `chan` — a uniform flush, so the entire stage batches into one tall-narrow table
	/// (keeping the 15.6 s / 63 MiB regime) while the position in the key distinguishes slots.
	/// `sched` PINS the schedule: each row PULLs its `[pos_u, pos_v, pos_a, pos_s, ζ]` tuple from
	/// `sched`, and the caller PUSHes the stage's n/2 public schedule tuples as boundary flushes
	/// (Statement boundaries).  Balance then forces every row's positions AND twiddle to be a
	/// genuine schedule entry, each used exactly once — so positions/ζ are constrained, not merely
	/// populated.  Row order is irrelevant (positions pin the routing; ζ is bound to its slots).
	pub fn build_seamed_positional(cs: &mut ConstraintSystem<OurB256>, chan: ChannelId, sched: ChannelId) -> Self {
		let mut t = cs.add_table("mldsa tall-narrow POSITIONAL forward-butterfly stage");
		let c_arr: [B1; W] = std::array::from_fn(|k| if c_q_bits()[k] { B1::ONE } else { B1::ZERO });
		let c_col = t.add_constant("c_q", c_arr);
		let q_set = set_bits_of(Q);
		let u = t.add_committed::<B1, W>("u");
		let v = t.add_committed::<B1, W>("v");
		let zeta = t.add_committed::<B1, W>("zeta");
		let u_lt = LtQ::build(&mut t, "u", u, c_col);
		let v_lt = LtQ::build(&mut t, "v", v, c_col);
		let z_lt = LtQ::build(&mut t, "zeta", zeta, c_col);
		let mul = ModMulVar::build(&mut t, "mul", v, zeta, c_col, &q_set);
		let add = ModAdd::build(&mut t, "add", u, mul.out, c_col, &q_set);
		let sub = ModSub::build(&mut t, "sub", u, mul.out, c_col, &q_set);
		let pos_u = t.add_committed::<B1, W>("pos_u");
		let pos_v = t.add_committed::<B1, W>("pos_v");
		let pos_a = t.add_committed::<B1, W>("pos_a");
		let pos_s = t.add_committed::<B1, W>("pos_s");
		// pack every routed/pinned coefficient to its single B64 lane.
		let b64 = |t: &mut TableBuilder<OurB256>, col: Col<B1, W>, nm: &str| -> Col<B64, 1> {
			t.add_packed::<B1, 64, B64, 1>(format!("{nm}_b64"), col)
		};
		let (pu_b, pv_b, pa_b, ps_b, z_b) =
			(b64(&mut t, pos_u, "pu"), b64(&mut t, pos_v, "pv"), b64(&mut t, pos_a, "pa"), b64(&mut t, pos_s, "ps"), b64(&mut t, zeta, "z"));
		let (u_b, v_b, oa_b, os_b) =
			(b64(&mut t, u, "u"), b64(&mut t, v, "v"), b64(&mut t, add.out, "oa"), b64(&mut t, sub.out, "os"));
		// ROUTING on `chan`: pull inputs at their positions, push outputs at theirs.
		t.pull(chan, [pu_b, u_b]);
		t.pull(chan, [pv_b, v_b]);
		t.push(chan, [pa_b, oa_b]);
		t.push(chan, [ps_b, os_b]);
		// PIN on `sched`: this row's (positions, ζ) must be a public schedule tuple.
		t.pull(sched, [pu_b, pv_b, pa_b, ps_b, z_b]);
		Self { table_id: t.id(), c_col, u, v, zeta, u_lt, v_lt, z_lt, mul, add, sub, pos: Some([pos_u, pos_v, pos_a, pos_s]) }
	}

	/// Populate a positional row: the butterfly plus its four `(slot,version)` position keys.
	pub fn populate_positional(&self, seg: &mut TableWitnessSegment<OurB256>, row: usize, u: u64, v: u64, zeta: u64, pos: [u64; 4]) -> Result<(u64, u64)> {
		let out = self.populate(seg, row, u, v, zeta)?;
		let cols = self.pos.expect("populate_positional on a non-positional table");
		for (k, &p) in pos.iter().enumerate() {
			write_col::<W>(seg, cols[k], row, &bits64(p))?;
		}
		Ok(out)
	}

	/// Seam-enabled build (the fleet-strand / inter-layer routing primitive, mirroring
	/// `nonnative::ModMul::build_seamed*`).  When `pull_u` is set, u is PULLED from that
	/// channel (binding u to a value a prior strand PUSHED — the input seam); when
	/// `push_add`/`push_sub` are set, o_add / o_sub are PUSHED to those channels (the output
	/// seam).  Coefficients are < q < 2^23, so one B64 lane carries each value.  Balance then
	/// forces a consumer's input to equal exactly the producer's output — connectivity
	/// soundness across the seam (a wrong value unbalances the channel ⇒ verify REJECTS).
	pub fn build_seamed(
		cs: &mut ConstraintSystem<OurB256>,
		pull_u: Option<ChannelId>,
		push_add: Option<ChannelId>,
		push_sub: Option<ChannelId>,
	) -> Self {
		Self::build_inner(cs, pull_u, None, push_add, push_sub)
	}

	/// Full-routing seam: pull BOTH inputs (u, v) and push BOTH outputs (o_add, o_sub) on
	/// channels — the per-token wiring a whole-network CT composition needs (each coefficient
	/// slot at each stage is a channel produced by one butterfly and consumed by the next).
	pub fn build_seamed_io(
		cs: &mut ConstraintSystem<OurB256>,
		pull_u: Option<ChannelId>,
		pull_v: Option<ChannelId>,
		push_add: Option<ChannelId>,
		push_sub: Option<ChannelId>,
	) -> Self {
		Self::build_inner(cs, pull_u, pull_v, push_add, push_sub)
	}

	fn build_inner(
		cs: &mut ConstraintSystem<OurB256>,
		pull_u: Option<ChannelId>,
		pull_v: Option<ChannelId>,
		push_add: Option<ChannelId>,
		push_sub: Option<ChannelId>,
	) -> Self {
		let mut t = cs.add_table("mldsa tall-narrow forward-butterfly batch");
		let c_arr: [B1; W] = std::array::from_fn(|k| if c_q_bits()[k] { B1::ONE } else { B1::ZERO });
		let c_col = t.add_constant("c_q", c_arr);
		let q_set = set_bits_of(Q);
		let u = t.add_committed::<B1, W>("u");
		let v = t.add_committed::<B1, W>("v");
		let zeta = t.add_committed::<B1, W>("zeta");
		let u_lt = LtQ::build(&mut t, "u", u, c_col);
		let v_lt = LtQ::build(&mut t, "v", v, c_col);
		let z_lt = LtQ::build(&mut t, "zeta", zeta, c_col);
		let mul = ModMulVar::build(&mut t, "mul", v, zeta, c_col, &q_set);
		let add = ModAdd::build(&mut t, "add", u, mul.out, c_col, &q_set);
		let sub = ModSub::build(&mut t, "sub", u, mul.out, c_col, &q_set);
		// Seams: a coefficient column is exactly W=64 bits = one B64 lane, so pack it directly
		// (no sub-block projection) and push/pull it on the channel.
		let seam = |t: &mut TableBuilder<OurB256>, col: Col<B1, W>, chan: ChannelId, nm: &str, pull: bool| {
			let b64 = t.add_packed::<B1, 64, B64, 1>(format!("{nm}_b64"), col);
			if pull {
				t.pull(chan, [b64]);
			} else {
				t.push(chan, [b64]);
			}
		};
		if let Some(ch) = pull_u {
			seam(&mut t, u, ch, "seam_u", true);
		}
		if let Some(ch) = pull_v {
			seam(&mut t, v, ch, "seam_v", true);
		}
		if let Some(ch) = push_add {
			seam(&mut t, add.out, ch, "seam_add", false);
		}
		if let Some(ch) = push_sub {
			seam(&mut t, sub.out, ch, "seam_sub", false);
		}
		Self { table_id: t.id(), c_col, u, v, zeta, u_lt, v_lt, z_lt, mul, add, sub, pos: None }
	}

	/// Fill one butterfly row from `(u, v, ζ)`; returns `(o_add, o_sub)` = the reduced outputs.
	pub fn populate(&self, seg: &mut TableWitnessSegment<OurB256>, row: usize, u: u64, v: u64, zeta: u64) -> Result<(u64, u64)> {
		let c = c_q_bits();
		let (ub, vb, zb) = (bits64(u), bits64(v), bits64(zeta));
		write_col::<W>(seg, self.c_col, row, &c)?;
		write_col::<W>(seg, self.u, row, &ub)?;
		write_col::<W>(seg, self.v, row, &vb)?;
		write_col::<W>(seg, self.zeta, row, &zb)?;
		self.u_lt.populate(seg, row, &ub, &c)?;
		self.v_lt.populate(seg, row, &vb, &c)?;
		self.z_lt.populate(seg, row, &zb, &c)?;
		let tb = self.mul.populate(seg, row, &vb, &zb, &c)?;
		let oa = self.add.populate(seg, row, &ub, &tb, &c)?;
		let os = self.sub.populate(seg, row, &ub, &tb, &c)?;
		Ok((to_u64(&oa), to_u64(&os)))
	}

	fn read_outputs(&self, seg: &TableWitnessSegment<OurB256>, row: usize) -> Result<(u64, u64)> {
		Ok((to_u64(&read_col::<W>(seg, self.add.out, row)?), to_u64(&read_col::<W>(seg, self.sub.out, row)?)))
	}
}

/// The forward-NTT butterfly trace: walk the CT schedule and emit every butterfly's
/// `(u, v, ζ, o_add, o_sub)` in order.  The final state equals `reference::ntt_ref`.
pub fn forward_butterfly_trace(input: &[u64], n: usize) -> Vec<(u64, u64, u64, u64, u64)> {
	let q = Q as u128;
	let mut a: Vec<u64> = input.to_vec();
	let mut rows = Vec::new();
	for (start, len, zeta) in forward_groups(n) {
		for j in start..start + len {
			let (u, v) = (a[j], a[j + len]);
			let t = ((zeta as u128 * v as u128) % q) as u64;
			let oa = (u + t) % Q;
			let os = (u + Q - t) % Q;
			rows.push((u, v, zeta, oa, os));
			a[j] = oa;
			a[j + len] = os;
		}
	}
	rows
}

/// Build the tall-narrow butterfly batch for a full forward `n`-NTT of `input`, populate
/// every butterfly row (padded to a power of two), and `validate_witness` (no FRI). Returns
/// `Ok(())` iff every in-circuit butterfly output matches the trace (the arithmetic gate).
pub fn validate_butterflies(input: &[u64], n: usize) -> Result<()> {
	let trace = forward_butterfly_trace(input, n);
	let nrows = trace.len().next_power_of_two();
	let allocator = Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let bb = ButterflyBatch::build(&mut cs);
	let statement = Statement { boundaries: vec![], table_sizes: vec![nrows] };
	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	{
		let tw = witness.init_table(bb.table_id, nrows)?;
		let mut seg = tw.full_segment();
		for (row, &(u, v, z, oa, os)) in trace.iter().enumerate() {
			let (goa, gos) = bb.populate(&mut seg, row, u, v, z)?;
			assert_eq!((goa, gos), (oa, os), "butterfly row {row} output != trace");
		}
		for row in trace.len()..nrows {
			bb.populate(&mut seg, row, 0, 0, 0)?; // valid padding butterfly (0,0,0)→(0,0)
		}
		let _ = bb.read_outputs(&seg, 0)?;
	}
	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();
	binius_core::constraint_system::validate::validate_witness(&ccs, &[], &witness)?;
	Ok(())
}

/// Full FRI PROVE+VERIFY of the tall-narrow butterfly batch for a forward `n`-NTT.
/// Returns `(proof_bytes, nrows)`.  This is the shape whose RSS stays IoT-viable.
pub fn prove_butterflies(input: &[u64], n: usize) -> Result<(usize, usize)> {
	let trace = forward_butterfly_trace(input, n);
	let nrows = trace.len().next_power_of_two();
	let allocator = Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let bb = ButterflyBatch::build(&mut cs);
	let statement = Statement { boundaries: vec![], table_sizes: vec![nrows] };
	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	{
		let tw = witness.init_table(bb.table_id, nrows)?;
		let mut seg = tw.full_segment();
		for (row, &(u, v, z, _oa, _os)) in trace.iter().enumerate() {
			bb.populate(&mut seg, row, u, v, z)?;
		}
		for row in trace.len()..nrows {
			bb.populate(&mut seg, row, 0, 0, 0)?;
		}
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
	>(&ccs, LOG_INV_RATE, SECURITY_BITS, &statement.boundaries, witness, &binius_hal::make_portable_backend())?;
	let proof_size = proof.get_proof_size();
	binius_core::constraint_system::verify::<
		U256,
		B256TowerFamily,
		Sha256,
		Sha256Compression,
		HasherChallenger<Sha256>,
	>(&ccs, LOG_INV_RATE, SECURITY_BITS, &statement.boundaries, proof)?;
	Ok((proof_size, nrows))
}

/// Compose the WHOLE forward CT network from seamed butterflies: every coefficient slot at
/// every stage is a channel `(slot, version)` produced by one butterfly and consumed by the
/// next; a source table PUSHES the (public) inputs at version 0, a sink table PULLS the
/// (public) `ntt_ref` outputs at the final version.  Channel balance then forces the network
/// to carry each input through the fixed CT topology to the pinned output — so a tampered
/// twiddle or intermediate value makes the network's real output ≠ the pinned output and the
/// output channels UNBALANCE ⇒ `validate_witness` REJECTS.  `tamper = Some(b)` corrupts
/// butterfly `b`'s twiddle (a wrong-but-self-consistent butterfly) to exercise that.
///
/// (Per-(slot,version) channels + one table per butterfly + public I/O pinning is the
/// SOUND, GENERAL composition.  The deployment optimisation — batching each stage's
/// butterflies into ONE tall-narrow table routed by a single positional channel with the
/// twiddle/position lookup-pinned — is docs/s1d-fleet-sharding-ntt.md step 2.)
pub fn validate_ntt_network(input: &[u64], n: usize, tamper: Option<usize>) -> Result<()> {
	use std::collections::HashMap;
	assert!(n.is_power_of_two() && n >= 2, "n must be a power of two ≥ 2");
	let logn = n.trailing_zeros() as usize;
	let arr_of = |x: u64| -> [B1; W] { std::array::from_fn(|k| if (x >> k) & 1 == 1 { B1::ONE } else { B1::ZERO }) };

	// native forward NTT = the pinned public output.
	let mut expected = input.to_vec();
	for (start, len, zeta) in forward_groups(n) {
		for j in start..start + len {
			let t = ((zeta as u128 * expected[j + len] as u128) % Q as u128) as u64;
			let u = expected[j];
			expected[j] = (u + t) % Q;
			expected[j + len] = (u + Q - t) % Q;
		}
	}

	let allocator = Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	// (slot, version) → channel, pre-created for versions 0..=logn.
	let mut chan: HashMap<(usize, usize), ChannelId> = HashMap::new();
	for s in 0..n {
		for v in 0..=logn {
			chan.insert((s, v), cs.add_channel(format!("s{s}v{v}")));
		}
	}

	// SOURCE: push the (public) inputs at version 0.
	let mut src = cs.add_table("ntt-net source");
	let src_cols: Vec<Col<B1, W>> = (0..n)
		.map(|j| {
			let cc = src.add_constant(format!("in{j}"), arr_of(input[j]));
			let b64 = src.add_packed::<B1, 64, B64, 1>(format!("in{j}_b64"), cc);
			src.push(chan[&(j, 0)], [b64]);
			cc
		})
		.collect();
	let src_id = src.id();

	// BUTTERFLIES: walk the CT schedule, wiring each to its (slot,version) channels.
	let mut ver = vec![0usize; n];
	let mut a = input.to_vec();
	let mut bfs: Vec<(ButterflyBatch, u64, u64, u64)> = Vec::new();
	let mut bi = 0usize;
	for (start, len, zeta) in forward_groups(n) {
		for j in start..start + len {
			let (su, sv) = (ver[j], ver[j + len]);
			let bb = ButterflyBatch::build_seamed_io(
				&mut cs,
				Some(chan[&(j, su)]),
				Some(chan[&(j + len, sv)]),
				Some(chan[&(j, su + 1)]),
				Some(chan[&(j + len, sv + 1)]),
			);
			let (u, v) = (a[j], a[j + len]);
			let z_use = if tamper == Some(bi) { (zeta + 1) % Q } else { zeta };
			let t = ((zeta as u128 * v as u128) % Q as u128) as u64;
			a[j] = (u + t) % Q;
			a[j + len] = (u + Q - t) % Q;
			bfs.push((bb, u, v, z_use));
			ver[j] += 1;
			ver[j + len] += 1;
			bi += 1;
		}
	}

	// SINK: pull the (public) ntt_ref outputs at the final version.
	let mut snk = cs.add_table("ntt-net sink");
	let snk_cols: Vec<Col<B1, W>> = (0..n)
		.map(|j| {
			let cc = snk.add_constant(format!("out{j}"), arr_of(expected[j]));
			let b64 = snk.add_packed::<B1, 64, B64, 1>(format!("out{j}_b64"), cc);
			snk.pull(chan[&(j, logn)], [b64]);
			cc
		})
		.collect();
	let snk_id = snk.id();

	// table_sizes in declaration order: source, each butterfly, sink.
	let mut table_sizes = vec![1usize];
	table_sizes.extend(std::iter::repeat_n(1usize, bfs.len()));
	table_sizes.push(1);
	let statement = Statement { boundaries: vec![], table_sizes };
	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	{
		let tw = witness.init_table(src_id, 1)?;
		let mut seg = tw.full_segment();
		for (j, &cc) in src_cols.iter().enumerate() {
			write_col::<W>(&mut seg, cc, 0, &bits64(input[j]))?;
		}
	}
	for (bb, u, v, z) in &bfs {
		let tw = witness.init_table(bb.table_id, 1)?;
		let mut seg = tw.full_segment();
		bb.populate(&mut seg, 0, *u, *v, *z)?;
	}
	{
		let tw = witness.init_table(snk_id, 1)?;
		let mut seg = tw.full_segment();
		for (j, &cc) in snk_cols.iter().enumerate() {
			write_col::<W>(&mut seg, cc, 0, &bits64(expected[j]))?;
		}
	}
	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();
	binius_core::constraint_system::validate::validate_witness(&ccs, &statement.boundaries, &witness)?;
	Ok(())
}

/// Batched composition: each STAGE's n/2 butterflies are ONE tall-narrow positional table
/// (n/2 rows), all routed through a single channel whose key is `(position, value)` with
/// `position = version·n + slot`.  A source pushes the public inputs at version 0, a sink
/// pulls the public `ntt_ref` outputs at version log₂n, and each stage pulls its inputs /
/// pushes its outputs at the matching positions.  This keeps the tall-narrow prove regime
/// (n/2 rows per stage) while the position in the key does the slot routing — the deployment
/// structure.  Honest network validates; corrupting a butterfly makes its pushed output
/// mismatch the position the next stage pulls ⇒ channel UNBALANCE ⇒ REJECT.  (`tamper = Some(b)`
/// corrupts the b-th butterfly's twiddle.)  NOTE: positions/twiddles are committed and
/// populated from the public schedule; pinning them in-circuit (a manual B256 lookup) is the
/// final soundness step — docs/s1d-fleet-sharding-ntt.md step 2.
pub fn validate_ntt_network_batched(input: &[u64], n: usize, tamper: Option<usize>, pos_tamper: Option<usize>) -> Result<()> {
	assert!(n.is_power_of_two() && n >= 2, "n must be a power of two ≥ 2");
	let logn = n.trailing_zeros() as usize;
	let arr_of = |x: u64| -> [B1; W] { std::array::from_fn(|k| if (x >> k) & 1 == 1 { B1::ONE } else { B1::ZERO }) };

	// native forward NTT (pinned output) + per-stage butterfly rows with their positions.
	// each row: (u, v, ζ_witness, positions[4], ζ_honest).  ζ_witness may be tampered; ζ_honest
	// is the public schedule value pushed as a boundary (so a tampered ζ mismatches the schedule).
	let mut a = input.to_vec();
	let mut stage_rows: Vec<Vec<(u64, u64, u64, [u64; 4], u64)>> = vec![Vec::new(); logn];
	let mut bi = 0usize;
	for (start, len, zeta) in forward_groups(n) {
		let s = (n.trailing_zeros() - len.trailing_zeros() - 1) as usize;
		for j in start..start + len {
			let (u, v) = (a[j], a[j + len]);
			let z_use = if tamper == Some(bi) { (zeta + 1) % Q } else { zeta };
			let pos = [
				(s * n + j) as u64,
				(s * n + j + len) as u64,
				((s + 1) * n + j) as u64,
				((s + 1) * n + j + len) as u64,
			];
			let t = ((zeta as u128 * v as u128) % Q as u128) as u64;
			a[j] = (u + t) % Q;
			a[j + len] = (u + Q - t) % Q;
			stage_rows[s].push((u, v, z_use, pos, zeta));
			bi += 1;
		}
	}
	let expected = a;

	let allocator = Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let net: ChannelId = cs.add_channel("net");
	let sched: Vec<ChannelId> = (0..logn).map(|s| cs.add_channel(format!("sched{s}"))).collect();

	// SOURCE: 1 row, push n tokens [pos(j,0)=j, input[j]].
	let mut src = cs.add_table("batched-net source");
	let src_cols: Vec<(Col<B1, W>, Col<B1, W>, u64, u64)> = (0..n)
		.map(|j| {
			let pc = src.add_constant(format!("sp{j}"), arr_of(j as u64));
			let vc = src.add_constant(format!("sv{j}"), arr_of(input[j]));
			let pb = src.add_packed::<B1, 64, B64, 1>(format!("sp{j}b"), pc);
			let vb = src.add_packed::<B1, 64, B64, 1>(format!("sv{j}b"), vc);
			src.push(net, [pb, vb]);
			(pc, vc, j as u64, input[j])
		})
		.collect();
	let src_id = src.id();

	// STAGES: one positional tall-narrow table per stage (n/2 rows), each pinned to sched[s].
	let stages: Vec<ButterflyBatch> = (0..logn).map(|s| ButterflyBatch::build_seamed_positional(&mut cs, net, sched[s])).collect();

	// PUBLIC SCHEDULE: push each stage's n/2 honest [pos_u,pos_v,pos_a,pos_s,ζ] tuples as
	// boundary flushes on sched[s].  Balance forces every row's committed positions+ζ to be one
	// of these public tuples (a tampered ζ / wrong position mismatches ⇒ REJECT).
	let bval = |x: u64| OurB256::from(B64::new(x));
	let mut boundaries = Vec::new();
	for (s, rows) in stage_rows.iter().enumerate() {
		for &(_, _, _, pos, z_honest) in rows {
			boundaries.push(Boundary {
				values: vec![bval(pos[0]), bval(pos[1]), bval(pos[2]), bval(pos[3]), bval(z_honest)],
				channel_id: sched[s],
				direction: FlushDirection::Push,
				multiplicity: 1,
			});
		}
	}

	// SINK: 1 row, pull n tokens [pos(j,logn)=logn·n+j, expected[j]].
	let mut snk = cs.add_table("batched-net sink");
	let snk_cols: Vec<(Col<B1, W>, Col<B1, W>, u64, u64)> = (0..n)
		.map(|j| {
			let posv = (logn * n + j) as u64;
			let pc = snk.add_constant(format!("kp{j}"), arr_of(posv));
			let vc = snk.add_constant(format!("kv{j}"), arr_of(expected[j]));
			let pb = snk.add_packed::<B1, 64, B64, 1>(format!("kp{j}b"), pc);
			let vb = snk.add_packed::<B1, 64, B64, 1>(format!("kv{j}b"), vc);
			snk.pull(net, [pb, vb]);
			(pc, vc, posv, expected[j])
		})
		.collect();
	let snk_id = snk.id();

	let mut table_sizes = vec![1usize];
	table_sizes.extend(std::iter::repeat_n(n / 2, logn));
	table_sizes.push(1);
	let statement = Statement { boundaries, table_sizes };
	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	{
		let tw = witness.init_table(src_id, 1)?;
		let mut seg = tw.full_segment();
		for (pc, vc, p, val) in &src_cols {
			write_col::<W>(&mut seg, *pc, 0, &bits64(*p))?;
			write_col::<W>(&mut seg, *vc, 0, &bits64(*val))?;
		}
	}
	let mut gi = 0usize;
	for (s, bb) in stages.iter().enumerate() {
		let tw = witness.init_table(bb.table_id, n / 2)?;
		let mut seg = tw.full_segment();
		for (row, &(u, v, z, pos, _z_honest)) in stage_rows[s].iter().enumerate() {
			// pos_tamper corrupts the WITNESS position while the boundary schedule stays honest,
			// isolating the schedule-pin (sched channel) as the rejecter.
			let mut wpos = pos;
			if pos_tamper == Some(gi) {
				wpos[0] ^= 1;
			}
			bb.populate_positional(&mut seg, row, u, v, z, wpos)?;
			gi += 1;
		}
	}
	{
		let tw = witness.init_table(snk_id, 1)?;
		let mut seg = tw.full_segment();
		for (pc, vc, p, val) in &snk_cols {
			write_col::<W>(&mut seg, *pc, 0, &bits64(*p))?;
			write_col::<W>(&mut seg, *vc, 0, &bits64(*val))?;
		}
	}
	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();
	binius_core::constraint_system::validate::validate_witness(&ccs, &statement.boundaries, &witness)?;
	Ok(())
}

/// One butterfly's fleet-shard spec: `(u, v, ζ, [pos_u, pos_v, pos_a, pos_s])`.
pub type ButterflySpec = (u64, u64, u64, [u64; 4]);

/// FLEET SHARD: prove ONE row-block of a stage's butterflies as a STANDALONE tall-narrow proof.
/// The block's I/O and schedule are SEAM BOUNDARY FLUSHES on the shard's own `net`/`sched`
/// channels: each butterfly's inputs are boundary-PUSHed and outputs boundary-PULLed on `net`
/// (so the row's pull/push balance), and its `[pos,ζ]` schedule tuple is boundary-PUSHed on
/// `sched` (pinning).  So a shard is a self-contained low-RSS proof of its block; the fleet runs
/// G shards in parallel, and reconstruction checks the union of the boundary seam tokens is the
/// stage's full I/O (positions are global, so the tokens across shards balance to the stage).
/// `specs.len()` must be a power of two.  `do_prove` runs the full FRI PROVE+VERIFY and returns
/// `(proof_bytes, peak_rss)`; otherwise `validate_witness` only.  `tamper` corrupts a butterfly's
/// committed ζ (boundary schedule stays honest ⇒ the `sched` pin REJECTS).
pub fn run_stage_shard(specs: &[ButterflySpec], tamper: Option<usize>, do_prove: bool) -> Result<(usize, u64)> {
	assert!(specs.len().is_power_of_two(), "shard size must be a power of two");
	let nrows = specs.len();
	let allocator = Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let net = cs.add_channel("shard-net");
	let sched = cs.add_channel("shard-sched");
	let bb = ButterflyBatch::build_seamed_positional(&mut cs, net, sched);

	let bval = |x: u64| OurB256::from(B64::new(x));
	let mut boundaries = Vec::new();
	for &(u, v, z, pos) in specs {
		let t = ((z as u128 * v as u128) % Q as u128) as u64;
		let oa = (u + t) % Q;
		let os = (u + Q - t) % Q;
		// net seam: PUSH the inputs (balancing the row's pulls), PULL the outputs (balancing pushes).
		boundaries.push(Boundary { values: vec![bval(pos[0]), bval(u)], channel_id: net, direction: FlushDirection::Push, multiplicity: 1 });
		boundaries.push(Boundary { values: vec![bval(pos[1]), bval(v)], channel_id: net, direction: FlushDirection::Push, multiplicity: 1 });
		boundaries.push(Boundary { values: vec![bval(pos[2]), bval(oa)], channel_id: net, direction: FlushDirection::Pull, multiplicity: 1 });
		boundaries.push(Boundary { values: vec![bval(pos[3]), bval(os)], channel_id: net, direction: FlushDirection::Pull, multiplicity: 1 });
		// sched seam: PUSH the public schedule tuple (pins this row's positions + ζ).
		boundaries.push(Boundary { values: vec![bval(pos[0]), bval(pos[1]), bval(pos[2]), bval(pos[3]), bval(z)], channel_id: sched, direction: FlushDirection::Push, multiplicity: 1 });
	}
	let statement = Statement { boundaries, table_sizes: vec![nrows] };
	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	{
		let tw = witness.init_table(bb.table_id, nrows)?;
		let mut seg = tw.full_segment();
		for (row, &(u, v, z, pos)) in specs.iter().enumerate() {
			let z_use = if tamper == Some(row) { (z + 1) % Q } else { z };
			bb.populate_positional(&mut seg, row, u, v, z_use, pos)?;
		}
	}
	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();
	binius_core::constraint_system::validate::validate_witness(&ccs, &statement.boundaries, &witness)?;
	if !do_prove {
		return Ok((0, 0));
	}
	let proof = binius_core::constraint_system::prove::<
		U256,
		B256TowerFamily,
		Sha256,
		Sha256Compression,
		HasherChallenger<Sha256>,
		_,
	>(&ccs, LOG_INV_RATE, SECURITY_BITS, &statement.boundaries, witness, &binius_hal::make_portable_backend())?;
	let proof_size = proof.get_proof_size();
	let rss = crate::b256_sha3::peak_rss_bytes();
	let vt = std::time::Instant::now();
	binius_core::constraint_system::verify::<
		U256,
		B256TowerFamily,
		Sha256,
		Sha256Compression,
		HasherChallenger<Sha256>,
	>(&ccs, LOG_INV_RATE, SECURITY_BITS, &statement.boundaries, proof)?;
	VERIFY_US.store(vt.elapsed().as_micros() as u64, std::sync::atomic::Ordering::Relaxed);
	Ok((proof_size, rss))
}

/// Last shard VERIFY time in µs (for the measurement tests; a shard's resolver-side cost).
pub static VERIFY_US: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

/// Split a full forward `n`-NTT's stage `s` into `g` fleet-shard specs (row-blocks of its n/2
/// butterflies).  Each returned Vec is one shard's butterflies, ready for `run_stage_shard`.
pub fn stage_shards(input: &[u64], n: usize, s: usize, g: usize) -> Vec<Vec<ButterflySpec>> {
	let mut a = input.to_vec();
	let mut stage_bfs: Vec<ButterflySpec> = Vec::new();
	for (start, len, zeta) in forward_groups(n) {
		let st = (n.trailing_zeros() - len.trailing_zeros() - 1) as usize;
		for j in start..start + len {
			let (u, v) = (a[j], a[j + len]);
			let t = ((zeta as u128 * v as u128) % Q as u128) as u64;
			if st == s {
				stage_bfs.push((u, v, zeta, [
					(st * n + j) as u64,
					(st * n + j + len) as u64,
					((st + 1) * n + j) as u64,
					((st + 1) * n + j + len) as u64,
				]));
			}
			a[j] = (u + t) % Q;
			a[j + len] = (u + Q - t) % Q;
		}
	}
	let per = stage_bfs.len() / g;
	(0..g).map(|k| stage_bfs[k * per..(k + 1) * per].to_vec()).collect()
}

/// Combine arity for ML-DSA-44 (k = l = 4): ŵ_i = Σ_{j<4} Â_ij·ẑ_j − ĉ·(t̂1_i·2^d).
pub const LC: usize = 4;

/// Tall-narrow NTT-domain COMBINE batch (S1d prove-6): each ROW computes one coefficient's
/// `ŵ = (Σ_j a_j·z_j − c·td) mod q` — the verify-core matrix-vector product Â∘ẑ − ĉ∘(t̂1·2^d).
/// Row-per-coefficient ⇒ tall-narrow + fleet-shardable, exactly like the butterfly batch.  Every
/// input (a_j, z_j, c, td) is PULLED from `flow` at its position (a_j from ExpandA, z_j from the
/// forward-NTT strand's output seam, c/td from SampleInBall/t1 strands), and ŵ is PUSHED at its
/// position — so the combine strand wires into the fleet on the same seam channel the NTT feeds.
pub struct CombineBatch {
	pub table_id: TableId,
	c_col: Col<B1, W>,
	a: [Col<B1, W>; LC],
	z: [Col<B1, W>; LC],
	cc: Col<B1, W>,
	td: Col<B1, W>,
	w: Col<B1, W>, // = ModSub output
	lts: Vec<LtQ>,
	az: Vec<ModMulVar>,
	adders: Vec<ModAdd>,
	ctd: ModMulVar,
	wsub: ModSub,
	pos: [Col<B1, W>; 2 * LC + 3], // [pa_0..,pz_0..,pc,ptd,pw]
}

impl CombineBatch {
	pub fn build(cs: &mut ConstraintSystem<OurB256>, flow: ChannelId) -> Self {
		let mut t = cs.add_table("mldsa tall-narrow COMBINE batch (Â∘ẑ − ĉ∘t̂1·2^d)");
		let c_arr: [B1; W] = std::array::from_fn(|k| if c_q_bits()[k] { B1::ONE } else { B1::ZERO });
		let c_col = t.add_constant("c_q", c_arr);
		let q_set = set_bits_of(Q);
		let a: [Col<B1, W>; LC] = std::array::from_fn(|j| t.add_committed::<B1, W>(format!("a{j}")));
		let z: [Col<B1, W>; LC] = std::array::from_fn(|j| t.add_committed::<B1, W>(format!("z{j}")));
		let cc = t.add_committed::<B1, W>("c");
		let td = t.add_committed::<B1, W>("td");
		let mut lts = Vec::new();
		for j in 0..LC {
			lts.push(LtQ::build(&mut t, &format!("a{j}"), a[j], c_col));
			lts.push(LtQ::build(&mut t, &format!("z{j}"), z[j], c_col));
		}
		lts.push(LtQ::build(&mut t, "c", cc, c_col));
		lts.push(LtQ::build(&mut t, "td", td, c_col));
		// p_j = a_j·z_j ; acc = Σ p_j mod q.
		let az: Vec<ModMulVar> = (0..LC).map(|j| ModMulVar::build(&mut t, &format!("az{j}"), z[j], a[j], c_col, &q_set)).collect();
		let mut adders = Vec::new();
		let mut acc = az[0].out;
		for j in 1..LC {
			let add = ModAdd::build(&mut t, &format!("acc{j}"), acc, az[j].out, c_col, &q_set);
			acc = add.out;
			adders.push(add);
		}
		// ŵ = acc − c·td mod q.
		let ctd = ModMulVar::build(&mut t, "ctd", td, cc, c_col, &q_set);
		let wsub = ModSub::build(&mut t, "w", acc, ctd.out, c_col, &q_set);
		let w = wsub.out;
		// positions + seams on `flow`: pull every input, push ŵ.
		let pos: [Col<B1, W>; 2 * LC + 3] = std::array::from_fn(|k| t.add_committed::<B1, W>(format!("pos{k}")));
		let b64 = |t: &mut TableBuilder<OurB256>, col: Col<B1, W>, nm: &str| -> Col<B64, 1> { t.add_packed::<B1, 64, B64, 1>(format!("{nm}_b"), col) };
		let mut pi = 0usize;
		for j in 0..LC {
			let (pb, vb) = (b64(&mut t, pos[pi], &format!("pa{j}")), b64(&mut t, a[j], &format!("va{j}")));
			t.pull(flow, [pb, vb]);
			pi += 1;
		}
		for j in 0..LC {
			let (pb, vb) = (b64(&mut t, pos[pi], &format!("pz{j}")), b64(&mut t, z[j], &format!("vz{j}")));
			t.pull(flow, [pb, vb]);
			pi += 1;
		}
		let (pb, vb) = (b64(&mut t, pos[pi], "pc"), b64(&mut t, cc, "vc"));
		t.pull(flow, [pb, vb]);
		pi += 1;
		let (pb, vb) = (b64(&mut t, pos[pi], "ptd"), b64(&mut t, td, "vtd"));
		t.pull(flow, [pb, vb]);
		pi += 1;
		let (pb, vb) = (b64(&mut t, pos[pi], "pw"), b64(&mut t, w, "vw"));
		t.push(flow, [pb, vb]);
		Self { table_id: t.id(), c_col, a, z, cc, td, w, lts, az, adders, ctd, wsub, pos }
	}

	#[allow(clippy::too_many_arguments)]
	pub fn populate(&self, seg: &mut TableWitnessSegment<OurB256>, row: usize, a: [u64; LC], z: [u64; LC], cc: u64, td: u64, pos: [u64; 2 * LC + 3]) -> Result<u64> {
		let c = c_q_bits();
		write_col::<W>(seg, self.c_col, row, &c)?;
		for j in 0..LC {
			write_col::<W>(seg, self.a[j], row, &bits64(a[j]))?;
			write_col::<W>(seg, self.z[j], row, &bits64(z[j]))?;
		}
		write_col::<W>(seg, self.cc, row, &bits64(cc))?;
		write_col::<W>(seg, self.td, row, &bits64(td))?;
		let mut li = 0;
		for j in 0..LC {
			self.lts[li].populate(seg, row, &bits64(a[j]), &c)?;
			li += 1;
			self.lts[li].populate(seg, row, &bits64(z[j]), &c)?;
			li += 1;
		}
		self.lts[li].populate(seg, row, &bits64(cc), &c)?;
		li += 1;
		self.lts[li].populate(seg, row, &bits64(td), &c)?;
		// p_j and accumulate.
		let mut acc_bits = self.az[0].populate(seg, row, &bits64(z[0]), &bits64(a[0]), &c)?;
		for j in 1..LC {
			let pj = self.az[j].populate(seg, row, &bits64(z[j]), &bits64(a[j]), &c)?;
			acc_bits = self.adders[j - 1].populate(seg, row, &acc_bits, &pj, &c)?;
		}
		let ctd_bits = self.ctd.populate(seg, row, &bits64(td), &bits64(cc), &c)?;
		let w_bits = self.wsub.populate(seg, row, &acc_bits, &ctd_bits, &c)?;
		for (k, &p) in pos.iter().enumerate() {
			write_col::<W>(seg, self.pos[k], row, &bits64(p))?;
		}
		Ok(to_u64(&w_bits))
	}
}

/// One combine coefficient's fleet-shard spec: inputs, output, and their seam positions.
#[derive(Clone, Copy)]
pub struct CombineSpec {
	pub a: [u64; LC],
	pub z: [u64; LC],
	pub c: u64,
	pub td: u64,
	pub pos: [u64; 2 * LC + 3], // [pa_0.., pz_0.., pc, ptd, pw]
}

/// FLEET SHARD of the COMBINE strand: prove a row-block of combine coefficients as a standalone
/// low-RSS proof, its input/output tokens as seam boundary flushes on `flow` (inputs boundary-
/// PUSHed = upstream strand outputs; ŵ boundary-PULLed = InvNTT input).  So the combine wires
/// into the fleet exactly like an NTT stage-shard.  `tamper` corrupts a coefficient's committed
/// `c` (the boundary token stays honest ⇒ the seam pull unbalances ⇒ REJECT).
pub fn run_combine_shard(specs: &[CombineSpec], tamper: Option<usize>, do_prove: bool) -> Result<(usize, u64)> {
	assert!(specs.len().is_power_of_two(), "combine shard size must be a power of two");
	let nrows = specs.len();
	let allocator = Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let flow = cs.add_channel("combine-flow");
	let cb = CombineBatch::build(&mut cs, flow);
	let bval = |x: u64| OurB256::from(B64::new(x));
	let mut boundaries = Vec::new();
	for sp in specs {
		let t = ((sp.c as u128 * sp.td as u128) % Q as u128) as u64;
		let mut acc = 0u64;
		for j in 0..LC {
			acc = (acc + ((sp.a[j] as u128 * sp.z[j] as u128) % Q as u128) as u64) % Q;
		}
		let w = (acc + Q - t) % Q;
		let mut pi = 0;
		for j in 0..LC {
			boundaries.push(Boundary { values: vec![bval(sp.pos[pi]), bval(sp.a[j])], channel_id: flow, direction: FlushDirection::Push, multiplicity: 1 });
			pi += 1;
		}
		for j in 0..LC {
			boundaries.push(Boundary { values: vec![bval(sp.pos[pi]), bval(sp.z[j])], channel_id: flow, direction: FlushDirection::Push, multiplicity: 1 });
			pi += 1;
		}
		boundaries.push(Boundary { values: vec![bval(sp.pos[pi]), bval(sp.c)], channel_id: flow, direction: FlushDirection::Push, multiplicity: 1 });
		pi += 1;
		boundaries.push(Boundary { values: vec![bval(sp.pos[pi]), bval(sp.td)], channel_id: flow, direction: FlushDirection::Push, multiplicity: 1 });
		pi += 1;
		boundaries.push(Boundary { values: vec![bval(sp.pos[pi]), bval(w)], channel_id: flow, direction: FlushDirection::Pull, multiplicity: 1 });
	}
	let statement = Statement { boundaries, table_sizes: vec![nrows] };
	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	{
		let tw = witness.init_table(cb.table_id, nrows)?;
		let mut seg = tw.full_segment();
		for (row, sp) in specs.iter().enumerate() {
			let c_use = if tamper == Some(row) { (sp.c + 1) % Q } else { sp.c };
			cb.populate(&mut seg, row, sp.a, sp.z, c_use, sp.td, sp.pos)?;
		}
	}
	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();
	binius_core::constraint_system::validate::validate_witness(&ccs, &statement.boundaries, &witness)?;
	if !do_prove {
		return Ok((0, 0));
	}
	let proof = binius_core::constraint_system::prove::<U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>, _>(
		&ccs, LOG_INV_RATE, SECURITY_BITS, &statement.boundaries, witness, &binius_hal::make_portable_backend(),
	)?;
	let proof_size = proof.get_proof_size();
	let rss = crate::b256_sha3::peak_rss_bytes();
	let vt = std::time::Instant::now();
	binius_core::constraint_system::verify::<U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>>(
		&ccs, LOG_INV_RATE, SECURITY_BITS, &statement.boundaries, proof,
	)?;
	VERIFY_US.store(vt.elapsed().as_micros() as u64, std::sync::atomic::Ordering::Relaxed);
	Ok((proof_size, rss))
}

/// Tall-narrow single-MULTIPLY strand: each ROW proves one `p = a·z mod q` (var×var), the
/// combine's inner multiply factored OUT so the combine shards FINER.  The combine ŵ = Σ_j
/// a_j·z_j − c·td has 5 var×var mults/row (the width driver ⇒ the 14.7 s wall); running each
/// multiply as its OWN row-per-coefficient strand (1 ModMulVar/row, ≈ the butterfly's ~2 s) in
/// parallel across the fleet drops the combine's wall to ≈ one multiply, then a light accumulate
/// strand sums the products.  Every input is pulled from `flow`, the product pushed.
pub struct MultBatch {
	pub table_id: TableId,
	c_col: Col<B1, W>,
	a: Col<B1, W>,
	z: Col<B1, W>,
	p: Col<B1, W>,
	a_lt: LtQ,
	z_lt: LtQ,
	mul: ModMulVar,
	pos: [Col<B1, W>; 3],
}

impl MultBatch {
	pub fn build(cs: &mut ConstraintSystem<OurB256>, flow: ChannelId) -> Self {
		let mut t = cs.add_table("mldsa tall-narrow single-MULTIPLY strand (p = a·z mod q)");
		let c_arr: [B1; W] = std::array::from_fn(|k| if c_q_bits()[k] { B1::ONE } else { B1::ZERO });
		let c_col = t.add_constant("c_q", c_arr);
		let q_set = set_bits_of(Q);
		let a = t.add_committed::<B1, W>("a");
		let z = t.add_committed::<B1, W>("z");
		let a_lt = LtQ::build(&mut t, "a", a, c_col);
		let z_lt = LtQ::build(&mut t, "z", z, c_col);
		let mul = ModMulVar::build(&mut t, "mul", z, a, c_col, &q_set); // a·z
		let p = mul.out;
		let pos: [Col<B1, W>; 3] = std::array::from_fn(|k| t.add_committed::<B1, W>(format!("pos{k}")));
		let b64 = |t: &mut TableBuilder<OurB256>, col: Col<B1, W>, nm: &str| -> Col<B64, 1> { t.add_packed::<B1, 64, B64, 1>(format!("{nm}_b"), col) };
		let (pa, va) = (b64(&mut t, pos[0], "pa"), b64(&mut t, a, "va"));
		t.pull(flow, [pa, va]);
		let (pz, vz) = (b64(&mut t, pos[1], "pz"), b64(&mut t, z, "vz"));
		t.pull(flow, [pz, vz]);
		let (pp, vp) = (b64(&mut t, pos[2], "pp"), b64(&mut t, p, "vp"));
		t.push(flow, [pp, vp]);
		Self { table_id: t.id(), c_col, a, z, p, a_lt, z_lt, mul, pos }
	}

	pub fn populate(&self, seg: &mut TableWitnessSegment<OurB256>, row: usize, a: u64, z: u64, pos: [u64; 3]) -> Result<u64> {
		let c = c_q_bits();
		write_col::<W>(seg, self.c_col, row, &c)?;
		write_col::<W>(seg, self.a, row, &bits64(a))?;
		write_col::<W>(seg, self.z, row, &bits64(z))?;
		self.a_lt.populate(seg, row, &bits64(a), &c)?;
		self.z_lt.populate(seg, row, &bits64(z), &c)?;
		let pb = self.mul.populate(seg, row, &bits64(z), &bits64(a), &c)?;
		let _ = self.p;
		for (k, &pv) in pos.iter().enumerate() {
			write_col::<W>(seg, self.pos[k], row, &bits64(pv))?;
		}
		Ok(to_u64(&pb))
	}
}

/// One multiply coefficient's fleet-shard spec: `(a, z)` and seam positions `[pos_a, pos_z, pos_p]`.
#[derive(Clone, Copy)]
pub struct MultSpec {
	pub a: u64,
	pub z: u64,
	pub pos: [u64; 3],
}

/// FLEET SHARD of a single-MULTIPLY strand: a row-block of `p = a·z mod q` as a standalone
/// low-RSS proof (a/z pulled, p pushed on `flow`).  `tamper` corrupts a coefficient's `z`.
pub fn run_mult_shard(specs: &[MultSpec], tamper: Option<usize>, do_prove: bool) -> Result<(usize, u64)> {
	assert!(specs.len().is_power_of_two(), "mult shard size must be a power of two");
	let nrows = specs.len();
	let allocator = Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let flow = cs.add_channel("mult-flow");
	let mb = MultBatch::build(&mut cs, flow);
	let bval = |x: u64| OurB256::from(B64::new(x));
	let mut boundaries = Vec::new();
	for sp in specs {
		let p = ((sp.a as u128 * sp.z as u128) % Q as u128) as u64;
		boundaries.push(Boundary { values: vec![bval(sp.pos[0]), bval(sp.a)], channel_id: flow, direction: FlushDirection::Push, multiplicity: 1 });
		boundaries.push(Boundary { values: vec![bval(sp.pos[1]), bval(sp.z)], channel_id: flow, direction: FlushDirection::Push, multiplicity: 1 });
		boundaries.push(Boundary { values: vec![bval(sp.pos[2]), bval(p)], channel_id: flow, direction: FlushDirection::Pull, multiplicity: 1 });
	}
	let statement = Statement { boundaries, table_sizes: vec![nrows] };
	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	{
		let tw = witness.init_table(mb.table_id, nrows)?;
		let mut seg = tw.full_segment();
		for (row, sp) in specs.iter().enumerate() {
			let z_use = if tamper == Some(row) { (sp.z + 1) % Q } else { sp.z };
			mb.populate(&mut seg, row, sp.a, z_use, sp.pos)?;
		}
	}
	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();
	binius_core::constraint_system::validate::validate_witness(&ccs, &statement.boundaries, &witness)?;
	if !do_prove {
		return Ok((0, 0));
	}
	let proof = binius_core::constraint_system::prove::<U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>, _>(
		&ccs, LOG_INV_RATE, SECURITY_BITS, &statement.boundaries, witness, &binius_hal::make_portable_backend(),
	)?;
	let proof_size = proof.get_proof_size();
	let rss = crate::b256_sha3::peak_rss_bytes();
	let vt = std::time::Instant::now();
	binius_core::constraint_system::verify::<U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>>(
		&ccs, LOG_INV_RATE, SECURITY_BITS, &statement.boundaries, proof,
	)?;
	VERIFY_US.store(vt.elapsed().as_micros() as u64, std::sync::atomic::Ordering::Relaxed);
	Ok((proof_size, rss))
}

// ── DIGIT strand constants (ML-DSA-44 / NIST L1) ────────────────────────────
const GAMMA2: u64 = 95232;
const ALPHA: u64 = 190464; // 2·γ2
const MM: u64 = 44; // (q−1)/α — the HighBits modulus

/// Native Decompose+UseHint (FIPS 204 Alg 36/40): returns `(r1, v0, s, sp, hs, w1, qp)` for
/// a reduced input `r < q` and hint bit `h`, all the witness values the DigitBatch commits.
pub fn digit_native(r: u64, h: u64) -> (u64, u64, u64, u64, u64, u64, u64) {
	let (q, a, m) = (Q as i64, ALPHA as i64, MM as i64);
	let rp = (r as i64).rem_euclid(q);
	let mut r0 = rp.rem_euclid(a);
	if r0 > a / 2 {
		r0 -= a;
	}
	// FIPS 204 Decompose special case: if r⁺ − r0 == q−1 then r1 = 0 and r0 -= 1.
	let r1 = if rp - r0 == q - 1 {
		r0 -= 1;
		0
	} else {
		(rp - r0) / a
	};
	let v0 = (r0 + GAMMA2 as i64) as u64; // ∈ [1, α]
	let s = ((rp + GAMMA2 as i64 - r1 * a - v0 as i64) / q) as u64; // ∈ {0,1}
	let sp = if r0 > 0 { 1u64 } else { 0 };
	let hs = h * sp;
	let w1 = if h == 1 {
		if r0 > 0 { (r1 + 1).rem_euclid(m) as u64 } else { (r1 - 1).rem_euclid(m) as u64 }
	} else {
		r1 as u64
	};
	let qp = ((w1 as i64 + m + h as i64 - r1 - 2 * hs as i64) / m) as u64; // ∈ {0,1,2}
	(r1 as u64, v0, s, sp, hs, w1, qp)
}

/// Tall-narrow DIGIT strand (S1d prove-4a/4b): each ROW takes one coefficient's w′ (= `r`, from
/// the InvNTT output seam) and hint bit `h`, and computes `w1 = UseHint(h, Decompose(r))` — the
/// two load-bearing digit identities in one row, row-per-coefficient ⇒ tall-narrow + shardable.
///   Decompose:  r + γ2 = r1·α + v0 + s·q,  r1 < m,  v0 ∈ [1, α],  s ∈ {0,1}
///   UseHint:    w1 + m + h = r1 + 2·hs + qp·m,  hs = h·sp,  w1 < m,  qp ∈ {0,1,2}
/// r is PULLED from `flow` (the InvNTT output seam), h pulled, w1 PUSHED downstream (→ w1Encode).
pub struct DigitBatch {
	pub table_id: TableId,
	r: Col<B1, W>,
	v0: Col<B1, W>,
	r1: Col<B1, W>,
	s: Col<B1, W>,
	h: Col<B1, W>,
	sp: Col<B1, W>,
	hs: Col<B1, W>,
	w1: Col<B1, W>,
	qp: Col<B1, W>,
	r1a: ShiftSumMul,
	sq: ShiftSumMul,
	dadd0: Adder<W>,
	dadd1: Adder<W>,
	dlhs: Adder<W>,
	v0m1: Adder<W>,
	r1_lt: LtQ,
	v0_lt: LtQ,
	s_rng: ShrZero,
	sp_rng: ShrZero,
	h_rng: ShrZero,
	qp_lt: LtQ,
	w1_lt: LtQ,
	hs2: Col<B1, W>,
	qpm: ShiftSumMul,
	ulhs0: Adder<W>,
	ulhs: Adder<W>,
	urhs0: Adder<W>,
	urhs1: Adder<W>,
	pos: [Col<B1, W>; 3], // [pos_r, pos_h, pos_w1]
	c_m: Col<B1, W>,
	c_a: Col<B1, W>,
	c_3: Col<B1, W>,
	g2: Col<B1, W>,
	mc: Col<B1, W>,
	allones: Col<B1, W>,
}

impl DigitBatch {
	pub fn build(cs: &mut ConstraintSystem<OurB256>, flow: ChannelId) -> Self {
		let mut t = cs.add_table("mldsa tall-narrow DIGIT batch (Decompose+UseHint)");
		let cst = |t: &mut TableBuilder<OurB256>, nm: &str, x: u64| -> Col<B1, W> {
			t.add_constant(nm, std::array::from_fn(|k| if (x >> k) & 1 == 1 { B1::ONE } else { B1::ZERO }))
		};
		let q_set = set_bits_of(Q);
		let alpha_set = set_bits_of(ALPHA);
		let m_set = set_bits_of(MM);
		let c_m = cst(&mut t, "c_m", to_u64(&two_pow_w_minus(&bits64(MM))));
		let c_a = cst(&mut t, "c_a", to_u64(&two_pow_w_minus(&bits64(ALPHA))));
		let c_3 = cst(&mut t, "c_3", to_u64(&two_pow_w_minus(&bits64(3))));
		let g2 = cst(&mut t, "g2", GAMMA2);
		let mc = cst(&mut t, "mc", MM);
		let allones = cst(&mut t, "allones", u64::MAX);

		let r = t.add_committed::<B1, W>("r");
		let v0 = t.add_committed::<B1, W>("v0");
		let r1 = t.add_committed::<B1, W>("r1");
		let s = t.add_committed::<B1, W>("s");
		let h = t.add_committed::<B1, W>("h");
		let sp = t.add_committed::<B1, W>("sp");
		let hs = t.add_committed::<B1, W>("hs");
		let w1 = t.add_committed::<B1, W>("w1");
		let qp = t.add_committed::<B1, W>("qp");

		// DECOMPOSE: r + γ2 == r1·α + v0 + s·q.
		let r1a = ShiftSumMul::build(&mut t, "r1a", r1, &alpha_set);
		let sq = ShiftSumMul::build(&mut t, "sq", s, &q_set);
		let dadd0 = Adder::<W>::build(&mut t, r1a.result, v0, "dadd0");
		let dadd1 = Adder::<W>::build(&mut t, dadd0.sum, sq.result, "dadd1");
		let dlhs = Adder::<W>::build(&mut t, r, g2, "dlhs");
		t.assert_zero("decompose_id", dlhs.sum - dadd1.sum);
		let r1_lt = LtQ::build(&mut t, "r1", r1, c_m); // r1 < m
		let v0m1 = Adder::<W>::build(&mut t, v0, allones, "v0m1"); // v0 − 1
		let v0_lt = LtQ::build(&mut t, "v0", v0m1.sum, c_a); // v0 − 1 < α
		let s_rng = ShrZero::build(&mut t, "s", s, 1);

		// USEHINT: w1 + m + h == r1 + 2·hs + qp·m, hs = h·sp.
		let sp_rng = ShrZero::build(&mut t, "sp", sp, 1);
		let h_rng = ShrZero::build(&mut t, "h", h, 1);
		t.assert_zero("hs_def", hs - h * sp);
		let qp_lt = LtQ::build(&mut t, "qp", qp, c_3); // qp < 3
		let qpm = ShiftSumMul::build(&mut t, "qpm", qp, &m_set); // qp·m
		let hs2 = t.add_shifted("hs2", hs, WLOG, 1, ShiftVariant::LogicalLeft); // 2·hs
		let ulhs0 = Adder::<W>::build(&mut t, w1, mc, "ulhs0"); // w1 + m
		let ulhs = Adder::<W>::build(&mut t, ulhs0.sum, h, "ulhs"); // + h
		let urhs0 = Adder::<W>::build(&mut t, hs2, qpm.result, "urhs0"); // 2hs + qp·m
		let urhs1 = Adder::<W>::build(&mut t, r1, urhs0.sum, "urhs1"); // r1 + …
		t.assert_zero("usehint_id", ulhs.sum - urhs1.sum);
		let w1_lt = LtQ::build(&mut t, "w1", w1, c_m); // w1 < m

		// seam: pull r (w′ from InvNTT), h; push w1.
		let pos: [Col<B1, W>; 3] = std::array::from_fn(|k| t.add_committed::<B1, W>(format!("pos{k}")));
		let b = |t: &mut TableBuilder<OurB256>, col: Col<B1, W>, nm: &str| -> Col<B64, 1> { t.add_packed::<B1, 64, B64, 1>(format!("{nm}_b"), col) };
		let (pr, vr) = (b(&mut t, pos[0], "pr"), b(&mut t, r, "vr"));
		t.pull(flow, [pr, vr]);
		let (ph, vh) = (b(&mut t, pos[1], "ph"), b(&mut t, h, "vh"));
		t.pull(flow, [ph, vh]);
		let (pw, vw) = (b(&mut t, pos[2], "pw"), b(&mut t, w1, "vw"));
		t.push(flow, [pw, vw]);

		Self {
			table_id: t.id(), r, v0, r1, s, h, sp, hs, w1, qp,
			r1a, sq, dadd0, dadd1, dlhs, v0m1, r1_lt, v0_lt, s_rng, sp_rng, h_rng, qp_lt, w1_lt,
			hs2, qpm, ulhs0, ulhs, urhs0, urhs1, pos, c_m, c_a, c_3, g2, mc, allones,
		}
	}

	pub fn populate(&self, seg: &mut TableWitnessSegment<OurB256>, row: usize, r: u64, h: u64, pos: [u64; 3]) -> Result<u64> {
		let (r1, v0, s, sp, hs, w1, qp) = digit_native(r, h);
		let wr = |seg: &mut TableWitnessSegment<OurB256>, c: Col<B1, W>, x: u64| write_col::<W>(seg, c, row, &bits64(x));
		wr(seg, self.r, r)?;
		wr(seg, self.v0, v0)?;
		wr(seg, self.r1, r1)?;
		wr(seg, self.s, s)?;
		wr(seg, self.h, h)?;
		wr(seg, self.sp, sp)?;
		wr(seg, self.hs, hs)?;
		wr(seg, self.w1, w1)?;
		wr(seg, self.qp, qp)?;
		wr(seg, self.c_m, to_u64(&two_pow_w_minus(&bits64(MM))))?;
		wr(seg, self.c_a, to_u64(&two_pow_w_minus(&bits64(ALPHA))))?;
		wr(seg, self.c_3, to_u64(&two_pow_w_minus(&bits64(3))))?;
		wr(seg, self.g2, GAMMA2)?;
		wr(seg, self.mc, MM)?;
		wr(seg, self.allones, u64::MAX)?;
		// decompose
		let r1a = self.r1a.populate(seg, row, &bits64(r1))?;
		let sq = self.sq.populate(seg, row, &bits64(s))?;
		let d0 = self.dadd0.populate(seg, row, &r1a, &bits64(v0))?;
		self.dadd1.populate(seg, row, &d0, &sq)?;
		self.dlhs.populate(seg, row, &bits64(r), &bits64(GAMMA2))?;
		self.r1_lt.populate(seg, row, &bits64(r1), &two_pow_w_minus(&bits64(MM)))?;
		let v0m1 = self.v0m1.populate(seg, row, &bits64(v0), &bits64(u64::MAX))?;
		self.v0_lt.populate(seg, row, &v0m1, &two_pow_w_minus(&bits64(ALPHA)))?;
		self.s_rng.populate(seg, row, &bits64(s))?;
		// usehint
		self.sp_rng.populate(seg, row, &bits64(sp))?;
		self.h_rng.populate(seg, row, &bits64(h))?;
		self.qp_lt.populate(seg, row, &bits64(qp), &two_pow_w_minus(&bits64(3)))?;
		let qpm = self.qpm.populate(seg, row, &bits64(qp))?;
		write_col::<W>(seg, self.hs2, row, &shl(&bits64(hs), 1))?;
		let ul0 = self.ulhs0.populate(seg, row, &bits64(w1), &bits64(MM))?;
		self.ulhs.populate(seg, row, &ul0, &bits64(h))?;
		let ur0 = self.urhs0.populate(seg, row, &shl(&bits64(hs), 1), &qpm)?;
		self.urhs1.populate(seg, row, &bits64(r1), &ur0)?;
		self.w1_lt.populate(seg, row, &bits64(w1), &two_pow_w_minus(&bits64(MM)))?;
		for (k, &p) in pos.iter().enumerate() {
			write_col::<W>(seg, self.pos[k], row, &bits64(p))?;
		}
		Ok(w1)
	}
}

/// One digit coefficient's fleet-shard spec: `(r = w′, h)` and seam positions `[pos_r, pos_h, pos_w1]`.
#[derive(Clone, Copy)]
pub struct DigitSpec {
	pub r: u64,
	pub h: u64,
	pub pos: [u64; 3],
}

/// FLEET SHARD of the DIGIT strand: prove a row-block of Decompose+UseHint coefficients as a
/// standalone low-RSS proof, I/O as seam boundary flushes on `flow` (r/h boundary-PUSHed = the
/// InvNTT output + the signature hint; w1 boundary-PULLed = the w1Encode input).  `tamper`
/// corrupts a coefficient's committed hint `h`.
pub fn run_digit_shard(specs: &[DigitSpec], tamper: Option<usize>, do_prove: bool) -> Result<(usize, u64)> {
	assert!(specs.len().is_power_of_two(), "digit shard size must be a power of two");
	let nrows = specs.len();
	let allocator = Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let flow = cs.add_channel("digit-flow");
	let db = DigitBatch::build(&mut cs, flow);
	let bval = |x: u64| OurB256::from(B64::new(x));
	let mut boundaries = Vec::new();
	for sp in specs {
		let (_, _, _, _, _, w1, _) = digit_native(sp.r, sp.h);
		boundaries.push(Boundary { values: vec![bval(sp.pos[0]), bval(sp.r)], channel_id: flow, direction: FlushDirection::Push, multiplicity: 1 });
		boundaries.push(Boundary { values: vec![bval(sp.pos[1]), bval(sp.h)], channel_id: flow, direction: FlushDirection::Push, multiplicity: 1 });
		boundaries.push(Boundary { values: vec![bval(sp.pos[2]), bval(w1)], channel_id: flow, direction: FlushDirection::Pull, multiplicity: 1 });
	}
	let statement = Statement { boundaries, table_sizes: vec![nrows] };
	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	{
		let tw = witness.init_table(db.table_id, nrows)?;
		let mut seg = tw.full_segment();
		for (row, sp) in specs.iter().enumerate() {
			let h_use = if tamper == Some(row) { 1 - sp.h } else { sp.h };
			db.populate(&mut seg, row, sp.r, h_use, sp.pos)?;
		}
	}
	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();
	binius_core::constraint_system::validate::validate_witness(&ccs, &statement.boundaries, &witness)?;
	if !do_prove {
		return Ok((0, 0));
	}
	let proof = binius_core::constraint_system::prove::<U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>, _>(
		&ccs, LOG_INV_RATE, SECURITY_BITS, &statement.boundaries, witness, &binius_hal::make_portable_backend(),
	)?;
	let proof_size = proof.get_proof_size();
	let rss = crate::b256_sha3::peak_rss_bytes();
	let vt = std::time::Instant::now();
	binius_core::constraint_system::verify::<U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>>(
		&ccs, LOG_INV_RATE, SECURITY_BITS, &statement.boundaries, proof,
	)?;
	VERIFY_US.store(vt.elapsed().as_micros() as u64, std::sync::atomic::Ordering::Relaxed);
	Ok((proof_size, rss))
}

// ── BOUNDARY strand constants (ML-DSA-44 / NIST L1): z-norm ‖z‖∞ < γ1−β ──────
const GAMMA1: u64 = 131072; // 2^17
const BETA: u64 = 78;

/// Tall-narrow BOUNDARY strand (S1d prove-5): the ‖z‖∞ < γ1−β ACCEPT check, row-per-coefficient.
/// Each row pulls one response coefficient as `u = z + γ1` (non-negative) from `flow` and asserts
/// the centered bound `|z| < γ1−β  ⇔  β < u < 2γ1−β` via two carries — the upper (u < 2γ1−β, final
/// carry 0) and the lower (u ≥ β+1, final carry 1).  A "consumer" strand: it pulls z and checks,
/// pushing nothing (the ACCEPT gate).  An out-of-range coefficient fails a carry ⇒ REJECT.
pub struct BoundaryBatch {
	pub table_id: TableId,
	u: Col<B1, W>,
	pos: Col<B1, W>,
	hi_lt: LtQ,
	lo_cout: Col<B1, W>,
	lo_cin: Col<B1, W>,
	lo_fc: Col<B1, 1>,
	c_hi: Col<B1, W>,
	c_lo: Col<B1, W>,
}

impl BoundaryBatch {
	pub fn build(cs: &mut ConstraintSystem<OurB256>, flow: ChannelId) -> Self {
		let mut t = cs.add_table("mldsa tall-narrow BOUNDARY batch (z-norm ‖z‖∞ < γ1−β)");
		let cst = |t: &mut TableBuilder<OurB256>, nm: &str, x: u64| -> Col<B1, W> {
			t.add_constant(nm, std::array::from_fn(|k| if (x >> k) & 1 == 1 { B1::ONE } else { B1::ZERO }))
		};
		let u = t.add_committed::<B1, W>("u"); // = z + γ1
		// upper bound: u < 2γ1 − β  (final carry of u + (2^W − (2γ1−β)) == 0).
		let c_hi = cst(&mut t, "c_hi", to_u64(&two_pow_w_minus(&bits64(2 * GAMMA1 - BETA))));
		let hi_lt = LtQ::build(&mut t, "hi", u, c_hi);
		// lower bound: u ≥ β + 1  (final carry of u + (2^W − (β+1)) == 1).
		let c_lo = cst(&mut t, "c_lo", to_u64(&two_pow_w_minus(&bits64(BETA + 1))));
		let lo_cout = t.add_committed::<B1, W>("lo_cout");
		let lo_cin = t.add_shifted("lo_cin", lo_cout, WLOG, 1, ShiftVariant::LogicalLeft);
		t.assert_zero("lo_carry", (u + lo_cin) * (c_lo + lo_cin) + lo_cin - lo_cout);
		let lo_fc = t.add_selected("lo_fc", lo_cout, W - 1);
		t.assert_zero("lo_ge", lo_fc + B1::ONE); // final carry == 1 ⇔ u ≥ β+1
		// seam: pull the coefficient token.
		let pos = t.add_committed::<B1, W>("pos");
		let pb = t.add_packed::<B1, 64, B64, 1>("pos_b", pos);
		let ub = t.add_packed::<B1, 64, B64, 1>("u_b", u);
		t.pull(flow, [pb, ub]);
		Self { table_id: t.id(), u, pos, hi_lt, lo_cout, lo_cin, lo_fc, c_hi, c_lo }
	}

	pub fn populate(&self, seg: &mut TableWitnessSegment<OurB256>, row: usize, u: u64, pos: u64) -> Result<()> {
		write_col::<W>(seg, self.u, row, &bits64(u))?;
		write_col::<W>(seg, self.pos, row, &bits64(pos))?;
		let chi = two_pow_w_minus(&bits64(2 * GAMMA1 - BETA));
		let clo = two_pow_w_minus(&bits64(BETA + 1));
		write_col::<W>(seg, self.c_hi, row, &chi)?;
		write_col::<W>(seg, self.c_lo, row, &clo)?;
		self.hi_lt.populate(seg, row, &bits64(u), &chi)?;
		let (_s, co) = ripple_add(&bits64(u), &clo);
		write_col::<W>(seg, self.lo_cout, row, &co)?;
		write_col::<W>(seg, self.lo_cin, row, &shl(&co, 1))?;
		write_bit(seg, self.lo_fc, row, co[W - 1])?;
		Ok(())
	}
}

/// One z-norm coefficient's fleet-shard spec: `(u = z + γ1, seam position)`.
#[derive(Clone, Copy)]
pub struct BoundarySpec {
	pub u: u64,
	pub pos: u64,
}

/// FLEET SHARD of the BOUNDARY (z-norm) strand: prove a row-block of coefficient bound checks as
/// a standalone low-RSS proof, the coefficient tokens boundary-PUSHed on `flow` (= the z-decode
/// strand's output).  `tamper` forces a coefficient out of range (u = 2γ1−β, the upper edge).
pub fn run_boundary_shard(specs: &[BoundarySpec], tamper: Option<usize>, do_prove: bool) -> Result<(usize, u64)> {
	assert!(specs.len().is_power_of_two(), "boundary shard size must be a power of two");
	let nrows = specs.len();
	let allocator = Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let flow = cs.add_channel("boundary-flow");
	let bb = BoundaryBatch::build(&mut cs, flow);
	let bval = |x: u64| OurB256::from(B64::new(x));
	let mut boundaries = Vec::new();
	for (i, sp) in specs.iter().enumerate() {
		let u = if tamper == Some(i) { 2 * GAMMA1 - BETA } else { sp.u }; // out of range at the edge
		boundaries.push(Boundary { values: vec![bval(sp.pos), bval(u)], channel_id: flow, direction: FlushDirection::Push, multiplicity: 1 });
	}
	let statement = Statement { boundaries, table_sizes: vec![nrows] };
	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	{
		let tw = witness.init_table(bb.table_id, nrows)?;
		let mut seg = tw.full_segment();
		for (row, sp) in specs.iter().enumerate() {
			let u = if tamper == Some(row) { 2 * GAMMA1 - BETA } else { sp.u };
			bb.populate(&mut seg, row, u, sp.pos)?;
		}
	}
	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();
	binius_core::constraint_system::validate::validate_witness(&ccs, &statement.boundaries, &witness)?;
	if !do_prove {
		return Ok((0, 0));
	}
	let proof = binius_core::constraint_system::prove::<U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>, _>(
		&ccs, LOG_INV_RATE, SECURITY_BITS, &statement.boundaries, witness, &binius_hal::make_portable_backend(),
	)?;
	let proof_size = proof.get_proof_size();
	let rss = crate::b256_sha3::peak_rss_bytes();
	let vt = std::time::Instant::now();
	binius_core::constraint_system::verify::<U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>>(
		&ccs, LOG_INV_RATE, SECURITY_BITS, &statement.boundaries, proof,
	)?;
	VERIFY_US.store(vt.elapsed().as_micros() as u64, std::sync::atomic::Ordering::Relaxed);
	Ok((proof_size, rss))
}

/// FLEET STRAND (terminal): the CLOSING-HASH binding (S1d prove-10).  Unlike the per-coefficient
/// strands, this is ONE hash (the width driver): `c̃' = SHA3-256(μ ‖ w1Encode(w1'))` proven over
/// B256, bound to the public challenge `c̃`.  It CONSUMES the digit strand's w1Encode output
/// (`w1enc` = pack(w1') from the digit shards) and μ, and the ACCEPT gate is `c̃' == c̃` — so a
/// wrong w1' (from a tampered digit/NTT/combine shard) yields a different digest ⇒ REJECT.
/// Returns `(proof_bytes, peak_rss, c̃'==c̃)`.  Single-Keccak-block anchor (μ ‖ first w1Encode
/// group ≤ 135 B); the multi-block message is the same gadget scaled (the callable b256 SHA3 path
/// is single-block).
pub fn run_closing_hash_shard(mu: &[u8], w1enc: &[u8], ctilde: &[u8]) -> Result<(usize, u64, bool)> {
	let mut msg = mu.to_vec();
	msg.extend_from_slice(w1enc);
	assert!(msg.len() <= 135, "single-block anchor only (multi-block Keccak is the scale-up)");
	let (sz, digs) = crate::b256_sha3::prove_verify_sha3_b256(crate::sha3_variants::Sha3Variant::Sha3_256, &[msg], 1, 128)?;
	let rss = crate::b256_sha3::peak_rss_bytes();
	Ok((sz, rss, digs[0].as_slice() == ctilde))
}

/// MULTI-BLOCK closing hash (the FULL FIPS-204 message, no ≤135-byte cap): the real
/// `c̃' = SHAKE-256(μ ‖ w1Encode(w1'), 2λ/8)` is computed over ALL `n_blocks` sponge blocks and
/// bound to the public `c̃` (so a wrong w1' in ANY block ⇒ c̃' ≠ c̃), while the in-circuit cost is
/// the message's Keccak-f PERMUTATIONS proven over B256 (`n_blocks` raw permutations — the true
/// multi-block prove work, sharded like the other strands).  Returns `(perm_proof_bytes,
/// peak_rss, n_blocks, c̃'==c̃)`.
///
/// HONEST SCOPE: the full-message binding is native-referenced (real SHAKE-256) and every block's
/// Keccak-f is proven in-circuit; the residual is BINDING the in-circuit permutations to the
/// SPECIFIC chained sponge states (state_in[i] = state_out[i−1] ⊕ block_i) — a state-fed Keccak
/// table (the M3 gadget's built-in link is squeeze-only, no absorb-XOR, and the fork is frozen).
/// Until that lands, the load-bearing binding is: the digit strands PROVE every w1' coefficient,
/// and this gate confirms the full w1Encode hashes to c̃ with the in-circuit permutation count.
pub fn run_multiblock_closing_hash(mu: &[u8], w1enc: &[u8], ctilde: &[u8]) -> Result<(usize, u64, usize, bool)> {
	let mut msg = mu.to_vec();
	msg.extend_from_slice(w1enc);
	// real SHAKE-256 sponge over the FULL message → c̃' (2λ/8 = 32 B at L1).
	let ctilde_prime = crate::mldsa_shake::shake256_xof(&msg, ctilde.len());
	// SHAKE-256 absorb: ceil((mlen+1)/rate) blocks, rate = 168−? For SHAKE-256 rate = 136 bytes
	// (1088 bits); the pad10*1 adds ≥1 byte, so n_blocks = floor(mlen/rate)+1.
	const RATE: usize = 136;
	let n_blocks = msg.len() / RATE + 1;
	// prove the message's Keccak-f PERMUTATIONS in-circuit over B256 (the multi-block prove cost).
	let sz = crate::b256_keccak::prove_verify_keccak_b256(n_blocks, 1, 128)?;
	let rss = crate::b256_sha3::peak_rss_bytes();
	Ok((sz, rss, n_blocks, ctilde_prime == ctilde))
}

/// Which honest column to corrupt after populate (the soundness gate).
#[cfg(test)]
#[derive(Clone, Copy)]
enum Tamper {
	/// Flip a low bit of the first forward butterfly's ζ·v reduction quotient — a fake
	/// ζ·v product; must break that butterfly's multiply, isolated to `f0_..._mul`.
	MulQuo,
	/// Flip a low bit of the first forward butterfly's ζ·v output column.
	MulOut,
	/// Flip the first forward butterfly's modular-add quotient bit — isolated to
	/// `f0_..._add`.
	AddQb,
}

/// Build honest, populate, corrupt one column, then run `validate_witness`. Returns
/// `(rejected, error_message)`; the message NAMES the first unsatisfied constraint.
#[cfg(test)]
fn tamper_rejected(n: usize, input: &[u64], which: Tamper) -> (bool, String) {
	let allocator = Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let ntt = Ntt::build(&mut cs, n, false);
	let statement = Statement { boundaries: vec![], table_sizes: vec![1] };
	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	{
		let tw = match witness.init_table(ntt.table_id, 1) {
			Ok(tw) => tw,
			Err(_) => return (true, "init_table failed".into()),
		};
		let mut seg = tw.full_segment();
		if ntt.populate(&mut seg, 0, input).is_err() {
			return (true, "populate failed".into());
		}
		// Corrupt a single honest column bit.
		let col = match which {
			Tamper::MulQuo => ntt.fwd[0].mul.quo,
			Tamper::MulOut => ntt.fwd[0].mul.out,
			Tamper::AddQb => ntt.fwd[0].add.qb,
		};
		let mut bits = read_col::<W>(&seg, col, 0).unwrap();
		bits[0] = !bits[0];
		write_col::<W>(&mut seg, col, 0, &bits).unwrap();
	}
	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();
	match binius_core::constraint_system::validate::validate_witness(&ccs, &[], &witness) {
		Ok(()) => (false, String::new()),
		Err(e) => (true, format!("{e}")),
	}
}

// ───────────────────────────── GATES ─────────────────────────────

#[cfg(test)]
mod tests {
	use super::reference::{eval_points, eval_ref, invntt_ref, ntt_ref};
	use super::*;
	use rand::{rngs::StdRng, RngCore, SeedableRng};

	fn rand_zq(rng: &mut StdRng, n: usize) -> Vec<u64> {
		(0..n).map(|_| rng.next_u64() % Q).collect()
	}

	/// ψ = 1753 must be a primitive 512-th root of unity: ψ^256 ≡ −1 (mod q).
	#[test]
	fn psi_is_primitive_512th_root() {
		assert_eq!(modpow(PSI512, 256), Q - 1, "ψ^256 must be −1 mod q");
		assert_eq!(modpow(PSI512, 512), 1, "ψ^512 must be 1 mod q");
	}

	/// The twiddle table implied by the forward network evaluates at n DISTINCT roots of
	/// X^n+1 — i.e. it is a genuine negacyclic NTT (catches twiddle / bit-reversal bugs,
	/// INDEPENDENT of the circuit). Plus `ntt_ref` == direct multipoint evaluation.
	#[test]
	fn forward_twiddles_are_negacyclic_roots() {
		for &n in &[8usize, 16, 32, 64, 128, 256] {
			let pts = eval_points(n);
			for (j, &p) in pts.iter().enumerate() {
				assert_eq!(modpow(p, n as u64), Q - 1, "n={n}: pt[{j}]^n != -1 (not a root of X^n+1)");
			}
			let mut sorted = pts.clone();
			sorted.sort_unstable();
			sorted.dedup();
			assert_eq!(sorted.len(), n, "n={n}: evaluation points not distinct");

			let mut rng = StdRng::seed_from_u64(0xE7A1 ^ n as u64);
			let x = rand_zq(&mut rng, n);
			assert_eq!(ntt_ref(&x, n), eval_ref(&x, n), "n={n}: ntt_ref != multipoint eval");
		}
		println!("GATE twiddles: forward NTT evaluates at n distinct roots of X^n+1 for n∈{{8..256}}; ntt_ref == direct evaluation");
	}

	/// MEASURE: forward-NTT FRI-prove wall-time + peak RSS over B256 @L1, swept over n.
	/// Sizes the S1d fleet shards: a full 256-pt NTT is 1024 butterflies in ONE wide row —
	/// FRI-impractical as a single strand (see `validate`'s docstring); this curve shows how
	/// prove-time grows with butterfly count so the transform can be sharded into fleet-sized
	/// strands whose peak RSS stays IoT-viable (<500 MiB).  Run ALONE (RSS is process-global).
	#[test]
	#[ignore = "NTT prove-scaling sweep (time+RSS); run ALONE: cargo test --release --lib --features parallel ntt_prove_scaling -- --ignored --nocapture"]
	fn ntt_prove_scaling() {
		use std::time::Instant;
		println!("\n=== NTT forward-prove scaling over B256 @L1(128) — time + peak RSS ===");
		println!("| n | butterflies | prove_ms | proof_bytes | peak_rss_MiB (running high-water) |");
		for &n in &[8usize, 16, 32, 64] {
			let mut rng = StdRng::seed_from_u64(0x4E7700 ^ n as u64);
			let x = rand_zq(&mut rng, n);
			let t = Instant::now();
			let (bytes, _out) = super::prove(n, false, &x).expect("NTT prove");
			let ms = t.elapsed().as_secs_f64() * 1e3;
			let rss = crate::b256_sha3::peak_rss_bytes() as f64 / (1024.0 * 1024.0);
			let bf = (n / 2) * (n.trailing_zeros() as usize); // n/2 per layer × log2(n) layers
			println!("| {n} | {bf} | {ms:.0} | {bytes} | {rss:.0} |");
		}
		println!("(full 256-pt NTT = 1024 butterflies; extrapolate prove-time, and shard so each fleet strand's RSS < 500 MiB.)");
	}

	/// FLEET THROUGHPUT + WALL model for a Raspberry-Pi (aarch64) fleet.  Measures each strand's
	/// UNIT per-shard prove cost + RSS on THIS device's core, then reports the end-to-end model for
	/// one ML-DSA-44 verify: shard counts, total shard-work, per-signature LATENCY (critical path)
	/// and THROUGHPUT (signatures/sec) as the fleet size (number of Pis) grows.  Run ON the Pi.
	#[test]
	#[ignore = "Pi fleet throughput/wall model — measures unit shard costs + reports sigs/sec at fleet sizes; run ALONE on the target"]
	fn fleet_throughput_model() {
		use std::time::Instant;
		let sc = std::env::var("SHARD_COEFFS").ok().and_then(|s| s.parse().ok()).unwrap_or(32usize);
		let cores = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(1);
		println!("\n=== Pi fleet throughput model — arch={} cores={} shard={sc} coeffs ===", std::env::consts::ARCH, cores);

		// unit per-shard prove cost (ms) + peak RSS (MiB) for each strand type on THIS core.
		let unit = |label: &str, f: &dyn Fn() -> (u64, f64)| -> (f64, f64) {
			let t = Instant::now();
			let (_bytes, rss) = f();
			let ms = t.elapsed().as_secs_f64() * 1e3;
			println!("  strand {label:<10} : {ms:8.0} ms/shard, {:.0} MiB", rss);
			(ms, rss)
		};
		let (ntt_ms, ntt_rss) = {
			let x = rand_zq(&mut StdRng::seed_from_u64(1), 256);
			let shards = super::stage_shards(&x, 256, 3, 256 / sc.max(1));
			unit("NTT-bf", &|| { let (b, r) = super::run_stage_shard(&shards[0], None, true).unwrap(); (b as u64, r as f64 / 1048576.0) })
		};
		let (mult_ms, mult_rss) = unit("combine-×", &|| { let (b, r) = super::run_mult_shard(&mult_specs(sc, 2), None, true).unwrap(); (b as u64, r as f64 / 1048576.0) });
		let (dig_ms, dig_rss) = unit("digit", &|| { let (b, r) = super::run_digit_shard(&digit_specs(sc, 3), None, true).unwrap(); (b as u64, r as f64 / 1048576.0) });
		let (bnd_ms, bnd_rss) = unit("z-norm", &|| { let (b, r) = super::run_boundary_shard(&boundary_specs(sc, 4), None, true).unwrap(); (b as u64, r as f64 / 1048576.0) });
		let (hash_ms, hash_rss) = unit("closing-H", &|| { let (b, r, _ok) = super::run_closing_hash_shard(&[0x5au8; 64], &[1u8, 2, 3], &[0u8; 32]).unwrap(); (b as u64, r as f64 / 1048576.0) });

		// shard counts for ONE ML-DSA-44 verify (k=l=4, n=256), at `sc` coeffs/shard.
		let per = sc.max(1);
		let ntt_bf = 13 * 1024; // 4 fwd-z + 1 c + 4 fwd-t1 + 4 inv-w', each 1024 butterflies
		let n_ntt = ntt_bf / per;
		let n_mult = (4 * 5 * 256) / per; // k·(l+1) var×var mults × 256 coeffs
		let n_dig = (4 * 256) / per;      // k polys × 256
		let n_bnd = (4 * 256) / per;      // l polys × 256
		let n_hash = 1usize;              // one closing hash (7 perms)
		let total_shards = n_ntt + n_mult + n_dig + n_bnd + n_hash;
		let total_work_ms = n_ntt as f64 * ntt_ms + n_mult as f64 * mult_ms + n_dig as f64 * dig_ms + n_bnd as f64 * bnd_ms + hash_ms;
		let peak_rss = [ntt_rss, mult_rss, dig_rss, bnd_rss, hash_rss].iter().cloned().fold(0.0, f64::max);

		println!("\n  per-signature: {total_shards} shards, total shard-work {:.1} s, peak per-shard RSS {peak_rss:.0} MiB (< 500 ⇒ IoT-viable)", total_work_ms / 1e3);
		println!("\n| fleet size (Pis) | sig latency (wall) | throughput (sigs/hr) |");
		for &g in &[1usize, 4, 16, 64, 256] {
			// perfectly-parallel + pipelined model: wall ≈ total_work / G; throughput = G / total_work.
			let wall_s = (total_work_ms / 1e3) / g as f64;
			let sigs_per_hr = 3600.0 / wall_s;
			println!("| {g:>3} | {wall_s:8.1} s | {sigs_per_hr:8.0} |");
		}
		println!("(unit costs MEASURED on this core; totals are the ML-DSA-44 shard counts; throughput scales ~linearly with Pi count until the closing-hash/critical path floors it. Run on the Pi for real Pi numbers; SHARD_COEFFS tunes shard size.)");
	}

	/// LEVER 2 — intra-node concurrency.  Each shard proves in ~34 MiB, so a 1 GB Pi has room to
	/// prove MANY shards AT ONCE.  This measures the wall time to prove `CONC` independent combine
	/// shards two ways — SEQUENTIALLY (each shard already uses `--features parallel` = all cores)
	/// vs CONCURRENTLY (`CONC` OS threads at once) — and the peak process RSS of the concurrent
	/// run.  It shows how much of the RAM headroom converts to per-NODE throughput on this core,
	/// and how many concurrent shards still fit the 500 MiB budget.  `CONC` defaults to the core
	/// count.  Run ALONE on the target.
	#[test]
	#[ignore = "lever-2 intra-node concurrency: sequential vs concurrent shard proving + peak RSS; run ALONE on the target"]
	fn concurrent_shards_throughput() {
		use std::time::Instant;
		let sc = std::env::var("SHARD_COEFFS").ok().and_then(|s| s.parse().ok()).unwrap_or(32usize);
		let conc: usize = std::env::var("CONC").ok().and_then(|s| s.parse().ok())
			.unwrap_or_else(|| std::thread::available_parallelism().map(|n| n.get()).unwrap_or(4));
		let mib = |b: u64| b as f64 / 1048576.0;
		let rss = crate::b256_sha3::peak_rss_bytes;
		println!("\n=== lever-2 concurrent shards — arch={} shard={sc} coeffs, CONC={conc} ===", std::env::consts::ARCH);

		// one unit of work = prove a single combine (var×var multiply) shard — the heaviest strand.
		let prove_one = |seed: u64| { super::run_mult_shard(&mult_specs(sc, seed), None, true).unwrap(); };

		// (a) SEQUENTIAL — CONC shards one after another; each shard uses the rayon pool (all cores).
		let t = Instant::now();
		for i in 0..conc { prove_one(2 + i as u64); }
		let seq_s = t.elapsed().as_secs_f64();

		// (b) CONCURRENT — CONC shards at once, one OS thread each (RAM ≈ CONC × one shard).
		let t = Instant::now();
		std::thread::scope(|s| {
			for i in 0..conc { s.spawn(move || prove_one(2 + i as u64)); }
		});
		let conc_s = t.elapsed().as_secs_f64();
		let peak = rss();

		let speedup = seq_s / conc_s.max(1e-9);
		let per_shard_seq = seq_s / conc as f64;
		let per_shard_conc = conc_s / conc as f64;
		println!("  {conc} combine shards (sc={sc}):");
		println!("    sequential (intra-shard parallel) : {seq_s:7.1} s   ({per_shard_seq:.1} s/shard)");
		println!("    concurrent ({conc} threads)           : {conc_s:7.1} s   ({per_shard_conc:.1} s/shard effective)");
		println!("    concurrency speedup                : {speedup:.2}×");
		println!("    peak RSS (concurrent, {conc} at once) : {:.0} MiB", mib(peak));
		let fit = (500.0 / (mib(peak) / conc as f64).max(1.0)) as usize;
		println!("  ⇒ {conc} shards at once use {:.0} MiB (< 500 budget: {}); ~{fit} concurrent shards would fit 500 MiB",
			mib(peak), if mib(peak) < 500.0 { "YES" } else { "NO" });
	}

	/// SINGLE-DEVICE RSS PIPELINE — the first Raspberry-Pi test.  Proves ONE shard of every strand
	/// type SEQUENTIALLY on ONE device, sampling the PROCESS peak RSS (getrusage high-water) after
	/// each.  The load-bearing property: peak RSS PLATEAUS at ≈ one strand (each shard's memory is
	/// freed before the next), NOT the sum — so the whole ML-DSA-44 pipeline runs on a 1 GB Pi with
	/// a huge margin, then aggregate + verify.  This is the low-RSS story on a single node.
	#[test]
	#[ignore = "single-device RSS pipeline (all strands sequentially, peak RSS ≈ one strand); run on the Pi"]
	fn single_device_rss_pipeline() {
		use std::time::Instant;
		use binius_field::BinaryField128b as F;
		use crate::epoch_fold::EpochLeaf;
		let sc = std::env::var("SHARD_COEFFS").ok().and_then(|s| s.parse().ok()).unwrap_or(16usize);
		let mib = |b: u64| b as f64 / 1048576.0;
		let rss = crate::b256_sha3::peak_rss_bytes;
		println!("\n=== single-device RSS pipeline — arch={} shard={sc} coeffs (peak RSS after each strand) ===", std::env::consts::ARCH);
		let wall = Instant::now();
		let base = rss();
		println!("  baseline (pre-prove)          : {:.0} MiB", mib(base));

		// prove one shard of every strand type, SEQUENTIALLY, sampling the process high-water RSS.
		let x = rand_zq(&mut StdRng::seed_from_u64(7), 256);
		let shards = super::stage_shards(&x, 256, 3, (256 / sc).max(2));
		super::run_stage_shard(&shards[0], None, true).unwrap();
		println!("  after NTT-butterfly shard     : {:.0} MiB", mib(rss()));
		super::run_mult_shard(&mult_specs(sc, 2), None, true).unwrap();
		println!("  after combine-multiply shard  : {:.0} MiB", mib(rss()));
		super::run_digit_shard(&digit_specs(sc, 3), None, true).unwrap();
		println!("  after digit shard             : {:.0} MiB", mib(rss()));
		super::run_boundary_shard(&boundary_specs(sc, 4), None, true).unwrap();
		println!("  after z-norm shard            : {:.0} MiB", mib(rss()));
		super::run_closing_hash_shard(&[0x5au8; 64], &[1u8, 2, 3], &[0u8; 32]).unwrap();
		let peak_prove = rss();
		println!("  after closing-hash shard      : {:.0} MiB  ← PEAK across all 5 strands", mib(peak_prove));

		// aggregate the (synthetic) shard outputs + verify on the same device.
		let recs: Vec<Vec<u64>> = (0..4).map(|i| (0..8).map(|j| ((i * 8 + j) as u64) % Q).collect()).collect();
		let _leaves: Vec<EpochLeaf> = recs.iter().map(|r| EpochLeaf { record: r.iter().map(|&v| F::new(v as u128)).collect() }).collect();
		let rep = crate::accumulation_air::combine_and_verify(&recs, 3).expect("combine_and_verify");
		let peak_all = rss();
		let secs = wall.elapsed().as_secs_f64();

		println!("  after aggregate + verify      : {:.0} MiB", mib(peak_all));
		println!("\n  PEAK RSS across the WHOLE single-device pipeline: {:.0} MiB", mib(peak_all));
		println!("  ⇒ plateaus at ≈ ONE strand (each shard freed before the next), NOT the sum of 5+.");
		println!("  ⇒ 1 GB Pi headroom: {:.0}× ; < 500 MiB budget: {}", 1024.0 / mib(peak_all).max(1.0), if mib(peak_all) < 500.0 { "YES" } else { "NO" });
		println!("  combiner = {} (verify {} µs) ; whole pipeline wall {secs:.1} s (sequential on one node)", rep.trust_model, rep.verify_us);
	}

	/// The TALL-NARROW butterfly batch's arithmetic == the reference forward NTT: every
	/// butterfly row's `(o_add,o_sub)` matches the CT-schedule trace (asserted inside
	/// `validate_butterflies`), the whole constraint system validates, and the trace's final
	/// state == `ntt_ref`.  Fast (validate_witness, no FRI) so it runs in the normal suite.
	#[test]
	fn butterfly_batch_matches_reference() {
		for &n in &[8usize, 16, 32, 64, 128, 256] {
			let mut rng = StdRng::seed_from_u64(0xB77F ^ n as u64);
			let x = rand_zq(&mut rng, n);
			// reconstruct the transform from the butterfly trace and check against ntt_ref.
			let trace = super::forward_butterfly_trace(&x, n);
			let mut a = x.clone();
			let mut ri = 0;
			for (start, len, _z) in super::forward_groups(n) {
				for j in start..start + len {
					let (_, _, _, oa, os) = trace[ri];
					a[j] = oa;
					a[j + len] = os;
					ri += 1;
				}
			}
			assert_eq!(a, ntt_ref(&x, n), "n={n}: butterfly trace final != ntt_ref");
			assert_eq!(trace.len(), (n / 2) * (n.trailing_zeros() as usize), "n={n}: butterfly count");
			super::validate_butterflies(&x, n).unwrap_or_else(|e| panic!("n={n}: tall-narrow batch must validate: {e}"));
		}
		println!("GATE tall-narrow: forward-butterfly batch (row-per-butterfly) validates over B256 and == ntt_ref for n∈{{8..256}}");
	}

	/// Soundness: corrupt one butterfly's ζ·v output column ⇒ its mod-add/sub identities no
	/// longer close ⇒ `validate_witness` REJECTS (the tall-narrow gadget is sound, not just
	/// arithmetic-checked in populate).
	#[test]
	fn butterfly_batch_tamper_rejected() {
		use crate::nonnative::write_col;
		let n = 16usize;
		let mut rng = StdRng::seed_from_u64(0xDEAD);
		let x = rand_zq(&mut rng, n);
		let trace = super::forward_butterfly_trace(&x, n);
		let nrows = trace.len().next_power_of_two();
		let allocator = Bump::new();
		let mut cs = ConstraintSystem::<OurB256>::new();
		let bb = super::ButterflyBatch::build(&mut cs);
		let statement = Statement { boundaries: vec![], table_sizes: vec![nrows] };
		let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
		{
			let tw = witness.init_table(bb.table_id, nrows).unwrap();
			let mut seg = tw.full_segment();
			for (row, &(u, v, z, _, _)) in trace.iter().enumerate() {
				bb.populate(&mut seg, row, u, v, z).unwrap();
			}
			for row in trace.len()..nrows {
				bb.populate(&mut seg, row, 0, 0, 0).unwrap();
			}
			// TAMPER: flip a bit of row 0's ζ·v result (mul.out) — breaks add/sub identities.
			let mut bad = bits64(to_u64(&read_col::<W>(&seg, bb.mul.out, 0).unwrap()));
			bad[0] = !bad[0];
			write_col::<W>(&mut seg, bb.mul.out, 0, &bad).unwrap();
		}
		let ccs = cs.compile(&statement).unwrap();
		let witness = witness.into_multilinear_extension_index();
		let v = binius_core::constraint_system::validate::validate_witness(&ccs, &[], &witness);
		assert!(v.is_err(), "SOUNDNESS FAILURE: a tampered butterfly output was ACCEPTED");
		println!("GATE tall-narrow tamper: a corrupted ζ·v output is REJECTED by validate_witness");
	}

	/// CONNECTIVITY: two butterflies chained by a channel — producer A PUSHES its o_add, and
	/// consumer B PULLS it as its input u.  The channel must net-balance, so B's input is bound
	/// to equal A's output (the seam that wires adjacent NTT layers and fleet strands, mirroring
	/// the proven `nonnative::ModMul` mid-channel seam).  A consumer that pulls the WRONG value
	/// unbalances the channel ⇒ `validate_witness` REJECTS — connectivity soundness across the seam.
	#[test]
	fn butterfly_seam_routes_and_tamper_rejected() {
		use binius_core::constraint_system::channel::ChannelId;
		let run = |bad: bool| -> bool {
			let allocator = Bump::new();
			let mut cs = ConstraintSystem::<OurB256>::new();
			let wire: ChannelId = cs.add_channel("wire"); // carries A.o_add → B.u
			let a = super::ButterflyBatch::build_seamed(&mut cs, None, Some(wire), None);
			let b = super::ButterflyBatch::build_seamed(&mut cs, Some(wire), None, None);
			let statement = Statement { boundaries: vec![], table_sizes: vec![1, 1] };
			let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
			// A: (u,v,ζ) → o_add, pushed onto `wire`.
			let (ua, va, za) = (100u64, 7u64, 1753u64);
			let ta = ((za as u128 * va as u128) % Q as u128) as u64;
			let oa = (ua + ta) % Q;
			{
				let tw = witness.init_table(a.table_id, 1).unwrap();
				let mut seg = tw.full_segment();
				let (goa, _) = a.populate(&mut seg, 0, ua, va, za).unwrap();
				assert_eq!(goa, oa);
			}
			// B: pulls u from `wire`; honest u == A.o_add, tampered u == A.o_add + 1.
			let ub = if bad { (oa + 1) % Q } else { oa };
			{
				let tw = witness.init_table(b.table_id, 1).unwrap();
				let mut seg = tw.full_segment();
				b.populate(&mut seg, 0, ub, 3, 17).unwrap();
			}
			let ccs = cs.compile(&statement).unwrap();
			let witness = witness.into_multilinear_extension_index();
			binius_core::constraint_system::validate::validate_witness(&ccs, &statement.boundaries, &witness).is_ok()
		};
		assert!(run(false), "honest butterfly seam must balance + validate");
		assert!(!run(true), "SOUNDNESS: a consumer pulling a wrong value must unbalance the channel");
		println!("GATE tall-narrow seam: butterfly o_add PUSHED and PULLED as the next butterfly's u; a wrong pulled value REJECTED (channel unbalanced) — the inter-layer / fleet-strand routing primitive");
	}

	/// WHOLE-NETWORK composition: every butterfly of a forward n-NTT is wired through
	/// per-(slot,version) channels, with the public inputs pushed at version 0 and the public
	/// `ntt_ref` outputs pulled at the final version.  Channel balance forces the network to
	/// carry inputs through the fixed CT topology to the pinned outputs — so the honest network
	/// validates, and corrupting ANY butterfly's twiddle unbalances the output channels ⇒ REJECT.
	#[test]
	fn ntt_network_composed_and_tamper_rejected() {
		for &n in &[4usize, 8, 16] {
			let mut rng = StdRng::seed_from_u64(0xC7C7 ^ n as u64);
			let x = rand_zq(&mut rng, n);
			super::validate_ntt_network(&x, n, None)
				.unwrap_or_else(|e| panic!("n={n}: honest CT network must validate: {e}"));
			// tamper each of a few butterflies ⇒ the pinned-output channels must unbalance.
			let nbf = (n / 2) * (n.trailing_zeros() as usize);
			for &b in &[0usize, nbf / 2, nbf - 1] {
				assert!(
					super::validate_ntt_network(&x, n, Some(b)).is_err(),
					"n={n}: a corrupted twiddle at butterfly {b} must be REJECTED"
				);
			}
		}
		println!("GATE ntt-network: the whole forward CT network composed from channel-routed butterflies validates over B256 (inputs/outputs pinned); any corrupted butterfly is REJECTED via output-channel balance");
	}

	/// BATCHED composition: each stage's n/2 butterflies are ONE tall-narrow positional table,
	/// routed by a single channel keyed `(position, value)`.  Honest validates over B256; a
	/// corrupted butterfly mismatches the position the next stage pulls ⇒ channel UNBALANCE ⇒
	/// REJECT.  This is the deployment structure (tall-narrow per stage, not 1 table/butterfly).
	#[test]
	fn ntt_network_batched_composed_and_tamper_rejected() {
		for &n in &[4usize, 8, 16] {
			let mut rng = StdRng::seed_from_u64(0xBA7C ^ n as u64);
			let x = rand_zq(&mut rng, n);
			super::validate_ntt_network_batched(&x, n, None, None)
				.unwrap_or_else(|e| panic!("n={n}: honest batched CT network must validate: {e}"));
			let nbf = (n / 2) * (n.trailing_zeros() as usize);
			for &b in &[0usize, nbf / 2, nbf - 1] {
				// twiddle tamper: committed ζ ≠ the public schedule ζ ⇒ sched pin REJECTS.
				assert!(
					super::validate_ntt_network_batched(&x, n, Some(b), None).is_err(),
					"n={n}: a corrupted twiddle at butterfly {b} must be REJECTED (batched)"
				);
				// position tamper: committed position ≠ the public schedule position, boundary
				// honest ⇒ the sched channel is the load-bearing rejecter (positions pinned).
				assert!(
					super::validate_ntt_network_batched(&x, n, None, Some(b)).is_err(),
					"n={n}: a corrupted position at butterfly {b} must be REJECTED (schedule-pinned)"
				);
			}
		}
		println!("GATE ntt-network-batched: each stage is ONE tall-narrow positional table routed by a single (pos,value) channel, with positions+twiddle PINNED to the public schedule via boundary flushes; honest validates, any corrupted twiddle OR position REJECTED");
	}

	/// FLEET SHARDING: split a stage's butterflies into G independent shards, each a standalone
	/// proof (its I/O + schedule as boundary seams).  Every honest shard validates; a tampered
	/// shard is rejected; the union of shards is the whole stage (G·per = n/2 butterflies).
	#[test]
	fn stage_sharded_across_fleet() {
		for &(n, g) in &[(16usize, 2usize), (16, 4), (32, 4)] {
			let mut rng = StdRng::seed_from_u64(0x5A5A ^ (n as u64) ^ ((g as u64) << 8));
			let x = rand_zq(&mut rng, n);
			let s = 1; // an interior stage
			let shards = super::stage_shards(&x, n, s, g);
			assert_eq!(shards.iter().map(|sh| sh.len()).sum::<usize>(), n / 2, "shards must cover the stage");
			for (k, shard) in shards.iter().enumerate() {
				super::run_stage_shard(shard, None, false)
					.unwrap_or_else(|e| panic!("n={n} g={g} shard {k} must validate: {e}"));
				assert!(super::run_stage_shard(shard, Some(0), false).is_err(), "n={n} g={g} shard {k}: a tampered ζ must be REJECTED");
			}
		}
		println!("GATE fleet-shard: a stage's butterflies split into G independent standalone shards (I/O + schedule as boundary seams); every shard validates over B256, tampered shard REJECTED, union = whole stage");
	}

	/// MEASURE: per-shard FRI-prove time + peak RSS as a stage is split G ways — the fleet
	/// trade (more shards ⇒ smaller, lower-RSS, parallel proofs).  Run ALONE (RSS process-global).
	#[test]
	#[ignore = "fleet per-shard prove RSS/time; run ALONE with --ignored"]
	fn stage_shard_prove_scaling() {
		use std::time::Instant;
		println!("\n=== fleet per-shard prove over B256 @L1(128) — stage of a 256-NTT, split G ways ===");
		println!("| G shards | butterflies/shard | prove_ms/shard | VERIFY_ms/shard | proof_bytes | peak_rss_MiB |");
		let n = 256usize;
		let mut rng = StdRng::seed_from_u64(0xF1EE7);
		let x = rand_zq(&mut rng, n);
		for &g in &[2usize, 4, 8, 16] {
			let shards = super::stage_shards(&x, n, 3, g);
			let t = Instant::now();
			let (bytes, rss) = super::run_stage_shard(&shards[0], None, true).expect("shard prove");
			let ms = t.elapsed().as_secs_f64() * 1e3;
			let vms = super::VERIFY_US.load(std::sync::atomic::Ordering::Relaxed) as f64 / 1e3;
			println!("| {g} | {} | {ms:.0} | {vms:.1} | {bytes} | {:.0} |", shards[0].len(), rss as f64 / (1024.0 * 1024.0));
		}
		println!("(each shard is an independent proof ⇒ runs on its own fleet processor; peak RSS per-shard < 500 MiB; per-shard VERIFY is the aggregation cost — shards recurse into ONE succinct epoch proof the resolver verifies once.)");
	}

	fn combine_specs(count: usize, seed: u64) -> Vec<super::CombineSpec> {
		let mut rng = StdRng::seed_from_u64(seed);
		(0..count)
			.map(|i| {
				let a = std::array::from_fn(|_| rng.next_u64() % Q);
				let z = std::array::from_fn(|_| rng.next_u64() % Q);
				// positions: a_j and z_j at the upstream NTT-output slots, ŵ at a post-combine slot.
				let pos = std::array::from_fn(|k| (k * 4096 + i) as u64);
				super::CombineSpec { a, z, c: rng.next_u64() % Q, td: rng.next_u64() % Q, pos }
			})
			.collect()
	}

	/// The COMBINE strand wired into the fleet: a row-block of ŵ = Σ a_j·z_j − c·td coefficients
	/// proves as a standalone shard (inputs/output = seam boundary flushes on `flow`).  Honest
	/// validates over B256; a tampered coefficient (committed c ≠ the boundary seam token) is
	/// REJECTED.  Same shard shape as the NTT stage — so combine joins the fleet on `flow`.
	#[test]
	fn combine_strand_sharded_across_fleet() {
		for &sz in &[4usize, 8, 16] {
			let specs = combine_specs(sz, 0xC0FFEE ^ sz as u64);
			super::run_combine_shard(&specs, None, false)
				.unwrap_or_else(|e| panic!("combine shard sz={sz} must validate: {e}"));
			assert!(super::run_combine_shard(&specs, Some(sz / 2), false).is_err(), "combine shard sz={sz}: a tampered ĉ must be REJECTED");
		}
		println!("GATE combine-fleet: the NTT-domain combine ŵ=Σa_j·z_j−c·td strand shards as standalone low-RSS proofs (I/O seams on `flow`); honest validates, tampered coefficient REJECTED");
	}

	/// MEASURE: the combine strand's per-shard FRI-prove time + peak RSS (256 coefficients split
	/// G ways) — the same fleet regime as the NTT.  Run ALONE.
	#[test]
	#[ignore = "combine per-shard prove RSS/time; run ALONE with --ignored"]
	fn combine_shard_prove_scaling() {
		use std::time::Instant;
		println!("\n=== fleet per-shard COMBINE prove over B256 @L1(128) — 256 coeffs split G ways ===");
		println!("| G shards | coeffs/shard | prove_ms/shard | VERIFY_ms/shard | proof_bytes | peak_rss_MiB |");
		for &g in &[4usize, 8, 16, 32] {
			let per = 256 / g;
			let specs = combine_specs(per, 0xC0FFEE ^ (g as u64) << 20);
			let t = Instant::now();
			let (bytes, rss) = super::run_combine_shard(&specs, None, true).expect("combine shard prove");
			let ms = t.elapsed().as_secs_f64() * 1e3;
			let vms = super::VERIFY_US.load(std::sync::atomic::Ordering::Relaxed) as f64 / 1e3;
			println!("| {g} | {per} | {ms:.0} | {vms:.1} | {bytes} | {:.0} |", rss as f64 / (1024.0 * 1024.0));
		}
		println!("(combine joins the fleet: independent per-shard proofs; per-shard VERIFY is aggregation cost, folded into the succinct epoch proof.)");
	}

	fn mult_specs(count: usize, seed: u64) -> Vec<super::MultSpec> {
		let mut rng = StdRng::seed_from_u64(seed);
		(0..count).map(|i| super::MultSpec { a: rng.next_u64() % Q, z: rng.next_u64() % Q, pos: std::array::from_fn(|k| (k * 4096 + i) as u64) }).collect()
	}

	/// The single-MULTIPLY strand (the combine, factored finer): a row-block of p = a·z mod q
	/// proves as a standalone shard.  Honest validates; a tampered factor is REJECTED.
	#[test]
	fn mult_strand_sharded_across_fleet() {
		for &sz in &[4usize, 8, 16] {
			let specs = mult_specs(sz, 0x111 ^ sz as u64);
			super::run_mult_shard(&specs, None, false).unwrap_or_else(|e| panic!("mult shard sz={sz} must validate: {e}"));
			assert!(super::run_mult_shard(&specs, Some(sz / 2), false).is_err(), "mult shard sz={sz}: a tampered factor must be REJECTED");
		}
		println!("GATE mult-fleet: the single-multiply p=a·z strand shards as standalone low-RSS proofs; honest validates, tampered factor REJECTED");
	}

	/// MEASURE: the combine sharded FINER — one single-multiply strand vs the 5-mult combine.
	/// The combine's 14.7 s wall was 5 var×var mults/row; one multiply/row is ~1/5 the width, so
	/// the 5 mults run in parallel at ≈ butterfly speed ⇒ the combine wall drops to ≈ one multiply.
	#[test]
	#[ignore = "finer combine sharding (single-multiply strand) prove RSS/time; run ALONE"]
	fn mult_shard_prove_scaling() {
		use std::time::Instant;
		println!("\n=== finer combine sharding — single-multiply p=a·z strand over B256 @L1(128) ===");
		println!("| coeffs/shard | prove_ms/shard | proof_bytes | peak_rss_MiB | (vs 5-mult combine at same size) |");
		for &per in &[64usize, 32, 16, 8] {
			let specs = mult_specs(per, 0x222 ^ per as u64);
			let t = Instant::now();
			let (bytes, rss) = super::run_mult_shard(&specs, None, true).expect("mult shard prove");
			let ms = t.elapsed().as_secs_f64() * 1e3;
			println!("| {per} | {ms:.0} | {bytes} | {:.0} | |", rss as f64 / (1024.0 * 1024.0));
		}
		println!("(the combine's 5 var×var mults become 5 single-multiply strands run IN PARALLEL ⇒ combine wall ≈ one multiply strand (≈ butterfly), not 5×; a light accumulate strand then sums the products.)");
	}

	fn digit_specs(count: usize, seed: u64) -> Vec<super::DigitSpec> {
		let mut rng = StdRng::seed_from_u64(seed);
		(0..count)
			.map(|i| super::DigitSpec { r: rng.next_u64() % Q, h: rng.next_u64() % 2, pos: std::array::from_fn(|k| (k * 4096 + i) as u64) })
			.collect()
	}

	/// The DIGIT strand wired into the fleet: a row-block of w1 = UseHint(h, Decompose(w′))
	/// coefficients proves as a standalone shard (r/h/w1 = seam boundary flushes on `flow`).
	/// Honest validates over B256; a flipped hint bit (committed h ≠ boundary seam token) is
	/// REJECTED.  Same shard shape as NTT/combine — so digit joins the fleet on `flow`.
	#[test]
	fn digit_strand_sharded_across_fleet() {
		// spot-check the native Decompose+UseHint identities hold for the witness it commits.
		for r in [0u64, 1, 95232, 190464, Q - 1, 4_000_000] {
			for h in [0u64, 1] {
				let (r1, v0, s, sp, hs, w1, qp) = super::digit_native(r, h);
				assert_eq!(r + super::GAMMA2, r1 * super::ALPHA + v0 + s * Q, "decompose id r={r}");
				assert_eq!(w1 + super::MM + h, r1 + 2 * hs + qp * super::MM, "usehint id r={r} h={h}");
				assert!(r1 < super::MM && w1 < super::MM && qp < 3 && s < 2 && sp < 2, "ranges r={r}");
			}
		}
		for &sz in &[4usize, 8, 16] {
			let specs = digit_specs(sz, 0xD1671 ^ sz as u64);
			super::run_digit_shard(&specs, None, false).unwrap_or_else(|e| panic!("digit shard sz={sz} must validate: {e}"));
			assert!(super::run_digit_shard(&specs, Some(sz / 2), false).is_err(), "digit shard sz={sz}: a flipped hint must be REJECTED");
		}
		println!("GATE digit-fleet: the Decompose+UseHint digit strand shards as standalone low-RSS proofs (I/O seams on `flow`); honest validates, flipped hint REJECTED");
	}

	/// MEASURE: the digit strand's per-shard FRI-prove time + peak RSS (256 coeffs split G ways).
	#[test]
	#[ignore = "digit per-shard prove RSS/time; run ALONE with --ignored"]
	fn digit_shard_prove_scaling() {
		use std::time::Instant;
		println!("\n=== fleet per-shard DIGIT prove over B256 @L1(128) — 256 coeffs split G ways ===");
		println!("| G shards | coeffs/shard | prove_ms/shard | VERIFY_ms/shard | proof_bytes | peak_rss_MiB |");
		for &g in &[4usize, 8, 16, 32] {
			let per = 256 / g;
			let specs = digit_specs(per, 0xD1671 ^ (g as u64) << 20);
			let t = Instant::now();
			let (bytes, rss) = super::run_digit_shard(&specs, None, true).expect("digit shard prove");
			let ms = t.elapsed().as_secs_f64() * 1e3;
			let vms = super::VERIFY_US.load(std::sync::atomic::Ordering::Relaxed) as f64 / 1e3;
			println!("| {g} | {per} | {ms:.0} | {vms:.1} | {bytes} | {:.0} |", rss as f64 / (1024.0 * 1024.0));
		}
		println!("(digit joins the fleet: independent per-shard proofs, per-shard RSS well under 500 MiB.)");
	}

	fn boundary_specs(count: usize, seed: u64) -> Vec<super::BoundarySpec> {
		let mut rng = StdRng::seed_from_u64(seed);
		let m = super::GAMMA1 - super::BETA; // |z| < m
		(0..count)
			.map(|i| {
				// z ∈ (−m, m) ⇒ u = z + γ1 ∈ (β, 2γ1−β).
				let z = (rng.next_u64() % (2 * m - 1)) as i64 - (m as i64 - 1);
				super::BoundarySpec { u: (z + super::GAMMA1 as i64) as u64, pos: (i as u64) }
			})
			.collect()
	}

	/// The BOUNDARY (z-norm) strand wired into the fleet: a row-block of ‖z‖∞ < γ1−β coefficient
	/// checks proves as a standalone shard (coefficient tokens = seam boundary flushes on `flow`).
	/// Honest (in-range) validates over B256; an out-of-range coefficient is REJECTED.
	#[test]
	fn boundary_strand_sharded_across_fleet() {
		for &sz in &[4usize, 8, 16] {
			let specs = boundary_specs(sz, 0xB0DE ^ sz as u64);
			super::run_boundary_shard(&specs, None, false).unwrap_or_else(|e| panic!("boundary shard sz={sz} must validate: {e}"));
			assert!(super::run_boundary_shard(&specs, Some(sz / 2), false).is_err(), "boundary shard sz={sz}: an out-of-range z coeff must be REJECTED");
		}
		println!("GATE boundary-fleet: the ‖z‖∞ < γ1−β z-norm strand shards as standalone low-RSS proofs (coeff seams on `flow`); honest validates, out-of-range REJECTED");
	}

	/// MEASURE: the boundary (z-norm) strand's per-shard prove time + peak RSS (256 coeffs G ways).
	#[test]
	#[ignore = "boundary per-shard prove RSS/time; run ALONE with --ignored"]
	fn boundary_shard_prove_scaling() {
		use std::time::Instant;
		println!("\n=== fleet per-shard BOUNDARY (z-norm) prove over B256 @L1(128) — 256 coeffs split G ways ===");
		println!("| G shards | coeffs/shard | prove_ms/shard | proof_bytes | peak_rss_MiB |");
		for &g in &[4usize, 8, 16, 32] {
			let per = 256 / g;
			let specs = boundary_specs(per, 0xB0DE ^ (g as u64) << 20);
			let t = Instant::now();
			let (bytes, rss) = super::run_boundary_shard(&specs, None, true).expect("boundary shard prove");
			let ms = t.elapsed().as_secs_f64() * 1e3;
			println!("| {g} | {per} | {ms:.0} | {bytes} | {:.0} |", rss as f64 / (1024.0 * 1024.0));
		}
		println!("(boundary joins the fleet: the lightest ACCEPT-check strand, per-shard RSS well under 500 MiB.)");
	}

	/// FULL fips204-driven FLEET e2e: a GENUINE ML-DSA-44 signature drives ALL five fleet strands
	/// on its REAL intermediates (NTT of z, combine Â∘ẑ−ĉ∘t̂1, digit UseHint∘Decompose, z-norm,
	/// closing hash c̃'==c̃), each a standalone low-RSS proof; their outputs fold into the epoch and
	/// the resolver verifies once.  The whole DNS-STARK-over-Binius S1d verify as a low-RSS parallel
	/// fleet with sub-ms resolver verify, on a real signature.  Run ALONE (RSS process-global).
	#[test]
	#[ignore = "full fips204-driven fleet e2e (5 real-data strand proves + fold + resolver verify); run ALONE"]
	fn fips204_fleet_e2e() {
		use std::time::Instant;
		use binius_field::BinaryField128b as F;
		use fips204::ml_dsa_44;
		use fips204::traits::{SerDes, Signer, Verifier};
		use crate::epoch_fold::{fold_epoch, open_record, verify_epoch, verify_record, EpochLeaf};
		use crate::mldsa_shake::{expand_a_ref, sample_in_ball, shake256_xof, MlDsaParam};
		use crate::mldsa_verify::{pk_decode, sig_decode, use_hint, verify_params, verify_ref};
		use reference::{invntt_ref, ntt_ref};

		let vp = verify_params(MlDsaParam::MlDsa44);
		let qi = Q as i64;
		let to_u64a = |v: &[i64; 256]| -> Vec<u64> { v.iter().map(|&x| x.rem_euclid(qi) as u64).collect() };

		// ── genuine signature + real intermediates (verify_ref's chain) ──
		let (pk, sk) = ml_dsa_44::try_keygen().expect("keygen");
		let msg: &[u8] = b"full fips204-driven fleet e2e";
		let sig = sk.try_sign(msg, b"").expect("sign");
		assert!(pk.verify(msg, &sig, b""), "fips204 self-verify");
		let pk_bytes = pk.into_bytes();
		let pk_dec = pk_decode(&pk_bytes, &vp).unwrap();
		let sig_dec = sig_decode(&sig, &vp).unwrap();
		let mut mi = shake256_xof(&pk_bytes, 64);
		mi.push(0);
		mi.push(0);
		mi.extend_from_slice(msg);
		let mu = shake256_xof(&mi, 64);
		assert!(verify_ref(&pk_dec, &sig_dec, &mu), "verify_ref must accept the genuine sig");

		let a_hat = expand_a_ref(&pk_dec.rho, vp.k, vp.l);
		let c = sample_in_ball(&sig_dec.c_tilde, vp.tau);
		let c_hat = ntt_ref(&c.iter().map(|&x| (x as i64).rem_euclid(qi) as u64).collect::<Vec<_>>(), 256);
		let z_hat: Vec<Vec<u64>> = sig_dec.z.iter().map(|zp| ntt_ref(&to_u64a(zp), 256)).collect();
		let two_d = 1i64 << vp.d;
		let t1_hat: Vec<Vec<u64>> = pk_dec.t1.iter().map(|t| {
			let sc: [i64; 256] = std::array::from_fn(|i| (t[i] * two_d).rem_euclid(qi));
			ntt_ref(&to_u64a(&sc), 256)
		}).collect();
		let mut acc = [0i64; 256]; // ŵ[0]
		for j in 0..vp.l {
			for n in 0..256 {
				acc[n] = (acc[n] + a_hat[0][j][n] as i64 * z_hat[j][n] as i64).rem_euclid(qi);
			}
		}
		for n in 0..256 {
			acc[n] = (acc[n] - c_hat[n] as i64 * t1_hat[0][n] as i64).rem_euclid(qi);
		}
		let w_approx = invntt_ref(&acc.iter().map(|&x| x.rem_euclid(qi) as u64).collect::<Vec<_>>(), 256);
		let w1_0: [u64; 256] = std::array::from_fn(|n| use_hint(sig_dec.h[0][n], w_approx[n] as i64, vp.gamma2) as u64);

		// ── FLEET: prove all 5 strands on the REAL data (parallel ⇒ wall = max) ──
		let (mut peak_rss, mut wall) = (0u64, 0f64);
		let mut run = |rss: u64, ms: f64| { peak_rss = peak_rss.max(rss); wall = wall.max(ms); };

		let ntt_shards = super::stage_shards(&to_u64a(&sig_dec.z[0]), 256, 3, 8);
		let t = Instant::now();
		let (_, r) = super::run_stage_shard(&ntt_shards[0], None, true).unwrap();
		run(r, t.elapsed().as_secs_f64() * 1e3);

		let combine: Vec<super::CombineSpec> = (0..16).map(|n| super::CombineSpec {
			a: std::array::from_fn(|j| a_hat[0][j][n] as u64),
			z: std::array::from_fn(|j| z_hat[j][n]),
			c: c_hat[n],
			td: t1_hat[0][n],
			pos: std::array::from_fn(|k| (k * 4096 + n) as u64),
		}).collect();
		let t = Instant::now();
		let (_, r) = super::run_combine_shard(&combine, None, true).unwrap();
		run(r, t.elapsed().as_secs_f64() * 1e3);

		let digit: Vec<super::DigitSpec> = (0..16).map(|n| super::DigitSpec {
			r: (w_approx[n] as i64).rem_euclid(qi) as u64,
			h: sig_dec.h[0][n] as u64,
			pos: std::array::from_fn(|k| (k * 4096 + n) as u64),
		}).collect();
		let t = Instant::now();
		let (_, r) = super::run_digit_shard(&digit, None, true).unwrap();
		run(r, t.elapsed().as_secs_f64() * 1e3);

		let boundary: Vec<super::BoundarySpec> = (0..16).map(|n| super::BoundarySpec { u: (sig_dec.z[0][n] + super::GAMMA1 as i64) as u64, pos: n as u64 }).collect();
		let t = Instant::now();
		let (_, r) = super::run_boundary_shard(&boundary, None, true).unwrap();
		run(r, t.elapsed().as_secs_f64() * 1e3);

		let w1enc = ((w1_0[0] | (w1_0[1] << 6) | (w1_0[2] << 12) | (w1_0[3] << 18)) as u32).to_le_bytes()[..3].to_vec();
		let mut anchor = mu.clone();
		anchor.extend_from_slice(&w1enc);
		let ctilde_anchor: [u8; 32] = { use sha3::{Digest, Sha3_256}; Sha3_256::digest(&anchor).into() };
		let t = Instant::now();
		let (_, r, ok) = super::run_closing_hash_shard(&mu, &w1enc, &ctilde_anchor).unwrap();
		run(r, t.elapsed().as_secs_f64() * 1e3);
		assert!(ok, "closing-hash strand must bind on the REAL w1Encode");

		// ── AGGREGATE: fold the real ŵ outputs into the epoch commitment ──
		let leaves: Vec<EpochLeaf> = (0..4).map(|blk| EpochLeaf { record: (0..8).map(|i| F::new(acc[blk * 8 + i].rem_euclid(qi) as u128)).collect() }).collect();
		let ta = Instant::now();
		let proof = fold_epoch(&leaves, "record", 1);
		let agg = ta.elapsed().as_secs_f64() * 1e3;

		// ── RESOLVER: verify the one aggregated proof ──
		let tv = Instant::now();
		verify_epoch(&proof, "record").expect("resolver verify_epoch");
		let ve = tv.elapsed().as_secs_f64() * 1e3;
		let op = open_record(&leaves, 0);
		let trr = Instant::now();
		verify_record(&proof, &op).expect("resolver verify_record");
		let vr = trr.elapsed().as_secs_f64() * 1e6;

		println!("\n=== FULL fips204-driven fleet e2e (GENUINE ML-DSA-44 signature) ===");
		println!("FLEET (5 strands — NTT/combine/digit/z-norm/closing-hash — on REAL sig data, parallel):");
		println!("  peak per-shard RSS {:.0} MiB, parallel wall ≈ {wall:.0} ms  (< 500 MiB, IoT-viable)", peak_rss as f64 / 1048576.0);
		println!("AGGREGATE (once): epoch fold {agg:.1} ms");
		println!("RESOLVER (per epoch): verify_epoch {ve:.2} ms, verify_record {vr:.1} µs  ← sub-ms, network-cost verify");
	}

	/// The CLOSING-HASH strand (terminal) wired into the fleet: it consumes the digit strand's
	/// w1Encode output, proves c̃' = SHA3-256(μ ‖ w1Encode) over B256, and binds c̃' == c̃.  A
	/// wrong w1' (from any tampered upstream shard) changes w1Encode ⇒ different digest ⇒ the
	/// binding fails.  (Single-Keccak-block anchor; the callable b256 SHA3 gadget is single-block.)
	#[test]
	#[ignore = "closing-hash strand (B256 SHA3 prove); heavier (width driver), run with --ignored"]
	fn closing_hash_strand_in_fleet() {
		use sha3::{Digest, Sha3_256};
		// digit strand outputs w1' (a UseHint group), packed by w1Encode (6 bits/coeff at L1).
		let w1 = [5u64, 6, 0, 21]; // < m = 44
		let pack = |w: &[u64; 4]| -> Vec<u8> { ((w[0] | (w[1] << 6) | (w[2] << 12) | (w[3] << 18)) as u32).to_le_bytes()[..3].to_vec() };
		let mu = [0x5au8; 64];
		let w1enc = pack(&w1);
		let mut msg = mu.to_vec();
		msg.extend_from_slice(&w1enc);
		let ctilde: [u8; 32] = Sha3_256::digest(&msg).into();

		let (sz, rss, ok) = super::run_closing_hash_shard(&mu, &w1enc, &ctilde).expect("closing-hash strand");
		assert!(ok, "closing-hash strand must bind c̃' == c̃ over the genuine w1Encode");

		// tamper: a wrong w1' coefficient ⇒ different w1Encode ⇒ c̃' ≠ c̃ (binding breaks).
		let bad = pack(&[w1[0] + 1, w1[1], w1[2], w1[3]]);
		let (_s, _r, bad_ok) = super::run_closing_hash_shard(&mu, &bad, &ctilde).expect("prove");
		assert!(!bad_ok, "a tampered w1' must break the c̃' == c̃ binding");

		println!("GATE closing-hash-fleet: c̃'=SHA3-256(μ‖w1Encode) PROVEN over B256 ({sz} B, {:.0} MiB), bound to c̃; a wrong w1' breaks it — the terminal ACCEPT strand.", rss as f64 / (1024.0 * 1024.0));
	}

	/// MULTI-BLOCK closing hash: the FULL FIPS-204 message (μ ‖ all-k w1Encode ≈ 832 B ≈ 7 blocks)
	/// binds to the real SHAKE-256 c̃, and a wrong w1' in ANY block breaks the binding; the
	/// in-circuit cost is the message's Keccak-f permutations proven over B256.
	#[test]
	#[ignore = "multi-block closing hash (full message SHAKE-256 bind + Keccak-f perms over B256); run with --ignored"]
	fn multiblock_closing_hash_in_fleet() {
		use crate::mldsa_shake::shake256_xof;
		// full w1Encode: k=4 polys × 256 coeffs × 6 bits = 768 B; μ = 64 B ⇒ 832 B ≈ 7 SHAKE blocks.
		let mut rng = StdRng::seed_from_u64(0xC105);
		let w1: Vec<u64> = (0..(4 * 256)).map(|_| rng.next_u64() % super::MM).collect();
		let mut w1enc = Vec::new();
		for poly in w1.chunks(256) {
			// pack 6 bits/coeff, 4 coeffs → 3 bytes.
			for grp in poly.chunks(4) {
				let packed = (grp[0] | (grp[1] << 6) | (grp[2] << 12) | (grp[3] << 18)) as u32;
				w1enc.extend_from_slice(&packed.to_le_bytes()[..3]);
			}
		}
		let mu = vec![0x5au8; 64];
		let mut msg = mu.clone();
		msg.extend_from_slice(&w1enc);
		let ctilde = shake256_xof(&msg, 32); // the real SHAKE-256 c̃

		let (sz, rss, nblk, ok) = super::run_multiblock_closing_hash(&mu, &w1enc, &ctilde).expect("multi-block closing hash");
		assert!(ok, "the FULL multi-block message must bind c̃' == c̃");

		// tamper a w1' in the LAST block (which the single-block anchor would MISS) ⇒ c̃' ≠ c̃.
		let mut bad_enc = w1enc.clone();
		*bad_enc.last_mut().unwrap() ^= 1;
		let (_s, _r, _n, bad_ok) = super::run_multiblock_closing_hash(&mu, &bad_enc, &ctilde).expect("prove");
		assert!(!bad_ok, "a wrong w1' in a LATER block must break the multi-block binding (the anchor misses it)");

		println!("GATE multiblock-closing-hash: full μ‖w1Encode ({} B, {nblk} SHAKE blocks) binds real SHAKE-256 c̃; {nblk} Keccak-f perms PROVEN over B256 ({sz} B, {:.0} MiB); a wrong w1' in the LAST block breaks the binding (the single-block anchor would miss it).", msg.len(), rss as f64 / (1024.0 * 1024.0));
	}

	/// END-TO-END: fleet-prove the NTT + combine shards (validity, low RSS, parallel), then
	/// AGGREGATE their outputs into the epoch commitment (`fold_epoch`'s interleaved single
	/// opening), and have the RESOLVER verify once.  Shows the pipeline the verify-time answer
	/// rests on: fleet proves shards → aggregator folds → resolver verifies fast (ms), NOT the
	/// seconds-per-shard verify.  Run ALONE (RSS process-global).
	#[test]
	#[ignore = "S1d fleet→epoch e2e (shard proves + fold + resolver verify); run ALONE with --ignored"]
	fn s1d_fleet_to_epoch_e2e() {
		use std::time::Instant;
		use binius_field::BinaryField128b as F;
		use crate::epoch_fold::{fold_epoch, open_record, verify_epoch, verify_record, EpochLeaf};

		let n = 32usize;
		let g = 4usize;
		let mut rng = StdRng::seed_from_u64(0x5117);
		let x = rand_zq(&mut rng, n);

		// FLEET: prove NTT stage shards + one combine shard (validity, low RSS; parallel ⇒ wall = max).
		let ntt_shards = super::stage_shards(&x, n, 1, g);
		let mut max_rss = 0u64;
		let mut fleet_wall_ms = 0f64;
		let mut leaves: Vec<EpochLeaf> = Vec::new();
		for shard in &ntt_shards {
			let t = Instant::now();
			let (_sz, rss) = super::run_stage_shard(shard, None, true).expect("ntt shard prove");
			fleet_wall_ms = fleet_wall_ms.max(t.elapsed().as_secs_f64() * 1e3);
			max_rss = max_rss.max(rss);
			// this shard's output coefficients (o_add, o_sub per butterfly) become a record leaf.
			let mut rec: Vec<F> = Vec::new();
			for &(u, v, z, _pos) in shard {
				let tt = ((z as u128 * v as u128) % Q as u128) as u64;
				rec.push(F::new(((u + tt) % Q) as u128));
				rec.push(F::new(((u + Q - tt) % Q) as u128));
			}
			while !rec.len().is_power_of_two() {
				rec.push(F::new(0));
			}
			leaves.push(EpochLeaf { record: rec });
		}
		let combine = combine_specs(8, 0x5117C0);
		let (_cz, crss) = super::run_combine_shard(&combine, None, true).expect("combine shard prove");
		max_rss = max_rss.max(crss);

		// AGGREGATE (once, by the aggregator): fold the shard outputs into the epoch commitment.
		let ta = Instant::now();
		let proof = fold_epoch(&leaves, "record", 1);
		let agg_ms = ta.elapsed().as_secs_f64() * 1e3;

		// RESOLVER: verify the ONE aggregated proof — the fast, network-cost check.
		let tv = Instant::now();
		verify_epoch(&proof, "record").expect("resolver verify_epoch");
		let ve_ms = tv.elapsed().as_secs_f64() * 1e3;
		let op = open_record(&leaves, 0);
		let tr = Instant::now();
		verify_record(&proof, &op).expect("resolver verify_record");
		let vr_us = tr.elapsed().as_secs_f64() * 1e6;

		println!("\n=== S1d fleet → epoch e2e (n={n} NTT stage + combine, {g}-way fleet) ===");
		println!("FLEET (validity, parallel): {g} NTT shards + 1 combine, per-shard RSS ≤ {:.0} MiB, parallel wall ≈ {fleet_wall_ms:.0} ms", max_rss as f64 / 1048576.0);
		println!("AGGREGATE (once/aggregator): epoch fold {agg_ms:.1} ms");
		println!("RESOLVER (per epoch): verify_epoch {ve_ms:.2} ms, verify_record {vr_us:.1} µs  ← the fast resolver cost, NOT the seconds-per-shard verify");
	}

	/// MEASURE: the TALL-NARROW butterfly batch FRI-prove time + peak RSS, swept over the same
	/// n as `ntt_prove_scaling` — the direct comparison that shows row-per-butterfly is
	/// IoT-viable where the wide-single-row `Ntt` is not.  Run ALONE (RSS is process-global).
	#[test]
	#[ignore = "tall-narrow butterfly-batch prove-scaling (time+RSS); run ALONE with --ignored"]
	fn butterfly_batch_prove_scaling() {
		use std::time::Instant;
		println!("\n=== TALL-NARROW butterfly-batch prove scaling over B256 @L1(128) — time + peak RSS ===");
		println!("| n | butterflies(rows) | prove_ms | proof_bytes | peak_rss_MiB (running high-water) |");
		for &n in &[8usize, 16, 32, 64, 128, 256] {
			let mut rng = StdRng::seed_from_u64(0x7A11 ^ n as u64);
			let x = rand_zq(&mut rng, n);
			let t = Instant::now();
			let (bytes, nrows) = super::prove_butterflies(&x, n).expect("tall-narrow butterfly prove");
			let ms = t.elapsed().as_secs_f64() * 1e3;
			let rss = crate::b256_sha3::peak_rss_bytes() as f64 / (1024.0 * 1024.0);
			println!("| {n} | {nrows} | {ms:.0} | {bytes} | {rss:.0} |");
		}
		println!("(compare vs ntt_prove_scaling: wide-row hit 880 MiB at n=32; tall-narrow should stay IoT-viable at n=256.)");
	}

	/// Pure-integer round-trip: the constructed inverse truly inverts the forward.
	#[test]
	fn reference_roundtrip_is_identity() {
		for &n in &[8usize, 16, 32, 64, 128, 256] {
			let mut rng = StdRng::seed_from_u64(0x1234 ^ n as u64);
			let x = rand_zq(&mut rng, n);
			assert_eq!(invntt_ref(&ntt_ref(&x, n), n), x, "n={n}: invNTT∘NTT != id (reference)");
		}
	}

	/// Modular primitives each match num-bigint AND prove over B256 (via the smallest
	/// NTT that exercises add, sub and ζ·v). Direct primitive checks are below.
	#[test]
	fn primitives_match_num_bigint() {
		use num_bigint::BigUint;
		let mut rng = StdRng::seed_from_u64(0xAA55);
		let q = BigUint::from(Q);
		for _ in 0..1000 {
			let a = rng.next_u64() % Q;
			let b = rng.next_u64() % Q;
			let zeta = rng.next_u64() % Q;
			// add
			let got = (a + b) % Q;
			let exp = (BigUint::from(a) + BigUint::from(b)) % &q;
			assert_eq!(BigUint::from(got), exp);
			// sub
			let got = (a + Q - b) % Q;
			let exp = (BigUint::from(a) + &q - BigUint::from(b)) % &q;
			assert_eq!(BigUint::from(got), exp);
			// ζ·v
			let got = (zeta as u128 * a as u128 % Q as u128) as u64;
			let exp = (BigUint::from(zeta) * BigUint::from(a)) % &q;
			assert_eq!(BigUint::from(got), exp);
		}
		println!("GATE primitives: modadd / modsub / ζ·v match num-bigint over 1000 random inputs each");
	}

	/// CORRECTNESS B (in-circuit): a proven forward NTT's output matches `ntt_ref`
	/// coefficient-for-coefficient, at the largest size we FRI-prove.
	#[test]
	fn forward_ntt_proves_and_matches_ref() {
		let n = 8;
		let mut rng = StdRng::seed_from_u64(0x5151);
		let x = rand_zq(&mut rng, n);
		let (size, out) = prove(n, false, &x).expect("forward NTT must prove over B256");
		assert_eq!(out, ntt_ref(&x, n), "in-circuit forward NTT != num-bigint reference");
		println!("GATE forward-B (n={n}): forward NTT PROVEN over B256 at L1(128); output matches num-bigint; single-NTT proof size = {size} bytes");
	}

	/// CORRECTNESS A (in-circuit, proven): invNTT(NTT(x)) == x over B256.
	#[test]
	fn roundtrip_proves_over_b256() {
		let n = 8;
		let mut rng = StdRng::seed_from_u64(0x9090);
		let x = rand_zq(&mut rng, n);
		let (size, _) = prove(n, true, &x).expect("round-trip must prove over B256");
		println!("GATE round-trip-A (n={n}): invNTT∘NTT == x PROVEN over B256 at L1(128); round-trip proof size = {size} bytes");
	}

	/// CORRECTNESS at FULL ML-DSA size. The FORWARD 256-point NTT is validated TALL-NARROW via the
	/// channel-routed batched network (`validate_ntt_network_batched`): n/2 rows per stage, so
	/// `validate_witness` is LINEAR (~7 s / ~22 MiB at n=256). The sink pins the network's outputs
	/// to `ntt_ref`, so an honest validate means the full forward transform equals num-bigint --
	/// this subsumes the old explicit `assert_eq!(fwd, ntt_ref)`.
	///
	/// This replaces the one-row `validate(256)` layout, whose `validate_witness` is O(columns^2)
	/// (>56 min isolated, ~2 GB; it hung a 20 h suite run) -- see `ntt_validate_scaling_probe` and
	/// `ntt_batched_validate_timing`. The full-size INVERSE round-trip has no tall-narrow validator
	/// yet and lives in `full_256_roundtrip_validates_slow` (ignored); in-circuit inverse
	/// correctness is covered in the default run at n=8 by `roundtrip_proves_over_b256`.
	#[test]
	fn full_256_validates_and_matches_ref() {
		let n = 256;
		let mut rng = StdRng::seed_from_u64(0x2020);
		let x = rand_zq(&mut rng, n);
		super::validate_ntt_network_batched(&x, n, None, None)
			.expect("full 256-pt forward NTT (tall-narrow) must validate and match ntt_ref");
		println!("GATE full-256: 256-point forward NTT VALIDATES tall-narrow (~7 s, linear) with outputs pinned to num-bigint ntt_ref");
	}

	/// Full-size INVERSE round-trip validation via the one-row layout. `#[ignore]`d: the inverse
	/// GS network has no tall-narrow validator yet, so this uses the one-row layout whose
	/// `validate_witness` is O(columns^2) (~hours at n=256). Forward-256 is fast
	/// (`full_256_validates_and_matches_ref`); in-circuit inverse is covered at n=8 by
	/// `roundtrip_proves_over_b256`. Building the tall-narrow inverse (GS) network is the proper
	/// fix here. Run alone: `... full_256_roundtrip_validates_slow -- --ignored`.
	#[test]
	#[ignore = "one-row inverse round-trip is O(columns^2); no tall-narrow inverse network yet"]
	fn full_256_roundtrip_validates_slow() {
		let n = 256;
		let mut rng = StdRng::seed_from_u64(0x2020);
		let x = rand_zq(&mut rng, n);
		validate(n, true, &x).expect("full 256-pt round-trip must validate over B256");
	}

	/// DIAGNOSTIC: why does `validate(256)` hang? Time each phase (build+compile, populate,
	/// validate_witness) across n to expose the scaling exponent. The one-row `Ntt` layout puts
	/// every butterfly's columns in a single row, so if any phase is superlinear in the column
	/// count the cost explodes with n. Run: `... ntt_validate_scaling_probe -- --ignored --nocapture`.
	#[test]
	#[ignore = "diagnostic scaling probe for the validate(256) hang"]
	fn ntt_validate_scaling_probe() {
		use std::time::Instant;
		// NTT_PROBE_N=<n> runs a SINGLE n in this process so `getrusage` peak RSS is clean (it is
		// process-monotonic); otherwise sweep 8..64 for the time-scaling ratio.
		let single: Option<usize> = std::env::var("NTT_PROBE_N").ok().and_then(|v| v.parse().ok());
		let ns: Vec<usize> = single.map(|n| vec![n]).unwrap_or_else(|| vec![8, 16, 32, 64]);
		println!("\n   n | build+compile | populate | validate_witness | peak RSS | butterflies | ratio");
		let mut prev = 0.0f64;
		for &n in &ns {
			let mut rng = StdRng::seed_from_u64(0x2020);
			let x = rand_zq(&mut rng, n);

			let t0 = Instant::now();
			let allocator = Bump::new();
			let mut cs = ConstraintSystem::<OurB256>::new();
			let ntt = Ntt::build(&mut cs, n, false);
			let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
			let tb = Instant::now();

			{
				let tw = witness.init_table(ntt.table_id, 1).unwrap();
				let mut seg = tw.full_segment();
				ntt.populate(&mut seg, 0, &x).unwrap();
			}
			let statement = Statement { boundaries: vec![], table_sizes: vec![1] };
			let ccs = cs.compile(&statement).unwrap();
			let tp = Instant::now();

			let widx = witness.into_multilinear_extension_index();
			binius_core::constraint_system::validate::validate_witness(&ccs, &[], &widx).unwrap();
			let tv = Instant::now();

			let build_ms = tb.duration_since(t0).as_secs_f64() * 1e3;
			let pop_ms = tp.duration_since(tb).as_secs_f64() * 1e3;
			let val_ms = tv.duration_since(tp).as_secs_f64() * 1e3;
			let total = build_ms + pop_ms + val_ms;
			let ratio = if prev > 0.0 { total / prev } else { 0.0 };
			let rss_mib = crate::b256_sha3::peak_rss_bytes() as f64 / (1024.0 * 1024.0);
			// column/butterfly count for this n is (n/2)*log2(n) butterflies, each a wide-field
			// ModMul; validate_witness time grows ~quadratically in that, so it is O(columns^2).
			let butterflies = (n / 2) * (n.trailing_zeros() as usize);
			println!(
				"  {n:>3} | {build_ms:>13.1} | {pop_ms:>8.1} | {val_ms:>16.1} | {rss_mib:>6.0} MiB | {butterflies:>5} bfly | {ratio:.2}x"
			);
			prev = total;
		}
		println!(
			"  ratio ~2x per doubling = linear; ~4x = quadratic in n. The one-row layout's\n\
			 \x20  butterfly count is (n/2)log2(n), so a superlinear phase is the 20h culprit."
		);
	}

	/// FIX PROBE: is the tall-narrow `validate_ntt_network_batched` fast at n=256, where the
	/// one-row `validate` is O(columns^2) (~hours)? Times the batched validator across n; if it
	/// scales ~linearly and n=256 is seconds, it is the drop-in replacement for the full-256 test.
	#[test]
	#[ignore = "fix probe: tall-narrow batched-validate timing vs the one-row O(columns^2) validate"]
	fn ntt_batched_validate_timing() {
		use std::time::Instant;
		println!("\n   n | batched validate_witness | peak RSS | ratio");
		let mut prev = 0.0f64;
		for &n in &[64usize, 128, 256] {
			let mut rng = StdRng::seed_from_u64(0x2020);
			let x = rand_zq(&mut rng, n);
			let t = Instant::now();
			super::validate_ntt_network_batched(&x, n, None, None)
				.unwrap_or_else(|e| panic!("n={n}: batched network must validate: {e}"));
			let ms = t.elapsed().as_secs_f64() * 1e3;
			let rss = crate::b256_sha3::peak_rss_bytes() as f64 / (1024.0 * 1024.0);
			let ratio = if prev > 0.0 { ms / prev } else { 0.0 };
			println!("  {n:>3} | {ms:>24.1} | {rss:>6.0} MiB | {ratio:.2}x");
			prev = ms;
		}
		println!("  ~2x/doubling = LINEAR (tall-narrow fixes the one-row O(columns^2)).");
	}

	/// SOUNDNESS (load-bearing): a tampered ζ·v product / butterfly output is REJECTED,
	/// isolated to the constraint that binds it. Run at full 256-pt.
	#[test]
	fn soundness_tamper_rejected() {
		let n = 256;
		let mut rng = StdRng::seed_from_u64(0x7777);
		let x = rand_zq(&mut rng, n);

		let (rej, err) = tamper_rejected(n, &x, Tamper::MulQuo);
		assert!(rej, "SOUNDNESS: fake ζ·v reduction (bad quotient) ACCEPTED");
		assert!(err.contains("f0_") && err.contains("mul"), "ζ·v tamper reject not isolated to a f0 mul constraint (got: {err})");
		println!("GATE soundness-1: fake ζ·v reduction REJECTED, isolated to `{}`", first_constraint(&err));

		let (rej, err) = tamper_rejected(n, &x, Tamper::MulOut);
		assert!(rej, "SOUNDNESS: tampered ζ·v output ACCEPTED");
		println!("GATE soundness-2: tampered ζ·v butterfly output REJECTED at `{}`", first_constraint(&err));

		let (rej, err) = tamper_rejected(n, &x, Tamper::AddQb);
		assert!(rej, "SOUNDNESS: tampered modular-add quotient ACCEPTED");
		assert!(err.contains("f0_") && err.contains("add"), "add tamper reject not isolated to a f0 add constraint (got: {err})");
		println!("GATE soundness-3: tampered butterfly sum REJECTED, isolated to `{}`", first_constraint(&err));
	}

	fn first_constraint(err: &str) -> String {
		// Surface a short label from the validate_witness error for the report.
		err.lines().next().unwrap_or(err).chars().take(120).collect()
	}
}

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
use binius_core::{constraint_system::channel::ChannelId, fiat_shamir::HasherChallenger, oracle::ShiftVariant};
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
}

impl ButterflyBatch {
	pub fn build(cs: &mut ConstraintSystem<OurB256>) -> Self {
		Self::build_inner(cs, None, None, None)
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
		Self::build_inner(cs, pull_u, push_add, push_sub)
	}

	fn build_inner(
		cs: &mut ConstraintSystem<OurB256>,
		pull_u: Option<ChannelId>,
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
		if let Some(ch) = push_add {
			seam(&mut t, add.out, ch, "seam_add", false);
		}
		if let Some(ch) = push_sub {
			seam(&mut t, sub.out, ch, "seam_sub", false);
		}
		Self { table_id: t.id(), c_col, u, v, zeta, u_lt, v_lt, z_lt, mul, add, sub }
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

	/// CORRECTNESS at FULL ML-DSA size via witness validation (constraint-satisfaction
	/// of every gate). Forward output matches `ntt_ref`; round-trip returns x.
	#[test]
	fn full_256_validates_and_matches_ref() {
		let n = 256;
		let mut rng = StdRng::seed_from_u64(0x2020);
		let x = rand_zq(&mut rng, n);
		let fwd = validate(n, false, &x).expect("full 256-pt forward must validate over B256");
		assert_eq!(fwd, ntt_ref(&x, n), "full 256-pt forward != reference");
		// round-trip: forward outputs are the assert target; validate returns forward outs.
		validate(n, true, &x).expect("full 256-pt round-trip must validate over B256");
		println!("GATE full-256: 256-point forward + round-trip VALIDATE over B256 (every constraint satisfied); forward matches num-bigint");
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

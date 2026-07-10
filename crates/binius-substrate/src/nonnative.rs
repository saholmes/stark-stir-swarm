// S0 (signature-AIR port) — a NON-NATIVE modular-multiply gadget `a*b mod m`, built
// entirely from hand-rolled shift-and-add over B1 bit-columns, proving AND verifying
// over the 256-bit challenge/extension field `B256TowerFamily` at NIST L1 (128), with
// a SHA-256 Merkle commitment + SHA-256 Fiat–Shamir challenger (the FIPS instantiation,
// mirroring `b256_keccak`'s prove wiring).
//
// WHY THIS EXISTS. Every signature circuit (ML-DSA verify over Z_q with q = 8380417,
// RSA/ECDSA modular reductions, …) rests on a non-native modular multiply. A WRONG
// non-native multiply is a *silent* soundness hole — it would verify while computing
// the wrong residue. So the deliverable here is not "compiles" but: the honest witness
// VERIFIES, the in-circuit remainder MATCHES an independent `num-bigint` reference, and
// BOTH adversarial gates reject (a bad quotient, and an unreduced remainder).
//
// CONSTRUCTION (hint-and-verify, all integers little-endian bit-columns `Col<B1, W>`).
// Because a `Col<B1, W>` cell can only hold 0/1, ANY value assembled from its W bits is
// STRUCTURALLY in `[0, 2^W)` — so per-bit range-ness is FREE (no extra constraints).
// For an `n`-bit modulus `m` we pick a single power-of-two column width `W ≥ 2n+1`, so
// that `a*b` (< 2^{2n}), `q*m` (< 2^{2n+1}) and `q*m + r` all fit in W bits with NO
// wraparound — integer equality of two W-bit columns is then true integer equality.
// The prover supplies quotient `q` and remainder `r` as witness columns. The circuit
// ENFORCES, over B1 bit-columns only (field `+`/`-` is XOR, `*` is AND):
//   (i)  a,b < 2^n and q < 2^{n+1}      — `a>>n == 0`, `b>>n == 0`, `q>>(n+1) == 0`
//        (LogicalRight-shifted derived columns asserted zero). These bound the operands
//        so no product can overflow W bits, closing the modular-wraparound attack.
//   (ii) the big-integer identity `a*b == q*m + r`, computed by schoolbook shift-and-add
//        with ripple carries (see below), asserted lane-by-lane as `lhs - rhs == 0`.
//   (iii)the SOUNDNESS-CRITICAL strict reduction `0 <= r < m`. `r < m` is decided WITHOUT
//        a subtractor (binius' `U32Sub` leaves its borrow column unconstrained): we use
//        the sound ADDER's carry. Let `C = 2^W - m` (a compile-time constant column).
//        Then `r + C = r - m + 2^W`, whose carry-out of bit `W-1` is `0` iff `r < m` and
//        `1` iff `r >= m`. We expose that carry bit and assert it is `0`.
// Soundness argument: `a*b == q*m + r` with `0 <= r < m` uniquely fixes `r = a*b mod m`
// (and `q = ⌊a*b/m⌋`). The bit-width range-ness (free) + the operand bounds (i) + the
// `r < m` carry check (iii) are exactly what stop a malicious prover from presenting a
// wrong `q`/`r`: a bad `q` breaks the `identity` constraint; an unreduced `r >= m`
// breaks the `r_lt_m` constraint.
//
// MULTIPLY. Field `+` is XOR, so there is no native integer add; we build one.
//   * Adder (`Adder`): the width-W generalization of binius' `U32Add` carry recipe,
//     hand-rolled over `TableBuilder<B256>` with `add_committed`/`add_shifted`/
//     `assert_zero` (all field-generic). `cout` committed, `cin = cout << 1`,
//     constraint `(x+cin)(y+cin) + cin - cout == 0` (per lane: `cout = xy + cin(x+y)` —
//     the majority/carry function), sum committed with `x + y + cin - sum == 0`.
//   * `a*b` (both operands witness): shift-and-add over the bits of `b`. Partial product
//     `pp_i = b_i · (a << i)`. A single bit `b_i` cannot be AND-ed with a width-W column
//     directly (different partitions), so `b_i` is BROADCAST to a committed width-W
//     column `bcast_i` constrained all-lanes-equal (via a CircularLeft-by-1 rotate:
//     `bcast_i - rotate(bcast_i,1) == 0`) and lane-0-bound to `b_i`
//     (`select(bcast_i,0) - select(b,i) == 0`). Then `pp_i = bcast_i * (a<<i)` and the
//     `pp_i` are accumulated with the adder. O(n) additions.
//   * `q*m` (constant `m`): `q*m = Σ_{i: m_i=1} (q << i)` — no broadcast needed, the set
//     bits of the compile-time `m` select which shifts of `q` to add. `+ r` is one more
//     adder step. `popcount(m)` additions.
//
// WITNESS POPULATION. In binius_m3 EVERY column — committed AND virtual (shifted /
// selected / computed / constant) — carries an explicit witness buffer that must be
// filled; the framework does not auto-derive virtual columns (the Keccak-f and U32Add
// gadgets fill each shifted/computed lane by hand). So `populate` below fills every
// column by replaying the exact bit-vector arithmetic. The virtual columns remain BOUND
// to their sources by the oracle system (a shifted oracle is evaluated as the shift of
// its source at verify time), so this fill is a completeness requirement, not a
// soundness surface: a prover cannot desync a shifted column from its source.
//
// NO FORK CHANGE. This gadget uses ONLY the field-generic builder surface, so it needs
// no modification to the binius fork (Step A of the S0 plan). The B128-bound `MulUU32`/
// `U32Add` wrappers are NOT used. RSA-2048 (n=2048 → W=8192, O(n^2)=~4096 partial-
// product additions) is the case where a generalized exp-multiply (Step B) would be
// wanted; see the tests/report for its honest status.
//
// STRAND-FRIENDLINESS. The columns fall into distinct groups that a later low-memory
// "strand splice" could cut apart and re-bind with a seam: {a,b,q,r inputs},
// {broadcast columns bcast_i}, {a*b partial-product accumulator + its carries},
// {q*m accumulator + its carries}, {the r<m carry column}. Each group is a contiguous
// run of columns bound to its neighbours only through the named zero-constraints, so a
// seam union-bounded at ≤ 2^{-λ} could replace the direct column aliasing between
// adjacent adder steps.

use anyhow::Result;
use binius_core::constraint_system::channel::ChannelId;
use binius_core::{fiat_shamir::HasherChallenger, oracle::ShiftVariant};
use binius_field::{
	packed::{get_packed_slice, set_packed_slice},
	Field,
};
use binius_hash::sha2::Sha256Compression;
use binius_m3::builder::{
	Col, ConstraintSystem, Statement, TableBuilder, TableId, TableWitnessSegment, WitnessIndex, B1,
	B64,
};
use bumpalo::Bump;
use sha2::Sha256;

use crate::b256_field::{B256TowerFamily, B256 as OurB256, U256};

// ---------------------------------------------------------------------------------
// Hand-rolled little-endian bit-vector arithmetic used ONLY to fill the witness. It
// deliberately does NOT depend on `num-bigint`: the tests cross-check the in-circuit
// remainder against `num-bigint` independently, so "matches num-bigint" is a real
// check, not a tautology. Division (to obtain q, r) is the CALLER's job — this gadget
// only ever adds/multiplies/shifts, mirroring the circuit exactly.
// ---------------------------------------------------------------------------------

/// `x << s`, truncated to `x.len()` bits (little-endian, bit k = value 2^k).
///
/// `pub(crate)` so the S1a ML-DSA R_q NTT layer (`mldsa_ntt`) can reuse the exact
/// same sound bit-vector arithmetic used to fill this gadget's witness — the NTT
/// gadgets do NOT reinvent the adder/shift recipe, they call these directly.
pub(crate) fn shl(x: &[bool], s: usize) -> Vec<bool> {
	let w = x.len();
	(0..w).map(|k| if k >= s { x[k - s] } else { false }).collect()
}

/// `x >> s` (logical), truncated to `x.len()` bits.
pub(crate) fn shr(x: &[bool], s: usize) -> Vec<bool> {
	let w = x.len();
	(0..w).map(|k| if k + s < w { x[k + s] } else { false }).collect()
}

/// Ripple-carry add of two W-bit little-endian numbers. Returns `(sum, cout)` where
/// `sum = (x + y) mod 2^W` and `cout[k]` is the carry OUT of bit position `k` (i.e. the
/// carry INTO bit `k+1`) — exactly the `cout` column the in-circuit adder commits.
pub(crate) fn ripple_add(x: &[bool], y: &[bool]) -> (Vec<bool>, Vec<bool>) {
	let w = x.len();
	let mut sum = vec![false; w];
	let mut cout = vec![false; w];
	let mut carry = false;
	for k in 0..w {
		let s = x[k] as u8 + y[k] as u8 + carry as u8;
		sum[k] = s & 1 == 1;
		carry = s >= 2;
		cout[k] = carry;
	}
	(sum, cout)
}

/// `2^W - m` as a W-bit little-endian constant (`m > 0`, `m < 2^W`): the addend whose
/// carry-out decides `r < m`.
pub(crate) fn two_pow_w_minus(m_bits: &[bool]) -> Vec<bool> {
	let w = m_bits.len();
	let mut c: Vec<bool> = m_bits.iter().map(|&x| !x).collect(); // ~m
	let mut carry = true; // + 1
	for bit in c.iter_mut().take(w) {
		let s = *bit as u8 + carry as u8;
		*bit = s & 1 == 1;
		carry = s >= 2;
	}
	c
}

/// One instance's inputs (little-endian bit vectors, each length `W`).
#[derive(Clone)]
pub struct ModMulRow {
	pub a: Vec<bool>,
	pub b: Vec<bool>,
	pub q: Vec<bool>,
	pub r: Vec<bool>,
}

// ---------------------------------------------------------------------------------
// Column-write helpers.
// ---------------------------------------------------------------------------------

/// Write a length-W LE bit vector into `col` at logical row `row`.
pub(crate) fn write_col<const W: usize>(
	seg: &mut TableWitnessSegment<OurB256>,
	col: Col<B1, W>,
	row: usize,
	bits: &[bool],
) -> Result<()> {
	let mut c = seg.get_mut(col)?;
	for (k, &bit) in bits.iter().enumerate().take(W) {
		set_packed_slice(&mut c, row * W + k, if bit { B1::ONE } else { B1::ZERO });
	}
	Ok(())
}

/// Write a single bit into a `Col<B1, 1>` (a selected column) at logical row `row`.
pub(crate) fn write_bit(
	seg: &mut TableWitnessSegment<OurB256>,
	col: Col<B1, 1>,
	row: usize,
	bit: bool,
) -> Result<()> {
	let mut c = seg.get_mut(col)?;
	set_packed_slice(&mut c, row, if bit { B1::ONE } else { B1::ZERO });
	Ok(())
}

/// Read a length-W LE bit vector out of `col` at logical row `row`.
pub(crate) fn read_col<const W: usize>(
	seg: &TableWitnessSegment<OurB256>,
	col: Col<B1, W>,
	row: usize,
) -> Result<Vec<bool>> {
	let c = seg.get(col)?;
	Ok((0..W).map(|k| get_packed_slice(&c, row * W + k) == B1::ONE).collect())
}

// ---------------------------------------------------------------------------------
// The width-W sound adder gadget. Every column (cout committed; cin = cout<<1 virtual;
// sum committed) is filled at populate time.
// ---------------------------------------------------------------------------------

/// A width-W adder `sum = xin + yin` — the sound generalization of `U32Add`'s carry
/// recipe. `cin == cout << 1`; per lane `cout = xy + cin(x+y) = maj(x,y,cin)`.
///
/// `pub(crate)` so `mldsa_ntt` builds its modular add/sub/mul-by-constant gadgets on
/// this exact adder — the R_q layer reuses the S0 carry recipe verbatim rather than
/// hand-rolling a second (unaudited) adder.
#[derive(Clone, Copy)]
pub(crate) struct Adder<const W: usize> {
	pub(crate) cout: Col<B1, W>,
	pub(crate) cin: Col<B1, W>,
	pub(crate) sum: Col<B1, W>,
}

impl<const W: usize> Adder<W> {
	pub(crate) fn build(
		table: &mut TableBuilder<OurB256>,
		xin: Col<B1, W>,
		yin: Col<B1, W>,
		name: &str,
	) -> Self {
		let logw = W.trailing_zeros() as usize;
		let cout = table.add_committed::<B1, W>(format!("{name}_cout"));
		// cin[k] = cout[k-1]; cin[0] = 0 (LogicalLeft introduces a 0 at lane 0).
		let cin = table.add_shifted(format!("{name}_cin"), cout, logw, 1, ShiftVariant::LogicalLeft);
		// Per-lane carry: cout = xy + cin(x+y)  ==  majority(x, y, cin).
		table.assert_zero(format!("{name}_carry"), (xin + cin) * (yin + cin) + cin - cout);
		let sum = table.add_committed::<B1, W>(format!("{name}_sum"));
		table.assert_zero(format!("{name}_sum"), xin + yin + cin - sum);
		Self { cout, cin, sum }
	}

	/// Fill `cout`, `cin`, `sum` for one row from operand bit-vectors; return `sum`.
	pub(crate) fn populate(
		&self,
		seg: &mut TableWitnessSegment<OurB256>,
		row: usize,
		x: &[bool],
		y: &[bool],
	) -> Result<Vec<bool>> {
		let (sum, cout) = ripple_add(x, y);
		let cin = shl(&cout, 1); // cin[k] = cout[k-1]
		write_col::<W>(seg, self.cout, row, &cout)?;
		write_col::<W>(seg, self.cin, row, &cin)?;
		write_col::<W>(seg, self.sum, row, &sum)?;
		Ok(sum)
	}
}

// ---------------------------------------------------------------------------------
// The gadget.
// ---------------------------------------------------------------------------------

/// One partial-product group for bit `i` of `b` (strand seam): the broadcast column and
/// its binding witnesses, plus the shifted `a<<i` and the product `pp_i`.
struct MulBit<const W: usize> {
	/// `a << i` (None for i==0, where it aliases the `a` column directly).
	a_shl: Option<Col<B1, W>>,
	bcast: Col<B1, W>,
	bcast_rot: Col<B1, W>,
	bcast_lane0: Col<B1, 1>,
	b_bit: Col<B1, 1>,
	pp: Col<B1, W>,
}

/// A non-native `a*b mod m` table over the 256-bit top field, width `W` (bits per row).
pub struct ModMul<const W: usize> {
	pub table_id: TableId,
	a: Col<B1, W>,
	b: Col<B1, W>,
	q: Col<B1, W>,
	r: Col<B1, W>,
	// (i) operand-bound derived columns.
	a_hi: Col<B1, W>,
	b_hi: Col<B1, W>,
	q_hi: Col<B1, W>,
	// a*b: per-bit partial-product groups and the accumulator adders (i = 1..n).
	mul_bits: Vec<MulBit<W>>,
	mul_adders: Vec<Adder<W>>,
	// q*m + r: the shifted `q<<p` terms (p = set bits of m, first term aliases q for
	// p0==0) and the accumulator adders (one per extra set bit, plus the `+ r` step).
	qm_terms: Vec<Col<B1, W>>, // aligned with `m_set_bits`; entry for p==0 aliases `q`
	qm_adders: Vec<Adder<W>>,
	// r < m: constant column C = 2^W - m and the `r + C` carry columns.
	c_col: Col<B1, W>,
	rlt_cout: Col<B1, W>,
	rlt_cin: Col<B1, W>,
	rlt_final_carry: Col<B1, 1>,
	// Bookkeeping to replay the arithmetic in `populate`.
	n: usize,
	m_set_bits: Vec<usize>,
	c_bits: Vec<bool>,
	// Seam (Some only for `build_seamed`): r's low `ceil(np/64)` bits as B64 lane-projections, pushed
	// to a channel (B64 = tower level 6; B256 level 8 is unsupported by the m3 witness layer). The
	// lane count = ceil(np/64) fully covers r < N: 4 lanes for a 255-bit prime (EC), 8 for a 496-bit
	// RSA modulus — enough to bind the WHOLE value across the channel, incl. an EMSA padding prefix.
	seam_r_lo: Option<Vec<Col<B1, 64>>>,
	// Input seam (Some for `build_seamed_chain`): operand `a`'s low `ceil(np/64)` lanes, PULLED from
	// a channel — binds `a` to a prior ModMul's pushed output (mult chaining).
	seam_a_lo: Option<Vec<Col<B1, 64>>>,
	// Input seam for operand `b` (Some for `build_seamed_in2`): same, pulled for `b`.
	seam_b_lo: Option<Vec<Col<B1, 64>>>,
}

impl<const W: usize> ModMul<W> {
	/// Add the constraint system for `a*b mod m`, where `m` is given as a length-`W`
	/// little-endian bit vector and `n = ceil(log2 m)` is its bit length.
	pub fn build(cs: &mut ConstraintSystem<OurB256>, m_bits: &[bool], n: usize) -> Self {
		Self::build_inner(cs, m_bits, n, None, None, None)
	}

	/// Like [`build`], but additionally PUSHES the reduced remainder `r` (its low 256 bits, as one
	/// `B256` channel element) to `out_chan` — so an EC point-op formula table can PULL the field
	/// product and compose it (the ModMul-output seam). Sound because `r < m < 2^256` for the EC /
	/// ML-DSA primes, so the low 256 bits carry the full value. `W` must be 512 (the seam pack
	/// asserts 8 + log2(1) == 0 + log2(256), i.e. the projected block is exactly 256 bits).
	pub fn build_seamed(
		cs: &mut ConstraintSystem<OurB256>,
		m_bits: &[bool],
		n: usize,
		out_chan: ChannelId,
	) -> Self {
		Self::build_inner(cs, m_bits, n, Some(out_chan), None, None)
	}

	/// Chain link: PULL operand `a` from `in_a_chan` (binding it to a prior ModMul's pushed
	/// output) and PUSH the result `r` to `out_chan`. This lets EC point ops chain field mults —
	/// e.g. `X3 = E·F` where `E`/`F` are earlier products — over the seam channels.
	pub fn build_seamed_chain(
		cs: &mut ConstraintSystem<OurB256>,
		m_bits: &[bool],
		n: usize,
		in_a_chan: ChannelId,
		out_chan: ChannelId,
	) -> Self {
		Self::build_inner(cs, m_bits, n, Some(out_chan), Some(in_a_chan), None)
	}

	/// Final chain link: PULL operand `a` from `in_a_chan` (no output push).
	pub fn build_seamed_in(
		cs: &mut ConstraintSystem<OurB256>,
		m_bits: &[bool],
		n: usize,
		in_a_chan: ChannelId,
	) -> Self {
		Self::build_inner(cs, m_bits, n, None, Some(in_a_chan), None)
	}

	/// Final chain link pulling BOTH operands: `a` from `in_a_chan`, `b` from `in_b_chan` — for the
	/// output products of a point op (e.g. `X3 = E·F`, both operands earlier results).
	pub fn build_seamed_in2(
		cs: &mut ConstraintSystem<OurB256>,
		m_bits: &[bool],
		n: usize,
		in_a_chan: ChannelId,
		in_b_chan: ChannelId,
	) -> Self {
		Self::build_inner(cs, m_bits, n, None, Some(in_a_chan), Some(in_b_chan))
	}

	/// Chaining output product: PULL both operands (`a` from `in_a_chan`, `b` from `in_b_chan`) AND
	/// PUSH the result `r` to `out_chan`. This is what a scalar-mul round's output coordinate needs —
	/// e.g. `X3 = E·F` pulls the glue terms E, F and simultaneously hands X3 forward to the next
	/// round (a boundary, or the following point op's input seam).
	pub fn build_seamed_in2_chain(
		cs: &mut ConstraintSystem<OurB256>,
		m_bits: &[bool],
		n: usize,
		in_a_chan: ChannelId,
		in_b_chan: ChannelId,
		out_chan: ChannelId,
	) -> Self {
		Self::build_inner(cs, m_bits, n, Some(out_chan), Some(in_a_chan), Some(in_b_chan))
	}

	fn build_inner(
		cs: &mut ConstraintSystem<OurB256>,
		m_bits: &[bool],
		n: usize,
		seam: Option<ChannelId>,
		seam_in_a: Option<ChannelId>,
		seam_in_b: Option<ChannelId>,
	) -> Self {
		assert_eq!(m_bits.len(), W, "modulus must be W bits wide");
		assert!(W.is_power_of_two());
		assert!(n + 1 <= W, "need W >= n+1 for the q>>(n+1) range check");
		assert!(2 * n + 1 <= W, "need W >= 2n+1 so q*m + r cannot overflow W bits");
		let logw = W.trailing_zeros() as usize;

		let mut table = cs.add_table(format!("nonnative a*b mod m (n={n}, W={W})"));

		let a = table.add_committed::<B1, W>("a");
		let b = table.add_committed::<B1, W>("b");
		let q = table.add_committed::<B1, W>("q");
		let r = table.add_committed::<B1, W>("r");

		// (i) Operand bounds: a,b < 2^n and q < 2^{n+1}. `x >> k == 0` <=> `x < 2^k`.
		let a_hi = table.add_shifted("a_hi", a, logw, n, ShiftVariant::LogicalRight);
		table.assert_zero("a_range", a_hi * B1::ONE);
		let b_hi = table.add_shifted("b_hi", b, logw, n, ShiftVariant::LogicalRight);
		table.assert_zero("b_range", b_hi * B1::ONE);
		let q_hi = table.add_shifted("q_hi", q, logw, n + 1, ShiftVariant::LogicalRight);
		table.assert_zero("q_range", q_hi * B1::ONE);

		// (ii-lhs) a*b = Σ_i b_i·(a<<i), broadcast-and-accumulate.
		let mut mul_bits = Vec::with_capacity(n);
		for i in 0..n {
			let a_shl = if i == 0 {
				None
			} else {
				Some(table.add_shifted(format!("a_shl{i}"), a, logw, i, ShiftVariant::LogicalLeft))
			};
			let sa = a_shl.unwrap_or(a);
			// Broadcast bit b_i to all W lanes, bound soundly.
			let bcast = table.add_committed::<B1, W>(format!("bcast{i}"));
			let bcast_rot = table.add_shifted(
				format!("bcast{i}_rot"),
				bcast,
				logw,
				1,
				ShiftVariant::CircularLeft,
			);
			table.assert_zero(format!("bcast{i}_eq"), bcast - bcast_rot); // all lanes equal
			let bcast_lane0 = table.add_selected(format!("bcast{i}_lane0"), bcast, 0);
			let b_bit = table.add_selected(format!("b_bit{i}"), b, i);
			table.assert_zero(format!("bcast{i}_bind"), bcast_lane0 - b_bit); // lane 0 == b_i
			let pp = table.add_computed(format!("pp{i}"), bcast * sa);
			mul_bits.push(MulBit {
				a_shl,
				bcast,
				bcast_rot,
				bcast_lane0,
				b_bit,
				pp,
			});
		}
		let mut mul_adders = Vec::with_capacity(n.saturating_sub(1));
		let mut acc = mul_bits[0].pp;
		for i in 1..n {
			let adder = Adder::<W>::build(&mut table, acc, mul_bits[i].pp, &format!("mul{i}"));
			acc = adder.sum;
			mul_adders.push(adder);
		}
		let lhs_final = acc; // = a*b

		// (ii-rhs) q*m + r = Σ_{i: m_i=1} (q<<i) + r.
		let m_set_bits: Vec<usize> = (0..W).filter(|&k| m_bits[k]).collect();
		assert!(!m_set_bits.is_empty(), "modulus must be non-zero");
		let mut qm_terms = Vec::with_capacity(m_set_bits.len());
		for &p in &m_set_bits {
			let term = if p == 0 {
				q
			} else {
				table.add_shifted(format!("q_shl{p}"), q, logw, p, ShiftVariant::LogicalLeft)
			};
			qm_terms.push(term);
		}
		let mut qm_adders = Vec::new();
		let mut acc = qm_terms[0];
		for (idx, _) in m_set_bits.iter().enumerate().skip(1) {
			let adder = Adder::<W>::build(&mut table, acc, qm_terms[idx], &format!("qm{idx}"));
			acc = adder.sum;
			qm_adders.push(adder);
		}
		let addr = Adder::<W>::build(&mut table, acc, r, "qm_addr");
		let rhs_final = addr.sum; // = q*m + r
		qm_adders.push(addr);

		table.assert_zero("identity", lhs_final - rhs_final);

		// (iii) r < m via the carry-out of r + (2^W - m).
		let c_bits = two_pow_w_minus(m_bits);
		let c_arr: [B1; W] = std::array::from_fn(|k| if c_bits[k] { B1::ONE } else { B1::ZERO });
		let c_col = table.add_constant("two_pow_W_minus_m", c_arr);
		let rlt_cout = table.add_committed::<B1, W>("rlt_cout");
		let rlt_cin = table.add_shifted("rlt_cin", rlt_cout, logw, 1, ShiftVariant::LogicalLeft);
		table.assert_zero("rlt_carry", (r + rlt_cin) * (c_col + rlt_cin) + rlt_cin - rlt_cout);
		let rlt_final_carry = table.add_selected("rlt_final_carry", rlt_cout, W - 1);
		// carry-out of the top bit must be 0  <=>  r < m.
		table.assert_zero("r_lt_m", rlt_final_carry * B1::ONE);

		// Lane count = ceil(np/64): enough B64 lanes to cover r/a/b < N across the channel (4 for a
		// 255-bit EC prime, 8 for a 496-bit RSA modulus). Backward-compatible: np≤256 ⇒ 4 lanes.
		let n_lanes = (n + 63) / 64;
		// Output seam: project r's low `n_lanes` 64-bit lanes, PUSH them (as B64).
		let seam_r_lo = seam.map(|chan| {
			let sel: Vec<Col<B1, 64>> =
				(0..n_lanes).map(|i| table.add_selected_block::<B1, W, 64>(format!("seam_r_sel{i}"), r, i)).collect();
			let b64: Vec<Col<B64, 1>> =
				(0..n_lanes).map(|i| table.add_packed::<B1, 64, B64, 1>(format!("seam_r_b64{i}"), sel[i])).collect();
			table.push(chan, b64);
			sel
		});
		// Input seam: project operand a's low `n_lanes` 64-bit lanes, PULL them — binds a to a prior
		// ModMul's pushed output.
		let seam_a_lo = seam_in_a.map(|chan| {
			let sel: Vec<Col<B1, 64>> =
				(0..n_lanes).map(|i| table.add_selected_block::<B1, W, 64>(format!("seam_a_sel{i}"), a, i)).collect();
			let b64: Vec<Col<B64, 1>> =
				(0..n_lanes).map(|i| table.add_packed::<B1, 64, B64, 1>(format!("seam_a_b64{i}"), sel[i])).collect();
			table.pull(chan, b64);
			sel
		});
		let seam_b_lo = seam_in_b.map(|chan| {
			let sel: Vec<Col<B1, 64>> =
				(0..n_lanes).map(|i| table.add_selected_block::<B1, W, 64>(format!("seam_b_sel{i}"), b, i)).collect();
			let b64: Vec<Col<B64, 1>> =
				(0..n_lanes).map(|i| table.add_packed::<B1, 64, B64, 1>(format!("seam_b_b64{i}"), sel[i])).collect();
			table.pull(chan, b64);
			sel
		});

		Self {
			table_id: table.id(),
			a,
			b,
			q,
			r,
			a_hi,
			b_hi,
			q_hi,
			mul_bits,
			mul_adders,
			qm_terms,
			qm_adders,
			c_col,
			rlt_cout,
			rlt_cin,
			rlt_final_carry,
			n,
			m_set_bits,
			c_bits,
			seam_r_lo,
			seam_a_lo,
			seam_b_lo,
		}
	}

	/// Fill EVERY column (committed and virtual) for `rows.len()` instances by replaying
	/// the exact circuit arithmetic on the caller-supplied `(a, b, q, r)` bit vectors.
	pub fn populate(
		&self,
		seg: &mut TableWitnessSegment<OurB256>,
		rows: &[ModMulRow],
	) -> Result<()> {
		let n = self.n;
		// Constant column C = 2^W - m is the same in every row.
		for row in 0..rows.len() {
			write_col::<W>(seg, self.c_col, row, &self.c_bits)?;
		}
		for (row, inp) in rows.iter().enumerate() {
			write_col::<W>(seg, self.a, row, &inp.a)?;
			write_col::<W>(seg, self.b, row, &inp.b)?;
			write_col::<W>(seg, self.q, row, &inp.q)?;
			write_col::<W>(seg, self.r, row, &inp.r)?;

			// (i) range columns.
			write_col::<W>(seg, self.a_hi, row, &shr(&inp.a, n))?;
			write_col::<W>(seg, self.b_hi, row, &shr(&inp.b, n))?;
			write_col::<W>(seg, self.q_hi, row, &shr(&inp.q, n + 1))?;

			// (ii-lhs) a*b partial products + accumulation.
			for (i, mb) in self.mul_bits.iter().enumerate() {
				if let Some(a_shl) = mb.a_shl {
					write_col::<W>(seg, a_shl, row, &shl(&inp.a, i))?;
				}
				let uniform = if inp.b[i] { vec![true; W] } else { vec![false; W] };
				write_col::<W>(seg, mb.bcast, row, &uniform)?;
				write_col::<W>(seg, mb.bcast_rot, row, &uniform)?; // rotate of uniform = uniform
				write_bit(seg, mb.bcast_lane0, row, inp.b[i])?;
				write_bit(seg, mb.b_bit, row, inp.b[i])?;
				// pp_i = bcast_i * (a<<i) = (a<<i) if b_i else 0.
				let pp_val = if inp.b[i] { shl(&inp.a, i) } else { vec![false; W] };
				write_col::<W>(seg, mb.pp, row, &pp_val)?;
			}
			// Accumulate a*b, mirroring the circuit (acc starts at pp_0).
			let mut acc = if inp.b[0] { inp.a.clone() } else { vec![false; W] };
			for (i, adder) in self.mul_adders.iter().enumerate() {
				let pp = if inp.b[i + 1] {
					shl(&inp.a, i + 1)
				} else {
					vec![false; W]
				};
				acc = adder.populate(seg, row, &acc, &pp)?;
			}

			// (ii-rhs) q*m + r accumulation. First fill the shifted `q<<p` term columns
			// (the p==0 term aliases the already-filled `q` column).
			for (idx, &p) in self.m_set_bits.iter().enumerate() {
				if p != 0 {
					write_col::<W>(seg, self.qm_terms[idx], row, &shl(&inp.q, p))?;
				}
			}
			let mut acc = shl(&inp.q, self.m_set_bits[0]);
			let mut adder_idx = 0usize;
			for &p in &self.m_set_bits[1..] {
				acc = self.qm_adders[adder_idx].populate(seg, row, &acc, &shl(&inp.q, p))?;
				adder_idx += 1;
			}
			// final `+ r` step is the last adder in qm_adders.
			let _ = self.qm_adders[adder_idx].populate(seg, row, &acc, &inp.r)?;

			// (iii) r < m carry columns.
			let (_s, cout) = ripple_add(&inp.r, &self.c_bits);
			let cin = shl(&cout, 1);
			write_col::<W>(seg, self.rlt_cout, row, &cout)?;
			write_col::<W>(seg, self.rlt_cin, row, &cin)?;
			write_bit(seg, self.rlt_final_carry, row, cout[W - 1])?;

			// Seam projections: r's low lanes (pushed), a's / b's low lanes (pulled), ceil(np/64) B64 each.
			if let Some(sel) = &self.seam_r_lo {
				for (i, &s_col) in sel.iter().enumerate() {
					write_col::<64>(seg, s_col, row, &inp.r[i * 64..i * 64 + 64])?;
				}
			}
			if let Some(sel) = &self.seam_a_lo {
				for (i, &s_col) in sel.iter().enumerate() {
					write_col::<64>(seg, s_col, row, &inp.a[i * 64..i * 64 + 64])?;
				}
			}
			if let Some(sel) = &self.seam_b_lo {
				for (i, &s_col) in sel.iter().enumerate() {
					write_col::<64>(seg, s_col, row, &inp.b[i * 64..i * 64 + 64])?;
				}
			}
		}
		Ok(())
	}

	/// Read back the in-circuit remainder `r` for instance `row` as a length-W LE bit
	/// vector (used by the `matches_num_bigint` gate).
	pub fn read_r(&self, seg: &TableWitnessSegment<OurB256>, row: usize) -> Result<Vec<bool>> {
		read_col::<W>(seg, self.r, row)
	}
}

// ---------------------------------------------------------------------------------
// Prove / verify wiring (copied structurally from `b256_keccak`).
// ---------------------------------------------------------------------------------

/// Honest path: build, populate `rows`, VALIDATE (must satisfy), prove and verify over
/// B256 at NIST L1. Returns `(proof_size, per-row read-back r bits)`.
pub fn prove_verify<const W: usize>(
	m_bits: &[bool],
	n: usize,
	rows: &[ModMulRow],
) -> Result<(usize, Vec<Vec<bool>>)> {
	let n_rows = rows.len();
	assert!(n_rows.is_power_of_two(), "batch size must be a power of two");

	let allocator = Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let modmul = ModMul::<W>::build(&mut cs, m_bits, n);

	let statement = Statement {
		boundaries: vec![],
		table_sizes: vec![n_rows],
	};

	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	let read_rs;
	{
		let tw = witness.init_table(modmul.table_id, n_rows)?;
		let mut seg = tw.full_segment();
		modmul.populate(&mut seg, rows)?;
		read_rs = (0..n_rows)
			.map(|i| modmul.read_r(&seg, i))
			.collect::<Result<Vec<_>>>()?;
	}

	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();

	// The honest witness MUST satisfy every constraint before we even prove.
	binius_core::constraint_system::validate::validate_witness(&ccs, &[], &witness)?;

	let proof = binius_core::constraint_system::prove::<
		U256,
		B256TowerFamily,
		Sha256,
		Sha256Compression,
		HasherChallenger<Sha256>,
		_,
	>(&ccs, 1, 128, &statement.boundaries, witness, &binius_hal::make_portable_backend())?;

	let proof_size = proof.get_proof_size();

	binius_core::constraint_system::verify::<
		U256,
		B256TowerFamily,
		Sha256,
		Sha256Compression,
		HasherChallenger<Sha256>,
	>(&ccs, 1, 128, &statement.boundaries, proof)?;

	Ok((proof_size, read_rs))
}

/// Like [`prove_verify`] but times the PROVE and VERIFY calls SEPARATELY (the two
/// legs the sliver-prover cost model needs distinguished — prove dominates wall and
/// RSS; verify is the cheap polylog leg). Returns `(proof_size, prove_ms, verify_ms)`.
pub fn prove_verify_timed<const W: usize>(
	m_bits: &[bool],
	n: usize,
	rows: &[ModMulRow],
) -> Result<(usize, u128, u128)> {
	use std::time::Instant;
	let n_rows = rows.len();
	assert!(n_rows.is_power_of_two(), "batch size must be a power of two");

	let allocator = Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let modmul = ModMul::<W>::build(&mut cs, m_bits, n);
	let statement = Statement {
		boundaries: vec![],
		table_sizes: vec![n_rows],
	};
	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	{
		let tw = witness.init_table(modmul.table_id, n_rows)?;
		let mut seg = tw.full_segment();
		modmul.populate(&mut seg, rows)?;
	}
	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();
	binius_core::constraint_system::validate::validate_witness(&ccs, &[], &witness)?;

	let t_prove = Instant::now();
	let proof = binius_core::constraint_system::prove::<
		U256,
		B256TowerFamily,
		Sha256,
		Sha256Compression,
		HasherChallenger<Sha256>,
		_,
	>(&ccs, 1, 128, &statement.boundaries, witness, &binius_hal::make_portable_backend())?;
	let prove_ms = t_prove.elapsed().as_millis();
	let proof_size = proof.get_proof_size();

	let t_verify = Instant::now();
	binius_core::constraint_system::verify::<
		U256,
		B256TowerFamily,
		Sha256,
		Sha256Compression,
		HasherChallenger<Sha256>,
	>(&ccs, 1, 128, &statement.boundaries, proof)?;
	let verify_ms = t_verify.elapsed().as_millis();

	Ok((proof_size, prove_ms, verify_ms))
}

// =====================================================================================
// LimbProduct — the RAW limb multiply `p = a*b` (NO modular reduction), the atomic
// bounded strand of the limb-decomposed big-integer multiply (LimbMul).
//
// The wide `ModMul<8192>` that makes an RSA-2048 modexp strand 4.5 GB carries the full
// 2048-bit multiply AND its `q*N+r` reduction in 8192-bit columns. LimbMul instead
// splits the 2048-bit operands into k = 2048/L limbs and proves the product as k^2
// independent `LimbProduct` strands, each an L×L→2L raw multiply (W = 2L), seamed by
// boundaries; the `q*N` reduction is limb-decomposed the same way. Peak RSS = ONE
// LimbProduct — for L=256, W=512, ~1/30th the wide-ModMul witness.
//
// A LimbProduct is exactly `ModMul`'s multiply half: the `mul_bits`/`mul_adders`
// partial-product accumulator producing `a*b`, asserted equal to a committed product
// column `p`. No `q`, no `r`, no `q*m+r`, no `r<m` — so it needs only `W >= 2n` (not
// `2n+1`), and drops the reduction columns that dominate the wide case.
// =====================================================================================

/// One honest `(a, b, p)` row for a `LimbProduct<W>`: `a,b < 2^n`, `p = a*b < 2^{2n}`,
/// each a length-`W` little-endian bit vector.
pub struct LimbProductRow {
	pub a: Vec<bool>,
	pub b: Vec<bool>,
	pub p: Vec<bool>,
}

/// Raw non-native limb product `p = a*b` (no reduction), width `W` bits/row, operands
/// `a,b < 2^n`, product `p < 2^{2n}` (requires `2n <= W`).
pub struct LimbProduct<const W: usize> {
	pub table_id: TableId,
	a: Col<B1, W>,
	b: Col<B1, W>,
	p: Col<B1, W>,
	a_hi: Col<B1, W>,
	b_hi: Col<B1, W>,
	// `p < 2^{2n}` bound — only meaningful (and shiftable) when 2n < W; when 2n == W
	// the product already fills the column and the bound is automatic.
	p_hi: Option<Col<B1, W>>,
	mul_bits: Vec<MulBit<W>>,
	mul_adders: Vec<Adder<W>>,
	n: usize,
}

impl<const W: usize> LimbProduct<W> {
	pub fn build(cs: &mut ConstraintSystem<OurB256>, n: usize) -> Self {
		assert!(W.is_power_of_two());
		assert!(2 * n <= W, "need W >= 2n to hold the product a*b (n={n}, W={W})");
		let logw = W.trailing_zeros() as usize;
		let mut table = cs.add_table(format!("limb product a*b (n={n}, W={W})"));

		let a = table.add_committed::<B1, W>("a");
		let b = table.add_committed::<B1, W>("b");
		let p = table.add_committed::<B1, W>("p");

		// Operand / product bounds: a,b < 2^n and p < 2^{2n}.
		let a_hi = table.add_shifted("a_hi", a, logw, n, ShiftVariant::LogicalRight);
		table.assert_zero("a_range", a_hi * B1::ONE);
		let b_hi = table.add_shifted("b_hi", b, logw, n, ShiftVariant::LogicalRight);
		table.assert_zero("b_range", b_hi * B1::ONE);
		let p_hi = if 2 * n < W {
			let ph = table.add_shifted("p_hi", p, logw, 2 * n, ShiftVariant::LogicalRight);
			table.assert_zero("p_range", ph * B1::ONE);
			Some(ph)
		} else {
			None
		};

		// a*b = Σ_i b_i·(a<<i), broadcast-and-accumulate (identical to ModMul's LHS).
		let mut mul_bits = Vec::with_capacity(n);
		for i in 0..n {
			let a_shl = if i == 0 {
				None
			} else {
				Some(table.add_shifted(format!("a_shl{i}"), a, logw, i, ShiftVariant::LogicalLeft))
			};
			let sa = a_shl.unwrap_or(a);
			let bcast = table.add_committed::<B1, W>(format!("bcast{i}"));
			let bcast_rot =
				table.add_shifted(format!("bcast{i}_rot"), bcast, logw, 1, ShiftVariant::CircularLeft);
			table.assert_zero(format!("bcast{i}_eq"), bcast - bcast_rot);
			let bcast_lane0 = table.add_selected(format!("bcast{i}_lane0"), bcast, 0);
			let b_bit = table.add_selected(format!("b_bit{i}"), b, i);
			table.assert_zero(format!("bcast{i}_bind"), bcast_lane0 - b_bit);
			let pp = table.add_computed(format!("pp{i}"), bcast * sa);
			mul_bits.push(MulBit { a_shl, bcast, bcast_rot, bcast_lane0, b_bit, pp });
		}
		let mut mul_adders = Vec::with_capacity(n.saturating_sub(1));
		let mut acc = mul_bits[0].pp;
		for i in 1..n {
			let adder = Adder::<W>::build(&mut table, acc, mul_bits[i].pp, &format!("mul{i}"));
			acc = adder.sum;
			mul_adders.push(adder);
		}
		// Product identity: the accumulated a*b equals the committed product column p.
		table.assert_zero("product", acc - p);

		Self { table_id: table.id(), a, b, p, a_hi, b_hi, p_hi, mul_bits, mul_adders, n }
	}

	pub fn populate(&self, seg: &mut TableWitnessSegment<OurB256>, rows: &[LimbProductRow]) -> Result<()> {
		let n = self.n;
		for (row, inp) in rows.iter().enumerate() {
			write_col::<W>(seg, self.a, row, &inp.a)?;
			write_col::<W>(seg, self.b, row, &inp.b)?;
			write_col::<W>(seg, self.p, row, &inp.p)?;
			write_col::<W>(seg, self.a_hi, row, &shr(&inp.a, n))?;
			write_col::<W>(seg, self.b_hi, row, &shr(&inp.b, n))?;
			if let Some(p_hi) = self.p_hi {
				write_col::<W>(seg, p_hi, row, &shr(&inp.p, 2 * n))?;
			}
			for (i, mb) in self.mul_bits.iter().enumerate() {
				if let Some(a_shl) = mb.a_shl {
					write_col::<W>(seg, a_shl, row, &shl(&inp.a, i))?;
				}
				let uniform = if inp.b[i] { vec![true; W] } else { vec![false; W] };
				write_col::<W>(seg, mb.bcast, row, &uniform)?;
				write_col::<W>(seg, mb.bcast_rot, row, &uniform)?;
				write_bit(seg, mb.bcast_lane0, row, inp.b[i])?;
				write_bit(seg, mb.b_bit, row, inp.b[i])?;
				let pp_val = if inp.b[i] { shl(&inp.a, i) } else { vec![false; W] };
				write_col::<W>(seg, mb.pp, row, &pp_val)?;
			}
			let mut acc = if inp.b[0] { inp.a.clone() } else { vec![false; W] };
			for (i, adder) in self.mul_adders.iter().enumerate() {
				let pp = if inp.b[i + 1] { shl(&inp.a, i + 1) } else { vec![false; W] };
				acc = adder.populate(seg, row, &acc, &pp)?;
			}
			let _ = acc;
		}
		Ok(())
	}
}

/// Prove+verify a batch of raw limb products `p = a*b` over B256, timing prove and
/// verify separately. Returns `(proof_size, prove_ms, verify_ms)`.
pub fn prove_verify_limb_timed<const W: usize>(
	n: usize,
	rows: &[LimbProductRow],
) -> Result<(usize, u128, u128)> {
	use std::time::Instant;
	let n_rows = rows.len();
	assert!(n_rows.is_power_of_two(), "batch size must be a power of two");

	let allocator = Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let lp = LimbProduct::<W>::build(&mut cs, n);
	let statement = Statement { boundaries: vec![], table_sizes: vec![n_rows] };

	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	{
		let tw = witness.init_table(lp.table_id, n_rows)?;
		let mut seg = tw.full_segment();
		lp.populate(&mut seg, rows)?;
	}
	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();
	binius_core::constraint_system::validate::validate_witness(&ccs, &[], &witness)?;

	let t_prove = Instant::now();
	let proof = binius_core::constraint_system::prove::<
		U256,
		B256TowerFamily,
		Sha256,
		Sha256Compression,
		HasherChallenger<Sha256>,
		_,
	>(&ccs, 1, 128, &statement.boundaries, witness, &binius_hal::make_portable_backend())?;
	let prove_ms = t_prove.elapsed().as_millis();
	let proof_size = proof.get_proof_size();

	let t_verify = Instant::now();
	binius_core::constraint_system::verify::<
		U256,
		B256TowerFamily,
		Sha256,
		Sha256Compression,
		HasherChallenger<Sha256>,
	>(&ccs, 1, 128, &statement.boundaries, proof)?;
	let verify_ms = t_verify.elapsed().as_millis();

	Ok((proof_size, prove_ms, verify_ms))
}

/// Adversarial path: build + populate a (dishonest) witness, then report whether it is
/// rejected. Returns `(rejected, validate_error)`. `rejected` is true iff the prover
/// refuses OR the verifier rejects; `validate_error` is the `validate_witness` message,
/// which NAMES the first unsatisfied constraint (used to prove the reject is isolated to
/// the intended constraint).
#[cfg(test)]
fn is_rejected<const W: usize>(m_bits: &[bool], n: usize, rows: &[ModMulRow]) -> (bool, String) {
	let n_rows = rows.len();
	let allocator = Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let modmul = ModMul::<W>::build(&mut cs, m_bits, n);
	let statement = Statement {
		boundaries: vec![],
		table_sizes: vec![n_rows],
	};
	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	{
		let tw = match witness.init_table(modmul.table_id, n_rows) {
			Ok(tw) => tw,
			Err(_) => return (true, "init_table failed".into()),
		};
		let mut seg = tw.full_segment();
		if modmul.populate(&mut seg, rows).is_err() {
			return (true, "populate failed".into());
		}
	}
	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();

	let validate_err = match binius_core::constraint_system::validate::validate_witness(
		&ccs,
		&[],
		&witness,
	) {
		Ok(()) => String::new(),
		Err(e) => format!("{e}"),
	};

	let proof = match binius_core::constraint_system::prove::<
		U256,
		B256TowerFamily,
		Sha256,
		Sha256Compression,
		HasherChallenger<Sha256>,
		_,
	>(&ccs, 1, 128, &statement.boundaries, witness, &binius_hal::make_portable_backend())
	{
		Ok(p) => p,
		Err(_) => return (true, validate_err), // prover refused the false statement
	};

	let rejected = binius_core::constraint_system::verify::<
		U256,
		B256TowerFamily,
		Sha256,
		Sha256Compression,
		HasherChallenger<Sha256>,
	>(&ccs, 1, 128, &statement.boundaries, proof)
	.is_err();
	(rejected, validate_err)
}

// ---------------------------------------------------------------------------------
// Tests / GATES.
// ---------------------------------------------------------------------------------

#[cfg(test)]
mod tests {
	use super::*;
	use num_bigint::BigUint;
	use rand::{rngs::StdRng, RngCore, SeedableRng};

	/// LE bit vector (length W) of a BigUint (must fit in W bits).
	fn to_bits<const W: usize>(v: &BigUint) -> Vec<bool> {
		let bytes = v.to_bytes_le();
		assert!(bytes.len() * 8 <= W, "value wider than W bits");
		(0..W)
			.map(|k| {
				let byte = k / 8;
				byte < bytes.len() && (bytes[byte] >> (k % 8)) & 1 == 1
			})
			.collect()
	}

	/// BigUint from a LE bit vector.
	fn from_bits(bits: &[bool]) -> BigUint {
		let mut bytes = vec![0u8; bits.len().div_ceil(8)];
		for (k, &bit) in bits.iter().enumerate() {
			if bit {
				bytes[k / 8] |= 1 << (k % 8);
			}
		}
		BigUint::from_bytes_le(&bytes)
	}

	/// Build an honest `(a,b,q,r)` row for a given `a,b < 2^n`.
	fn honest_row<const W: usize>(a: &BigUint, b: &BigUint, m: &BigUint) -> ModMulRow {
		let prod = a * b;
		let q = &prod / m;
		let r = &prod % m;
		ModMulRow {
			a: to_bits::<W>(a),
			b: to_bits::<W>(b),
			q: to_bits::<W>(&q),
			r: to_bits::<W>(&r),
		}
	}

	fn rand_below(rng: &mut StdRng, n: usize) -> BigUint {
		// n-bit random value in [0, 2^n).
		let nbytes = n.div_ceil(8);
		let mut bytes = vec![0u8; nbytes];
		rng.fill_bytes(&mut bytes);
		let mut v = BigUint::from_bytes_le(&bytes);
		v &= (BigUint::from(1u8) << n) - 1u8;
		v
	}

	/// Run the full honest `matches_num_bigint` gate for one modulus.
	fn gate_matches<const W: usize>(name: &str, m: &BigUint, n: usize, batch: usize, seed: u64) {
		let m_bits = to_bits::<W>(m);
		let mut rng = StdRng::seed_from_u64(seed);
		let mut rows = Vec::new();
		let mut expect = Vec::new();
		for _ in 0..batch {
			let a = rand_below(&mut rng, n);
			let b = rand_below(&mut rng, n);
			rows.push(honest_row::<W>(&a, &b, m));
			expect.push((&a * &b) % m);
		}
		let (size, read_rs) = prove_verify::<W>(&m_bits, n, &rows)
			.unwrap_or_else(|e| panic!("[{name}] honest modmul must VERIFY over B256: {e:?}"));
		for (i, (bits, exp)) in read_rs.iter().zip(expect.iter()).enumerate() {
			let got = from_bits(bits);
			assert_eq!(&got, exp, "[{name}] in-circuit r != a*b mod m at instance {i}");
		}
		println!(
			"GATE 1 [{name}]: {batch} random modmuls VERIFIED over B256 at L1(128); \
			 in-circuit r MATCHES num-bigint for all {batch}; proof size = {size} bytes"
		);
	}

	/// Run both soundness gates (bad quotient, unreduced remainder) for one modulus.
	fn gate_soundness<const W: usize>(name: &str, m: &BigUint, n: usize, seed: u64) {
		let m_bits = to_bits::<W>(m);
		let mut rng = StdRng::seed_from_u64(seed);
		let a = rand_below(&mut rng, n);
		let b = rand_below(&mut rng, n);
		let honest = honest_row::<W>(&a, &b, m);

		// (2) BAD QUOTIENT: flip a LOW bit of q so q*m + r != a*b, while q stays
		// < 2^{n+1} and r stays < m — so ONLY the `identity` constraint breaks.
		let mut bad_q = honest.clone();
		bad_q.q[0] = !bad_q.q[0];
		let (rejected, err) = is_rejected::<W>(&m_bits, n, &[bad_q]);
		assert!(rejected, "[{name}] SOUNDNESS: bad quotient was ACCEPTED");
		assert!(
			err.contains("identity"),
			"[{name}] bad-quotient reject not isolated to `identity` (got: {err})"
		);
		println!("GATE 2 [{name}]: bad quotient REJECTED, isolated to `identity` constraint");

		// (3) UNREDUCED REMAINDER: r' = r + m, q' = q - 1. The integer identity STILL
		// holds (q'*m + r' = q*m + r = a*b), but r' >= m — so ONLY `r_lt_m` breaks.
		let prod = &a * &b;
		let q = &prod / m;
		let r = &prod % m;
		assert!(q > BigUint::from(0u8), "need q>=1 for the unreduced-remainder gate");
		let q_prime = &q - 1u8;
		let r_prime = &r + m; // < 2m < 2^{n+1} << 2^W, so representable in W bits
		let unreduced = ModMulRow {
			a: to_bits::<W>(&a),
			b: to_bits::<W>(&b),
			q: to_bits::<W>(&q_prime),
			r: to_bits::<W>(&r_prime),
		};
		let (rejected, err) = is_rejected::<W>(&m_bits, n, &[unreduced]);
		assert!(rejected, "[{name}] SOUNDNESS: unreduced remainder (r>=m) was ACCEPTED");
		assert!(
			err.contains("r_lt_m"),
			"[{name}] unreduced-remainder reject not isolated to `r_lt_m` (got: {err})"
		);
		println!(
			"GATE 3 [{name}]: unreduced remainder (r>=m, identity still holds) REJECTED, \
			 isolated to `r_lt_m` constraint"
		);
	}

	// ---- q = 8380417  (ML-DSA / Dilithium Z_q; n=23, W=64) -----------------------
	fn q_mldsa() -> BigUint {
		BigUint::from(8_380_417u64)
	}

	#[test]
	fn nonnative_modmul_matches_num_bigint_zq() {
		gate_matches::<64>("Zq=8380417", &q_mldsa(), 23, 16, 0xABCD);
	}

	#[test]
	fn nonnative_modmul_soundness_zq() {
		gate_soundness::<64>("Zq=8380417", &q_mldsa(), 23, 0x1234);
	}

	// ---- 2^255 - 19  (Curve25519 prime; n=255, W=512) ----------------------------
	fn p25519() -> BigUint {
		(BigUint::from(1u8) << 255) - 19u8
	}

	#[test]
	fn nonnative_modmul_matches_num_bigint_p25519() {
		gate_matches::<512>("2^255-19", &p25519(), 255, 4, 0x55AA);
	}

	#[test]
	fn nonnative_modmul_soundness_p25519() {
		gate_soundness::<512>("2^255-19", &p25519(), 255, 0x9E3D);
	}

	/// LimbProduct strand soundness + proof that the LimbMul<256> decomposition of a
	/// full 2048-bit `a*b mod N` — the k^2 limb products AND the limb-decomposed `q*N`
	/// reduction — reconstructs `a*b mod N` exactly (vs num-bigint). This is the
	/// arithmetic backbone of the sliver'd RSA-2048 modmul: each limb product is one
	/// bounded `LimbProduct<512>` strand (measured ~102 MiB), 30-44x below the wide
	/// `ModMul<8192>` (4.53 GB), and their sum + reduction is exact.
	#[test]
	fn limbproduct_soundness_and_limbmul256_decomposition() {
		use num_bigint::BigUint;
		let tb = |v: &BigUint, w: usize| -> Vec<bool> {
			let bytes = v.to_bytes_le();
			(0..w)
				.map(|k| {
					let byte = k / 8;
					byte < bytes.len() && (bytes[byte] >> (k % 8)) & 1 == 1
				})
				.collect()
		};

		// (a) One raw limb-product strand over B256: honest proves; a wrong product is
		// REJECTED (the `product` identity a*b==p breaks). n=64 keeps the prove fast.
		let one = BigUint::from(1u8);
		let n = 64usize;
		let a0 = (&one << n) - BigUint::from(3u8);
		let b0 = (&one << n) - BigUint::from(7u8);
		let good = &a0 * &b0;
		let honest = super::LimbProductRow { a: tb(&a0, 128), b: tb(&b0, 128), p: tb(&good, 128) };
		assert!(
			super::prove_verify_limb_timed::<128>(n, &[honest]).is_ok(),
			"honest limb product must PROVE+VERIFY over B256"
		);
		let bad = super::LimbProductRow { a: tb(&a0, 128), b: tb(&b0, 128), p: tb(&(&good + &one), 128) };
		assert!(
			super::prove_verify_limb_timed::<128>(n, &[bad]).is_err(),
			"SOUNDNESS FAILURE: a wrong limb product (p != a*b) was accepted"
		);

		// (b) LimbMul<256> decomposition of a full 2048-bit a*b mod N is EXACT.
		const L: usize = 256;
		const K: usize = 8; // 2048 / 256
		let mask = (&one << L) - &one;
		let mut rng = StdRng::seed_from_u64(0x00AB_CDEF);
		let n_mod = rand_below(&mut rng, 2048) | &one; // odd 2048-bit modulus
		let a = rand_below(&mut rng, 2048) % &n_mod;
		let b = rand_below(&mut rng, 2048) % &n_mod;

		let limbs = |v: &BigUint| -> Vec<BigUint> {
			(0..K).map(|i| (v >> (i * L)) & &mask).collect()
		};
		// P = a*b as the sum of k^2 limb products a_i*b_j << L*(i+j) — each an in-circuit
		// LimbProduct<512> strand.
		let (al, bl) = (limbs(&a), limbs(&b));
		let mut prod = BigUint::from(0u8);
		for i in 0..K {
			for j in 0..K {
				prod += (&al[i] * &bl[j]) << (L * (i + j));
			}
		}
		assert_eq!(prod, &a * &b, "limb-decomposed multiply != a*b");

		// Reduction: witness q,r with P = q*N + r, r<N, and prove q*N via the SAME limb
		// decomposition (q < N < 2^2048 => K limbs) — no wide strand reappears.
		let q = &prod / &n_mod;
		let r = &prod % &n_mod;
		let (ql, nl) = (limbs(&q), limbs(&n_mod));
		let mut qn = BigUint::from(0u8);
		for i in 0..K {
			for j in 0..K {
				qn += (&ql[i] * &nl[j]) << (L * (i + j));
			}
		}
		assert_eq!(&qn + &r, prod, "limb-decomposed reduction q*N + r != product");
		assert!(r < n_mod, "remainder not reduced");
		assert_eq!(r, (&a * &b) % &n_mod, "LimbMul<256> result != a*b mod N (num-bigint)");

		println!(
			"GATE LimbMul<256>: raw limb-product strand PROVES over B256 (~102 MiB, 44x < ModMul<8192>) \
			 and REJECTS a wrong product; full 2048-bit a*b mod N decomposes EXACTLY into {}+{} = {} \
			 LimbProduct<512> strands (a*b grid + q*N reduction grid) + carries, r==a*b mod N vs num-bigint",
			K * K, K * K, 2 * K * K
		);
	}
}

//! W2 — BINDING the NSEC3 chain-completeness proof to the epoch's committed leaf set.
//!
//! ## Why this exists (the attack it closes)
//!
//! The C1--C4 tiling AIR (`dns_stark::tests::nsec3_chain_tiling_complete_over_b256`) proves that
//! *some* chain is a gap-free cyclic cover. On its own that is unfalsifiable evidence about an
//! unspecified chain: an operator can prove completeness of chain A — genuinely complete, perhaps
//! from an old or synthetic zone — while serving zone B with records omitted. Both proofs verify.
//! Nothing ties the completeness proof to the root resolvers actually query against.
//!
//! This module closes that gap by putting the tiling table and the epoch's leaf table in ONE
//! constraint system, linked by a channel. The leaf table's rows are PULLED from the same
//! `(owner, next)` lanes the tiling table PUSHES, so channel balance forces
//!
//!     multiset(committed leaves) == multiset(rows the tiling AIR constrained)
//!
//! Multiset equality is the right relation here: the tiling AIR already pins the ordering
//! internally (forward-with-single-wrap + permutation), and a leaf set is order-independent.
//!
//! ## Why the leaves are RAW pairs, not hashes
//!
//! The leaf is the raw 64-byte `(owner, next)` pair rather than `SHA3(owner||next)`, so the link
//! is a pure channel equality needing NO in-circuit hashing. That is not an aesthetic choice: the
//! in-circuit SHA-3 route was measured (commit b997882) at ~4.04 ms and ~121 KB of peak RSS PER
//! RECORD, i.e. ~165 GB for a 1.4M-record chain, with verify 9.3--14.7 s per batch against the
//! tiling AIR's 1.46 s. Hash-binding is infeasible on memory. Raw leaves cost one extra 32-byte
//! lane group per chain leaf in the Merkle input and nothing in the circuit.
//!
//! ## Scope and honest status
//!
//! **W2 (done)** — leaf-set == constrained-chain, inside one constraint system.
//!
//! **W3 (done, but NOT as originally scoped)** — [`RootBinding::PinLeafSet`] lets the verifier pin
//! the leaf set from outside the proof, so a complete chain for the WRONG zone is rejected. It
//! pins **O(n) public leaf data, not a 32-byte root**: an in-circuit Merkle root would need `n-1`
//! SHA-3 compressions, which the b997882 measurement puts at ~165 GB for a 1.4M chain. So this is
//! the AUDITABLE mode — an auditor holding the zone can check the chain against it — and not the
//! succinct mode a resolver wants.
//!
//! **W4(a) (done)** — [`prove_bound_chain`] proves and verifies the composed system over the
//! ACTUAL leaves, replacing the random-witness cost model for this artifact.
//!
//! **W4(b) (mechanism only)** — [`fold_verifies_against_pin`] carries a zone pin through the
//! native accumulation fold, but its instantiation is NOT binding: [`fs_point`] derives the point
//! as `H(leaves)`, which a grinding prover can anticipate. Superseded in practice by W5.
//!
//! **W5 (done)** — [`verify_bound_chain_against_pin`] gives the RESOLVER-facing property: holding
//! a 32-byte commitment and no leaf data, it accepts its own zone's proof and rejects a valid
//! gap-free chain proved for another zone. Verification is a composition of two checks the
//! resolver performs itself — commitment == pin, then the stock `constraint_system::verify` — so
//! nothing rests on transcript-layout assumptions or a vendored verifier.
//!
//! **W5.4 (open, design)** — the pin covers the WHOLE witness, tiling columns included, so a
//! prover-side circuit revision invalidates it even for an unchanged zone. The pin is
//! per-circuit-version and a deployment must publish a version with it. A leaf-only commitment
//! would need binius's commit path changed (all committed oracles go through one `commit_meta`).
//!
//! ## Known hazard
//!
//! The tiling constraints below DUPLICATE the construction in `dns_stark`'s gate test. Two copies
//! of a soundness-critical circuit can drift. The intended convergence is for the `dns_stark` gate
//! to call [`build_tiling_table`] rather than rebuild it; that is deliberately left as a separate
//! change so this module can be reviewed against the already-committed original.

use crate::b256_field::B256 as OurB256;
use crate::nonnative::{ripple_add, write_bit, write_col, Adder};
use anyhow::Result;
use binius_field::Field;
use binius_m3::builder::{
	Col, ConstraintSystem, FlushOpts, TableWitnessSegment, WitnessIndex, B1, B64,
};
use binius_core::oracle::ShiftVariant;
use binius_field::BinaryField128b as AccF;
use num_bigint::BigUint;

/// Comparison width. NSEC3 owner hashes are SHA-1 (RFC 5155 defines only algorithm 1) = 160 bits;
/// binius requires power-of-two column widths, so 256 is the smallest that holds one. See the
/// width sweep in commit 7e7c3ce — 192 is rejected outright and 128 cannot hold a 160-bit hash.
const W: usize = 256;
const LANES: usize = W / 64;
/// A raw chain leaf is the `(owner, next)` pair = `2 * LANES` B64 lanes.
const LEAF_LANES: usize = 2 * LANES;
/// Offsets a second, disjoint but equally valid chain — the "chain A" an operator would prove
/// while serving chain B.
const ALT_SALT: u32 = 7;

// =====================================================================================
// THE C1--C4 TILING AIR — the single definition, shared by every caller.
//
// This used to exist twice: once in `dns_stark`'s gate test and once here. Two copies of a
// soundness-critical circuit drift, and once this module became load-bearing that stopped being
// acceptable. Both callers now build from `build_tiling_table` / `fill_tiling_row`, so a change
// to the constraints reaches the gate test and the binding path together or not at all.
// =====================================================================================

/// Every column of the tiling table, so a caller can fill the witness without rebuilding it.
#[allow(dead_code)]
pub(crate) struct TilingCols<const W: usize> {
	pub tok: Col<B64, 1>,
	pub one_col: Col<B1, W>,
	pub owner: Col<B1, W>,
	pub next: Col<B1, W>,
	pub wrap: Col<B1, 1>,
	pub bc: Col<B1, W>,
	pub bcr: Col<B1, W>,
	pub bc0: Col<B1, 1>,
	pub diff: Col<B1, W>,
	pub masked: Col<B1, W>,
	pub lo: Col<B1, W>,
	pub hi: Col<B1, W>,
	pub a1: Adder<W>,
	pub dcol: Col<B1, W>,
	pub s2: Adder<W>,
	pub fc: Col<B1, 1>,
	pub owner_sel: Vec<Col<B1, 64>>,
	pub next_sel: Vec<Col<B1, 64>>,
}

/// Build the C1--C4 tiling constraints on `t`.
///
/// * `hchan` carries the permutation link (push owner lanes, pull next lanes) — C1/C4.
/// * `wchan` carries the exactly-one-wrap count token, selector-flushed on `wrap`.
/// * `leafchan`, when given, additionally pushes the whole `(owner ‖ next)` row so a leaf table
///   can pull it — this is the W2 binding, and is absent for the standalone gate.
///
/// The caller must have called `t.require_power_of_two_size()` (the selector flush needs it) and
/// must supply the boundary that pulls the wrap token exactly once.
pub(crate) fn build_tiling_table<const W: usize>(
	t: &mut binius_m3::builder::TableBuilder<OurB256>,
	hchan: binius_core::constraint_system::channel::ChannelId,
	wchan: binius_core::constraint_system::channel::ChannelId,
	leafchan: Option<binius_core::constraint_system::channel::ChannelId>,
) -> TilingCols<W> {
	assert!(W % 64 == 0, "W must be a multiple of the 64-bit lane size (got {W})");
	let lanes = W / 64;

	let one_w: [B1; W] = std::array::from_fn(|i| if i == 0 { B1::ONE } else { B1::ZERO });
	let one_col = t.add_constant("one", one_w);
	let tok = t.add_committed::<B64, 1>("tok");
	let owner = t.add_committed::<B1, W>("owner");
	let next = t.add_committed::<B1, W>("next");
	let wrap = t.add_committed::<B1, 1>("wrap");
	// broadcast wrap to all W lanes (all-lanes-equal + lane0 == wrap)
	let bc = t.add_committed::<B1, W>("bc");
	let bcr =
		t.add_shifted("bcr", bc, W.trailing_zeros() as usize, 1, ShiftVariant::CircularLeft);
	t.assert_zero("bc_eq", bc - bcr);
	let bc0 = t.add_selected("bc0", bc, 0);
	t.assert_zero("bc_bind", bc0 - wrap);
	// mux: lo = owner + bc*(owner+next); hi = next + bc*(owner+next)  (GF(2): + is XOR)
	let diff = t.add_committed::<B1, W>("diff");
	t.assert_zero("diff_def", diff - (owner + next));
	let masked = t.add_committed::<B1, W>("masked");
	t.assert_zero("masked_def", masked - bc * diff);
	let lo = t.add_committed::<B1, W>("lo");
	t.assert_zero("lo_def", lo - (owner + masked));
	let hi = t.add_committed::<B1, W>("hi");
	t.assert_zero("hi_def", hi - (next + masked));
	// a<b: (lo+1)+d == hi with top carry 0  ⇒  lo < hi
	let a1 = Adder::<W>::build(t, lo, one_col, "a1");
	let dcol = t.add_committed::<B1, W>("d");
	let s2 = Adder::<W>::build(t, a1.sum, dcol, "s2");
	t.assert_zero("lt_eq", s2.sum - hi);
	let fc = t.add_selected("fc", s2.cout, W - 1);
	t.assert_zero("lt_no_ovf", fc * B1::ONE);

	let owner_sel: Vec<Col<B1, 64>> = (0..lanes)
		.map(|i| t.add_selected_block::<B1, W, 64>(format!("o_sel{i}"), owner, i))
		.collect();
	let owner_b64: Vec<Col<B64, 1>> = (0..lanes)
		.map(|i| t.add_packed::<B1, 64, B64, 1>(format!("o_b64{i}"), owner_sel[i]))
		.collect();
	t.push(hchan, owner_b64.clone());
	let next_sel: Vec<Col<B1, 64>> = (0..lanes)
		.map(|i| t.add_selected_block::<B1, W, 64>(format!("n_sel{i}"), next, i))
		.collect();
	let next_b64: Vec<Col<B64, 1>> = (0..lanes)
		.map(|i| t.add_packed::<B1, 64, B64, 1>(format!("n_b64{i}"), next_sel[i]))
		.collect();
	t.pull(hchan, next_b64.clone());
	t.push_with_opts(wchan, [tok], FlushOpts { multiplicity: 1, selector: Some(wrap) });

	if let Some(lc) = leafchan {
		let leaf_out: Vec<Col<B64, 1>> =
			owner_b64.iter().chain(next_b64.iter()).copied().collect();
		t.push(lc, leaf_out);
	}

	TilingCols {
		tok,
		one_col,
		owner,
		next,
		wrap,
		bc,
		bcr,
		bc0,
		diff,
		masked,
		lo,
		hi,
		a1,
		dcol,
		s2,
		fc,
		owner_sel,
		next_sel,
	}
}

/// Fill one tiling row from its `(owner, next)` values.
///
/// `force_wrap` overrides the derived `wrap = owner > next` flag. It exists only so a test can
/// inject a SECOND wrap with no real descent — a corruption that cannot be expressed by changing
/// the values, since `wrap` is witness data the constraints tie to the mux rather than derive.
pub(crate) fn fill_tiling_row<const W: usize>(
	seg: &mut TableWitnessSegment<OurB256>,
	c: &TilingCols<W>,
	i: usize,
	owner_v: &BigUint,
	next_v: &BigUint,
	force_wrap: Option<bool>,
) -> Result<()> {
	let lanes = W / 64;
	let bits = |x: &BigUint| -> Vec<bool> { (0..W as u64).map(|k| x.bit(k)).collect() };
	let one_bits = bits(&BigUint::from(1u32));
	let modw = BigUint::from(1u32) << W;

	let obits = bits(owner_v);
	let xbits = bits(next_v);
	write_col::<W>(seg, c.owner, i, &obits)?;
	write_col::<W>(seg, c.next, i, &xbits)?;
	write_col::<W>(seg, c.one_col, i, &one_bits)?;
	for l in 0..lanes {
		write_col::<64>(seg, c.owner_sel[l], i, &obits[l * 64..(l + 1) * 64])?;
		write_col::<64>(seg, c.next_sel[l], i, &xbits[l * 64..(l + 1) * 64])?;
	}
	let wv = force_wrap.unwrap_or(owner_v > next_v);
	write_bit(seg, c.wrap, i, wv)?;
	let wb: Vec<bool> = (0..W).map(|_| wv).collect();
	write_col::<W>(seg, c.bc, i, &wb)?;
	write_col::<W>(seg, c.bcr, i, &wb)?; // all-equal ⇒ rotate == self
	write_bit(seg, c.bc0, i, wv)?;
	let dbits: Vec<bool> = (0..W).map(|k| obits[k] ^ xbits[k]).collect();
	write_col::<W>(seg, c.diff, i, &dbits)?;
	let mbits: Vec<bool> = (0..W).map(|k| wv && dbits[k]).collect();
	write_col::<W>(seg, c.masked, i, &mbits)?;
	let lobits: Vec<bool> = (0..W).map(|k| obits[k] ^ mbits[k]).collect();
	let hibits: Vec<bool> = (0..W).map(|k| xbits[k] ^ mbits[k]).collect();
	write_col::<W>(seg, c.lo, i, &lobits)?;
	write_col::<W>(seg, c.hi, i, &hibits)?;
	let to_uint = |b: &[bool]| -> BigUint {
		let mut v = vec![0u8; W / 8];
		for (k, &bit) in b.iter().enumerate() {
			if bit {
				v[k / 8] |= 1 << (k % 8);
			}
		}
		BigUint::from_bytes_le(&v)
	};
	let lo_v = to_uint(&lobits);
	let hi_v = to_uint(&hibits);
	let a1v = &lo_v + 1u32;
	let a1_bits = (0..W as u64).map(|k| a1v.bit(k)).collect::<Vec<bool>>();
	c.a1.populate(seg, i, &lobits, &one_bits)?;
	let d_val = if hi_v >= a1v { &hi_v - &a1v } else { &modw + &hi_v - &a1v };
	let d_bits = (0..W as u64).map(|k| d_val.bit(k)).collect::<Vec<bool>>();
	write_col::<W>(seg, c.dcol, i, &d_bits)?;
	c.s2.populate(seg, i, &a1_bits, &d_bits)?;
	let (_s, cout) = ripple_add(&a1_bits, &d_bits);
	write_bit(seg, c.fc, i, cout[W - 1])?;
	Ok(())
}

/// What to corrupt, so each guarantee has a test that fails without it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum BindTamper {
	/// Honest: leaf table carries exactly the constrained chain.
	None,
	/// NEGATIVE CONTROL — honest, but over the ALTERNATE chain (`salt = 7`) in BOTH tables. This
	/// must VALIDATE, which is what proves the alternate chain is itself a genuine gap-free cover.
	/// Without this control, [`BindTamper::SwapWholeChain`]'s rejection would be ambiguous: it
	/// could mean "the binding caught the substitution" or merely "that chain was malformed".
	NoneAlternateChain,
	/// The leaf set is a DIFFERENT but internally complete chain — the attack this module exists
	/// to stop. The tiling constraints still pass (that chain really is a gap-free cover); only
	/// the channel link can catch it.
	SwapWholeChain,
	/// One leaf row altered — the leaf set no longer matches the constrained rows.
	AlterOneLeaf,
	/// One chain record omitted from the leaf table (a duplicate padded in its place), i.e.
	/// censorship applied at the commitment rather than in the chain.
	OmitOneLeaf,
}

fn to_bits(x: &BigUint) -> Vec<bool> {
	(0..W as u64).map(|i| x.bit(i)).collect()
}

/// The 64-bit little-endian lanes of a width-W value, as the channel carries them.
fn lanes_of(x: &BigUint) -> Vec<u64> {
	let bits = to_bits(x);
	(0..LANES)
		.map(|l| {
			(0..64).fold(0u64, |acc, k| if bits[l * 64 + k] { acc | (1u64 << k) } else { acc })
		})
		.collect()
}

/// Build a synthetic closed cyclic sorted chain: `owner[i]` ascending, `next[i] = owner[(i+1) % n]`,
/// with exactly one wrap row. `salt` shifts the whole chain to a disjoint region of hash space so
/// two chains can be built that are each internally complete but different from one another.
fn synth_chain(n: usize, salt: u32) -> (Vec<BigUint>, Vec<BigUint>) {
	let step = BigUint::from(1u32) << (W - 16);
	let base = BigUint::from(0x51E3u32) + BigUint::from(salt) * (BigUint::from(1u32) << (W - 40));
	let owners: Vec<BigUint> = (0..n).map(|i| &base + BigUint::from(i as u32) * &step).collect();
	let nexts: Vec<BigUint> = (0..n).map(|i| owners[(i + 1) % n].clone()).collect();
	(owners, nexts)
}

/// W3 — what the VERIFIER pins from outside the proof.
///
/// A succinct hash root is NOT available here. Binding `nsec3_chain_root` would mean proving
/// `root == MerkleRoot(leaves)` in-circuit, i.e. `n-1` SHA-3 compressions over 64-byte inputs —
/// exactly the shape measured in commit b997882 at ~4.04 ms and ~121 KB peak RSS PER record, so
/// ~1.6 h and ~165 GB for a 1.4M chain. The same measurement that ruled out hash-based leaf
/// binding rules out an in-circuit hash root.
///
/// What IS available at ~zero circuit cost is to make the leaf set itself the public statement:
/// the leaf table pushes every leaf onto a channel that the verifier's boundaries pull. Channel
/// balance then forces `committed leaves == the leaf list the verifier holds`. The cost is O(n)
/// public data instead of a 32-byte root, so this is the AUDITABLE mode (an auditor who holds the
/// zone can check the chain against it), not the succinct mode a resolver wants. Succinct binding
/// needs the evaluation-claim fold of W4.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum RootBinding {
	/// No external pin: proves only "the leaves are SOME valid chain" (W2).
	None,
	/// The verifier pins the leaf set to the chain at `salt`, as O(n) boundary data.
	PinLeafSet { salt: u32 },
}

/// Compose the tiling table and the raw-leaf table in ONE constraint system and validate.
///
/// Returns `Ok(true)` iff the composed witness validates. The honest case must validate; every
/// [`BindTamper`] must not.
pub fn validate_bound_chain_pinned(
	n: usize,
	tamper: BindTamper,
	binding: RootBinding,
) -> Result<bool> {
	validate_bound_chain_inner(n, tamper, binding)
}

/// W2-only entry point: no external pin. Kept so the W2 gate reads unchanged.
pub fn validate_bound_chain(n: usize, tamper: BindTamper) -> Result<bool> {
	validate_bound_chain_inner(n, tamper, RootBinding::None)
}

/// Cost of a REAL proof over the composed system — not a model.
#[derive(Clone, Debug)]
pub struct BoundChainCost {
	pub prove_ms: u128,
	pub verify_ms: u128,
	pub proof_bytes: usize,
	pub peak_rss_bytes: u64,
	/// Boundary values the verifier must hold. 1 under [`RootBinding::None`]; grows with the
	/// chain under [`RootBinding::PinLeafSet`], which is the O(n)-public-data cost of W3.
	pub n_boundaries: usize,
	/// W4(b) probe — the first 32 transcript bytes, which `prove.rs` writes as the polynomial
	/// commitment (`writer.write(&commitment)` is the FIRST message written, before exp evals,
	/// non-zero products or flush products). If this is a stable, leaf-set-dependent value then a
	/// resolver could in principle pin it as a short root. THIS IS A PROBE, NOT A MECHANISM: the
	/// offset is an assumption about transcript layout, not a documented API, and nothing in
	/// `constraint_system::verify` checks it — see [`transcript_commitment_probe`].
	pub commitment_prefix: Vec<u8>,
	/// Full proof transcript, so [`read_proof_commitment`] can recover the commitment through the
	/// transcript API rather than the byte-offset assumption `commitment_prefix` encodes.
	pub transcript: Vec<u8>,
}

/// W4(a) — PROVE and VERIFY the composed system over the ACTUAL leaves.
///
/// This is what replaces `measure_epoch_verify_hash` for the chain: that function builds a
/// synthetic table of B256 multiplications, fills it with RANDOM field elements, and proves that
/// — it never sees a leaf, a root, or a chain, so its timings are a cost model rather than a
/// verification of anything. Here the witness IS the constrained chain and its committed leaves,
/// so the numbers describe the real artifact.
pub fn prove_bound_chain(n: usize, binding: RootBinding) -> Result<BoundChainCost> {
	prove_bound_chain_of(n, BindTamper::None, binding)
}

/// Prove a specific (honest) chain — `BindTamper::NoneAlternateChain` selects the alternate one,
/// so two different zones can be proved and their commitments compared.
pub fn prove_bound_chain_of(
	n: usize,
	tamper: BindTamper,
	binding: RootBinding,
) -> Result<BoundChainCost> {
	build_bound_chain(n, tamper, binding, true).map(|(_, c)| c.expect("prove requested"))
}

fn validate_bound_chain_inner(n: usize, tamper: BindTamper, binding: RootBinding) -> Result<bool> {
	build_bound_chain(n, tamper, binding, false).map(|(ok, _)| ok)
}

/// W5.2 — RESOLVER-SIDE verification against a pinned commitment.
///
/// Two checks, both performed by the verifier itself, which is what makes the composition sound:
///   1. the proof's polynomial commitment equals `expected_commitment` (the resolver's pin), and
///   2. the proof verifies against the constraint system.
///
/// The verifier rebuilds the constraint system from `(n, binding)` alone — it never sees a
/// witness, a leaf, or a chain — and reuses the SAME builder the prover used, so the two cannot
/// drift apart. Passing check 1 without check 2 would prove nothing about completeness; passing
/// check 2 without check 1 is exactly the prove-A-serve-B hole W2/W3 left open for a resolver.
///
/// ★ The pin is PER-CIRCUIT-VERSION: the commitment covers the whole witness, tiling columns
/// included, so any prover-side circuit revision changes it even for an unchanged zone. A
/// deployment must publish a circuit version alongside the pin (W5.4).
pub fn verify_bound_chain_against_pin(
	n: usize,
	binding: RootBinding,
	proof_transcript: &[u8],
	expected_commitment: &[u8],
) -> Result<bool> {
	build_bound_chain_inner(
		n,
		BindTamper::None,
		binding,
		false,
		Some((proof_transcript, expected_commitment)),
	)
	.map(|(ok, _)| ok)
}

fn build_bound_chain(
	n: usize,
	tamper: BindTamper,
	binding: RootBinding,
	do_prove: bool,
) -> Result<(bool, Option<BoundChainCost>)> {
	build_bound_chain_inner(n, tamper, binding, do_prove, None)
}

fn build_bound_chain_inner(
	n: usize,
	tamper: BindTamper,
	binding: RootBinding,
	do_prove: bool,
	verify_against: Option<(&[u8], &[u8])>,
) -> Result<(bool, Option<BoundChainCost>)> {
	assert!(n.is_power_of_two(), "n must be a power of two (selector-flushed wrap count)");
	assert!(n <= 1 << 15, "chain must fit W bits: n <= 2^15 for step = 2^(W-16)");

	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let hchan = cs.add_channel("nsec3_hashes");
	let wchan = cs.add_channel("nsec3_wrap_count");
	// THE BINDING CHANNEL: chain rows out of the tiling table, into the committed leaf set.
	let leafchan = cs.add_channel("nsec3_chain_leaves");
	// W3: carries every committed leaf out to the verifier's boundaries (declared here because
	// channels must be added before any table borrows the constraint system).
	let rootchan = cs.add_channel("nsec3_public_leaf_set");

	// The tiling table is built over the alternate chain ONLY for the negative control; every
	// other case constrains chain 0, so a rejection can be attributed to the leaf side alone.
	let tiling_salt = if tamper == BindTamper::NoneAlternateChain { ALT_SALT } else { 0 };
	let (owners, nexts) = synth_chain(n, tiling_salt);

	// ---- table A: the C1--C4 tiling AIR, plus a push of each row onto `leafchan` -------------
	let mut t = cs.add_table("NSEC3 tiling C1-C4 over B256");
	t.require_power_of_two_size();
	let tc = build_tiling_table::<W>(&mut t, hchan, wchan, Some(leafchan));
	let tiling_id = t.id();

	// ---- table B: the epoch's raw chain leaves, PULLED from the same channel -----------------
	// Each row is one raw 64-byte leaf. Because these columns are what the epoch commits (W4),
	// pulling them here is what makes "the committed leaves" and "the constrained chain" the
	// same object rather than two things that merely look alike.
	let mut lt = cs.add_table("NSEC3 raw chain leaves");
	let leaf_cols: Vec<Col<B64, 1>> =
		(0..LEAF_LANES).map(|i| lt.add_committed::<B64, 1>(format!("leaf{i}"))).collect();
	lt.pull(leafchan, leaf_cols.clone());
	// W3: re-export every committed leaf so the verifier's boundaries can pin the whole set.
	if binding != RootBinding::None {
		lt.push(rootchan, leaf_cols.clone());
	}
	let leaf_id = lt.id();

	let mut boundaries = vec![binius_m3::builder::Boundary {
		values: vec![OurB256::from(B64::new(1))],
		channel_id: wchan,
		direction: binius_m3::builder::FlushDirection::Pull,
		multiplicity: 1,
	}];
	// The verifier's own view of the zone, supplied from OUTSIDE the proof. If the committed
	// leaves are any other set — including a different but perfectly valid chain — the rootchan
	// cannot balance and the statement is rejected.
	if let RootBinding::PinLeafSet { salt } = binding {
		let (po, px) = synth_chain(n, salt);
		for i in 0..n {
			let mut values: Vec<OurB256> = Vec::with_capacity(LEAF_LANES);
			for l in lanes_of(&po[i]) {
				values.push(OurB256::from(B64::new(l)));
			}
			for l in lanes_of(&px[i]) {
				values.push(OurB256::from(B64::new(l)));
			}
			boundaries.push(binius_m3::builder::Boundary {
				values,
				channel_id: rootchan,
				direction: binius_m3::builder::FlushDirection::Pull,
				multiplicity: 1,
			});
		}
	}

	let statement = binius_m3::builder::Statement { boundaries, table_sizes: vec![n, n] };

	// W5.2 RESOLVER PATH — no witness is built at all: the verifier holds only the proof and its
	// pin. Both checks below are its own, so their conjunction is what the resolver relies on.
	if let Some((proof_transcript, expected_commitment)) = verify_against {
		let ccs = cs.compile(&statement)?;
		// (1) the pin: does this proof commit the zone the resolver asked about?
		let got = read_proof_commitment(proof_transcript, &statement.boundaries)?;
		if got != expected_commitment {
			return Ok((false, None));
		}
		// (2) the proof: is the committed data actually a gap-free cover, bound to those leaves?
		use crate::b256_field::{B256TowerFamily, U256};
		use binius_core::fiat_shamir::HasherChallenger;
		use binius_hash::sha2::Sha256Compression;
		use sha2::Sha256;
		let ok = binius_core::constraint_system::verify::<
			U256,
			B256TowerFamily,
			Sha256,
			Sha256Compression,
			HasherChallenger<Sha256>,
		>(
			&ccs,
			2,
			128,
			&statement.boundaries,
			binius_core::constraint_system::Proof { transcript: proof_transcript.to_vec() },
		)
		.is_ok();
		return Ok((ok, None));
	}

	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);

	// ---- fill table A (honest chain always: the tamper lives in the LEAF set) ----------------
	{
		let tw = witness.init_table(tiling_id, n)?;
		let mut seg = tw.full_segment();
		{
			let mut tv = seg.get_scalars_mut(tc.tok)?;
			for v in tv.iter_mut() {
				*v = B64::new(1);
			}
		}
		for i in 0..n {
			fill_tiling_row::<W>(&mut seg, &tc, i, &owners[i], &nexts[i], None)?;
		}
	}

	// ---- fill table B: the committed leaf set, corrupted per `tamper` ------------------------
	{
		// SwapWholeChain uses a DIFFERENT internally-complete chain: every tiling constraint
		// would still be satisfiable over it, so only the channel can reject this.
		let (lo_owners, lo_nexts) = match tamper {
			// SwapWholeChain: tiling constrains chain 0, leaves carry the alternate chain.
			// NoneAlternateChain: BOTH are the alternate chain, so this must validate.
			BindTamper::SwapWholeChain | BindTamper::NoneAlternateChain => synth_chain(n, ALT_SALT),
			_ => (owners.clone(), nexts.clone()),
		};
		let tw = witness.init_table(leaf_id, n)?;
		let mut seg: TableWitnessSegment<OurB256> = tw.full_segment();
		let mut cols: Vec<_> = Vec::with_capacity(LEAF_LANES);
		for c in &leaf_cols {
			cols.push(seg.get_scalars_mut(*c)?);
		}
		for i in 0..n {
			// OmitOneLeaf: row `n/2` repeats row 0, so one record never appears in the leaf set.
			let src = if tamper == BindTamper::OmitOneLeaf && i == n / 2 { 0 } else { i };
			let o_lanes = lanes_of(&lo_owners[src]);
			let x_lanes = lanes_of(&lo_nexts[src]);
			for l in 0..LANES {
				cols[l][i] = B64::new(o_lanes[l]);
				cols[LANES + l][i] = B64::new(x_lanes[l]);
			}
			if tamper == BindTamper::AlterOneLeaf && i == n / 3 {
				// flip one lane so this leaf is no longer any constrained row
				cols[0][i] = B64::new(o_lanes[0] ^ 1);
			}
		}
	}

	let n_boundaries = statement.boundaries.len();
	let ccs = cs.compile(&statement)?;
	let witness = witness.into_multilinear_extension_index();
	let ok = binius_core::constraint_system::validate::validate_witness(
		&ccs,
		&statement.boundaries,
		&witness,
	)
	.is_ok();
	if !ok || !do_prove {
		return Ok((ok, None));
	}

	use crate::b256_field::{B256TowerFamily, U256};
	use binius_core::fiat_shamir::HasherChallenger;
	use binius_hash::sha2::Sha256Compression;
	use sha2::Sha256;
	// rate 2^-2: measured in 7e7c3ce as the knee — 28% smaller proof and ~9% lower peak RSS than
	// 2^-1 for ~9% more prove time, at the SAME 128-bit soundness target.
	const LOG_INV_RATE: usize = 2;
	const SECURITY_BITS: usize = 128;
	let t0 = std::time::Instant::now();
	let proof = binius_core::constraint_system::prove::<
		U256,
		B256TowerFamily,
		Sha256,
		Sha256Compression,
		HasherChallenger<Sha256>,
		_,
	>(
		&ccs,
		LOG_INV_RATE,
		SECURITY_BITS,
		&statement.boundaries,
		witness,
		&binius_hal::make_portable_backend(),
	)?;
	let prove_ms = t0.elapsed().as_millis();
	let proof_bytes = proof.get_proof_size();
	// W4(b) probe: prove.rs writes the polynomial commitment as the FIRST transcript message.
	let commitment_prefix: Vec<u8> = proof.transcript.iter().copied().take(32).collect();
	let transcript_bytes = proof.transcript.clone();
	let peak_rss_bytes = crate::b256_sha3::peak_rss_bytes();
	let t1 = std::time::Instant::now();
	binius_core::constraint_system::verify::<
		U256,
		B256TowerFamily,
		Sha256,
		Sha256Compression,
		HasherChallenger<Sha256>,
	>(&ccs, LOG_INV_RATE, SECURITY_BITS, &statement.boundaries, proof)?;
	let verify_ms = t1.elapsed().as_millis();

	Ok((
		true,
		Some(BoundChainCost {
			prove_ms,
			verify_ms,
			proof_bytes,
			peak_rss_bytes,
			n_boundaries,
			commitment_prefix,
			transcript: transcript_bytes,
		}),
	))
}

// =====================================================================================
// W4(b) option 3 — the SUCCINCT pin, carried as an evaluation claim through the fold.
// =====================================================================================

/// The leaf set as a multilinear polynomial over `BinaryField128b` — the SAME bytes the leaf
/// table commits (`LEAF_LANES` u64 lanes per leaf, packed two lanes to a 128-bit element), so a
/// claim about this polynomial is a claim about the committed leaves.
pub fn leaf_polynomial(n: usize, salt: u32) -> Vec<AccF> {
	use binius_field::BinaryField128b;
	let (owners, nexts) = synth_chain(n, salt);
	let pack = |a: u64, b: u64| BinaryField128b::new(((b as u128) << 64) | a as u128);
	let mut out = Vec::with_capacity(2 * LANES * n);
	for i in 0..n {
		let ol = lanes_of(&owners[i]);
		let xl = lanes_of(&nexts[i]);
		for l in (0..LANES).step_by(2) {
			out.push(pack(ol[l], ol[l + 1]));
		}
		for l in (0..LANES).step_by(2) {
			out.push(pack(xl[l], xl[l + 1]));
		}
	}
	let padded = out.len().next_power_of_two();
	out.resize(padded, <AccF as binius_field::Field>::ZERO);
	out
}

/// Derive the evaluation point the way Fiat–Shamir must: from a digest of the committed data.
///
/// ★★ THIS HELPER IS NOT SOUND AS A PROTOCOL, and the gap is specific, not hypothetical.
///
/// The point here is `H(leaves)`, so a prover can DERIVE the resolver's point before choosing what
/// to serve. `fold_verify` checks a single field equation, `g(0) == pinned_value`. A prover wanting
/// to serve chain B against a pin for chain A needs only `mle_eval(B, point_A) == value_A` — one
/// equation, with the whole of B free to vary, so it can be ground out. The wrong-zone rejection
/// demonstrated by [`fold_verifies_against_pin`] shows the MECHANISM works against an honest-ish
/// prover; it does NOT show the pin is binding against a grinding adversary.
///
/// The fix is structural, not a parameter change. In a real accumulation protocol the resolver
/// holds a short COMMITMENT, not a precomputed `(point, value)`; the point is derived by the
/// transcript challenger AFTER the prover commits, so it cannot be anticipated, and the PCS proves
/// the committed polynomial's evaluation there. That requires wiring this into binius's PIOP —
/// `accumulation.rs` is explicitly a native model with no circuit — which is NOT done here.
pub fn fs_point(poly: &[AccF], n_vars: usize) -> Vec<AccF> {
	use binius_field::BinaryField128b;
	use sha3::{Digest, Sha3_256};
	let mut h = Sha3_256::new();
	h.update(b"NSEC3-LEAFSET-EVAL-POINT-V1");
	for e in poly {
		h.update(binius_field::underlier::WithUnderlier::to_underlier(*e).to_le_bytes());
	}
	let seed: [u8; 32] = h.finalize().into();
	(0..n_vars)
		.map(|j| {
			let mut hj = Sha3_256::new();
			hj.update(seed);
			hj.update((j as u64).to_le_bytes());
			let d: [u8; 32] = hj.finalize().into();
			BinaryField128b::new(u128::from_le_bytes(d[0..16].try_into().unwrap()))
		})
		.collect()
}

/// The resolver's SHORT PIN for a zone: `log2(leafset size) + 1` field elements, versus the
/// O(n) leaf list that [`RootBinding::PinLeafSet`] requires.
pub fn zone_pin(n: usize, salt: u32) -> crate::accumulation::EvalClaim {
	use crate::accumulation::{mle_eval, EvalClaim};
	let poly = leaf_polynomial(n, salt);
	let n_vars = poly.len().trailing_zeros() as usize;
	let point = fs_point(&poly, n_vars);
	let value = mle_eval(&poly, &point);
	EvalClaim { point, value }
}

/// W4(b) — fold the chain's leaf-set record into an epoch alongside other records, and have a
/// verifier that holds ONLY short claims replay the fold.
///
/// `served_salt` is the chain the operator actually commits and folds; `pinned_salt` is the zone
/// the resolver holds a pin for. When they differ this is prove-A-serve-B, and it must be
/// rejected even though the served chain is itself a perfectly valid gap-free cover.
///
/// Returns `true` iff the verifier accepts.
pub fn fold_verifies_against_pin(n: usize, served_salt: u32, pinned_salt: u32) -> bool {
	use crate::accumulation::{accumulate, accumulate_verify, lifted_claim, mle_eval, Record};
	use binius_field::{BinaryField128b, Field};

	// The operator's real leaf set, and three companion epoch records standing in for the rest
	// of the epoch (positive delegations etc.) — 4 records so the fold chain is non-trivial.
	let served = leaf_polynomial(n, served_salt);
	let n_vars = served.len().trailing_zeros() as usize;
	// One shared inner point, as `accumulate` requires. Derived from the SERVED data: a prover
	// cannot gain by shifting it, because the resolver's pinned value was computed at the point
	// derived from ITS zone, and a mismatch in either the point or the value fails the fold.
	let point = fs_point(&served, n_vars);

	let mut records: Vec<Record> = Vec::with_capacity(4);
	records.push(Record {
		claim: crate::accumulation::EvalClaim { point: point.clone(), value: mle_eval(&served, &point) },
		evals: served.clone(),
	});
	for k in 1..4u64 {
		let filler: Vec<AccF> = (0..served.len())
			.map(|i| BinaryField128b::new(((k as u128) << 96) ^ (i as u128).wrapping_mul(0x9E37)))
			.collect();
		records.push(Record {
			claim: crate::accumulation::EvalClaim { point: point.clone(), value: mle_eval(&filler, &point) },
			evals: filler,
		});
	}

	let challenges: Vec<AccF> = (0..records.len() - 1)
		.map(|k| BinaryField128b::new(0xA5A5_0000_0000_0001u128 + k as u128))
		.collect();
	let (_interleaved, _acc, proofs) = accumulate(&records, &challenges);

	// The VERIFIER holds only claims — never the leaves. For record 0 it substitutes the claim
	// for the zone it actually cares about; the rest it takes from the epoch package.
	let m = records.len().trailing_zeros() as usize;
	let pin = zone_pin(n, pinned_salt);
	let mut verifier_claims: Vec<crate::accumulation::EvalClaim> =
		records.iter().enumerate().map(|(i, r)| lifted_claim(r, i, m)).collect();
	verifier_claims[0] = {
		// lift the pin to record index 0: append m zero bits, exactly as `lifted_claim` does.
		let mut c = pin.clone();
		c.point.extend(std::iter::repeat(AccF::ZERO).take(m));
		c
	};

	accumulate_verify(&verifier_claims, &proofs, &challenges).is_some()
}

/// W5.1 — read the polynomial commitment out of a proof through the PROPER transcript API.
///
/// `constraint_system::verify` does exactly this (`verify.rs`: `observe().write_slice(boundaries)`
/// then `reader.read::<Output<Hash>>()`), and `piop::verify` takes the commitment as an explicit
/// parameter — so the commitment is a first-class value, not something that must be recovered by
/// guessing a byte offset. If this works, a resolver can check "commitment == my pinned value AND
/// the proof verifies", which is a sound composition of two checks it performs itself.
///
/// `proof_transcript` is `Proof::transcript`; `boundaries` must be the SAME boundaries the proof
/// was produced against, because they are observed into the challenger before the first message.
pub fn read_proof_commitment(
	proof_transcript: &[u8],
	boundaries: &[binius_m3::builder::Boundary<OurB256>],
) -> Result<Vec<u8>> {
	use binius_core::fiat_shamir::HasherChallenger;
	use binius_core::transcript::VerifierTranscript;
	use sha2::Sha256;

	let mut transcript =
		VerifierTranscript::<HasherChallenger<Sha256>>::new(proof_transcript.to_vec());
	transcript.observe().write_slice(boundaries);
	let mut reader = transcript.message();
	let commitment = reader
		.read::<sha2::digest::Output<Sha256>>()
		.map_err(|e| anyhow::anyhow!("could not read commitment from transcript: {e}"))?;
	Ok(commitment.to_vec())
}

#[cfg(test)]
mod tests {
	use super::*;

	/// W2 GATE — the committed leaf set is provably the chain the tiling AIR constrained.
	///
	/// `swap_whole_chain` is the load-bearing case: it is the attack the binding exists to stop,
	/// and it is the one that an unbound tiling proof cannot detect, because the substituted
	/// chain is itself a genuine gap-free cover.
	#[test]
	fn nsec3_leaves_bound_to_constrained_chain() {
		const N: usize = 8;
		assert!(
			validate_bound_chain(N, BindTamper::None).expect("honest"),
			"honest: leaf set == constrained chain must VALIDATE"
		);
		// NEGATIVE CONTROL FIRST: the alternate chain is itself a genuine gap-free cover, so
		// constraining AND committing it validates. This is what gives the swap case below its
		// meaning — the rejection there cannot be blamed on a malformed chain.
		assert!(
			validate_bound_chain(N, BindTamper::NoneAlternateChain).expect("alt honest"),
			"control: the ALTERNATE chain must itself VALIDATE when both tables use it — \
			 otherwise the swap rejection below proves nothing about the binding"
		);
		assert!(
			!validate_bound_chain(N, BindTamper::SwapWholeChain).expect("swap"),
			"★ a DIFFERENT but internally-complete chain in the leaf set must be REJECTED — this \
			 is the prove-A-serve-B attack, invisible to an unbound tiling proof. Paired with the \
			 control above, the ONLY difference between validate and reject is the binding."
		);
		assert!(
			!validate_bound_chain(N, BindTamper::AlterOneLeaf).expect("alter"),
			"an altered leaf must be REJECTED"
		);
		assert!(
			!validate_bound_chain(N, BindTamper::OmitOneLeaf).expect("omit"),
			"omitting a record from the leaf set must be REJECTED"
		);
		println!(
			"W2 GATE nsec3-leaf-binding: N={N} raw (owner,next) leaves PULLED from the same \
			 channel the C1--C4 tiling table PUSHES ⇒ multiset(committed leaves) == \
			 multiset(constrained chain), in ONE constraint system. Whole-chain swap, altered \
			 leaf, and omitted leaf are each REJECTED. No in-circuit hashing (raw leaves). \
			 NOT YET load-bearing end to end: chain root is not a public boundary (W3) and epoch \
			 aggregation is still modelled (W4)."
		);
	}

	/// W3 GATE — the verifier pins the leaf set from OUTSIDE the proof.
	///
	/// W2 alone proves "the leaves are SOME valid chain". That is not enough: an operator can
	/// prove a genuinely complete chain A while serving zone B. The `honest_proof_wrong_zone`
	/// case below is exactly that attack — every constraint inside the proof is satisfied, the
	/// chain really is a gap-free cover, and it is still REJECTED because it is not the zone the
	/// verifier asked about. That case is what makes completeness load-bearing rather than
	/// unfalsifiable evidence about an unspecified chain.
	#[test]
	fn nsec3_leaf_set_pinned_by_verifier() {
		const N: usize = 8;
		let pin0 = RootBinding::PinLeafSet { salt: 0 };

		assert!(
			validate_bound_chain_pinned(N, BindTamper::None, pin0).expect("honest pinned"),
			"honest: committed leaves == the verifier's leaf set must VALIDATE"
		);

		// ★ THE W3 CASE. Internally flawless proof over the ALTERNATE chain — it validates
		// unpinned (the W2 control proves it is a real gap-free cover) — but the verifier is
		// asking about chain 0. Rejected on the binding alone.
		assert!(
			validate_bound_chain(N, BindTamper::NoneAlternateChain).expect("alt unpinned"),
			"control: the alternate chain validates when NOT pinned"
		);
		assert!(
			!validate_bound_chain_pinned(N, BindTamper::NoneAlternateChain, pin0)
				.expect("alt pinned"),
			"★ a COMPLETE, internally-valid chain for the WRONG ZONE must be REJECTED once the \
			 verifier pins its own leaf set — this is prove-A-serve-B, and W2 alone cannot catch it"
		);

		// And pinning to the alternate chain accepts it again: the pin is what selects the zone.
		assert!(
			validate_bound_chain_pinned(N, BindTamper::NoneAlternateChain, RootBinding::PinLeafSet {
				salt: ALT_SALT
			})
			.expect("alt pinned to itself"),
			"pinning to the alternate chain must ACCEPT it — the pin selects the zone, nothing else"
		);

		println!(
			"W3 GATE nsec3-leaf-set-pin: N={N} the verifier pins the leaf set from outside the \
			 proof via {LEAF_LANES}-lane channel boundaries. A complete chain for the WRONG zone \
			 is REJECTED; the same chain pinned to itself is ACCEPTED. \
			 ★ LIMITATION: this pins O(n) public leaf data, NOT a 32-byte root — an in-circuit \
			 Merkle root would cost n-1 SHA-3 compressions (~4.04 ms and ~121 KB RSS per record, \
			 ~165 GB at 1.4M records), so it is infeasible by the same measurement that ruled out \
			 hash leaf-binding. This is the AUDITABLE mode (an auditor holding the zone can check \
			 it); SUCCINCT binding for a resolver needs the evaluation-claim fold of W4."
		);
	}

	/// W4(a) — REAL prove+verify over the actual leaves, replacing the modelled epoch numbers.
	///
	/// `measure_epoch_verify_hash` proves a synthetic table of B256 multiplications filled with
	/// RANDOM field elements: it never sees a leaf, a root, or a chain, so its timings model a
	/// cost rather than verify anything. These numbers are over the real constrained chain and
	/// its committed leaves, in both binding modes, so the O(n)-public-data cost of W3 is visible.
	/// Run: `cargo test --release --lib bound_chain_real_cost -- --ignored --nocapture`
	#[test]
	#[ignore = "real prove+verify of the composed system: ~1-3 min"]
	fn bound_chain_real_cost() {
		let threads = std::env::var("RAYON_NUM_THREADS").unwrap_or_else(|_| "unset (all cores)".into());
		println!(
			"\n  REAL PROVE of the BOUND chain (tiling ⊗ leaves), B256@L1(128), rate 2^-2, \
			 threads={threads}"
		);
		println!("    n     mode        prove ms   verify ms   proof KiB   RSS MiB   boundaries");
		for &n in &[64usize, 512, 4096] {
			for (label, binding) in
				[("unpinned", RootBinding::None), ("pinned  ", RootBinding::PinLeafSet { salt: 0 })]
			{
				let c = prove_bound_chain(n, binding).expect("real prove");
				println!(
					"  {n:>5}   {label}   {:>8}   {:>9}   {:>9.0}   {:>7.0}   {:>10}",
					c.prove_ms,
					c.verify_ms,
					c.proof_bytes as f64 / 1024.0,
					c.peak_rss_bytes as f64 / (1024.0 * 1024.0),
					c.n_boundaries,
				);
			}
		}
		println!(
			"  The `pinned` rows carry n+1 boundaries — the verifier holds the whole leaf set. \
			 That is the AUDITABLE mode. A resolver wanting a SHORT pin is still unserved: a hash \
			 root would need n-1 in-circuit SHA-3 compressions (~165 GB at 1.4M records, b997882).\n"
		);
	}

	/// W4(b) OPTION-1 PROBE — is the transcript's leading commitment usable as a resolver's short
	/// pin? Checks the three properties that would have to hold before option 3 (the fold) is
	/// worth building, and records exactly which of them the probe can and cannot establish.
	///
	/// This does NOT implement succinct binding. `constraint_system::verify` never checks this
	/// value, so anything here is an out-of-band comparison layered on top of verification, and
	/// the 32-byte offset is an assumption about transcript layout rather than a documented API.
	#[test]
	fn transcript_commitment_probe() {
		const N: usize = 64;
		let hex = |b: &[u8]| b.iter().map(|x| format!("{x:02x}")).collect::<String>();

		let a1 = prove_bound_chain_of(N, BindTamper::None, RootBinding::None).expect("a1");
		let a2 = prove_bound_chain_of(N, BindTamper::None, RootBinding::None).expect("a2");
		let b1 = prove_bound_chain_of(N, BindTamper::NoneAlternateChain, RootBinding::None)
			.expect("b1");
		let a_pinned =
			prove_bound_chain_of(N, BindTamper::None, RootBinding::PinLeafSet { salt: 0 })
				.expect("a_pinned");

		println!("\n  W4(b) OPTION-1 PROBE — transcript[0..32] as a candidate short pin (n={N})");
		println!("    chain A, run 1        {}", hex(&a1.commitment_prefix));
		println!("    chain A, run 2        {}", hex(&a2.commitment_prefix));
		println!("    chain B (alternate)   {}", hex(&b1.commitment_prefix));
		println!("    chain A, pinned mode  {}", hex(&a_pinned.commitment_prefix));

		// (P1) DETERMINISTIC: same zone, same commitment. Without this a resolver could never
		// hold a stable pin at all.
		let deterministic = a1.commitment_prefix == a2.commitment_prefix;
		// (P2) ZONE-SEPARATING: a different zone gives a different commitment. Without this the
		// pin cannot distinguish the zone it is supposed to identify.
		let separating = a1.commitment_prefix != b1.commitment_prefix;
		// (P3) BINDING-MODE-INVARIANT: the commitment covers the witness, which is identical in
		// both modes, so pinning should not disturb it. If this fails the value depends on the
		// statement as well as the data, and is not a property of the zone.
		let mode_invariant = a1.commitment_prefix == a_pinned.commitment_prefix;

		println!(
			"    P1 deterministic (A run1 == A run2)      : {deterministic}\n\
			 \x20   P2 zone-separating (A != B)              : {separating}\n\
			 \x20   P3 mode-invariant (unpinned == pinned)   : {mode_invariant}"
		);

		assert!(deterministic, "P1: the same zone must yield the same commitment");
		assert!(separating, "P2: a different zone must yield a different commitment");

		println!(
			"  VERDICT: P1 and P2 hold, so a leading-32-byte commitment IS a stable, \
			 zone-separating value — the shape a short pin needs. What the probe CANNOT establish, \
			 and what keeps this from being a mechanism:\n\
			 \x20   (a) constraint_system::verify NEVER checks it. Comparing it is an out-of-band \
			 step bolted onto verification, so soundness would rest on that comparison rather than \
			 on the verifier.\n\
			 \x20   (b) the 32-byte offset is inferred from prove.rs writing the commitment as its \
			 first message; it is not a documented API and would break silently on a binius change \
			 or a different hash/compression choice.\n\
			 \x20   (c) it commits the WHOLE witness, not the leaf set — every tiling column too — \
			 so it changes whenever the circuit changes, even for an identical zone. A resolver's \
			 pin would be invalidated by a prover-side circuit revision.\n\
			 \x20  So option 1 CONFIRMS the approach is viable in principle and is NOT a shippable \
			 mechanism. Option 3 (evaluation-claim fold) is the one that puts the pin inside what \
			 the verifier checks and scopes it to the leaves."
		);
	}

	/// W4(b) OPTION 3 — the SUCCINCT pin. A resolver holding only an evaluation claim, never the
	/// leaf list, rejects a complete chain served for the wrong zone.
	///
	/// This is the resolver-facing half that W2+W3 could not deliver: W3 works but costs O(n)
	/// public leaf data, so it serves an auditor rather than a resolver.
	#[test]
	fn succinct_pin_rejects_wrong_zone() {
		for &n in &[8usize, 64, 256] {
			assert!(
				fold_verifies_against_pin(n, 0, 0),
				"n={n}: serving the pinned zone must VERIFY"
			);
			assert!(
				!fold_verifies_against_pin(n, ALT_SALT, 0),
				"★ n={n}: serving a DIFFERENT (but perfectly valid, gap-free) chain while the \
				 resolver pins zone 0 must be REJECTED — caught at the fold, with the verifier \
				 holding only a short claim"
			);
			assert!(
				fold_verifies_against_pin(n, ALT_SALT, ALT_SALT),
				"n={n}: pinning the alternate zone accepts it — the pin selects the zone"
			);
		}

		// The whole point: how short IS the pin, against the O(n) leaf list W3 needs?
		let n = 256usize;
		let pin = zone_pin(n, 0);
		let pin_elems = pin.point.len() + 1;
		let pin_bytes = pin_elems * 16;
		let w3_bytes = n * LEAF_LANES * 8;
		println!(
			"\n  W4(b) OPTION-3 GATE succinct-pin: a resolver holding ONE EvalClaim rejects a \
			 valid chain served for the wrong zone, at every n tested.\n\
			 \x20   pin size  @ n={n}: {pin_elems} field elements = {pin_bytes} B \
			 (log2(leafset)+1)\n\
			 \x20   W3 O(n)   @ n={n}: {w3_bytes} B of leaf data — {:.0}x larger\n\
			 \x20   At a 1.4M-record chain the pin is ~{} B while the leaf list is ~{} MB.\n\
			 \x20   ★★ WHAT THIS DOES AND DOES NOT SHOW. It shows the fold MECHANISM carries a \
			 zone pin: a verifier holding one short claim, never the leaves, rejects a valid chain \
			 served for another zone. It does NOT show the pin is BINDING against a grinding \
			 adversary. fs_point derives the point as H(leaves), so a prover can compute the \
			 resolver's point before choosing what to serve, and fold_verify checks a single field \
			 equation g(0)==pinned_value — one equation with all of chain B free to vary, so it can \
			 be ground out. The fix is structural: the resolver must hold a COMMITMENT, with the \
			 point derived by the transcript challenger AFTER the prover commits. That needs \
			 binius PIOP integration; accumulation.rs is a native model with no circuit.",
			w3_bytes as f64 / pin_bytes as f64,
			(1_400_000f64 * 4.0).log2().ceil() as usize * 16 + 16,
			(1_400_000usize * LEAF_LANES * 8) / 1_000_000,
		);
	}

	/// W5.1 EXPERIMENT — can the commitment be recovered through the transcript API?
	///
	/// The whole W5 scope rests on this. If it works, a resolver can perform two checks it owns —
	/// "the commitment equals my pinned value" AND "the proof verifies" — which is a sound
	/// composition, and no byte-offset assumption or vendored verifier is needed.
	#[test]
	fn w5_1_read_commitment_via_transcript() {
		use binius_m3::builder::{Boundary, FlushDirection};
		const N: usize = 64;
		let hex = |b: &[u8]| b.iter().map(|x| format!("{x:02x}")).collect::<String>();

		// Unpinned proofs, so the boundary set is the single wrap-count boundary and can be
		// reconstructed here exactly as `build_bound_chain` builds it.
		let a = prove_bound_chain_of(N, BindTamper::None, RootBinding::None).expect("a");
		let b = prove_bound_chain_of(N, BindTamper::NoneAlternateChain, RootBinding::None)
			.expect("b");
		let rebuild_boundaries = || {
			// channel_id 1 == wchan: channels are added in order hchan(0), wchan(1), leafchan(2).
			vec![Boundary::<OurB256> {
				values: vec![OurB256::from(B64::new(1))],
				channel_id: 1,
				direction: FlushDirection::Pull,
				multiplicity: 1,
			}]
		};

		let ca = read_proof_commitment(&a.transcript, &rebuild_boundaries())
			.expect("commitment must be readable through the transcript API");
		let cb = read_proof_commitment(&b.transcript, &rebuild_boundaries()).expect("b commitment");

		println!("\n  W5.1 — commitment via VerifierTranscript (n={N})");
		println!("    chain A  transcript-API  {}", hex(&ca));
		println!("    chain A  byte-offset     {}", hex(&a.commitment_prefix));
		println!("    chain B  transcript-API  {}", hex(&cb));

		// (1) The API read agrees with the byte-offset probe, confirming BOTH readings and
		// retiring the offset assumption in favour of the supported path.
		assert_eq!(
			ca,
			a.commitment_prefix,
			"transcript-API read must agree with the leading 32 bytes"
		);
		// (2) Still zone-separating, which is what makes it usable as a pin.
		assert_ne!(ca, cb, "different zones must give different commitments");

		println!(
			"    ✓ transcript-API read == byte-offset read, and zones still separate.\n\
			 \x20   ⇒ W5.2 is a pure composition: check commitment == pinned, then call the stock \
			 constraint_system::verify. No vendored verifier, no offset assumption.\n\
			 \x20   REMAINING COUPLING (W5.4): the commitment covers the WHOLE witness, tiling \
			 columns included, so a prover-side circuit revision invalidates a resolver's pin even \
			 for an unchanged zone. The pin is per-circuit-version and must be published with one."
		);
	}

	/// W5.3 GATE — the RESOLVER-facing property, for real.
	///
	/// A resolver holding a 32-byte pin and nothing else accepts its own zone's proof and rejects
	/// a proof of a different, perfectly valid, gap-free chain. This is the case W2 and W3 could
	/// not serve: W2 proves "some valid chain", W3 pins the zone but costs O(n) leaf data.
	///
	/// The three assertions are deliberately paired so neither check can be silently doing all the
	/// work: the wrong-zone proof VERIFIES on its own terms (it is a real proof of a real chain)
	/// and is rejected only by the pin; the honest proof is rejected once the pin is corrupted.
	#[test]
	fn w5_3_resolver_verifies_against_pin() {
		const N: usize = 64;
		let binding = RootBinding::None; // resolver holds ONLY the 32-byte pin, no leaf data

		let mine = prove_bound_chain_of(N, BindTamper::None, binding).expect("my zone");
		let other =
			prove_bound_chain_of(N, BindTamper::NoneAlternateChain, binding).expect("other zone");
		let my_pin = mine.commitment_prefix.clone();

		// (1) my zone's proof, against my pin → ACCEPT
		assert!(
			verify_bound_chain_against_pin(N, binding, &mine.transcript, &my_pin)
				.expect("verify mine"),
			"a resolver must accept its own zone's proof against its pin"
		);

		// (2) ★ a DIFFERENT zone's proof, against my pin → REJECT.
		//     The proof itself is perfectly valid — assertion (3) below confirms it verifies
		//     against its OWN pin — so the rejection is the pin doing the work, not a bad proof.
		assert!(
			!verify_bound_chain_against_pin(N, binding, &other.transcript, &my_pin)
				.expect("verify other"),
			"★ prove-A-serve-B: a valid gap-free chain for ANOTHER zone must be REJECTED against \
			 my pin — this is the resolver-facing property W2/W3 could not deliver"
		);

		// (3) control: that same proof IS valid against its own pin, so (2) rejected on identity
		//     rather than on validity.
		assert!(
			verify_bound_chain_against_pin(N, binding, &other.transcript, &other.commitment_prefix)
				.expect("verify other vs own pin"),
			"control: the other zone's proof must verify against ITS OWN pin — otherwise (2) \
			 proves nothing about the pin"
		);

		// (4) control the other way: a corrupted pin rejects an otherwise-good proof, so the
		//     commitment check is actually consulted rather than incidental.
		let mut bad_pin = my_pin.clone();
		bad_pin[0] ^= 0x01;
		assert!(
			!verify_bound_chain_against_pin(N, binding, &mine.transcript, &bad_pin)
				.expect("verify vs bad pin"),
			"a corrupted pin must reject an otherwise-valid proof"
		);

		println!(
			"\n  W5.3 GATE resolver-pin: a resolver holding a {}-byte pin and NO leaf data\n\
			 \x20   accepts its own zone's proof, REJECTS a valid gap-free chain proved for another\n\
			 \x20   zone, and rejects its own zone under a corrupted pin. Both controls hold, so\n\
			 \x20   neither the pin check nor the proof check is carrying the result alone.\n\
			 \x20   Verification is a composition of two checks the RESOLVER performs: commitment\n\
			 \x20   == pin, then the stock constraint_system::verify. No witness, no leaf list, no\n\
			 \x20   vendored verifier.\n\
			 \x20   ★ CAVEAT (W5.4): the pin covers the WHOLE witness including tiling columns, so\n\
			 \x20   a prover-side circuit revision invalidates it even for an unchanged zone. The\n\
			 \x20   pin is per-circuit-version and must be published with a version.",
			my_pin.len()
		);
	}

	/// The binding must hold as the chain grows, not just at the toy size.
	#[test]
	fn nsec3_leaf_binding_scales() {
		for n in [16usize, 64, 256] {
			assert!(validate_bound_chain(n, BindTamper::None).expect("honest"), "honest at n={n}");
			assert!(
				!validate_bound_chain(n, BindTamper::SwapWholeChain).expect("swap"),
				"chain swap must be rejected at n={n}"
			);
		}
	}
}

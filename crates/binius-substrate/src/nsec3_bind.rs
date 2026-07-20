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
//! **W4 (not done)** — epoch aggregation is still the random-witness cost model
//! (`measure_epoch_verify_hash`), which binds none of this, and it is also where succinct binding
//! must come from: an evaluation-claim fold gives the resolver a short pin where a hash root
//! cannot. Until W4 lands, chain completeness is load-bearing for an AUDITOR but not for a
//! resolver holding only a short commitment.
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

fn build_bound_chain(
	n: usize,
	tamper: BindTamper,
	binding: RootBinding,
	do_prove: bool,
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
	let one_w: [B1; W] = std::array::from_fn(|i| if i == 0 { B1::ONE } else { B1::ZERO });
	let one_col = t.add_constant("one", one_w);
	let tok = t.add_committed::<B64, 1>("tok");
	let owner = t.add_committed::<B1, W>("owner");
	let next = t.add_committed::<B1, W>("next");
	let wrap = t.add_committed::<B1, 1>("wrap");
	let bc = t.add_committed::<B1, W>("bc");
	let bcr = t.add_shifted("bcr", bc, W.trailing_zeros() as usize, 1, ShiftVariant::CircularLeft);
	t.assert_zero("bc_eq", bc - bcr);
	let bc0 = t.add_selected("bc0", bc, 0);
	t.assert_zero("bc_bind", bc0 - wrap);
	let diff = t.add_committed::<B1, W>("diff");
	t.assert_zero("diff_def", diff - (owner + next));
	let masked = t.add_committed::<B1, W>("masked");
	t.assert_zero("masked_def", masked - bc * diff);
	let lo = t.add_committed::<B1, W>("lo");
	t.assert_zero("lo_def", lo - (owner + masked));
	let hi = t.add_committed::<B1, W>("hi");
	t.assert_zero("hi_def", hi - (next + masked));
	let a1 = Adder::<W>::build(&mut t, lo, one_col, "a1");
	let dcol = t.add_committed::<B1, W>("d");
	let s2 = Adder::<W>::build(&mut t, a1.sum, dcol, "s2");
	t.assert_zero("lt_eq", s2.sum - hi);
	let fc = t.add_selected("fc", s2.cout, W - 1);
	t.assert_zero("lt_no_ovf", fc * B1::ONE);

	let owner_sel: Vec<Col<B1, 64>> =
		(0..LANES).map(|i| t.add_selected_block::<B1, W, 64>(format!("o_sel{i}"), owner, i)).collect();
	let owner_b64: Vec<Col<B64, 1>> =
		(0..LANES).map(|i| t.add_packed::<B1, 64, B64, 1>(format!("o_b64{i}"), owner_sel[i])).collect();
	t.push(hchan, owner_b64.clone());
	let next_sel: Vec<Col<B1, 64>> =
		(0..LANES).map(|i| t.add_selected_block::<B1, W, 64>(format!("n_sel{i}"), next, i)).collect();
	let next_b64: Vec<Col<B64, 1>> =
		(0..LANES).map(|i| t.add_packed::<B1, 64, B64, 1>(format!("n_b64{i}"), next_sel[i])).collect();
	t.pull(hchan, next_b64.clone());
	t.push_with_opts(wchan, [tok], FlushOpts { multiplicity: 1, selector: Some(wrap) });

	// the binding push: the WHOLE row (owner ‖ next) as one 8-lane flush.
	let leaf_out: Vec<Col<B64, 1>> =
		owner_b64.iter().chain(next_b64.iter()).copied().collect();
	t.push(leafchan, leaf_out);
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

	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);

	// ---- fill table A (honest chain always: the tamper lives in the LEAF set) ----------------
	{
		let tw = witness.init_table(tiling_id, n)?;
		let mut seg = tw.full_segment();
		{
			let mut tc = seg.get_scalars_mut(tok)?;
			for v in tc.iter_mut() {
				*v = B64::new(1);
			}
		}
		let one_bits = to_bits(&BigUint::from(1u32));
		let modw = BigUint::from(1u32) << W;
		for i in 0..n {
			let (o, x) = (owners[i].clone(), nexts[i].clone());
			let obits = to_bits(&o);
			let xbits = to_bits(&x);
			write_col::<W>(&mut seg, owner, i, &obits)?;
			write_col::<W>(&mut seg, next, i, &xbits)?;
			write_col::<W>(&mut seg, one_col, i, &one_bits)?;
			for l in 0..LANES {
				write_col::<64>(&mut seg, owner_sel[l], i, &obits[l * 64..(l + 1) * 64])?;
				write_col::<64>(&mut seg, next_sel[l], i, &xbits[l * 64..(l + 1) * 64])?;
			}
			let wv = o > x;
			write_bit(&mut seg, wrap, i, wv)?;
			let wb: Vec<bool> = (0..W).map(|_| wv).collect();
			write_col::<W>(&mut seg, bc, i, &wb)?;
			write_col::<W>(&mut seg, bcr, i, &wb)?;
			write_bit(&mut seg, bc0, i, wv)?;
			let dbits: Vec<bool> = (0..W).map(|k| obits[k] ^ xbits[k]).collect();
			write_col::<W>(&mut seg, diff, i, &dbits)?;
			let mbits: Vec<bool> = (0..W).map(|k| wv && dbits[k]).collect();
			write_col::<W>(&mut seg, masked, i, &mbits)?;
			let lobits: Vec<bool> = (0..W).map(|k| obits[k] ^ mbits[k]).collect();
			let hibits: Vec<bool> = (0..W).map(|k| xbits[k] ^ mbits[k]).collect();
			write_col::<W>(&mut seg, lo, i, &lobits)?;
			write_col::<W>(&mut seg, hi, i, &hibits)?;
			let bits_to_uint = |bits: &[bool]| -> BigUint {
				let mut b = vec![0u8; W / 8];
				for (k, &bit) in bits.iter().enumerate() {
					if bit {
						b[k / 8] |= 1 << (k % 8);
					}
				}
				BigUint::from_bytes_le(&b)
			};
			let lo_v = bits_to_uint(&lobits);
			let hi_v = bits_to_uint(&hibits);
			let a1v = &lo_v + 1u32;
			let a1_bits = to_bits(&a1v);
			a1.populate(&mut seg, i, &lobits, &one_bits)?;
			let d_val = if hi_v >= a1v { &hi_v - &a1v } else { &modw + &hi_v - &a1v };
			let d_bits = to_bits(&d_val);
			write_col::<W>(&mut seg, dcol, i, &d_bits)?;
			s2.populate(&mut seg, i, &a1_bits, &d_bits)?;
			let (_s, cout) = ripple_add(&a1_bits, &d_bits);
			write_bit(&mut seg, fc, i, cout[W - 1])?;
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
		}),
	))
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

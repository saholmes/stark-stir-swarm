// binius-substrate — M2b-4 "in-circuit CROSS-TABLE CHANNEL JOIN"
// (the "master-binds-inner-root" aggregation primitive).
//
// M2b-2/M2b-3 chained two hashes IN ONE TABLE and (M2b-3) exposed the chain root
// on a channel that an OUTER, PUBLIC `Statement.boundaries` PULL enforced. M2b-4
// moves the PULL *inside the circuit*, into a SECOND table, so the binding is a
// pure intra-proof multiset balance between two sub-circuits — no public value is
// involved. This is the shape a "master binds inner root" aggregation needs.
//
// ============================ TOPOLOGY ======================================
// ONE `ConstraintSystem`, ONE shared channel `join`, TWO tables:
//
//   CHILD  table:  R_child  = SHA3-256( A ‖ B )            (single block, mlen=64)
//                  push R_child (4 B64 lanes) -> join
//
//   PARENT table:  R_parent = SHA3-256( inner_root ‖ D )   (single block, mlen=64)
//                  pull inner_root (4 B64 lanes) <- join
//
// The `join` channel gets EXACTLY one push (child) and one pull (parent) per row.
// A single-message channel balances as a MULTISET iff the pushed tuple equals the
// pulled tuple, i.e. iff
//
//        parent.state_in lanes 0..3   ==   child's genuine SHA3-256(A‖B) digest.
//
// That equality — enforced by the verifier's channel-balance check across BOTH
// tables — IS the join. Feed the parent any other 32-byte "inner root" and the
// channel is unbalanced: the verifier REJECTS.
//
// ============================ WHY THE PULL IS THE PARENT'S REAL INPUT ========
// The soundness hinge is that the columns pulled from `join` are the SAME columns
// that feed the parent Keccak permutation — not some unrelated committed value.
// The parent gadget's permutation input is `g.packed_state_in()` on TRACK 0
// (`STATE_IN_TRACK = 0`). For lanes 0..3 we take THAT column and derive the pulled
// value as a Projected virtual oracle:
//
//     inner_sel[i] = add_selected_block::<B1,512,64>( state_in_inner[i], IN_TRACK )
//     inner_b64[i] = add_packed::<B1,64,B64,1>( inner_sel[i] )      // same bits
//     table.pull(join, inner_b64[0..4])
//
// `inner_sel[i]` is a structural projection (track 0, 64 bits) of the parent's
// committed `state_in[i]` column — the exact lane the permutation consumes. There
// is no separate "inner root" column the prover could set independently of the
// hash input. Hence the join binds the parent's REAL first-32-byte hash input to
// the child's REAL digest. (Child side is the dual: push the Projected track-7
// block of `packed_state_out()`, i.e. the genuine digest — same mechanism M2b-3
// used for its root boundary.)
//
// The parent's lanes 4..7 (= D) are message-bound to a committed `msg_d` column
// exactly like M2b-2's g2 second-32-bytes; the parent's lanes 0..3 are bound
// SOLELY by the join pull. Remove the pull and the parent's first 32 input bytes
// are free — which is precisely what the adversarial test forges.
//
// ============================ SOUNDNESS BOUNDARY (HONEST) ===================
//  * IN-CIRCUIT & SOUND (this milestone): both single-block SHA3-256 permutations;
//    both FIPS-202 mlen=64 paddings; the message binding of A,B (child) and D
//    (parent, second 32 bytes); and the child->parent CHANNEL JOIN binding the
//    parent's committed inner-root INPUT to the child's genuine digest.
//  * THIS IS AGGREGATION / INTRA-PROOF CROSS-TABLE BINDING, **NOT** PROOF-CARRYING
//    RECURSION. The parent does NOT verify the child's STARK proof in-circuit. It
//    binds to the child's *hash output value* via a shared multiset channel inside
//    ONE proof. A true recursive-verifier milestone would additionally require the
//    parent circuit to run the Binius verifier (FRI/sumcheck/Merkle-path checks)
//    over the child proof as witness — orders of magnitude more constraints, and
//    out of scope here. We do NOT overclaim.
//  * Optionally (secondary) the parent's own digest R_parent is exposed as a
//    public boundary via a second channel, reusing the M2b-3 root-boundary path.
// ============================================================================

use anyhow::Result;
use binius_circuits::builder::types::U;
use binius_core::constraint_system::channel::ChannelId;
use binius_core::fiat_shamir::HasherChallenger;
use binius_field::tower::CanonicalTowerFamily;
use binius_hash::sha2::Sha256Compression;
use binius_m3::{
	builder::{
		Boundary, Col, ConstraintSystem, FlushDirection, Statement, TableId, WitnessIndex, B1, B64,
		B128,
	},
	gadgets::hash::keccak::{self, Keccakf, StateMatrix},
};
use sha2::Sha256;

use crate::sha3_gadget::digest_from_state;
use crate::sha3_seam::{
	fill_track0_const, padded_state_64, track0_pattern, IN_TRACK_INDEX, LANE64_BITS, LANE_BITS,
	MASK_FULL, OUT_TRACK_INDEX, P, TARGET_LANE8, TARGET_LANE16,
};

/// Fill the padding + message binding constraints for a single-block SHA3-256
/// over 64 bytes (`first32 ‖ second32`). `s` are the gadget's committed
/// `state_in` lanes; `msg_bind` lists (lane_index, committed_msg_col) pairs the
/// message bytes are pinned to. Lanes NOT in `msg_bind` (used for the pulled
/// inner-root on the parent) are left free for the channel to bind.
fn bind_padding_and_msg(
	table: &mut binius_m3::builder::TableBuilder<'_>,
	tag: &str,
	s: &[Col<B1, LANE_BITS>],
	msg_bind: &[(usize, Col<B1, LANE_BITS>)],
	mask_full: Col<B1, LANE_BITS>,
	target_lane8: Col<B1, LANE_BITS>,
	target_lane16: Col<B1, LANE_BITS>,
) {
	for &(lane, col) in msg_bind {
		table.assert_zero(format!("{tag}_bind_msg_lane{lane}"), (s[lane] - col) * mask_full);
	}
	// lane 8: SHA-3 domain separator 0x06 (+ zero fill on bytes 1..7).
	table.assert_zero(format!("{tag}_pad_lane8"), (s[8] - target_lane8) * mask_full);
	// lanes 9..15: message region past pad start — all zero.
	for i in 9..=15 {
		table.assert_zero(format!("{tag}_pad_zero_lane{i}"), s[i] * mask_full);
	}
	// lane 16 (byte 135): pad10*1 closing bit 0x80.
	table.assert_zero(format!("{tag}_pad_lane16"), (s[16] - target_lane16) * mask_full);
	// lanes 17..24: the 512-bit capacity — all zero.
	for i in 17..=24 {
		table.assert_zero(format!("{tag}_cap_zero_lane{i}"), s[i] * mask_full);
	}
}

/// Extract the 64-bit `track` block of each of `lanes` 0..4 as a `Col<B1,64>`
/// Projected virtual oracle, then pack each to a `Col<B64,1>` aliasing the same
/// bits — the tuple form pushed to / pulled from a channel.
fn track_lanes_to_b64(
	table: &mut binius_m3::builder::TableBuilder<'_>,
	name: &str,
	lanes: &[Col<B1, LANE_BITS>],
	track: usize,
) -> ([Col<B1, LANE64_BITS>; 4], [Col<B64, 1>; 4]) {
	let sel: [Col<B1, LANE64_BITS>; 4] = std::array::from_fn(|i| {
		table.add_selected_block::<B1, LANE_BITS, LANE64_BITS>(
			format!("{name}_sel[{i}]"),
			lanes[i],
			track,
		)
	});
	let b64: [Col<B64, 1>; 4] =
		std::array::from_fn(|i| table.add_packed::<B1, LANE64_BITS, B64, 1>(format!("{name}_b64[{i}]"), sel[i]));
	(sel, b64)
}

/// Write the genuine per-row lane values (one u64 per row) into a Projected
/// selected-block column so its witness matches the source track it projects.
fn fill_selected_lanes(
	seg: &mut binius_m3::builder::TableWitnessSegment<P>,
	cols: &[Col<B1, LANE64_BITS>; 4],
	states: &[StateMatrix<u64>],
) -> Result<()> {
	for (i, &col) in cols.iter().enumerate() {
		let mut d: std::cell::RefMut<'_, [u64]> = seg.get_mut_as(col)?;
		for (k, cell) in d.iter_mut().take(states.len()).enumerate() {
			*cell = states[k].as_inner()[i];
		}
	}
	Ok(())
}

// ================================ CHILD TABLE ===============================

/// Child sub-circuit: `R_child = SHA3-256(A ‖ B)`; pushes `R_child` to `join`.
pub struct ChildTable {
	pub table_id: TableId,
	g: Keccakf,
	msg: [Col<B1, LANE_BITS>; 8], // A ‖ B
	mask_full: Col<B1, LANE_BITS>,
	target_lane8: Col<B1, LANE_BITS>,
	target_lane16: Col<B1, LANE_BITS>,
	// Digest track-7 lanes (Projected), pushed to `join`.
	root_sel: [Col<B1, LANE64_BITS>; 4],
}

impl ChildTable {
	pub fn new(cs: &mut ConstraintSystem, join: ChannelId) -> Self {
		let mut table = cs.add_table("M2b-4 child SHA3-256 (push root to join)");

		let state_in: StateMatrix<Col<B1, LANE_BITS>> =
			StateMatrix::from_fn(|(x, y)| table.add_committed(format!("in[{x},{y}]")));
		let g = keccak::Keccakf::new(&mut table, state_in.clone());

		let msg: [Col<B1, LANE_BITS>; 8] =
			std::array::from_fn(|i| table.add_committed(format!("msg[{i}]")));
		let mask_full = table.add_constant("mask_full", track0_pattern(MASK_FULL));
		let target_lane8 = table.add_constant("target_lane8", track0_pattern(TARGET_LANE8));
		let target_lane16 = table.add_constant("target_lane16", track0_pattern(TARGET_LANE16));

		let s = state_in.as_inner();
		// Full 64-byte message A‖B bound to committed `msg` lanes 0..7.
		let binds: Vec<(usize, Col<B1, LANE_BITS>)> = (0..8).map(|i| (i, msg[i])).collect();
		bind_padding_and_msg(&mut table, "child", s, &binds, mask_full, target_lane8, target_lane16);

		// PUSH: child's genuine digest = state_out track-7 lanes 0..3.
		let g_out = g.packed_state_out();
		let g_out_inner = g_out.as_inner();
		let (root_sel, root_b64) =
			track_lanes_to_b64(&mut table, "root", g_out_inner, OUT_TRACK_INDEX);
		table.push(join, root_b64);

		Self {
			table_id: table.id(),
			g,
			msg,
			mask_full,
			target_lane8,
			target_lane16,
			root_sel,
		}
	}

	/// Populate one row: hashes `A ‖ B`. Returns the genuine digest `R_child`.
	pub fn populate(
		&self,
		seg: &mut binius_m3::builder::TableWitnessSegment<P>,
		a: &[u8; 32],
		b: &[u8; 32],
	) -> Result<[u8; 32]> {
		let state = padded_state_64(a, b, None);
		self.g.populate_state_in(seg, std::iter::once(&state))?;
		self.g.populate(seg)?;
		let out_states: Vec<StateMatrix<u64>> = self.g.read_state_outs(seg)?.collect();
		let digest = digest_from_state(&out_states[0]);

		// Message columns = state_in lanes 0..7 (= A‖B).
		let in_states = vec![state];
		for (i, &col) in self.msg.iter().enumerate() {
			let mut d: std::cell::RefMut<'_, [u64]> = seg.get_mut_as(col)?;
			for (k, chunk) in d.chunks_exact_mut(8).enumerate() {
				let lane = in_states[k].as_inner()[i];
				chunk.copy_from_slice(&[lane, 0, 0, 0, 0, 0, 0, 0]);
			}
		}
		fill_track0_const(seg, self.mask_full, MASK_FULL)?;
		fill_track0_const(seg, self.target_lane8, TARGET_LANE8)?;
		fill_track0_const(seg, self.target_lane16, TARGET_LANE16)?;
		// Pushed root lanes = genuine digest (track-7 out).
		fill_selected_lanes(seg, &self.root_sel, &out_states)?;
		Ok(digest)
	}
}

// ================================ PARENT TABLE ==============================

/// Parent sub-circuit: `R_parent = SHA3-256(inner_root ‖ D)`; PULLs `inner_root`
/// (its own first-32-byte hash input) from `join`.
pub struct ParentTable {
	pub table_id: TableId,
	g: Keccakf,
	msg_d: [Col<B1, LANE_BITS>; 4], // D = second 32 bytes
	mask_full: Col<B1, LANE_BITS>,
	target_lane8: Col<B1, LANE_BITS>,
	target_lane16: Col<B1, LANE_BITS>,
	// Inner-root track-0 lanes (Projected from state_in), pulled from `join`.
	inner_sel: [Col<B1, LANE64_BITS>; 4],
	// Optional: R_parent digest track-7 lanes pushed to a public root channel.
	root_sel: Option<[Col<B1, LANE64_BITS>; 4]>,
}

impl ParentTable {
	pub fn new(
		cs: &mut ConstraintSystem,
		join: ChannelId,
		root_channel: Option<ChannelId>,
	) -> Self {
		let mut table = cs.add_table("M2b-4 parent SHA3-256 (pull inner root from join)");

		let state_in: StateMatrix<Col<B1, LANE_BITS>> =
			StateMatrix::from_fn(|(x, y)| table.add_committed(format!("in[{x},{y}]")));
		let g = keccak::Keccakf::new(&mut table, state_in.clone());

		let msg_d: [Col<B1, LANE_BITS>; 4] =
			std::array::from_fn(|j| table.add_committed(format!("msg_d[{j}]")));
		let mask_full = table.add_constant("mask_full", track0_pattern(MASK_FULL));
		let target_lane8 = table.add_constant("target_lane8", track0_pattern(TARGET_LANE8));
		let target_lane16 = table.add_constant("target_lane16", track0_pattern(TARGET_LANE16));

		let s = state_in.as_inner();
		// lanes 4..7 = D bound to msg_d; lanes 0..3 (inner root) bound ONLY by pull.
		let binds: Vec<(usize, Col<B1, LANE_BITS>)> =
			(0..4).map(|j| (4 + j, msg_d[j])).collect();
		bind_padding_and_msg(&mut table, "parent", s, &binds, mask_full, target_lane8, target_lane16);

		// PULL: parent's REAL first-32-byte hash input = state_in track-0 lanes 0..3.
		// `g.packed_state_in()` is exactly the committed `state_in` fed to the
		// permutation, so the pulled columns ARE the permutation's input.
		let g_in = g.packed_state_in();
		let g_in_inner = g_in.as_inner();
		let (inner_sel, inner_b64) =
			track_lanes_to_b64(&mut table, "inner", g_in_inner, IN_TRACK_INDEX);
		table.pull(join, inner_b64);

		// Optional secondary: expose R_parent as a public boundary (M2b-3 path).
		let root_sel: Option<[Col<B1, LANE64_BITS>; 4]> = root_channel.map(|ch| {
			let g_out = g.packed_state_out();
			let g_out_inner = g_out.as_inner();
			let (sel, b64) = track_lanes_to_b64(&mut table, "proot", g_out_inner, OUT_TRACK_INDEX);
			table.push(ch, b64);
			sel
		});

		Self {
			table_id: table.id(),
			g,
			msg_d,
			mask_full,
			target_lane8,
			target_lane16,
			inner_sel,
			root_sel,
		}
	}

	/// Populate one row: hashes `inner_root ‖ D`. In HONEST runs `inner_root` is
	/// the child's genuine digest; in the forged run it is any other value (both
	/// still valid Keccak-f pairs with valid padding). Returns `R_parent`.
	pub fn populate(
		&self,
		seg: &mut binius_m3::builder::TableWitnessSegment<P>,
		inner_root: &[u8; 32],
		d: &[u8; 32],
	) -> Result<[u8; 32]> {
		let state = padded_state_64(inner_root, d, None);
		self.g.populate_state_in(seg, std::iter::once(&state))?;
		self.g.populate(seg)?;
		let out_states: Vec<StateMatrix<u64>> = self.g.read_state_outs(seg)?.collect();
		let digest = digest_from_state(&out_states[0]);

		let in_states = vec![state];
		// D bound to msg_d = state_in lanes 4..7.
		for (j, &col) in self.msg_d.iter().enumerate() {
			let mut dd: std::cell::RefMut<'_, [u64]> = seg.get_mut_as(col)?;
			for (k, chunk) in dd.chunks_exact_mut(8).enumerate() {
				let lane = in_states[k].as_inner()[4 + j];
				chunk.copy_from_slice(&[lane, 0, 0, 0, 0, 0, 0, 0]);
			}
		}
		fill_track0_const(seg, self.mask_full, MASK_FULL)?;
		fill_track0_const(seg, self.target_lane8, TARGET_LANE8)?;
		fill_track0_const(seg, self.target_lane16, TARGET_LANE16)?;
		// Pulled inner-root lanes = parent state_in track-0 lanes 0..3.
		fill_selected_lanes(seg, &self.inner_sel, &in_states)?;
		// Optional pushed parent-root lanes = genuine R_parent (track-7 out).
		if let Some(root_sel) = &self.root_sel {
			fill_selected_lanes(seg, root_sel, &out_states)?;
		}
		Ok(digest)
	}
}

// ================================ HARNESS ===================================

/// Honest vs. forged inner-root for the join gate.
#[derive(Clone, Copy, Debug)]
pub enum JoinMode {
	/// Parent's inner-root input = child's genuine `R_child` -> channel balances.
	Honest,
	/// Parent's inner-root input = `forged` != `R_child`, with both child and
	/// parent still valid Keccak-f pairs and valid paddings -> channel unbalanced.
	ForgedInnerRoot { forged: [u8; 32] },
}

/// End-to-end outcome, recording every stage so the gate can prove exactly WHERE
/// (and whether) a forged inner root is rejected.
#[derive(Debug)]
pub struct JoinOutcome {
	/// Child's genuine digest `R_child`.
	pub r_child: [u8; 32],
	/// Parent's genuine digest `R_parent = SHA3-256(inner_root ‖ D)`.
	pub r_parent: [u8; 32],
	pub proof_size: usize,
	pub validate_ok: bool,
	pub validate_error: String,
	pub prove_ok: bool,
	pub prove_error: String,
	pub verify_ok: bool,
	pub verify_error: String,
	/// First stage that rejected: "none" | "validate" | "prove" | "verify".
	pub reject_stage: &'static str,
}

impl JoinOutcome {
	pub fn accepted(&self) -> bool {
		self.reject_stage == "none"
	}
}

/// Build the two-table, one-channel join for a SINGLE child->parent pair, then
/// run `validate_witness` and the full SHA-256 (FIPS 180-4) prove/verify.
///
/// * `JoinMode::Honest`         -> every stage ACCEPTS; `R_parent == SHA3-256(R_child ‖ D)`.
/// * `JoinMode::ForgedInnerRoot`-> the `join` channel is UNBALANCED and the
///   pipeline REJECTS (see `reject_stage` / `*_error`).
///
/// If `parent_root_claim` is `Some`, `R_parent` is additionally exposed as a
/// public boundary (secondary; balances iff the claim equals `R_parent`).
pub fn prove_verify_join(
	a: [u8; 32],
	b: [u8; 32],
	d: [u8; 32],
	mode: JoinMode,
	parent_root_claim: Option<[u8; 32]>,
	log_inv_rate: usize,
	security_bits: usize,
) -> Result<JoinOutcome> {
	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::new();
	let join = cs.add_channel("join");
	let root_channel = parent_root_claim.map(|_| cs.add_channel("parent_root"));

	let child = ChildTable::new(&mut cs, join);
	let parent = ParentTable::new(&mut cs, join, root_channel);

	let mut boundaries = vec![];
	if let (Some(ch), Some(claim)) = (root_channel, parent_root_claim) {
		boundaries.push(Boundary {
			values: (0..4)
				.map(|i| {
					let lane =
						u64::from_le_bytes(claim[i * 8..i * 8 + 8].try_into().unwrap());
					B128::from(B64::new(lane))
				})
				.collect(),
			channel_id: ch,
			direction: FlushDirection::Pull,
			multiplicity: 1,
		});
	}
	let statement = Statement {
		boundaries,
		// table_sizes indexed by table id: child == 0, parent == 1.
		table_sizes: vec![1, 1],
	};

	let mut witness = WitnessIndex::<P>::new(&cs, &allocator);

	// Child table witness.
	let child_tw = witness.init_table(child.table_id, 1)?;
	let mut child_seg = child_tw.full_segment();
	let r_child = child.populate(&mut child_seg, &a, &b)?;
	drop(child_seg);

	// Parent table witness. The pulled inner root is the parent's REAL hash input.
	let inner_root = match mode {
		JoinMode::Honest => r_child,
		JoinMode::ForgedInnerRoot { forged } => forged,
	};
	let parent_tw = witness.init_table(parent.table_id, 1)?;
	let mut parent_seg = parent_tw.full_segment();
	let r_parent = parent.populate(&mut parent_seg, &inner_root, &d)?;
	drop(parent_seg);

	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();

	// Stage 1: deterministic channel-balance + constraint check.
	let validate = binius_core::constraint_system::validate::validate_witness(
		&ccs,
		&statement.boundaries,
		&witness,
	);
	let validate_ok = validate.is_ok();
	let validate_error = validate.err().map(|e| e.to_string()).unwrap_or_default();

	// Stage 2/3: full SHA-256 prove, then verify.
	let proof = binius_core::constraint_system::prove::<
		U,
		CanonicalTowerFamily,
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
	);

	let (proof_size, prove_ok, prove_error, verify_ok, verify_error) = match proof {
		Err(e) => (0, false, e.to_string(), false, String::new()),
		Ok(proof) => {
			let proof_size = proof.get_proof_size();
			let verify = binius_core::constraint_system::verify::<
				U,
				CanonicalTowerFamily,
				Sha256,
				Sha256Compression,
				HasherChallenger<Sha256>,
			>(&ccs, log_inv_rate, security_bits, &statement.boundaries, proof);
			match verify {
				Err(e) => (proof_size, true, String::new(), false, e.to_string()),
				Ok(()) => (proof_size, true, String::new(), true, String::new()),
			}
		}
	};

	let reject_stage = if !validate_ok {
		"validate"
	} else if !prove_ok {
		"prove"
	} else if !verify_ok {
		"verify"
	} else {
		"none"
	};

	Ok(JoinOutcome {
		r_child,
		r_parent,
		proof_size,
		validate_ok,
		validate_error,
		prove_ok,
		prove_error,
		verify_ok,
		verify_error,
		reject_stage,
	})
}

#[cfg(test)]
mod tests {
	use super::*;
	use sha3::{Digest, Sha3_256};

	fn native_sha3_256(msg: &[u8]) -> [u8; 32] {
		let mut h = Sha3_256::new();
		h.update(msg);
		h.finalize().into()
	}

	fn native_join(a: &[u8; 32], b: &[u8; 32], d: &[u8; 32]) -> ([u8; 32], [u8; 32]) {
		let mut m1 = Vec::with_capacity(64);
		m1.extend_from_slice(a);
		m1.extend_from_slice(b);
		let r_child = native_sha3_256(&m1);
		let mut m2 = Vec::with_capacity(64);
		m2.extend_from_slice(&r_child);
		m2.extend_from_slice(d);
		let r_parent = native_sha3_256(&m2);
		(r_child, r_parent)
	}

	/// M2b-4 gate #1: honest join — parent's pulled inner root == child's genuine
	/// R_child. The two-table one-channel system proves + verifies under SHA-256,
	/// and R_parent matches native SHA3-256(SHA3-256(A‖B)‖D).
	#[test]
	fn join_honest_accepts() {
		let a = [0xAAu8; 32];
		let b = [0xBBu8; 32];
		let d = [0xDDu8; 32];
		let (rc_exp, rp_exp) = native_join(&a, &b, &d);

		let outcome = prove_verify_join(a, b, d, JoinMode::Honest, None, 1, 100)
			.expect("honest join harness must run to completion");

		assert_eq!(outcome.r_child, rc_exp, "in-circuit R_child != native SHA3-256(A‖B)");
		assert_eq!(
			outcome.r_parent, rp_exp,
			"in-circuit R_parent != native SHA3-256(SHA3-256(A‖B)‖D)"
		);
		assert!(
			outcome.accepted(),
			"honest join rejected at stage '{}': validate='{}' prove='{}' verify='{}'",
			outcome.reject_stage,
			outcome.validate_error,
			outcome.prove_error,
			outcome.verify_error
		);
		assert!(outcome.validate_ok && outcome.prove_ok && outcome.verify_ok);
		assert!(outcome.proof_size > 0);
		println!(
			"M2b-4 join honest ACCEPTS: child->parent channel balanced; R_parent matches native; proof = {} bytes",
			outcome.proof_size
		);
	}

	/// M2b-4 THE DELIVERABLE (gate #2): the parent commits an inner-root INPUT that
	/// is NOT the child's genuine R_child (0xDE..), with BOTH child and parent
	/// internally valid Keccak-f pairs and valid paddings. The ONLY broken relation
	/// is the child->parent channel binding, so the `join` channel is unbalanced
	/// and the SHA-256 verifier MUST reject.
	#[test]
	fn join_forged_inner_root_rejected() {
		let a = [0xAAu8; 32];
		let b = [0xBBu8; 32];
		let d = [0xDDu8; 32];
		let (rc_exp, _rp_exp) = native_join(&a, &b, &d);

		// A forged inner root that is (whp) not any real SHA3-256(A‖B).
		let forged = [0xDEu8; 32];
		assert_ne!(forged, rc_exp);

		let outcome =
			prove_verify_join(a, b, d, JoinMode::ForgedInnerRoot { forged }, None, 1, 100)
				.expect("forged-join harness must run to completion");

		// Child still pushes its genuine digest; only the parent's pulled input differs.
		assert_eq!(outcome.r_child, rc_exp);
		// R_parent = SHA3-256(forged ‖ D) — a valid hash, but not bound to the child.
		assert_eq!(outcome.r_parent, native_sha3_256(&{
			let mut m = Vec::with_capacity(64);
			m.extend_from_slice(&forged);
			m.extend_from_slice(&d);
			m
		}));

		assert!(
			!outcome.accepted(),
			"SOUNDNESS FAILURE: a FORGED inner root was ACCEPTED (join did not bind child->parent)"
		);
		assert!(
			!outcome.verify_ok,
			"SOUNDNESS FAILURE: SHA-256 verify ACCEPTED a forged inner root"
		);
		println!(
			"M2b-4 forged-inner-root REJECTED at stage '{}':\n  validate: ok={} err='{}'\n  prove   : ok={} err='{}'\n  verify  : ok={} err='{}'",
			outcome.reject_stage,
			outcome.validate_ok,
			outcome.validate_error,
			outcome.prove_ok,
			outcome.prove_error,
			outcome.verify_ok,
			outcome.verify_error
		);
	}

	/// M2b-4 secondary: honest join AND expose R_parent as a public boundary; both
	/// the in-circuit join and the public root claim must balance.
	#[test]
	fn join_with_parent_root_boundary_accepts() {
		let a = [0x01u8; 32];
		let b = [0x02u8; 32];
		let d = [0x03u8; 32];
		let (_rc, rp_exp) = native_join(&a, &b, &d);

		let outcome = prove_verify_join(a, b, d, JoinMode::Honest, Some(rp_exp), 1, 100)
			.expect("join+root-boundary harness must run to completion");

		assert_eq!(outcome.r_parent, rp_exp);
		assert!(
			outcome.accepted(),
			"honest join+root-boundary rejected at '{}': validate='{}' verify='{}'",
			outcome.reject_stage,
			outcome.validate_error,
			outcome.verify_error
		);
		println!(
			"M2b-4 join+parent-root-boundary ACCEPTS: proof = {} bytes",
			outcome.proof_size
		);
	}
}

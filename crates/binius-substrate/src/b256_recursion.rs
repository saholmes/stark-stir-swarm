// binius-substrate — M2b-2 / M2b-3 / M2b-4 recursion-binding primitives ported
// onto the 256-bit challenge/extension field `B256TowerFamily` (tower level 8), so
// the seam, root-boundary and cross-table channel-join all prove AND verify at NIST
// L1/L3 Fiat–Shamir security with their adversarial rejects firing.
//
// These are the B128 primitives in `sha3_seam.rs` (M2b-2 + M2b-3) and
// `sha3_join.rs` (M2b-4) re-threaded through the B256 prove wiring proven out in
// `b256_keccak.rs`. NO FORK CHANGE is required: every m3 op these primitives use —
// `add_shifted`, `add_selected_block`, `add_packed`, `push`, `pull`, `assert_zero`,
// `add_constant` — lives on `impl<'a, F: TowerField> TableBuilder<'a, F>` and is
// generic over the top field; `Statement<F>` and `Boundary<F>` are likewise
// generic. The ONLY thing that changes vs the B128 versions is:
//   * `ConstraintSystem::<B256>` / `TableBuilder<'_, B256>` / `WitnessIndex::<B256>`,
//     so the witness segment is `TableWitnessSegment<B256>`;
//   * `prove/verify::<U256, B256TowerFamily, Sha256, Sha256Compression,
//     HasherChallenger<Sha256>>`;
//   * the public boundary values are elements of the TOP field, which is now `B256`
//     (the `FExt` slot), so a claimed root lane is `B256::from(B64::new(lane))`
//     instead of `B128::from(..)`. This is the single spot where the B128 versions
//     named the concrete top field; it is in OUR harness (not a fork op), and the
//     fix is mechanical because `Boundary<F>` is generic.
//
// The field-agnostic helpers (FIPS-202 padding of a 64-byte block, the track-0
// constant pattern, the padding-corruption enum) are REUSED unchanged from
// `sha3_seam.rs` — they operate on `u64` lanes / `[B1;512]` patterns and carry no
// field parameter.
//
// SOUNDNESS BOUNDARY: identical to the B128 M2b-2/3/4 (see those modules). Moving to
// B256 only raises the challenge/extension field to 2^256 so the FRI/sumcheck error
// terms clear NIST L1(128)/L3(192); it changes nothing about WHICH relations are
// in-circuit. In particular M2b-4 remains aggregation / intra-proof cross-table
// binding, NOT proof-carrying recursion (the parent does not verify the child's
// STARK in-circuit). We do NOT overclaim.

use anyhow::Result;
use binius_core::constraint_system::channel::ChannelId;
use binius_core::fiat_shamir::HasherChallenger;
use binius_core::oracle::ShiftVariant;
use binius_hash::sha2::Sha256Compression;
use binius_m3::{
	builder::{
		Boundary, Col, ConstraintSystem, FlushDirection, Statement, TableBuilder, TableId,
		WitnessIndex, B1, B64,
	},
	gadgets::hash::keccak::{self, Keccakf, StateMatrix},
};
use sha2::Sha256;

use crate::b256_field::{B256TowerFamily, B256 as OurB256, U256};
use crate::sha3_gadget::digest_from_state;
// Field-agnostic helpers reused verbatim from the B128 seam module.
use crate::sha3_seam::{
	padded_state_64, track0_pattern, PadCorruption, IN_TRACK_INDEX, LANE64_BITS, LANE_BITS,
	MASK_FULL, OUT_TRACK_INDEX, TARGET_LANE8, TARGET_LANE16,
};

const LOG_LANE_BITS: usize = 9; // log2(512)
const OUT_TRACK_SHIFT: usize = 7 * 64; // track 7 -> track 0 (LogicalRight by 448)

/// Witness segment packed type over B256 (B256 is its own width-1 packed field).
type Seg<'a> = binius_m3::builder::TableWitnessSegment<'a, OurB256>;
/// Table builder over the B256 top field.
type Tbl<'a> = TableBuilder<'a, OurB256>;

/// Write a track-0 constant `val` (interior tracks 0) into every row of a
/// `Col<B1,512>` witness buffer over the B256 segment.
fn fill_track0_const(seg: &mut Seg<'_>, col: Col<B1, LANE_BITS>, val: u64) -> Result<()> {
	let mut d: std::cell::RefMut<'_, [u64]> = seg.get_mut_as(col)?;
	for chunk in d.chunks_exact_mut(8) {
		chunk.copy_from_slice(&[val, 0, 0, 0, 0, 0, 0, 0]);
	}
	Ok(())
}

/// Extract the 64-bit `track` block of each lane 0..4 as a `Col<B1,64>` projected
/// virtual oracle, then pack each to a `Col<B64,1>` aliasing the same bits — the
/// tuple form pushed to / pulled from a channel. Over the B256 top field.
fn track_lanes_to_b64(
	table: &mut Tbl<'_>,
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
	let b64: [Col<B64, 1>; 4] = std::array::from_fn(|i| {
		table.add_packed::<B1, LANE64_BITS, B64, 1>(format!("{name}_b64[{i}]"), sel[i])
	});
	(sel, b64)
}

/// Write the genuine per-row lane values into a projected selected-block column.
fn fill_selected_lanes(
	seg: &mut Seg<'_>,
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

/// Convert a 32-byte claimed root into 4 top-field (`B256`) boundary values: each
/// 8-byte little-endian lane is a `B64` embedded into `B256` (the channel operates
/// in the top field). This is the B256 analogue of the B128 `B128::from(B64::new)`.
fn claimed_root_to_boundary_values(claimed_root: [u8; 32]) -> Vec<OurB256> {
	(0..4)
		.map(|i| {
			let lane = u64::from_le_bytes(claimed_root[i * 8..i * 8 + 8].try_into().unwrap());
			OurB256::from(B64::new(lane))
		})
		.collect()
}

// ============================================================================
// M2b-2 / M2b-3 — depth-2 SHA3-256 binding seam (optionally with a public root).
// ============================================================================

#[derive(Clone, Copy, Debug)]
pub(crate) enum SeamMode {
	Honest,
	ForgedPrefix { forged: [u8; 32] },
	BadPadding { on_g2: bool, kind: PadCorruption },
}

/// One-table, two-gadget depth-2 SHA3-256 chain with an in-circuit binding seam,
/// over the B256 top field.
pub struct SeamTableB256 {
	pub table_id: TableId,
	g1: Keccakf,
	g2: Keccakf,
	g1_out_lo: [Col<B1, LANE_BITS>; 4],
	msg_g1: [Col<B1, LANE_BITS>; 8],
	msg_c: [Col<B1, LANE_BITS>; 4],
	mask_full: Col<B1, LANE_BITS>,
	target_lane8: Col<B1, LANE_BITS>,
	target_lane16: Col<B1, LANE_BITS>,
	root_sel: Option<[Col<B1, LANE64_BITS>; 4]>,
}

impl SeamTableB256 {
	pub fn new(cs: &mut ConstraintSystem<OurB256>) -> Self {
		Self::build(cs, None)
	}

	pub(crate) fn new_with_root_boundary(
		cs: &mut ConstraintSystem<OurB256>,
		root_channel: ChannelId,
	) -> Self {
		Self::build(cs, Some(root_channel))
	}

	fn build(cs: &mut ConstraintSystem<OurB256>, root_channel: Option<ChannelId>) -> Self {
		let mut table = cs.add_table("SHA3-256 depth-2 binding seam over B256 (M2b-2/3)");

		let g1_state_in: StateMatrix<Col<B1, LANE_BITS>>;
		let g1;
		{
			let mut t = table.with_namespace("g1");
			g1_state_in = StateMatrix::from_fn(|(x, y)| t.add_committed(format!("in[{x},{y}]")));
			g1 = keccak::Keccakf::new(&mut t, g1_state_in.clone());
		}

		let g2_state_in: StateMatrix<Col<B1, LANE_BITS>>;
		let g2;
		{
			let mut t = table.with_namespace("g2");
			g2_state_in = StateMatrix::from_fn(|(x, y)| t.add_committed(format!("in[{x},{y}]")));
			g2 = keccak::Keccakf::new(&mut t, g2_state_in.clone());
		}

		// Seam realignment columns: g1 output track7 -> track0 (LogicalRight 448).
		let g1_out = g1.packed_state_out();
		let g1_out_inner = g1_out.as_inner();
		let g1_out_lo: [Col<B1, LANE_BITS>; 4] = std::array::from_fn(|i| {
			table.add_shifted(
				format!("g1_out_lo[{i}]"),
				g1_out_inner[i],
				LOG_LANE_BITS,
				OUT_TRACK_SHIFT,
				ShiftVariant::LogicalRight,
			)
		});

		let msg_g1: [Col<B1, LANE_BITS>; 8] =
			std::array::from_fn(|i| table.add_committed(format!("msg_g1[{i}]")));
		let msg_c: [Col<B1, LANE_BITS>; 4] =
			std::array::from_fn(|j| table.add_committed(format!("msg_c[{j}]")));
		let mask_full = table.add_constant("mask_full", track0_pattern(MASK_FULL));
		let target_lane8 = table.add_constant("target_lane8", track0_pattern(TARGET_LANE8));
		let target_lane16 = table.add_constant("target_lane16", track0_pattern(TARGET_LANE16));

		let s1 = g1_state_in.as_inner();
		let s2 = g2_state_in.as_inner();

		// g1 padding + message binding (mlen = 64).
		for i in 0..8 {
			table.assert_zero(format!("g1_bind_msg_lane{i}"), (s1[i] - msg_g1[i]) * mask_full);
		}
		table.assert_zero("g1_pad_lane8", (s1[8] - target_lane8) * mask_full);
		for i in 9..=15 {
			table.assert_zero(format!("g1_pad_zero_lane{i}"), s1[i] * mask_full);
		}
		table.assert_zero("g1_pad_lane16", (s1[16] - target_lane16) * mask_full);
		for i in 17..=24 {
			table.assert_zero(format!("g1_cap_zero_lane{i}"), s1[i] * mask_full);
		}

		// g2 padding + message binding (mlen = 64); lanes 0..3 bound ONLY by the seam.
		for j in 0..4 {
			table.assert_zero(
				format!("g2_bind_c_lane{}", 4 + j),
				(s2[4 + j] - msg_c[j]) * mask_full,
			);
		}
		table.assert_zero("g2_pad_lane8", (s2[8] - target_lane8) * mask_full);
		for i in 9..=15 {
			table.assert_zero(format!("g2_pad_zero_lane{i}"), s2[i] * mask_full);
		}
		table.assert_zero("g2_pad_lane16", (s2[16] - target_lane16) * mask_full);
		for i in 17..=24 {
			table.assert_zero(format!("g2_cap_zero_lane{i}"), s2[i] * mask_full);
		}

		// THE SEAM: g2 input lanes 0..3 == g1 digest lanes 0..3.
		for i in 0..4 {
			table.assert_zero(
				format!("seam_g1_to_g2_lane{i}"),
				(g1_out_lo[i] - s2[i]) * mask_full,
			);
		}

		// M2b-3 root-as-public-boundary (only when a channel is supplied).
		let root_sel: Option<[Col<B1, LANE64_BITS>; 4]> = root_channel.map(|ch| {
			let g2_out = g2.packed_state_out();
			let g2_out_inner = g2_out.as_inner();
			let (sel, b64) = track_lanes_to_b64(&mut table, "root", g2_out_inner, OUT_TRACK_INDEX);
			table.push(ch, b64);
			sel
		});

		Self {
			table_id: table.id(),
			g1,
			g2,
			g1_out_lo,
			msg_g1,
			msg_c,
			mask_full,
			target_lane8,
			target_lane16,
			root_sel,
		}
	}

	pub(crate) fn populate(
		&self,
		seg: &mut Seg<'_>,
		children: &[(([u8; 32], [u8; 32]), [u8; 32])],
		mode: SeamMode,
	) -> Result<(Vec<[u8; 32]>, Vec<[u8; 32]>)> {
		let g1_states: Vec<StateMatrix<u64>> = children
			.iter()
			.map(|((a, b), _)| {
				let g1_bad = matches!(mode, SeamMode::BadPadding { on_g2: false, .. });
				let kind = if let SeamMode::BadPadding { kind, .. } = mode {
					Some(kind)
				} else {
					None
				};
				padded_state_64(a, b, if g1_bad { kind } else { None })
			})
			.collect();
		self.g1.populate_state_in(seg, &g1_states)?;
		self.g1.populate(seg)?;

		let g1_out_states: Vec<StateMatrix<u64>> = self.g1.read_state_outs(seg)?.collect();
		let g1_digests: Vec<[u8; 32]> = g1_out_states.iter().map(digest_from_state).collect();

		let g2_states: Vec<StateMatrix<u64>> = children
			.iter()
			.enumerate()
			.map(|(k, (_, c))| {
				let prefix = match mode {
					SeamMode::ForgedPrefix { forged } => forged,
					_ => g1_digests[k],
				};
				let g2_bad = matches!(mode, SeamMode::BadPadding { on_g2: true, .. });
				let kind = if let SeamMode::BadPadding { kind, .. } = mode {
					Some(kind)
				} else {
					None
				};
				padded_state_64(&prefix, c, if g2_bad { kind } else { None })
			})
			.collect();
		self.g2.populate_state_in(seg, &g2_states)?;
		self.g2.populate(seg)?;
		let g2_out_states: Vec<StateMatrix<u64>> = self.g2.read_state_outs(seg)?.collect();
		let g2_digests: Vec<[u8; 32]> = g2_out_states.iter().map(digest_from_state).collect();

		// Seam realignment columns: track0 = g1 digest lane i.
		for (i, &col) in self.g1_out_lo.iter().enumerate() {
			let mut d: std::cell::RefMut<'_, [u64]> = seg.get_mut_as(col)?;
			for (k, chunk) in d.chunks_exact_mut(8).enumerate() {
				let lane = g1_out_states[k].as_inner()[i];
				chunk.copy_from_slice(&[lane, 0, 0, 0, 0, 0, 0, 0]);
			}
		}

		for (i, &col) in self.msg_g1.iter().enumerate() {
			let mut d: std::cell::RefMut<'_, [u64]> = seg.get_mut_as(col)?;
			for (k, chunk) in d.chunks_exact_mut(8).enumerate() {
				let lane = g1_states[k].as_inner()[i];
				chunk.copy_from_slice(&[lane, 0, 0, 0, 0, 0, 0, 0]);
			}
		}
		for (j, &col) in self.msg_c.iter().enumerate() {
			let mut d: std::cell::RefMut<'_, [u64]> = seg.get_mut_as(col)?;
			for (k, chunk) in d.chunks_exact_mut(8).enumerate() {
				let c = children[k].1;
				let lane = u64::from_le_bytes(c[j * 8..j * 8 + 8].try_into().unwrap());
				chunk.copy_from_slice(&[lane, 0, 0, 0, 0, 0, 0, 0]);
			}
		}

		fill_track0_const(seg, self.mask_full, MASK_FULL)?;
		fill_track0_const(seg, self.target_lane8, TARGET_LANE8)?;
		fill_track0_const(seg, self.target_lane16, TARGET_LANE16)?;

		if let Some(root_sel) = &self.root_sel {
			fill_selected_lanes(seg, root_sel, &g2_out_states)?;
		}

		Ok((g1_digests, g2_digests))
	}
}

/// Honest end-to-end depth-2 seam over B256. Returns `(proof_size, g1_digests, roots)`.
pub fn prove_verify_seam_b256(
	children: &[(([u8; 32], [u8; 32]), [u8; 32])],
	log_inv_rate: usize,
	security_bits: usize,
) -> Result<(usize, Vec<[u8; 32]>, Vec<[u8; 32]>)> {
	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let table = SeamTableB256::new(&mut cs);

	let n = children.len();
	let statement = Statement {
		boundaries: vec![],
		table_sizes: vec![n],
	};

	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	let table_witness = witness.init_table(table.table_id, n)?;
	let mut segment = table_witness.full_segment();
	let (g1_digests, roots) = table.populate(&mut segment, children, SeamMode::Honest)?;
	drop(segment);

	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();

	binius_core::constraint_system::validate::validate_witness(&ccs, &[], &witness)
		.map_err(|e| anyhow::anyhow!("honest seam witness failed validate_witness over B256: {e}"))?;

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
	let proof_size = proof.get_proof_size();

	binius_core::constraint_system::verify::<
		U256,
		B256TowerFamily,
		Sha256,
		Sha256Compression,
		HasherChallenger<Sha256>,
	>(&ccs, log_inv_rate, security_bits, &statement.boundaries, proof)?;

	Ok((proof_size, g1_digests, roots))
}

/// Which stage rejected an adversarial witness, and which constraint fired.
#[derive(Debug)]
pub struct SeamRejectReport {
	pub validate_rejected: bool,
	pub validate_error: String,
	pub pipeline_rejected: bool,
	pub pipeline_stage: &'static str,
	pub pipeline_error: String,
}

fn seam_adversarial_reject(
	mode: SeamMode,
	log_inv_rate: usize,
	security_bits: usize,
) -> Result<SeamRejectReport> {
	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let table = SeamTableB256::new(&mut cs);

	let a = [0x11u8; 32];
	let b = [0x22u8; 32];
	let c = [0x33u8; 32];
	let children = vec![((a, b), c)];
	let statement = Statement {
		boundaries: vec![],
		table_sizes: vec![1],
	};

	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	let table_witness = witness.init_table(table.table_id, 1)?;
	let mut segment = table_witness.full_segment();
	table.populate(&mut segment, &children, mode)?;
	drop(segment);

	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();

	let validate = binius_core::constraint_system::validate::validate_witness(&ccs, &[], &witness);
	let validate_rejected = validate.is_err();
	let validate_error = validate.err().map(|e| e.to_string()).unwrap_or_default();

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
	);

	let (pipeline_rejected, pipeline_stage, pipeline_error) = match proof {
		Err(e) => (true, "prove", e.to_string()),
		Ok(proof) => {
			let verify = binius_core::constraint_system::verify::<
				U256,
				B256TowerFamily,
				Sha256,
				Sha256Compression,
				HasherChallenger<Sha256>,
			>(&ccs, log_inv_rate, security_bits, &statement.boundaries, proof);
			match verify {
				Err(e) => (true, "verify", e.to_string()),
				Ok(()) => (false, "none", String::new()),
			}
		}
	};

	Ok(SeamRejectReport {
		validate_rejected,
		validate_error,
		pipeline_rejected,
		pipeline_stage,
		pipeline_error,
	})
}

/// Public wrapper: forged g1->g2 link over B256 (the M2b-2 deliverable).
pub fn forged_link_rejected_b256(
	forged_prefix: [u8; 32],
	log_inv_rate: usize,
	security_bits: usize,
) -> Result<SeamRejectReport> {
	seam_adversarial_reject(
		SeamMode::ForgedPrefix {
			forged: forged_prefix,
		},
		log_inv_rate,
		security_bits,
	)
}

// ============================================================================
// M2b-3 — expose the depth-2 chain ROOT as a PUBLIC BOUNDARY over B256.
// ============================================================================

#[derive(Debug)]
pub struct RootBoundaryOutcome {
	pub root: [u8; 32],
	pub proof_size: usize,
	pub validate_ok: bool,
	pub validate_error: String,
	pub prove_ok: bool,
	pub prove_error: String,
	pub verify_ok: bool,
	pub verify_error: String,
	pub reject_stage: &'static str,
}

impl RootBoundaryOutcome {
	pub fn accepted(&self) -> bool {
		self.reject_stage == "none"
	}
}

/// M2b-3 over B256. Build the honest depth-2 seam for a SINGLE chain, PUSH the g2
/// digest to a channel, and supply `claimed_root` as the channel's public PULL in
/// `Statement.boundaries` (top-field = B256).
pub fn prove_verify_seam_root_boundary_b256(
	children: &[(([u8; 32], [u8; 32]), [u8; 32])],
	claimed_root: [u8; 32],
	log_inv_rate: usize,
	security_bits: usize,
) -> Result<RootBoundaryOutcome> {
	assert_eq!(children.len(), 1, "root-boundary gate is a single depth-2 chain");

	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let root_channel = cs.add_channel("depth2_root");
	let table = SeamTableB256::new_with_root_boundary(&mut cs, root_channel);

	let n = children.len();
	let statement = Statement {
		boundaries: vec![Boundary {
			values: claimed_root_to_boundary_values(claimed_root),
			channel_id: root_channel,
			direction: FlushDirection::Pull,
			multiplicity: 1,
		}],
		table_sizes: vec![n],
	};

	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	let table_witness = witness.init_table(table.table_id, n)?;
	let mut segment = table_witness.full_segment();
	let (_g1, roots) = table.populate(&mut segment, children, SeamMode::Honest)?;
	drop(segment);
	let root = roots[0];

	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();

	let validate = binius_core::constraint_system::validate::validate_witness(
		&ccs,
		&statement.boundaries,
		&witness,
	);
	let validate_ok = validate.is_ok();
	let validate_error = validate.err().map(|e| e.to_string()).unwrap_or_default();

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
	);

	let (proof_size, prove_ok, prove_error, verify_ok, verify_error) = match proof {
		Err(e) => (0, false, e.to_string(), false, String::new()),
		Ok(proof) => {
			let proof_size = proof.get_proof_size();
			let verify = binius_core::constraint_system::verify::<
				U256,
				B256TowerFamily,
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

	Ok(RootBoundaryOutcome {
		root,
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

// ============================================================================
// M2b-4 — in-circuit CROSS-TABLE CHANNEL JOIN over B256.
// ============================================================================

fn bind_padding_and_msg(
	table: &mut Tbl<'_>,
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
	table.assert_zero(format!("{tag}_pad_lane8"), (s[8] - target_lane8) * mask_full);
	for i in 9..=15 {
		table.assert_zero(format!("{tag}_pad_zero_lane{i}"), s[i] * mask_full);
	}
	table.assert_zero(format!("{tag}_pad_lane16"), (s[16] - target_lane16) * mask_full);
	for i in 17..=24 {
		table.assert_zero(format!("{tag}_cap_zero_lane{i}"), s[i] * mask_full);
	}
}

/// Child sub-circuit: `R_child = SHA3-256(A ‖ B)`; pushes `R_child` to `join`.
pub struct ChildTableB256 {
	pub table_id: TableId,
	g: Keccakf,
	msg: [Col<B1, LANE_BITS>; 8],
	mask_full: Col<B1, LANE_BITS>,
	target_lane8: Col<B1, LANE_BITS>,
	target_lane16: Col<B1, LANE_BITS>,
	root_sel: [Col<B1, LANE64_BITS>; 4],
}

impl ChildTableB256 {
	pub fn new(cs: &mut ConstraintSystem<OurB256>, join: ChannelId) -> Self {
		let mut table = cs.add_table("M2b-4 child SHA3-256 over B256 (push root to join)");

		let state_in: StateMatrix<Col<B1, LANE_BITS>> =
			StateMatrix::from_fn(|(x, y)| table.add_committed(format!("in[{x},{y}]")));
		let g = keccak::Keccakf::new(&mut table, state_in.clone());

		let msg: [Col<B1, LANE_BITS>; 8] =
			std::array::from_fn(|i| table.add_committed(format!("msg[{i}]")));
		let mask_full = table.add_constant("mask_full", track0_pattern(MASK_FULL));
		let target_lane8 = table.add_constant("target_lane8", track0_pattern(TARGET_LANE8));
		let target_lane16 = table.add_constant("target_lane16", track0_pattern(TARGET_LANE16));

		let s = state_in.as_inner();
		let binds: Vec<(usize, Col<B1, LANE_BITS>)> = (0..8).map(|i| (i, msg[i])).collect();
		bind_padding_and_msg(&mut table, "child", s, &binds, mask_full, target_lane8, target_lane16);

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

	pub fn populate(&self, seg: &mut Seg<'_>, a: &[u8; 32], b: &[u8; 32]) -> Result<[u8; 32]> {
		let state = padded_state_64(a, b, None);
		self.g.populate_state_in(seg, std::iter::once(&state))?;
		self.g.populate(seg)?;
		let out_states: Vec<StateMatrix<u64>> = self.g.read_state_outs(seg)?.collect();
		let digest = digest_from_state(&out_states[0]);

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
		fill_selected_lanes(seg, &self.root_sel, &out_states)?;
		Ok(digest)
	}
}

/// Parent sub-circuit: `R_parent = SHA3-256(inner_root ‖ D)`; PULLs `inner_root`.
pub struct ParentTableB256 {
	pub table_id: TableId,
	g: Keccakf,
	msg_d: [Col<B1, LANE_BITS>; 4],
	mask_full: Col<B1, LANE_BITS>,
	target_lane8: Col<B1, LANE_BITS>,
	target_lane16: Col<B1, LANE_BITS>,
	inner_sel: [Col<B1, LANE64_BITS>; 4],
	root_sel: Option<[Col<B1, LANE64_BITS>; 4]>,
}

impl ParentTableB256 {
	pub fn new(
		cs: &mut ConstraintSystem<OurB256>,
		join: ChannelId,
		root_channel: Option<ChannelId>,
	) -> Self {
		let mut table = cs.add_table("M2b-4 parent SHA3-256 over B256 (pull inner root from join)");

		let state_in: StateMatrix<Col<B1, LANE_BITS>> =
			StateMatrix::from_fn(|(x, y)| table.add_committed(format!("in[{x},{y}]")));
		let g = keccak::Keccakf::new(&mut table, state_in.clone());

		let msg_d: [Col<B1, LANE_BITS>; 4] =
			std::array::from_fn(|j| table.add_committed(format!("msg_d[{j}]")));
		let mask_full = table.add_constant("mask_full", track0_pattern(MASK_FULL));
		let target_lane8 = table.add_constant("target_lane8", track0_pattern(TARGET_LANE8));
		let target_lane16 = table.add_constant("target_lane16", track0_pattern(TARGET_LANE16));

		let s = state_in.as_inner();
		let binds: Vec<(usize, Col<B1, LANE_BITS>)> = (0..4).map(|j| (4 + j, msg_d[j])).collect();
		bind_padding_and_msg(&mut table, "parent", s, &binds, mask_full, target_lane8, target_lane16);

		let g_in = g.packed_state_in();
		let g_in_inner = g_in.as_inner();
		let (inner_sel, inner_b64) =
			track_lanes_to_b64(&mut table, "inner", g_in_inner, IN_TRACK_INDEX);
		table.pull(join, inner_b64);

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

	pub fn populate(
		&self,
		seg: &mut Seg<'_>,
		inner_root: &[u8; 32],
		d: &[u8; 32],
	) -> Result<[u8; 32]> {
		let state = padded_state_64(inner_root, d, None);
		self.g.populate_state_in(seg, std::iter::once(&state))?;
		self.g.populate(seg)?;
		let out_states: Vec<StateMatrix<u64>> = self.g.read_state_outs(seg)?.collect();
		let digest = digest_from_state(&out_states[0]);

		let in_states = vec![state];
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
		fill_selected_lanes(seg, &self.inner_sel, &in_states)?;
		if let Some(root_sel) = &self.root_sel {
			fill_selected_lanes(seg, root_sel, &out_states)?;
		}
		Ok(digest)
	}
}

#[derive(Clone, Copy, Debug)]
pub enum JoinMode {
	Honest,
	ForgedInnerRoot { forged: [u8; 32] },
}

#[derive(Debug)]
pub struct JoinOutcome {
	pub r_child: [u8; 32],
	pub r_parent: [u8; 32],
	pub proof_size: usize,
	pub validate_ok: bool,
	pub validate_error: String,
	pub prove_ok: bool,
	pub prove_error: String,
	pub verify_ok: bool,
	pub verify_error: String,
	pub reject_stage: &'static str,
}

impl JoinOutcome {
	pub fn accepted(&self) -> bool {
		self.reject_stage == "none"
	}
}

/// Two-table, one-channel child->parent join over B256.
pub fn prove_verify_join_b256(
	a: [u8; 32],
	b: [u8; 32],
	d: [u8; 32],
	mode: JoinMode,
	parent_root_claim: Option<[u8; 32]>,
	log_inv_rate: usize,
	security_bits: usize,
) -> Result<JoinOutcome> {
	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let join = cs.add_channel("join");
	let root_channel = parent_root_claim.map(|_| cs.add_channel("parent_root"));

	let child = ChildTableB256::new(&mut cs, join);
	let parent = ParentTableB256::new(&mut cs, join, root_channel);

	let mut boundaries: Vec<Boundary<OurB256>> = vec![];
	if let (Some(ch), Some(claim)) = (root_channel, parent_root_claim) {
		boundaries.push(Boundary {
			values: claimed_root_to_boundary_values(claim),
			channel_id: ch,
			direction: FlushDirection::Pull,
			multiplicity: 1,
		});
	}
	let statement = Statement {
		boundaries,
		table_sizes: vec![1, 1],
	};

	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);

	let child_tw = witness.init_table(child.table_id, 1)?;
	let mut child_seg = child_tw.full_segment();
	let r_child = child.populate(&mut child_seg, &a, &b)?;
	drop(child_seg);

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

	let validate = binius_core::constraint_system::validate::validate_witness(
		&ccs,
		&statement.boundaries,
		&witness,
	);
	let validate_ok = validate.is_ok();
	let validate_error = validate.err().map(|e| e.to_string()).unwrap_or_default();

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
	);

	let (proof_size, prove_ok, prove_error, verify_ok, verify_error) = match proof {
		Err(e) => (0, false, e.to_string(), false, String::new()),
		Ok(proof) => {
			let proof_size = proof.get_proof_size();
			let verify = binius_core::constraint_system::verify::<
				U256,
				B256TowerFamily,
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
	fn native_chain(a: &[u8; 32], b: &[u8; 32], c: &[u8; 32]) -> ([u8; 32], [u8; 32]) {
		let mut m1 = Vec::with_capacity(64);
		m1.extend_from_slice(a);
		m1.extend_from_slice(b);
		let d1 = native_sha3_256(&m1);
		let mut m2 = Vec::with_capacity(64);
		m2.extend_from_slice(&d1);
		m2.extend_from_slice(c);
		(d1, native_sha3_256(&m2))
	}
	fn native_join(a: &[u8; 32], b: &[u8; 32], d: &[u8; 32]) -> ([u8; 32], [u8; 32]) {
		let mut m1 = Vec::with_capacity(64);
		m1.extend_from_slice(a);
		m1.extend_from_slice(b);
		let r_child = native_sha3_256(&m1);
		let mut m2 = Vec::with_capacity(64);
		m2.extend_from_slice(&r_child);
		m2.extend_from_slice(d);
		(r_child, native_sha3_256(&m2))
	}

	// ---------------------------- M2b-2 seam over B256 -----------------------

	#[test]
	fn seam_over_b256_honest_accepts() {
		let a = [0xAAu8; 32];
		let b = [0xBBu8; 32];
		let c = [0xCCu8; 32];
		let (d1_exp, root_exp) = native_chain(&a, &b, &c);

		let children = vec![((a, b), c)];
		let (proof_size, g1_digests, roots) =
			prove_verify_seam_b256(&children, 1, 128).expect("honest seam over B256 must verify");

		assert_eq!(g1_digests[0], d1_exp, "in-circuit g1 digest over B256 != native");
		assert_eq!(roots[0], root_exp, "in-circuit root over B256 != native");
		assert!(proof_size > 0);
		println!(
			"M2b-2/B256 seam honest ACCEPTS at L1(128): depth-2 chain verified over the 256-bit field; \
			 g1 digest & root match native; proof = {proof_size} bytes"
		);
	}

	#[test]
	fn seam_over_b256_forged_link_rejected() {
		let forged = [0xDEu8; 32];
		let report =
			forged_link_rejected_b256(forged, 1, 128).expect("adversarial harness must run over B256");

		assert!(report.validate_rejected, "SOUNDNESS FAILURE: validate accepted forged link over B256");
		assert!(report.pipeline_rejected, "SOUNDNESS FAILURE: pipeline accepted forged link over B256");
		assert!(
			report.validate_error.contains("seam_g1_to_g2_lane"),
			"reject not isolated to the seam; got: {}",
			report.validate_error
		);
		println!(
			"M2b-2/B256 forged-link REJECTED (isolated to seam) at L1(128):\n  \
			 firing constraint: {}\n  pipeline stage   : {}\n  pipeline error   : {}",
			report.validate_error, report.pipeline_stage, report.pipeline_error
		);
	}

	// ------------------------- M2b-3 root boundary over B256 -----------------

	#[test]
	fn root_boundary_over_b256_correct_accepts() {
		let a = [0xAAu8; 32];
		let b = [0xBBu8; 32];
		let c = [0xCCu8; 32];
		let (_d1, root_exp) = native_chain(&a, &b, &c);

		let children = vec![((a, b), c)];
		let outcome = prove_verify_seam_root_boundary_b256(&children, root_exp, 1, 128)
			.expect("root-boundary harness must run over B256");

		assert_eq!(outcome.root, root_exp, "in-circuit root over B256 != native");
		assert!(
			outcome.accepted(),
			"correct root over B256 rejected at '{}': validate='{}' prove='{}' verify='{}'",
			outcome.reject_stage,
			outcome.validate_error,
			outcome.prove_error,
			outcome.verify_error
		);
		assert!(outcome.proof_size > 0);
		println!(
			"M2b-3/B256 correct-root ACCEPTS at L1(128): root enforced as public boundary (top field = B256); proof = {} bytes",
			outcome.proof_size
		);
	}

	#[test]
	fn root_boundary_over_b256_wrong_rejected() {
		let a = [0xAAu8; 32];
		let b = [0xBBu8; 32];
		let c = [0xCCu8; 32];
		let (_d1, root_exp) = native_chain(&a, &b, &c);

		let mut wrong = root_exp;
		wrong[0] ^= 0x01;

		let children = vec![((a, b), c)];
		let outcome = prove_verify_seam_root_boundary_b256(&children, wrong, 1, 128)
			.expect("root-boundary harness must run over B256");

		assert_eq!(outcome.root, root_exp);
		assert!(
			!outcome.accepted(),
			"SOUNDNESS FAILURE: a WRONG claimed root was ACCEPTED over B256"
		);
		assert!(
			!outcome.verify_ok,
			"SOUNDNESS FAILURE: SHA-256 verify over B256 accepted a wrong claimed root"
		);
		println!(
			"M2b-3/B256 wrong-root REJECTED at stage '{}':\n  validate: ok={} err='{}'\n  verify  : ok={} err='{}'",
			outcome.reject_stage,
			outcome.validate_ok,
			outcome.validate_error,
			outcome.verify_ok,
			outcome.verify_error
		);
	}

	// ---------------------------- M2b-4 join over B256 -----------------------

	#[test]
	fn join_over_b256_honest_accepts() {
		let a = [0xAAu8; 32];
		let b = [0xBBu8; 32];
		let d = [0xDDu8; 32];
		let (rc_exp, rp_exp) = native_join(&a, &b, &d);

		let outcome = prove_verify_join_b256(a, b, d, JoinMode::Honest, None, 1, 128)
			.expect("honest join harness must run over B256");

		assert_eq!(outcome.r_child, rc_exp, "in-circuit R_child over B256 != native");
		assert_eq!(outcome.r_parent, rp_exp, "in-circuit R_parent over B256 != native");
		assert!(
			outcome.accepted(),
			"honest join over B256 rejected at '{}': validate='{}' prove='{}' verify='{}'",
			outcome.reject_stage,
			outcome.validate_error,
			outcome.prove_error,
			outcome.verify_error
		);
		assert!(outcome.proof_size > 0);
		println!(
			"M2b-4/B256 join honest ACCEPTS at L1(128): child->parent channel balanced over the 256-bit field; \
			 R_parent matches native; proof = {} bytes",
			outcome.proof_size
		);
	}

	#[test]
	fn join_over_b256_forged_inner_root_rejected() {
		let a = [0xAAu8; 32];
		let b = [0xBBu8; 32];
		let d = [0xDDu8; 32];
		let (rc_exp, _rp) = native_join(&a, &b, &d);

		let forged = [0xDEu8; 32];
		assert_ne!(forged, rc_exp);

		let outcome =
			prove_verify_join_b256(a, b, d, JoinMode::ForgedInnerRoot { forged }, None, 1, 128)
				.expect("forged-join harness must run over B256");

		assert_eq!(outcome.r_child, rc_exp);
		assert!(
			!outcome.accepted(),
			"SOUNDNESS FAILURE: a FORGED inner root was ACCEPTED over B256"
		);
		assert!(
			!outcome.verify_ok,
			"SOUNDNESS FAILURE: SHA-256 verify over B256 accepted a forged inner root"
		);
		println!(
			"M2b-4/B256 forged-inner-root REJECTED at stage '{}':\n  validate: ok={} err='{}'\n  verify  : ok={} err='{}'",
			outcome.reject_stage,
			outcome.validate_ok,
			outcome.validate_error,
			outcome.verify_ok,
			outcome.verify_error
		);
	}
}

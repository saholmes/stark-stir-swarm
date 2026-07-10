// merkle_air — Tier-B M2: in-circuit SHA-256 Merkle-path verification over B256.
//
// A FRI query opening is a Merkle authentication path: the verifier recomputes the
// path hashes from a leaf up to the committed root and checks equality. The recursive
// master must do that IN-CIRCUIT, so this gadget chains the M1 SHA-256 compression
// (`sha256_air::Sha256Compress`) up an authentication path, selecting child order by
// the query-index bits, and binds the resulting root to a public boundary.
//
// The node hash is binius's `Sha256Compression` 2-to-1: parent = compress256(IV_binius,
// L‖R) with IV_binius = SHA-256("BINIUS SHA-256 COMPRESS"), the 64-byte block = the two
// 32-byte child digests read big-endian, and the digest = the output state cast to
// little-endian bytes. We match it exactly and gate the native reference against the
// real `binius_hash::Sha256Compression`.

use anyhow::Result;
use sha2::{Digest, Sha256};

use binius_core::fiat_shamir::HasherChallenger;
use binius_core::oracle::ShiftVariant;
use binius_field::Field;
use binius_hal::make_portable_backend;
use binius_hash::sha2::Sha256Compression;
use binius_m3::builder::{
	Col, ConstraintSystem, Statement, TableBuilder, TableWitnessSegment, WitnessIndex, B1,
};

use crate::b256_field::{B256TowerFamily, B256 as OurB256, U256};
use crate::nonnative::write_col;
use crate::sha256_air::{
	build_k_cols, build_sha256_core, compress256_ref, populate_sha256_core,
	prove_verify_merkle_compress, Sha256Core, K256,
};

/// Domain-separated compression IV binius uses for its Merkle 2-to-1 (little-endian
/// u32 view of SHA-256("BINIUS SHA-256 COMPRESS")).
pub fn binius_compress_iv() -> [u32; 8] {
	let h = Sha256::digest(b"BINIUS SHA-256 COMPRESS");
	std::array::from_fn(|i| u32::from_le_bytes(h[i * 4..i * 4 + 4].try_into().unwrap()))
}

/// A 32-byte digest as 8 big-endian u32 block words (how `compress256` reads the block).
pub fn digest_to_words(d: &[u8; 32]) -> [u32; 8] {
	std::array::from_fn(|i| u32::from_be_bytes(d[i * 4..i * 4 + 4].try_into().unwrap()))
}

/// The compression output state as a 32-byte digest (little-endian byte cast, matching
/// binius's `must_cast::<[u32;8],[u8;32]>`).
pub fn state_to_digest(s: &[u32; 8]) -> [u8; 32] {
	let mut out = [0u8; 32];
	for i in 0..8 {
		out[i * 4..i * 4 + 4].copy_from_slice(&s[i].to_le_bytes());
	}
	out
}

/// Native binius Merkle node hash: parent = Sha256Compression(left, right).
pub fn merkle_compress(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
	let mut block = [0u32; 16];
	block[..8].copy_from_slice(&digest_to_words(left));
	block[8..].copy_from_slice(&digest_to_words(right));
	state_to_digest(&compress256_ref(&binius_compress_iv(), &block))
}

/// Native reference: fold a leaf up an authentication path to the root. `index` is the
/// leaf's position (bit k selects whether the current node is the RIGHT child at level
/// k), `siblings[k]` the co-path digest at level k.
pub fn merkle_root_from_path(leaf: &[u8; 32], index: usize, siblings: &[[u8; 32]]) -> [u8; 32] {
	let mut acc = *leaf;
	for (k, sib) in siblings.iter().enumerate() {
		acc = if (index >> k) & 1 == 0 {
			merkle_compress(&acc, sib) // current is LEFT child
		} else {
			merkle_compress(sib, &acc) // current is RIGHT child
		};
	}
	acc
}

/// Prove + verify ONE Merkle node hash `parent = Sha256Compression(left, right)`
/// IN-CIRCUIT over B256 (constant-IV SHA-256 compression). Returns `(proof_bytes,
/// parent_digest)`. This is the atomic FRI-query-opening step: the recursive master
/// recomputes each authentication-path node this way.
pub fn prove_verify_merkle_node(left: &[u8; 32], right: &[u8; 32]) -> Result<(usize, [u8; 32])> {
	let mut block = [0u32; 16];
	block[..8].copy_from_slice(&digest_to_words(left));
	block[8..].copy_from_slice(&digest_to_words(right));
	let (size, out_state) = prove_verify_merkle_compress(binius_compress_iv(), &block)?;
	Ok((size, state_to_digest(&out_state)))
}

// ---- M2b: the in-circuit authentication PATH (one proof) -------------------------
//
// D compression nodes inlined in ONE table, column-wired leaf -> root: each node hashes
// the ordered (current, sibling) children (order MUXed by the query-index bit) with the
// M1 compression; between levels a byte-swap converts the little-endian output digest
// into the big-endian block words the next node reads (binius's Merkle endianness).
// One proof verifies the whole path — the O(1)-in-depth check the recursive master needs.

fn u32_bits(v: u32) -> Vec<bool> {
	(0..32).map(|k| (v >> k) & 1 == 1).collect()
}
fn wc(seg: &mut TableWitnessSegment<OurB256>, col: Col<B1, 32>, row: usize, v: u32) -> Result<()> {
	write_col::<32>(seg, col, row, &u32_bits(v))
}

/// A byte-swap (endianness bridge) of one 32-bit word: out = reverse_bytes(x).
#[derive(Clone, Copy)]
struct BSwap {
	s24: Col<B1, 32>,
	s8: Col<B1, 32>,
	r8: Col<B1, 32>,
	r24: Col<B1, 32>,
	out: Col<B1, 32>,
}

impl BSwap {
	fn build(
		t: &mut TableBuilder<OurB256>,
		x: Col<B1, 32>,
		m1: Col<B1, 32>, // 0x0000_FF00
		m2: Col<B1, 32>, // 0x00FF_0000
		nm: &str,
	) -> Self {
		let s24 = t.add_shifted(format!("{nm}_s24"), x, 5, 24, ShiftVariant::LogicalLeft);
		let s8 = t.add_shifted(format!("{nm}_s8"), x, 5, 8, ShiftVariant::LogicalLeft);
		let r8 = t.add_shifted(format!("{nm}_r8"), x, 5, 8, ShiftVariant::LogicalRight);
		let r24 = t.add_shifted(format!("{nm}_r24"), x, 5, 24, ShiftVariant::LogicalRight);
		// reverse_bytes(x) = (x<<24) | (x<<8 & 0xFF0000) | (x>>8 & 0xFF00) | (x>>24)
		let out = t.add_computed(format!("{nm}_bswap"), s24 + s8 * m2 + r8 * m1 + r24);
		Self { s24, s8, r8, r24, out }
	}
	fn populate(&self, seg: &mut TableWitnessSegment<OurB256>, row: usize, x: u32) -> Result<()> {
		wc(seg, self.s24, row, x << 24)?;
		wc(seg, self.s8, row, x << 8)?;
		wc(seg, self.r8, row, x >> 8)?;
		wc(seg, self.r24, row, x >> 24)?;
		wc(seg, self.out, row, x.swap_bytes())?;
		Ok(())
	}
}

struct PathNode {
	sib: [Col<B1, 32>; 8],
	b: Col<B1, 1>,
	bcast: Col<B1, 32>,
	bcast_rot: Col<B1, 32>,
	bcast_lane0: Col<B1, 1>,
	block: [Col<B1, 32>; 16],
	core: Sha256Core,
	next_bswap: Option<[BSwap; 8]>, // None on the last level (root is read directly)
}

/// An `depth`-level SHA-256 Merkle authentication path, verified in ONE proof.
pub struct MerklePath {
	pub(crate) table_id: binius_m3::builder::TableId,
	pub(crate) leaf: [Col<B1, 32>; 8],
	nodes: Vec<PathNode>,
	root_state: [Col<B1, 32>; 8],
	// Constant columns (must be populated explicitly).
	ivc: [Col<B1, 32>; 8],
	k_cols: Vec<Col<B1, 32>>,
	m1: Col<B1, 32>,
	m2: Col<B1, 32>,
}

impl MerklePath {
	pub fn build(cs: &mut ConstraintSystem<OurB256>, depth: usize) -> Self {
		let mut table = cs.add_table(format!("sha256 merkle path (depth {depth})"));
		Self::build_in(&mut table, depth)
	}

	/// Add the authentication-path columns onto a CALLER-OWNED table, so a larger circuit
	/// (e.g. the query verifier) can bind the leaf columns to a bridge + fold in the same
	/// table. `build` is the standalone wrapper around this.
	pub(crate) fn build_in(table: &mut TableBuilder<OurB256>, depth: usize) -> Self {
		let k_cols = build_k_cols(table);
		// Constant IV columns (binius compress IV) + byte masks.
		let iv = binius_compress_iv();
		let ivc: [Col<B1, 32>; 8] = std::array::from_fn(|i| {
			let bits = u32_bits(iv[i]);
			let arr: [B1; 32] = std::array::from_fn(|k| if bits[k] { B1::ONE } else { B1::ZERO });
			table.add_constant(format!("iv{i}"), arr)
		});
		let mkmask = |t: &mut TableBuilder<OurB256>, nm: &str, v: u32| {
			let bits = u32_bits(v);
			let arr: [B1; 32] = std::array::from_fn(|k| if bits[k] { B1::ONE } else { B1::ZERO });
			t.add_constant(nm.to_string(), arr)
		};
		let m1 = mkmask(table, "mask_ff00", 0x0000_FF00);
		let m2 = mkmask(table, "mask_ff0000", 0x00FF_0000);

		let leaf: [Col<B1, 32>; 8] =
			std::array::from_fn(|i| table.add_committed::<B1, 32>(format!("leaf{i}")));

		let mut acc = leaf;
		let mut nodes = Vec::with_capacity(depth);
		for k in 0..depth {
			let sib: [Col<B1, 32>; 8] =
				std::array::from_fn(|i| table.add_committed::<B1, 32>(format!("sib{k}_{i}")));
			// index bit b, broadcast to 32 lanes (sound: all lanes equal + lane0 == b).
			let b = table.add_committed::<B1, 1>(format!("b{k}"));
			let bcast = table.add_committed::<B1, 32>(format!("bcast{k}"));
			let bcast_rot =
				table.add_shifted(format!("bcast{k}_rot"), bcast, 5, 1, ShiftVariant::CircularLeft);
			table.assert_zero(format!("bcast{k}_eq"), bcast - bcast_rot);
			let bcast_lane0 = table.add_selected(format!("bcast{k}_l0"), bcast, 0);
			table.assert_zero(format!("bcast{k}_bind"), bcast_lane0 - b);
			// block = order(acc, sib, b): left = b?sib:acc, right = b?acc:sib.
			let block: [Col<B1, 32>; 16] = std::array::from_fn(|j| {
				if j < 8 {
					table.add_computed(format!("blk{k}_{j}"), acc[j] + bcast * (acc[j] + sib[j]))
				} else {
					let j8 = j - 8;
					table.add_computed(format!("blk{k}_{j}"), sib[j8] + bcast * (acc[j8] + sib[j8]))
				}
			});
			let core = build_sha256_core(&mut table.with_namespace(format!("n{k}")), ivc, block, &k_cols);
			let next_bswap = if k < depth - 1 {
				let bs: [BSwap; 8] = std::array::from_fn(|i| {
					BSwap::build(table, core.h_out[i], m1, m2, &format!("bs{k}_{i}"))
				});
				acc = std::array::from_fn(|i| bs[i].out);
				Some(bs)
			} else {
				None
			};
			nodes.push(PathNode { sib, b, bcast, bcast_rot, bcast_lane0, block, core, next_bswap });
		}
		let root_state = nodes[depth - 1].core.h_out;
		MerklePath { table_id: table.id(), leaf, nodes, root_state, ivc, k_cols, m1, m2 }
	}

	pub(crate) fn populate(
		&self,
		seg: &mut TableWitnessSegment<OurB256>,
		row: usize,
		leaf: &[u8; 32],
		index: usize,
		siblings: &[[u8; 32]],
	) -> Result<()> {
		let iv = binius_compress_iv();
		// Constant columns are not auto-filled — populate IV, round keys, byte masks.
		for i in 0..8 {
			wc(seg, self.ivc[i], row, iv[i])?;
		}
		for (t, col) in self.k_cols.iter().enumerate() {
			wc(seg, *col, row, K256[t])?;
		}
		wc(seg, self.m1, row, 0x0000_FF00)?;
		wc(seg, self.m2, row, 0x00FF_0000)?;

		let mut acc = digest_to_words(leaf);
		for (i, &w) in acc.iter().enumerate() {
			wc(seg, self.leaf[i], row, w)?;
		}
		for (k, node) in self.nodes.iter().enumerate() {
			let sib_words = digest_to_words(&siblings[k]);
			for (i, &w) in sib_words.iter().enumerate() {
				wc(seg, node.sib[i], row, w)?;
			}
			let bit = (index >> k) & 1 == 1;
			write_col::<1>(seg, node.b, row, &[bit])?;
			let bmask = if bit { 0xFFFF_FFFFu32 } else { 0 };
			wc(seg, node.bcast, row, bmask)?;
			wc(seg, node.bcast_rot, row, bmask)?;
			write_col::<1>(seg, node.bcast_lane0, row, &[bit])?;
			// block = order(acc, sib, b)
			let mut block = [0u32; 16];
			for j in 0..8 {
				let (lo, hi) = if bit { (sib_words[j], acc[j]) } else { (acc[j], sib_words[j]) };
				block[j] = lo;
				block[8 + j] = hi;
				wc(seg, node.block[j], row, lo)?;
				wc(seg, node.block[8 + j], row, hi)?;
			}
			populate_sha256_core(&node.core, seg, row, &iv, &block)?;
			let out = compress256_ref(&iv, &block);
			if let Some(bs) = &node.next_bswap {
				for i in 0..8 {
					bs[i].populate(seg, row, out[i])?;
				}
				acc = std::array::from_fn(|i| out[i].swap_bytes());
			}
		}
		Ok(())
	}

	pub(crate) fn read_root(&self, seg: &TableWitnessSegment<OurB256>, row: usize) -> Result<[u8; 32]> {
		let mut state = [0u32; 8];
		for i in 0..8 {
			let bits = crate::nonnative::read_col::<32>(seg, self.root_state[i], row)?;
			state[i] = (0..32).fold(0u32, |a, k| a | ((bits[k] as u32) << k));
		}
		Ok(state_to_digest(&state))
	}
}

/// Prove + verify a SHA-256 Merkle authentication path IN-CIRCUIT (one proof); returns
/// `(proof_bytes, recomputed_root)`.
pub fn prove_verify_merkle_path(
	leaf: &[u8; 32],
	index: usize,
	siblings: &[[u8; 32]],
) -> Result<(usize, [u8; 32])> {
	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let path = MerklePath::build(&mut cs, siblings.len());
	let statement = Statement { boundaries: vec![], table_sizes: vec![1] };

	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	let root;
	{
		let tw = witness.init_table(path.table_id, 1)?;
		let mut seg = tw.full_segment();
		path.populate(&mut seg, 0, leaf, index, siblings)?;
		root = path.read_root(&seg, 0)?;
	}
	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();
	binius_core::constraint_system::validate::validate_witness(&ccs, &[], &witness)?;
	let proof = binius_core::constraint_system::prove::<
		U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>, _,
	>(&ccs, 1, 128, &statement.boundaries, witness, &make_portable_backend())?;
	let proof_size = proof.get_proof_size();
	binius_core::constraint_system::verify::<
		U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>,
	>(&ccs, 1, 128, &statement.boundaries, proof)?;
	Ok((proof_size, root))
}

#[cfg(test)]
mod tests {
	use super::*;
	use binius_hash::{sha2::Sha256Compression, PseudoCompressionFunction};

	/// Our native node hash matches the real `binius_hash::Sha256Compression`.
	#[test]
	fn merkle_compress_matches_binius() {
		let compressor = Sha256Compression::default();
		for seed in 0u8..4 {
			let left: [u8; 32] = std::array::from_fn(|i| (i as u8).wrapping_mul(7).wrapping_add(seed));
			let right: [u8; 32] = std::array::from_fn(|i| (i as u8).wrapping_mul(11).wrapping_add(seed ^ 0x5a));
			let want = compressor.compress([left.into(), right.into()]);
			let got = merkle_compress(&left, &right);
			assert_eq!(&got[..], want.as_slice(), "merkle_compress != binius Sha256Compression (seed {seed})");
		}
	}

	/// A path folds to the root of a small tree built with binius's compression.
	#[test]
	fn merkle_path_folds_to_root() {
		let compressor = Sha256Compression::default();
		// 4 leaves -> depth-2 tree.
		let leaves: [[u8; 32]; 4] = std::array::from_fn(|j| std::array::from_fn(|i| (i as u8) ^ (j as u8) << 4 ^ 0x11));
		let n01 = compressor.compress([leaves[0].into(), leaves[1].into()]);
		let n23 = compressor.compress([leaves[2].into(), leaves[3].into()]);
		let root = compressor.compress([n01, n23]);
		let root: [u8; 32] = root.as_slice().try_into().unwrap();
		// path for leaf index 2: level-0 sibling = leaf3, level-1 sibling = n01.
		let sib0: [u8; 32] = leaves[3];
		let sib1: [u8; 32] = n01.as_slice().try_into().unwrap();
		let got = merkle_root_from_path(&leaves[2], 2, &[sib0, sib1]);
		assert_eq!(got, root, "path fold != tree root");
	}

	/// GATE M2a — one Merkle node hash proves+verifies IN-CIRCUIT over B256, output ==
	/// binius `Sha256Compression(left, right)`; a wrong child is REJECTED.
	#[test]
	fn merkle_node_proves_over_b256() {
		let left: [u8; 32] = std::array::from_fn(|i| (i as u8).wrapping_mul(3).wrapping_add(0x10));
		let right: [u8; 32] = std::array::from_fn(|i| (i as u8).wrapping_mul(5).wrapping_add(0x20));
		let want = merkle_compress(&left, &right);
		let (size, got) = prove_verify_merkle_node(&left, &right)
			.expect("Merkle node must PROVE+VERIFY over B256");
		assert_eq!(got, want, "in-circuit Merkle node != binius Sha256Compression");
		// Soundness cross-check: a different right child yields a different node.
		let mut right_bad = right;
		right_bad[0] ^= 1;
		assert_ne!(merkle_compress(&left, &right_bad), want, "node not bound to right child");
		println!(
			"GATE M2a merkle-node: SHA-256 Merkle 2-to-1 (constant IV) PROVES+VERIFIES over B256 \
			 @L1(128); in-circuit parent == binius Sha256Compression; proof = {size} bytes"
		);
	}

	/// GATE M2b — a full depth-2 SHA-256 authentication PATH proves+verifies IN-CIRCUIT
	/// over B256 in ONE proof; the in-circuit root == the native binius Merkle root, and
	/// a corrupted sibling yields a different root (bound to the co-path).
	#[test]
	fn merkle_path_proves_over_b256() {
		let compressor = Sha256Compression::default();
		let leaves: [[u8; 32]; 4] =
			std::array::from_fn(|j| std::array::from_fn(|i| (i as u8).wrapping_mul(9) ^ (j as u8) << 5 ^ 0x33));
		let n01 = compressor.compress([leaves[0].into(), leaves[1].into()]);
		let n23 = compressor.compress([leaves[2].into(), leaves[3].into()]);
		let root_ga = compressor.compress([n01, n23]);
		let root: [u8; 32] = root_ga.as_slice().try_into().unwrap();
		// leaf index 2: level-0 sibling = leaf3, level-1 sibling = n01.
		let sib0 = leaves[3];
		let sib1: [u8; 32] = n01.as_slice().try_into().unwrap();
		let siblings = [sib0, sib1];
		// native cross-check
		assert_eq!(merkle_root_from_path(&leaves[2], 2, &siblings), root);

		let (size, got) = prove_verify_merkle_path(&leaves[2], 2, &siblings)
			.expect("Merkle path must PROVE+VERIFY over B256");
		assert_eq!(got, root, "in-circuit path root != native binius root");
		// binding: a corrupted level-0 sibling changes the root.
		let mut bad = siblings;
		bad[0][0] ^= 1;
		assert_ne!(merkle_root_from_path(&leaves[2], 2, &bad), root, "root not bound to co-path");
		println!(
			"GATE M2b merkle-path: depth-2 SHA-256 authentication path (index-MUX + inter-level \
			 byte-swap) PROVES+VERIFIES over B256 @L1(128) in ONE proof; in-circuit root == \
			 binius Merkle root; proof = {size} bytes"
		);
	}
}

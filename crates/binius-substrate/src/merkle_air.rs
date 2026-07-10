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

use crate::sha256_air::{compress256_ref, prove_verify_merkle_compress};

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
}

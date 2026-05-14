//! Merkle authentication-path verification gadget.
//!
//! # Statement
//!
//! Public:  variant ∈ {SHA3-256, SHA3-384, SHA3-512}, root R, leaf-index i
//! Witness: leaf L, authentication path π = (s₀, s₁, ..., s_{d-1})
//! Claim:   hashing L up the tree using π (selecting left/right at each
//!          level by the bits of i) yields R, i.e. `MerkleVerify(L, π, i) = R`
//!
//! # AIR layout (high level)
//!
//! Each row encodes ONE Merkle hop:
//!
//! ```text
//!   row r:
//!     current_node   ← the running hash so far (= L at row 0)
//!     sibling        ← s_r from the path
//!     index_bit_r    ← bit r of the leaf index (0 = sibling on right; 1 = on left)
//!     left           ← {current_node, sibling} depending on index_bit_r
//!     right          ← the other one
//!     parent         ← SHA-3(left || right)
//!     selector       ← s_merkle(r) = 1 on Merkle-hop rows, 0 elsewhere
//! ```
//!
//! Cross-row threading binds `current_node[r+1] = parent[r]` so each
//! row's output becomes the next row's running hash.
//!
//! Boundary constraints at the tree's leaf and root:
//!   - row 0:    `current_node = L`           (public leaf)
//!   - row d-1:  `parent       = R`           (public root)
//!
//! Each hop's SHA-3 evaluation is delegated to [`crate::sponge_air`]
//! (one absorb block — 97 rows of permutation) inside the same AIR
//! trace.  Total trace for a depth-`d` Merkle path:
//!   `d × (1 merkle-hop row + 97 sponge rows) = d × 98 rows`.
//!
//! # Status
//!
//! Foundation only (types + docs + structural tests).  Real constraint
//! generator + trace synthesiser land in subsequent commits.  The
//! pattern matches [`crate::wrapper_prover`] — prove + verify entry
//! points eventually plus a runnable example
//! `examples/merkle_path_verification.rs`.

use crate::sha3_absorb_air::Sha3Variant;

/// One node in a Merkle tree — opaque hash bytes of the variant's
/// output length.  Stored as `Vec<u8>` for flexibility; in production
/// the AIR will witness these as field-element-encoded bit cells.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct MerkleNode(pub Vec<u8>);

impl MerkleNode {
    pub fn zero(variant: Sha3Variant) -> Self {
        Self(vec![0u8; variant.output_bytes()])
    }

    pub fn from_bytes(bytes: &[u8], variant: Sha3Variant) -> Self {
        assert_eq!(bytes.len(), variant.output_bytes(),
            "MerkleNode: byte length must equal variant.output_bytes()");
        Self(bytes.to_vec())
    }
}

/// The public-statement + private-witness shape for one Merkle path.
#[derive(Clone, Debug)]
pub struct MerklePathClaim {
    pub variant: Sha3Variant,
    /// Public: the root of the tree.
    pub root: MerkleNode,
    /// Public: the leaf's index within the layer (drives left/right at each hop).
    pub leaf_index: u64,
    /// Witness: the leaf value (typically the hash of the prover's actual data).
    pub leaf: MerkleNode,
    /// Witness: authentication path siblings, leaf-side first.
    /// `path.len()` = tree depth.
    pub path: Vec<MerkleNode>,
}

impl MerklePathClaim {
    /// Tree depth = path length.  Each hop verifies one level of the tree.
    pub fn depth(&self) -> usize { self.path.len() }

    /// Sanity-check: all nodes are the right length, leaf_index fits the depth.
    pub fn check_shape(&self) -> Result<(), String> {
        let n = self.variant.output_bytes();
        if self.root.0.len() != n {
            return Err(format!("root has {} bytes, expected {n}", self.root.0.len()));
        }
        if self.leaf.0.len() != n {
            return Err(format!("leaf has {} bytes, expected {n}", self.leaf.0.len()));
        }
        for (i, sib) in self.path.iter().enumerate() {
            if sib.0.len() != n {
                return Err(format!("path[{i}] has {} bytes, expected {n}", sib.0.len()));
            }
        }
        let d = self.depth();
        if d > 0 && d < 64 && self.leaf_index >= (1u64 << d) {
            return Err(format!(
                "leaf_index {} doesn't fit in {} depth bits", self.leaf_index, d
            ));
        }
        Ok(())
    }
}

/// Native reference: verify a Merkle path by hashing the chain.  Used
/// as the oracle for AIR cross-validation (the AIR's emitted root
/// must equal what this function computes from leaf + path + index).
pub fn merkle_verify_native(claim: &MerklePathClaim) -> bool {
    use crate::sha3_absorb_air::hash;
    let mut current = claim.leaf.0.clone();
    let mut idx = claim.leaf_index;
    for sibling in &claim.path {
        // index_bit = 0 → sibling on the right (current is left)
        // index_bit = 1 → sibling on the left  (current is right)
        let (left, right) = if (idx & 1) == 0 {
            (current.as_slice(), sibling.0.as_slice())
        } else {
            (sibling.0.as_slice(), current.as_slice())
        };
        let mut concat = Vec::with_capacity(left.len() + right.len());
        concat.extend_from_slice(left);
        concat.extend_from_slice(right);
        current = hash(claim.variant, &concat);
        idx >>= 1;
    }
    current == claim.root.0
}

/// Build a small Merkle tree from leaves and produce a path for one
/// of them.  Test helper — production code constructs trees via the
/// authority's signing logic, not via this function.
pub fn merkle_build_and_open(
    variant: Sha3Variant,
    leaves: &[MerkleNode],
    open_index: usize,
) -> MerklePathClaim {
    use crate::sha3_absorb_air::hash;
    assert!(open_index < leaves.len());
    assert!(leaves.len().is_power_of_two(),
        "merkle_build_and_open: leaf count must be a power of 2");

    let mut layers: Vec<Vec<MerkleNode>> = vec![leaves.to_vec()];
    while layers.last().unwrap().len() > 1 {
        let prev = layers.last().unwrap();
        let mut next = Vec::with_capacity(prev.len() / 2);
        for pair in prev.chunks(2) {
            let mut concat = Vec::with_capacity(pair[0].0.len() + pair[1].0.len());
            concat.extend_from_slice(&pair[0].0);
            concat.extend_from_slice(&pair[1].0);
            next.push(MerkleNode(hash(variant, &concat)));
        }
        layers.push(next);
    }

    let root = layers.last().unwrap()[0].clone();
    let mut path: Vec<MerkleNode> = Vec::with_capacity(layers.len() - 1);
    let mut idx = open_index;
    for layer in &layers[..layers.len() - 1] {
        let sibling_idx = idx ^ 1;
        path.push(layer[sibling_idx].clone());
        idx /= 2;
    }

    MerklePathClaim {
        variant, root, leaf_index: open_index as u64,
        leaf: leaves[open_index].clone(), path,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fake_leaf(variant: Sha3Variant, byte: u8) -> MerkleNode {
        MerkleNode(vec![byte; variant.output_bytes()])
    }

    #[test]
    fn merkle_node_zero_has_correct_length() {
        for variant in [Sha3Variant::Sha3_256, Sha3Variant::Sha3_384, Sha3Variant::Sha3_512] {
            assert_eq!(MerkleNode::zero(variant).0.len(), variant.output_bytes());
        }
    }

    #[test]
    fn claim_shape_validation() {
        let variant = Sha3Variant::Sha3_256;
        let claim = MerklePathClaim {
            variant,
            root: fake_leaf(variant, 0xAA),
            leaf_index: 0,
            leaf: fake_leaf(variant, 0x11),
            path: vec![fake_leaf(variant, 0x22), fake_leaf(variant, 0x33)],
        };
        assert!(claim.check_shape().is_ok());
        assert_eq!(claim.depth(), 2);
    }

    #[test]
    fn shape_rejects_wrong_root_length() {
        let variant = Sha3Variant::Sha3_256;
        let claim = MerklePathClaim {
            variant,
            root: MerkleNode(vec![0; 5]),  // wrong length
            leaf_index: 0,
            leaf: fake_leaf(variant, 0x11),
            path: vec![],
        };
        assert!(claim.check_shape().is_err());
    }

    #[test]
    fn shape_rejects_leaf_index_out_of_range() {
        let variant = Sha3Variant::Sha3_256;
        let claim = MerklePathClaim {
            variant,
            root: fake_leaf(variant, 0xAA),
            leaf_index: 100,  // depth=2 → max index = 3
            leaf: fake_leaf(variant, 0x11),
            path: vec![fake_leaf(variant, 0x22), fake_leaf(variant, 0x33)],
        };
        assert!(claim.check_shape().is_err());
    }

    #[test]
    fn merkle_build_and_verify_8_leaves() {
        // Build a depth-3 tree, open every leaf, verify each path.
        let variant = Sha3Variant::Sha3_256;
        let leaves: Vec<MerkleNode> = (0..8u8)
            .map(|i| fake_leaf(variant, 0x10 + i))
            .collect();

        for open_index in 0..8 {
            let claim = merkle_build_and_open(variant, &leaves, open_index);
            assert!(claim.check_shape().is_ok());
            assert_eq!(claim.depth(), 3);
            assert!(merkle_verify_native(&claim),
                "honest path at index {open_index} must verify");
        }
    }

    #[test]
    fn merkle_native_rejects_tampered_leaf() {
        let variant = Sha3Variant::Sha3_256;
        let leaves: Vec<MerkleNode> = (0..4u8)
            .map(|i| fake_leaf(variant, 0x10 + i))
            .collect();
        let mut claim = merkle_build_and_open(variant, &leaves, 1);
        claim.leaf.0[0] ^= 0xFF;
        assert!(!merkle_verify_native(&claim),
            "tampered leaf must fail native verify");
    }

    #[test]
    fn merkle_native_rejects_tampered_path() {
        let variant = Sha3Variant::Sha3_256;
        let leaves: Vec<MerkleNode> = (0..4u8)
            .map(|i| fake_leaf(variant, 0x10 + i))
            .collect();
        let mut claim = merkle_build_and_open(variant, &leaves, 1);
        claim.path[0].0[0] ^= 0xFF;
        assert!(!merkle_verify_native(&claim),
            "tampered path sibling must fail native verify");
    }

    #[test]
    fn merkle_native_rejects_wrong_index() {
        let variant = Sha3Variant::Sha3_256;
        let leaves: Vec<MerkleNode> = (0..4u8)
            .map(|i| fake_leaf(variant, 0x10 + i))
            .collect();
        let mut claim = merkle_build_and_open(variant, &leaves, 1);
        claim.leaf_index = 2;  // wrong index for this leaf+path
        assert!(!merkle_verify_native(&claim),
            "wrong index must fail native verify");
    }

    #[test]
    fn merkle_works_at_all_variants() {
        for variant in [Sha3Variant::Sha3_256, Sha3Variant::Sha3_384, Sha3Variant::Sha3_512] {
            let leaves: Vec<MerkleNode> = (0..4u8)
                .map(|i| fake_leaf(variant, 0x40 + i))
                .collect();
            let claim = merkle_build_and_open(variant, &leaves, 2);
            assert!(merkle_verify_native(&claim),
                "variant {variant:?} merkle path must verify natively");
        }
    }
}

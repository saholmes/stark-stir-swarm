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

// ─── Row-uniform constraints for one Merkle hop ─────────────────────
//
// The left/right selection at each hop is:
//   left  = (1 - bit) * current_node + bit * sibling
//   right = bit       * current_node + (1 - bit) * sibling
//
// Equivalently (the form we encode as polynomial constraints):
//   left  - current_node - bit · (sibling - current_node) = 0
//   right - sibling      - bit · (current_node - sibling) = 0
//
// Plus booleanity on `bit` and a binding constraint that `parent =
// SHA-3(left || right)` — the latter delegates to `sponge_air` and
// lands in a subsequent commit.
//
// Each "hop" is encoded one bit-position at a time across the hash
// output width.  For SHA-3-256 with 256-bit hashes, that's 256
// (current, sibling, left, right) tuples per hop.

use crate::bit_constraint::{BitOp, CellRef, FieldTraceAccess};
use ark_ff::Field;

/// Column-layout (within one row) for ONE Merkle hop's left/right
/// selection cells.  Hash-output bits are packed contiguously per
/// role (current, sibling, left, right).
#[derive(Clone, Debug)]
pub struct MerkleHopLayout {
    pub row: usize,
    pub n_hash_bits: usize,
    pub current_start: usize,
    pub sibling_start: usize,
    pub left_start:    usize,
    pub right_start:   usize,
    pub bit_col:       usize,   // 1 cell — the index bit for this hop
    pub width:         usize,
}

impl MerkleHopLayout {
    pub fn new(row: usize, col_start: usize, n_hash_bits: usize) -> Self {
        let current_start = col_start;
        let sibling_start = current_start + n_hash_bits;
        let left_start    = sibling_start + n_hash_bits;
        let right_start   = left_start    + n_hash_bits;
        let bit_col       = right_start   + n_hash_bits;
        let width         = bit_col + 1 - col_start;
        Self {
            row, n_hash_bits,
            current_start, sibling_start, left_start, right_start,
            bit_col, width,
        }
    }

    pub fn current_bit(&self, i: usize) -> CellRef {
        debug_assert!(i < self.n_hash_bits);
        CellRef::new(self.row, self.current_start + i)
    }
    pub fn sibling_bit(&self, i: usize) -> CellRef {
        debug_assert!(i < self.n_hash_bits);
        CellRef::new(self.row, self.sibling_start + i)
    }
    pub fn left_bit(&self, i: usize) -> CellRef {
        debug_assert!(i < self.n_hash_bits);
        CellRef::new(self.row, self.left_start + i)
    }
    pub fn right_bit(&self, i: usize) -> CellRef {
        debug_assert!(i < self.n_hash_bits);
        CellRef::new(self.row, self.right_start + i)
    }
    pub fn bit(&self) -> CellRef {
        CellRef::new(self.row, self.bit_col)
    }
}

/// Polynomial constraint specialised for Merkle left/right selection.
/// Encodes the degree-2 identity directly (not via primitive BitOp,
/// because the multiplication includes `bit × (sibling - current)`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MerkleSelOp {
    /// `left - current - bit · (sibling - current) = 0`
    LeftSelect  { left: CellRef, current: CellRef, sibling: CellRef, bit: CellRef },
    /// `right - sibling - bit · (current - sibling) = 0`
    RightSelect { right: CellRef, current: CellRef, sibling: CellRef, bit: CellRef },
}

impl MerkleSelOp {
    pub fn degree(&self) -> usize { 2 }   // bit · X term

    pub fn eval_field<F: Field>(&self, trace: &impl FieldTraceAccess<F>) -> F {
        match *self {
            Self::LeftSelect { left, current, sibling, bit } => {
                let left = trace.get_cell_f(left);
                let cur  = trace.get_cell_f(current);
                let sib  = trace.get_cell_f(sibling);
                let b    = trace.get_cell_f(bit);
                left - cur - b * (sib - cur)
            }
            Self::RightSelect { right, current, sibling, bit } => {
                let right = trace.get_cell_f(right);
                let cur   = trace.get_cell_f(current);
                let sib   = trace.get_cell_f(sibling);
                let b     = trace.get_cell_f(bit);
                right - sib - b * (cur - sib)
            }
        }
    }

    pub fn satisfied_by_field<F: Field>(
        &self, trace: &impl FieldTraceAccess<F>,
    ) -> bool {
        self.eval_field::<F>(trace).is_zero()
    }
}

/// Emit the selection-side constraints for one Merkle hop.  Per bit:
/// 2 selection constraints + 1 booleanity on the bit (only once per hop,
/// emitted only at bit 0 to avoid duplication).  Total:
///   2 · n_hash_bits + 1 = 2N+1 constraints for an N-bit hash hop.
/// Boundary + parent = SHA-3(left || right) come from other generators.
pub fn merkle_hop_selection_constraints(
    layout: &MerkleHopLayout,
) -> (Vec<MerkleSelOp>, Vec<BitOp>) {
    let mut sel = Vec::with_capacity(2 * layout.n_hash_bits);
    let mut bools = Vec::with_capacity(layout.n_hash_bits * 3 + 1);

    for i in 0..layout.n_hash_bits {
        sel.push(MerkleSelOp::LeftSelect {
            left:    layout.left_bit(i),
            current: layout.current_bit(i),
            sibling: layout.sibling_bit(i),
            bit:     layout.bit(),
        });
        sel.push(MerkleSelOp::RightSelect {
            right:   layout.right_bit(i),
            current: layout.current_bit(i),
            sibling: layout.sibling_bit(i),
            bit:     layout.bit(),
        });
        // Booleanity on bit cells participating in the operations.
        bools.push(BitOp::Boolean { b: layout.current_bit(i) });
        bools.push(BitOp::Boolean { b: layout.sibling_bit(i) });
        bools.push(BitOp::Boolean { b: layout.left_bit(i) });
        bools.push(BitOp::Boolean { b: layout.right_bit(i) });
    }
    // The index bit itself.
    bools.push(BitOp::Boolean { b: layout.bit() });

    (sel, bools)
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

    // ─── Merkle hop selection-constraint tests ──────────────────────

    use crate::bit_constraint::FieldMockTrace;
    use ark_goldilocks::Goldilocks;
    use ark_ff::Zero;

    #[test]
    fn hop_layout_width() {
        let layout = MerkleHopLayout::new(0, 0, 256);
        // 4 × 256 + 1 = 1025 cells
        assert_eq!(layout.width, 4 * 256 + 1);
    }

    #[test]
    fn hop_constraint_counts_match_design() {
        let layout = MerkleHopLayout::new(0, 0, 256);
        let (sel, bools) = merkle_hop_selection_constraints(&layout);
        // 2 selection per bit (left+right) + booleanity (4 per bit + 1 indicator)
        assert_eq!(sel.len(), 2 * 256);
        assert_eq!(bools.len(), 4 * 256 + 1);
    }

    #[test]
    fn left_select_satisfied_when_bit_is_zero() {
        // bit=0 → left=current, right=sibling
        let layout = MerkleHopLayout::new(0, 0, 8);  // small hash for test
        let mut trace = FieldMockTrace::<Goldilocks>::zeros(1, layout.width);
        // Set the bit to 0
        trace.set(layout.bit(), Goldilocks::from(0u64));
        // current = 1, sibling = 0, left should be 1, right should be 0
        trace.set(layout.current_bit(0), Goldilocks::from(1u64));
        trace.set(layout.sibling_bit(0), Goldilocks::from(0u64));
        trace.set(layout.left_bit(0),    Goldilocks::from(1u64));   // = current
        trace.set(layout.right_bit(0),   Goldilocks::from(0u64));   // = sibling

        let (sel, _) = merkle_hop_selection_constraints(&layout);
        // Check both constraints at bit 0
        let l = sel[0]; // LeftSelect at bit 0
        let r = sel[1]; // RightSelect at bit 0
        assert!(l.satisfied_by_field::<Goldilocks>(&trace));
        assert!(r.satisfied_by_field::<Goldilocks>(&trace));
    }

    #[test]
    fn left_select_satisfied_when_bit_is_one() {
        // bit=1 → left=sibling, right=current
        let layout = MerkleHopLayout::new(0, 0, 8);
        let mut trace = FieldMockTrace::<Goldilocks>::zeros(1, layout.width);
        trace.set(layout.bit(), Goldilocks::from(1u64));
        trace.set(layout.current_bit(0), Goldilocks::from(1u64));
        trace.set(layout.sibling_bit(0), Goldilocks::from(0u64));
        trace.set(layout.left_bit(0),    Goldilocks::from(0u64));   // = sibling
        trace.set(layout.right_bit(0),   Goldilocks::from(1u64));   // = current

        let (sel, _) = merkle_hop_selection_constraints(&layout);
        assert!(sel[0].satisfied_by_field::<Goldilocks>(&trace));
        assert!(sel[1].satisfied_by_field::<Goldilocks>(&trace));
    }

    #[test]
    fn selection_constraints_reject_swapped_assignment() {
        // bit=0 but prover claims left=sibling, right=current (the
        // bit=1 selection).  Constraints must reject.
        let layout = MerkleHopLayout::new(0, 0, 8);
        let mut trace = FieldMockTrace::<Goldilocks>::zeros(1, layout.width);
        trace.set(layout.bit(), Goldilocks::from(0u64));
        trace.set(layout.current_bit(0), Goldilocks::from(1u64));
        trace.set(layout.sibling_bit(0), Goldilocks::from(0u64));
        // SWAP: left=0 (sibling), right=1 (current) — wrong for bit=0
        trace.set(layout.left_bit(0),    Goldilocks::from(0u64));
        trace.set(layout.right_bit(0),   Goldilocks::from(1u64));

        let (sel, _) = merkle_hop_selection_constraints(&layout);
        assert!(!sel[0].satisfied_by_field::<Goldilocks>(&trace));
        assert!(!sel[1].satisfied_by_field::<Goldilocks>(&trace));
    }

    #[test]
    fn merkle_sel_op_degree_is_two() {
        let r = CellRef::new(0, 0);
        let op = MerkleSelOp::LeftSelect {
            left: r, current: r, sibling: r, bit: r,
        };
        assert_eq!(op.degree(), 2);
    }

    #[test]
    fn hop_layout_at_arbitrary_col_offset() {
        let layout = MerkleHopLayout::new(5, 100, 256);
        assert_eq!(layout.current_bit(0), CellRef::new(5, 100));
        assert_eq!(layout.bit(),
            CellRef::new(5, 100 + 4 * 256));
    }
}

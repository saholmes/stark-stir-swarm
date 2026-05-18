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
    /// **Phase 2.5**: Public per-hop domain-separation prefix bytes.
    /// When non-empty, must have length == `path.len()` and each entry
    /// is prepended to that hop's sponge input (the in-AIR gadget
    /// hashes `ds_prefix_per_hop[hop] || left || right` instead of just
    /// `left || right`).  Matches FRI/STIR Merkle's
    /// `DsLabel.to_bytes()` (32-byte fixed prefix per hop) so the AIR
    /// reproduces `MerkleTreeChannel::verify_opening`'s hash protocol.
    /// Empty Vec is the backward-compatible plain-SHA3 mode.
    pub ds_prefix_per_hop: Vec<Vec<u8>>,
}

impl MerklePathClaim {
    /// Tree depth = path length.  Each hop verifies one level of the tree.
    pub fn depth(&self) -> usize { self.path.len() }

    /// Whether this claim carries per-hop DS prefixes (Phase 2.5 mode).
    pub fn has_ds_prefix(&self) -> bool { !self.ds_prefix_per_hop.is_empty() }

    /// Per-hop DS prefix length in bytes (panics if `has_ds_prefix() == false`).
    pub fn ds_prefix_bytes(&self) -> usize {
        self.ds_prefix_per_hop.first().map(Vec::len).unwrap_or(0)
    }

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
        // Phase 2.5: validate ds_prefix_per_hop shape if present.
        if self.has_ds_prefix() {
            if self.ds_prefix_per_hop.len() != d {
                return Err(format!(
                    "ds_prefix_per_hop has {} entries, expected {d} (= path depth)",
                    self.ds_prefix_per_hop.len()
                ));
            }
            let ds_len = self.ds_prefix_bytes();
            for (i, ds) in self.ds_prefix_per_hop.iter().enumerate() {
                if ds.len() != ds_len {
                    return Err(format!(
                        "ds_prefix_per_hop[{i}] has {} bytes, expected {ds_len} \
                         (DS-prefix length must be uniform across hops)",
                        ds.len()
                    ));
                }
            }
        }
        Ok(())
    }
}

/// Native reference: verify a Merkle path by hashing the chain.  Used
/// as the oracle for AIR cross-validation (the AIR's emitted root
/// must equal what this function computes from leaf + path + index).
///
/// **Phase 2.5**: When `claim.ds_prefix_per_hop` is non-empty, each
/// hop's hash input is `ds_prefix_per_hop[hop] || left || right`
/// (matching FRI/STIR Merkle's `DsLabel`-prefixed `hash_node`).  Else
/// (empty), backward-compatible plain `SHA3(left || right)`.
pub fn merkle_verify_native(claim: &MerklePathClaim) -> bool {
    use crate::sha3_absorb_air::hash;
    if claim.check_shape().is_err() {
        return false;
    }
    let mut current = claim.leaf.0.clone();
    let mut idx = claim.leaf_index;
    let has_ds = claim.has_ds_prefix();
    for (hop, sibling) in claim.path.iter().enumerate() {
        // index_bit = 0 → sibling on the right (current is left)
        // index_bit = 1 → sibling on the left  (current is right)
        let (left, right) = if (idx & 1) == 0 {
            (current.as_slice(), sibling.0.as_slice())
        } else {
            (sibling.0.as_slice(), current.as_slice())
        };
        let ds_bytes: &[u8] = if has_ds {
            &claim.ds_prefix_per_hop[hop]
        } else {
            &[]
        };
        let mut concat = Vec::with_capacity(ds_bytes.len() + left.len() + right.len());
        concat.extend_from_slice(ds_bytes);
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
        ds_prefix_per_hop: Vec::new(),  // backward-compat plain SHA3 mode
    }
}

/// Build a small Merkle tree where each internal-node hash is
/// `SHA3(ds_prefix_per_hop[level] || left || right)` — matching FRI's
/// `DsLabel`-prefixed `hash_node` protocol.  Test helper for
/// DS-aware in-AIR Merkle gadget round-trip verification.
///
/// `ds_prefix_per_hop[level]` is the DS bytes prepended at level
/// `level` (level 0 = first hop above the leaves).
pub fn merkle_build_and_open_with_ds(
    variant: Sha3Variant,
    leaves: &[MerkleNode],
    open_index: usize,
    ds_prefix_per_hop: &[Vec<u8>],
) -> MerklePathClaim {
    use crate::sha3_absorb_air::hash;
    assert!(open_index < leaves.len());
    assert!(leaves.len().is_power_of_two(),
        "merkle_build_and_open_with_ds: leaf count must be a power of 2");
    let depth = leaves.len().trailing_zeros() as usize;
    assert_eq!(ds_prefix_per_hop.len(), depth,
        "ds_prefix_per_hop must have one entry per hop (= log2(leaves.len()))");

    let mut layers: Vec<Vec<MerkleNode>> = vec![leaves.to_vec()];
    let mut level = 0usize;
    while layers.last().unwrap().len() > 1 {
        let prev = layers.last().unwrap();
        let mut next = Vec::with_capacity(prev.len() / 2);
        let ds_bytes = &ds_prefix_per_hop[level];
        for pair in prev.chunks(2) {
            let mut concat = Vec::with_capacity(
                ds_bytes.len() + pair[0].0.len() + pair[1].0.len(),
            );
            concat.extend_from_slice(ds_bytes);
            concat.extend_from_slice(&pair[0].0);
            concat.extend_from_slice(&pair[1].0);
            next.push(MerkleNode(hash(variant, &concat)));
        }
        layers.push(next);
        level += 1;
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
        ds_prefix_per_hop: ds_prefix_per_hop.to_vec(),
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

// ─── Multi-hop layout + trace synthesiser ──────────────────────────
//
// One Merkle hop occupies one trace row in this gadget's layout.
// A depth-`d` path has `d` rows.  Cross-hop threading ensures
// `parent[r] = current[r+1]`, propagating the running hash up the tree.

/// Layout for a depth-`d` Merkle path verification trace.
#[derive(Clone, Debug)]
pub struct MerklePathLayout {
    pub variant: Sha3Variant,
    pub depth: usize,
    pub n_hash_bits: usize,
    /// One column-allocation per row; identical shape across all rows
    /// (different `row` field).  Inlined as `Vec<MerkleHopLayout>` for
    /// clarity; the column allocation is uniform.
    pub hops: Vec<MerkleHopLayout>,
}

impl MerklePathLayout {
    pub fn new(variant: Sha3Variant, depth: usize, row_offset: usize) -> Self {
        let n_hash_bits = variant.output_bits();
        let mut hops = Vec::with_capacity(depth);
        for r in 0..depth {
            hops.push(MerkleHopLayout::new(row_offset + r, 0, n_hash_bits));
        }
        Self { variant, depth, n_hash_bits, hops }
    }

    pub fn row_width(&self) -> usize {
        if self.hops.is_empty() { 0 } else { self.hops[0].width }
    }
}

/// Native trace synthesiser for a Merkle path.  Produces cell values
/// satisfying the selection + threading constraints; the `parent` cells
/// are filled by the NATIVE SHA-3 hash (the AIR's SHA-3 sub-circuit
/// will eventually verify these via composition with sponge_air, but
/// the synthesiser produces the same values either way).
pub fn synthesize_merkle_path_trace(
    claim: &MerklePathClaim,
    layout: &MerklePathLayout,
    trace: &mut crate::bit_constraint::MockTrace,
) -> Result<MerkleNode, String> {
    use crate::sha3_absorb_air::hash;
    claim.check_shape()?;
    if claim.depth() != layout.depth {
        return Err(format!(
            "claim depth {} != layout depth {}", claim.depth(), layout.depth
        ));
    }

    let n_bits = layout.n_hash_bits;
    let mut current = claim.leaf.0.clone();
    let mut idx = claim.leaf_index;

    for (hop_idx, hop) in layout.hops.iter().enumerate() {
        let bit = (idx & 1) as u8;
        let sibling_bytes = &claim.path[hop_idx].0;

        // Write current + sibling bit-by-bit (LE within each byte).
        for i in 0..n_bits {
            let cur_bit = (current[i / 8] >> (i % 8)) & 1;
            let sib_bit = (sibling_bytes[i / 8] >> (i % 8)) & 1;
            trace.set(hop.current_bit(i), cur_bit as u64);
            trace.set(hop.sibling_bit(i), sib_bit as u64);
        }
        trace.set(hop.bit(), bit as u64);

        // Compute left/right per the selection rule + write them.
        let (left_bytes, right_bytes): (&[u8], &[u8]) = if bit == 0 {
            (current.as_slice(), sibling_bytes.as_slice())
        } else {
            (sibling_bytes.as_slice(), current.as_slice())
        };
        for i in 0..n_bits {
            let l_bit = (left_bytes[i / 8] >> (i % 8)) & 1;
            let r_bit = (right_bytes[i / 8] >> (i % 8)) & 1;
            trace.set(hop.left_bit(i), l_bit as u64);
            trace.set(hop.right_bit(i), r_bit as u64);
        }

        // Native hash to produce parent.  In the full AIR, this is
        // delegated to the sponge_air sub-circuit; the synthesiser
        // produces the same value either way.
        let mut concat = Vec::with_capacity(left_bytes.len() + right_bytes.len());
        concat.extend_from_slice(left_bytes);
        concat.extend_from_slice(right_bytes);
        current = hash(layout.variant, &concat);
        idx >>= 1;
    }

    Ok(MerkleNode(current))
}

// ─── Composed layout: Merkle hop + sponge_air sub-trace ─────────────
//
// Each Merkle hop occupies 1 + 97 = 98 trace rows:
//   row 98·r + 0:    merkle-hop row (selection cells + bit)
//   rows 98·r + 1.. : 97 rows of sponge_air absorbing `left || right`
//
// Total trace for depth-d Merkle path:  d × 98 rows.
//
// Cross-row binding (the soundness link between Merkle hop and sponge):
//   - At sponge absorb row (98·r + 1):
//       block_bits[0..N]   = left_bits[0..N]   (from merkle row 98·r)
//       block_bits[N..2N]  = right_bits[0..N]  (from merkle row 98·r)
//   - At sponge final ι row (98·r + 97):
//       state_out's first N bits = parent (becomes current at 98·(r+1))
//
// This commit lands the TYPES + TRACE SYNTHESISER for the composed
// layout.  The constraint generators for the cross-row bindings
// (block_bits ← left||right, parent → next-current) come in the
// following commit, building on the row-uniform infrastructure
// already in `row_uniform.rs`.

use crate::row_uniform::{ROWS_PER_BLOCK, UniformRowSchema, UniformTrace};

/// Composed layout: Merkle path verification using sponge_air for the
/// `parent = SHA-3(left || right)` computation at each hop.
///
/// Uses the existing `UniformRowSchema` (sponge_air's schema) for the
/// sponge sub-trace rows.  The Merkle hop row at the start of each
/// hop block has a small additional column footprint that overlays
/// the unused absorb-row columns (block_bits + state_in are repurposed
/// to hold current/sibling/left/right at the hop row).
#[derive(Clone, Debug)]
pub struct MerkleSpongeLayout {
    pub variant: Sha3Variant,
    pub depth: usize,
    pub schema: UniformRowSchema,
    /// Per-hop starting row in the trace.  Hop `r` starts at
    /// `hop_starts[r]`; sub-rows are at `hop_starts[r] + 1 ..
    /// hop_starts[r] + 98`.
    pub hop_starts: Vec<usize>,
}

impl MerkleSpongeLayout {
    /// Each hop = 1 merkle-hop row + (n_blocks × 97) sponge rows.
    /// For sha3-256/384 with 2N ≤ rate, n_blocks = 1 (single absorb).
    /// For sha3-512 with 2N > rate, n_blocks = 2.
    /// Use [`Self::rows_per_hop`] / [`Self::sponge_blocks_per_hop`]
    /// for variant-aware row math instead of the L1/L3 default
    /// `ROWS_PER_HOP` constant.
    pub const ROWS_PER_HOP: usize = 1 + ROWS_PER_BLOCK;  // 98 for sha3-256/384

    /// Number of SHA-3 absorb blocks needed for one Merkle hop,
    /// computing `parent = SHA-3(left || right)` where each of left
    /// and right is variant.output_bytes() long.
    pub fn sponge_blocks_per_hop(variant: Sha3Variant) -> usize {
        let n_bytes = variant.output_bytes();
        let block_len = variant.block_bytes();
        let input_len = 2 * n_bytes;
        // FIPS 202 padding adds at least 1 byte (0x06) + at most
        // block_len bytes — needs at least one more block when
        // input_len % block_len == 0.
        if input_len < block_len {
            1
        } else {
            // input + padding: ceil((input_len + 1) / block_len)
            (input_len + 1 + block_len - 1) / block_len
        }
    }

    pub fn rows_per_hop(variant: Sha3Variant) -> usize {
        1 + Self::sponge_blocks_per_hop(variant) * ROWS_PER_BLOCK
    }

    pub fn new(variant: Sha3Variant, depth: usize, row_offset: usize) -> Self {
        let schema = UniformRowSchema::new(variant);
        let rows_per_hop = Self::rows_per_hop(variant);
        let hop_starts = (0..depth)
            .map(|r| row_offset + r * rows_per_hop)
            .collect();
        Self { variant, depth, schema, hop_starts }
    }

    pub fn total_rows(&self) -> usize {
        self.depth * Self::rows_per_hop(self.variant)
    }

    pub fn row_width(&self) -> usize {
        self.schema.width
    }

    /// Row index of the FIRST absorb-XOR row for hop `r` (start of
    /// the first sponge block in this hop's sub-trace).
    pub fn sponge_absorb_row(&self, r: usize) -> usize {
        self.hop_starts[r] + 1
    }

    /// Row index of the final ι row (= last permutation row of the
    /// LAST sponge block) for hop `r`.  This is the row whose
    /// state_out carries the `parent = SHA-3(left || right)` value.
    pub fn sponge_final_iota_row(&self, r: usize) -> usize {
        let n_blocks = Self::sponge_blocks_per_hop(self.variant);
        self.hop_starts[r] + n_blocks * ROWS_PER_BLOCK
    }
}

// ─── Merkle hop row cell allocation (within sponge schema) ──────────
//
// The merkle hop row repurposes existing sponge_air columns to hold
// the hop's per-bit cells.  At hop rows:
//   state_in [0..N]    = current_bits   (running hash from prev hop, or leaf)
//   block_bits [0..N]  = sibling_bits   (auth path sibling)
//   state_out [0..N]   = left_bits      (selection result)
//   state_out [N..2N]  = right_bits
//   helpers [0]        = index_bit      (this hop's bit of leaf_index)
//
// All N = variant.output_bits() (256 / 384 / 512).
//
// The next-row binding (cross-row Copy from sponge absorb to merkle
// hop):
//   absorb_row.block_bits [0..2N] ≡ merkle_hop_row.state_out [0..2N]
//
// will be enforced by the constraint generator in the next commit.

/// Address the merkle hop row's `current_bits` cell.
pub fn hop_current_col(schema: &UniformRowSchema, bit: usize) -> usize {
    debug_assert!(bit < schema.state_in.len());
    schema.state_in_bit(bit / 64, bit % 64)
}

/// Address the merkle hop row's `sibling_bits` cell.
pub fn hop_sibling_col(schema: &UniformRowSchema, bit: usize) -> usize {
    debug_assert!(bit < schema.block_bits.len());
    schema.block_bit(bit)
}

/// Address the merkle hop row's `left_bits` cell.
pub fn hop_left_col(schema: &UniformRowSchema, bit: usize) -> usize {
    debug_assert!(bit < schema.state_out.len());
    schema.state_out_bit(bit / 64, bit % 64)
}

/// Address the merkle hop row's `right_bits` cell.  `bit ∈ [0..N)`.
pub fn hop_right_col(schema: &UniformRowSchema, n_hash_bits: usize, bit: usize) -> usize {
    debug_assert!(bit < n_hash_bits);
    // Pack right_bits AFTER left_bits in state_out: lanes (N/64)..(2N/64).
    let lane = (n_hash_bits / 64) + bit / 64;
    let bit_in_lane = bit % 64;
    schema.state_out_bit(lane, bit_in_lane)
}

/// Address the merkle hop row's `index_bit` cell.
pub fn hop_index_bit_col(schema: &UniformRowSchema) -> usize {
    schema.helper_bit(0)
}

/// Synthesise the composed Merkle-path + sponge trace.  Fills every row:
///
/// - Merkle hop row (at `hop_starts[r]`): writes current/sibling/left/
///   right bits + indicator bit into the sponge schema's state_in /
///   block_bits / state_out columns (re-used for Merkle role).  Selector
///   set to a sentinel value (Merkle hop rows are NOT in sponge_air's
///   selector set; the AIR will use a separate `s_merkle` selector
///   wired in by a future commit).
///
/// - Sponge sub-trace (rows `hop_starts[r] + 1 .. hop_starts[r] + 98`):
///   one absorb-XOR row + 96 permutation rows.  Input block is
///   `left || right` padded per FIPS 202; output state's first N bits
///   = parent = hash(left || right).
///
/// Returns the synthesised root (= the final hop's parent).  Must equal
/// `claim.root` on a valid claim.
pub fn synthesize_merkle_sponge_trace(
    claim: &MerklePathClaim,
    layout: &MerkleSpongeLayout,
) -> Result<(UniformTrace, MerkleNode), String> {
    use crate::row_uniform::synthesize_uniform_trace;
    use crate::sha3_absorb_air::hash;

    claim.check_shape()?;
    if claim.depth() != layout.depth {
        return Err(format!(
            "claim depth {} != layout depth {}", claim.depth(), layout.depth
        ));
    }

    let n_bytes = layout.variant.output_bytes();
    let block_bytes = layout.variant.block_bytes();
    let mut current = claim.leaf.0.clone();
    let mut idx = claim.leaf_index;

    // We synthesise sponge sub-trace per hop into a fresh UniformTrace
    // (per-hop) and stitch them into the composed layout's trace.
    let mut composed = UniformTrace::zeros(layout.schema.clone(), layout.total_rows());

    for r in 0..layout.depth {
        let bit = (idx & 1) as u8;
        let sibling_bytes = &claim.path[r].0;
        let (left_bytes, right_bytes): (&[u8], &[u8]) = if bit == 0 {
            (current.as_slice(), sibling_bytes.as_slice())
        } else {
            (sibling_bytes.as_slice(), current.as_slice())
        };

        // 1. Build the SHA-3 sponge input.  Phase 2.5: if the claim
        //    carries DS bytes (FRI/STIR Merkle's DsLabel mode), the
        //    input becomes `ds_bytes || left || right`; else it's the
        //    backward-compat `left || right`.  Padded per FIPS 202.
        let ds_bytes: &[u8] = if claim.has_ds_prefix() {
            &claim.ds_prefix_per_hop[r]
        } else {
            &[]
        };
        let mut sponge_input = Vec::with_capacity(ds_bytes.len() + 2 * n_bytes);
        sponge_input.extend_from_slice(ds_bytes);
        sponge_input.extend_from_slice(left_bytes);
        sponge_input.extend_from_slice(right_bytes);
        let blocks = pad_for_absorb(&sponge_input, layout.variant);
        // Multi-block support: at sha3-256 with DS prefix the input is
        // 32+32+32=96 B (1 block at rate 136 B — unchanged from 64 B).
        // At sha3-384/512, DS prefix could push into a new block — the
        // current MerkleSpongeLayout doesn't yet model that case; fail
        // loudly here if it happens, so M2 stays scoped to sha3-256.
        let expected_blocks = MerkleSpongeLayout::sponge_blocks_per_hop(layout.variant);
        if blocks.len() != expected_blocks {
            return Err(format!(
                "merkle sponge hop block count mismatch: expected {} blocks, \
                 got {} (variant {:?}, ds_prefix_bytes={}) — \
                 DS-mode multi-block is a follow-up (M2 scope: sha3-256 only)",
                expected_blocks, blocks.len(), layout.variant, ds_bytes.len(),
            ));
        }

        // 2. Synthesise the sponge sub-trace (97 rows for 1 block).
        let block_refs: Vec<&[u8]> = blocks.iter().map(|b| b.as_slice()).collect();
        let sub_trace = synthesize_uniform_trace(&block_refs, layout.variant);
        debug_assert_eq!(sub_trace.n_rows, ROWS_PER_BLOCK);

        // 3. Copy the sub-trace into the composed trace, starting at
        //    `hop_starts[r] + 1`.
        let dst_offset = layout.hop_starts[r] + 1;
        for sub_row in 0..sub_trace.n_rows {
            for col in 0..sub_trace.schema.width {
                let v = sub_trace.get(sub_row, col);
                composed.set(dst_offset + sub_row, col, v);
            }
        }

        // 4. Populate the merkle hop row at `hop_starts[r]` with
        //    current / sibling / left / right / bit per the column
        //    allocation in `hop_*_col` helpers.
        let hop_row = layout.hop_starts[r];
        let n_bits = layout.variant.output_bits();
        for i in 0..n_bits {
            let cur_bit = (current[i / 8] >> (i % 8)) & 1;
            let sib_bit = (sibling_bytes[i / 8] >> (i % 8)) & 1;
            let l_bit   = (left_bytes[i / 8]    >> (i % 8)) & 1;
            let r_bit   = (right_bytes[i / 8]   >> (i % 8)) & 1;
            composed.set(hop_row, hop_current_col(&layout.schema, i), cur_bit as u8);
            composed.set(hop_row, hop_sibling_col(&layout.schema, i), sib_bit as u8);
            composed.set(hop_row, hop_left_col(&layout.schema, i),    l_bit as u8);
            composed.set(hop_row, hop_right_col(&layout.schema, n_bits, i), r_bit as u8);
        }
        composed.set(hop_row, hop_index_bit_col(&layout.schema), bit);

        // 5. Update current ← parent for the next hop.
        current = hash(layout.variant, &sponge_input);
        debug_assert_eq!(current.len(), n_bytes);
        let _ = block_bytes;
        idx >>= 1;
    }

    Ok((composed, MerkleNode(current)))
}

/// FIPS 202 §B.2 padding into rate-sized blocks.  Caller-friendly
/// helper used by the Merkle-sponge synthesiser.
fn pad_for_absorb(input: &[u8], variant: Sha3Variant) -> Vec<Vec<u8>> {
    let block_len = variant.block_bytes();
    let mut blocks: Vec<Vec<u8>> = Vec::new();
    let mut offset = 0;
    while offset + block_len <= input.len() {
        blocks.push(input[offset..offset + block_len].to_vec());
        offset += block_len;
    }
    let mut last = vec![0u8; block_len];
    let tail = &input[offset..];
    last[..tail.len()].copy_from_slice(tail);
    last[tail.len()] = 0x06;
    last[block_len - 1] |= 0x80;
    blocks.push(last);
    blocks
}

// ─── Cross-row binding polynomial constraints ────────────────────────
//
// These constraints encode the four invariants validated empirically
// in the previous commit, as polynomials over trace cells with
// explicit (row, col) addressing.  Together they pin the Merkle hop
// row's output to the sponge sub-trace's input AND the sponge
// sub-trace's output to the next hop's input.
//
// The constraints DO reference specific (row, col) cells rather than
// uniform-column shapes — they sit at the boundary between hops and
// fire at specific row offsets.  Soundness in FRI is enforced the
// same way our existing per-cell boundary constraints work: via the
// composed polynomial that includes them with FS-derived α weights.

/// One cross-row Merkle binding constraint.  All variants are
/// Copy-shaped (`dst - src = 0`) with the cells at specific rows.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MerkleCrossRowConstraint {
    /// `block_bits[i]@absorb_row - left[i]@hop_row = 0`
    SpongeInputLeft { sponge_block_col: usize, hop_left_col: usize, absorb_row: usize, hop_row: usize },
    /// `block_bits[N+i]@absorb_row - right[i]@hop_row = 0`
    SpongeInputRight { sponge_block_col: usize, hop_right_col: usize, absorb_row: usize, hop_row: usize },
    /// `state_out[i]@final_iota_row - current[i]@next_hop_row = 0`
    SpongeOutputThreading { state_out_col: usize, next_current_col: usize, final_iota_row: usize, next_hop_row: usize },
    /// **Phase 2.5**: bind one sponge `block_bits[i]@absorb_row` to a
    /// public DS bit value (0 or 1) — `block_bits[i] − ds_bit_value = 0`.
    /// Fires per DS bit at each hop's absorb row.
    SpongeInputDsByte {
        sponge_block_col: usize,
        ds_bit_value: u8,
        absorb_row: usize,
    },
}

impl MerkleCrossRowConstraint {
    /// Evaluate this constraint against a UniformTrace.  Returns the
    /// residue (0 if satisfied).
    pub fn eval(&self, trace: &UniformTrace) -> i128 {
        match *self {
            Self::SpongeInputLeft { sponge_block_col, hop_left_col, absorb_row, hop_row } => {
                let block = trace.get(absorb_row, sponge_block_col) as i128;
                let left  = trace.get(hop_row, hop_left_col) as i128;
                block - left
            }
            Self::SpongeInputRight { sponge_block_col, hop_right_col, absorb_row, hop_row } => {
                let block = trace.get(absorb_row, sponge_block_col) as i128;
                let right = trace.get(hop_row, hop_right_col) as i128;
                block - right
            }
            Self::SpongeOutputThreading { state_out_col, next_current_col, final_iota_row, next_hop_row } => {
                let state_out = trace.get(final_iota_row, state_out_col) as i128;
                let next_curr = trace.get(next_hop_row, next_current_col) as i128;
                state_out - next_curr
            }
            Self::SpongeInputDsByte { sponge_block_col, ds_bit_value, absorb_row } => {
                let block = trace.get(absorb_row, sponge_block_col) as i128;
                block - ds_bit_value as i128
            }
        }
    }

    pub fn satisfied_by(&self, trace: &UniformTrace) -> bool {
        self.eval(trace) == 0
    }

    /// Polynomial degree: all variants are degree-1 (linear Copy or
    /// constant-binding).
    pub fn degree(&self) -> usize { 1 }

    /// **Phase 2.5 helper**: for DS-aware constraints, returns Some
    /// (anchor_row, sponge_block_col, ds_bit_value).  None for the
    /// other variants — they reference trace cells via the existing
    /// pair-shape interpretation.
    pub fn as_ds_byte(&self) -> Option<(usize, usize, u8)> {
        match *self {
            Self::SpongeInputDsByte { absorb_row, sponge_block_col, ds_bit_value } => {
                Some((absorb_row, sponge_block_col, ds_bit_value))
            }
            _ => None,
        }
    }
}

/// Emit ALL cross-row binding constraints for a depth-d Merkle path
/// composed with sponge_air.  **Plain (no-DS) mode** — calls into
/// `merkle_cross_row_constraints_with_ds` with `ds_prefix_per_hop=None`.
pub fn merkle_cross_row_constraints(
    layout: &MerkleSpongeLayout,
) -> Vec<MerkleCrossRowConstraint> {
    merkle_cross_row_constraints_with_ds(layout, None)
}

/// **Phase 2.5**: Emit cross-row binding constraints for a depth-d
/// Merkle path with optional per-hop DS prefix.  Per hop:
///   - If DS prefix is set: `ds_bits` constraints binding
///     `block_bits[0..ds_bits]` to the public DS bit values
///     (`SpongeInputDsByte`).
///   - N constraints for `block_bits[ds_bits..ds_bits+N] = left[0..N]`
///     (SpongeInputLeft, offset by ds_bits when DS is set; ds_bits=0
///     otherwise).
///   - N constraints for `block_bits[ds_bits+N..ds_bits+2N] = right[0..N]`
///     (SpongeInputRight, similarly offset).
///   - (only between hops r and r+1) N constraints for
///     `state_out[0..N] = current[0..N]@next_hop_row`
///     (SpongeOutputThreading) — unchanged by DS mode.
///
/// `ds_prefix_per_hop[r]` is the DS bytes prepended at hop r when DS
/// is enabled.  All entries must have the same byte length.
pub fn merkle_cross_row_constraints_with_ds(
    layout: &MerkleSpongeLayout,
    ds_prefix_per_hop: Option<&[Vec<u8>]>,
) -> Vec<MerkleCrossRowConstraint> {
    let schema = &layout.schema;
    let n_bits = layout.variant.output_bits();
    let ds_bits = ds_prefix_per_hop
        .and_then(|ds| ds.first())
        .map(|v| v.len() * 8)
        .unwrap_or(0);
    let mut out = Vec::with_capacity(
        layout.depth * (ds_bits + 2 * n_bits) + (layout.depth - 1) * n_bits,
    );

    for r in 0..layout.depth {
        let hop_row = layout.hop_starts[r];
        let absorb_row = layout.sponge_absorb_row(r);

        // Phase 2.5: SpongeInputDsByte — bind first ds_bits of block_bits
        // to PUBLIC DS bits at this hop.
        if let Some(ds_per_hop) = ds_prefix_per_hop {
            let ds_bytes = &ds_per_hop[r];
            for byte_idx in 0..ds_bytes.len() {
                let byte_val = ds_bytes[byte_idx];
                for bit_in_byte in 0..8 {
                    let i = byte_idx * 8 + bit_in_byte;
                    let ds_bit = (byte_val >> bit_in_byte) & 1;
                    out.push(MerkleCrossRowConstraint::SpongeInputDsByte {
                        sponge_block_col: schema.block_bit(i),
                        ds_bit_value: ds_bit,
                        absorb_row,
                    });
                }
            }
        }

        // SpongeInputLeft: block_bits[ds_bits + i] = left[i]
        for i in 0..n_bits {
            out.push(MerkleCrossRowConstraint::SpongeInputLeft {
                sponge_block_col: schema.block_bit(ds_bits + i),
                hop_left_col:     hop_left_col(schema, i),
                absorb_row, hop_row,
            });
        }
        // SpongeInputRight: block_bits[ds_bits + N + i] = right[i]
        for i in 0..n_bits {
            out.push(MerkleCrossRowConstraint::SpongeInputRight {
                sponge_block_col: schema.block_bit(ds_bits + n_bits + i),
                hop_right_col:    hop_right_col(schema, n_bits, i),
                absorb_row, hop_row,
            });
        }

        // SpongeOutputThreading: state_out[i] at final ι row = current[i]
        // at next hop row.  Only between consecutive hops.  DS doesn't
        // affect this — the output state still carries the parent hash.
        if r + 1 < layout.depth {
            let final_iota_row = layout.sponge_final_iota_row(r);
            let next_hop_row = layout.hop_starts[r + 1];
            for i in 0..n_bits {
                let lane = i / 64;
                let bit_in_lane = i % 64;
                out.push(MerkleCrossRowConstraint::SpongeOutputThreading {
                    state_out_col: schema.state_out_bit(lane, bit_in_lane),
                    next_current_col: hop_current_col(schema, i),
                    final_iota_row, next_hop_row,
                });
            }
        }
    }

    out
}

// ─── Phase 1: Batched in-AIR Merkle path verification ────────────────
//
// A `BatchedMerklePathClaim` bundles `B` independent Merkle path
// statements that share a `Sha3Variant` and are verified in ONE STARK.
// Each sub-claim may have a different root, leaf, leaf_index, and
// depth — the batched layout stacks each sub-claim's `MerkleSpongeLayout`
// vertically at increasing row offsets and synthesises one composed
// trace.  Cross-row binding constraints fire WITHIN each block; there
// is NO threading between blocks (each path is independent).
//
// This unlocks O(M_paths)-budget binding of FRI Merkle openings at the
// master-recursion layer: instead of M_paths individual `MerklePathProof`
// STARKs (each with its own ~500 KiB FRI overhead), we emit ⌈M/B⌉ batched
// proofs of B paths each.  See `scripts/results/fri-merkle-binding-phase0-design.md`.

/// Statement bundle of B Merkle authentication paths under one variant.
///
/// All B sub-claims share `variant` (different Sha3Variants would mean
/// different sponge schemas → different row widths → unbatchable).
/// Sub-claims may have arbitrary distinct `(root, leaf, leaf_index, path)`
/// and arbitrary depths.
#[derive(Clone, Debug)]
pub struct BatchedMerklePathClaim {
    pub variant: Sha3Variant,
    pub paths: Vec<MerklePathClaim>,
}

impl BatchedMerklePathClaim {
    /// Number of sub-claims in this batch.
    pub fn batch_size(&self) -> usize { self.paths.len() }

    /// Per-sub-claim shape check; mirrors `MerklePathClaim::check_shape`.
    pub fn check_shape(&self) -> Result<(), String> {
        if self.paths.is_empty() {
            return Err("BatchedMerklePathClaim: paths must be non-empty".into());
        }
        for (i, p) in self.paths.iter().enumerate() {
            if p.variant != self.variant {
                return Err(format!(
                    "BatchedMerklePathClaim: paths[{i}].variant {:?} != bundle variant {:?}",
                    p.variant, self.variant
                ));
            }
            p.check_shape().map_err(|e| format!("paths[{i}]: {e}"))?;
        }
        Ok(())
    }
}

/// Native reference: verify every sub-claim's Merkle path.  Used as
/// the oracle for AIR cross-validation — every block's emitted root
/// must equal what this computes from leaf + path + index.
pub fn batched_merkle_verify_native(claim: &BatchedMerklePathClaim) -> bool {
    if claim.check_shape().is_err() {
        return false;
    }
    claim.paths.iter().all(merkle_verify_native)
}

/// Composed layout for a batched B-path Merkle verification.  Holds
/// per-block `MerkleSpongeLayout`s stacked vertically at cumulative
/// row offsets.  The total trace height is the sum of per-block
/// `total_rows`, padded externally to a power of two by the prover.
#[derive(Clone, Debug)]
pub struct BatchedMerklePathLayout {
    pub variant: Sha3Variant,
    /// Per-sub-claim layout, in batch order.  `blocks[j].hop_starts[*]`
    /// are absolute row indices in the composed trace.
    pub blocks: Vec<MerkleSpongeLayout>,
}

impl BatchedMerklePathLayout {
    /// Build a layout that stacks B per-sub-claim `MerkleSpongeLayout`s
    /// vertically.  Block j starts at `row_offset + Σ_{k<j} blocks[k].total_rows()`.
    pub fn new(claim: &BatchedMerklePathClaim, row_offset: usize) -> Self {
        let variant = claim.variant;
        let mut blocks = Vec::with_capacity(claim.paths.len());
        let mut cursor = row_offset;
        for sub in &claim.paths {
            let block = MerkleSpongeLayout::new(variant, sub.depth(), cursor);
            cursor += block.total_rows();
            blocks.push(block);
        }
        Self { variant, blocks }
    }

    /// Number of sub-claims (= batch size B).
    pub fn batch_size(&self) -> usize { self.blocks.len() }

    /// Total trace rows occupied by all B blocks (unpadded).  The prover
    /// pads this to a power of 2 externally.
    pub fn total_rows(&self) -> usize {
        self.blocks.iter().map(MerkleSpongeLayout::total_rows).sum()
    }

    /// Row width (same across all blocks — they share the variant's
    /// `UniformRowSchema`).
    pub fn row_width(&self) -> usize {
        self.blocks.first().map(MerkleSpongeLayout::row_width).unwrap_or(0)
    }

    /// First row of block `j` in the composed trace.
    pub fn block_start_row(&self, j: usize) -> usize {
        self.blocks[j].hop_starts[0]
    }
}

/// Synthesise the composed UniformTrace for a batched Merkle path
/// verification.  Stitches B per-sub-claim sponge sub-traces into one
/// trace, with each block's `MerkleSpongeLayout` already pre-offset.
///
/// Returns the composed trace plus B per-block emitted roots (each
/// must equal the corresponding sub-claim's `root` field on an honest
/// claim).
pub fn synthesize_batched_merkle_sponge_trace(
    claim: &BatchedMerklePathClaim,
    layout: &BatchedMerklePathLayout,
) -> Result<(UniformTrace, Vec<MerkleNode>), String> {
    claim.check_shape()?;
    if claim.paths.len() != layout.blocks.len() {
        return Err(format!(
            "BatchedMerklePathLayout: paths {} != blocks {}",
            claim.paths.len(), layout.blocks.len()
        ));
    }
    if layout.variant != claim.variant {
        return Err(format!(
            "BatchedMerklePathLayout variant {:?} != claim variant {:?}",
            layout.variant, claim.variant
        ));
    }

    let total_rows = layout.total_rows();
    let schema = layout.blocks[0].schema.clone();
    let mut composed = UniformTrace::zeros(schema, total_rows);

    let mut emitted_roots = Vec::with_capacity(claim.paths.len());
    for (j, sub) in claim.paths.iter().enumerate() {
        let block_layout = &layout.blocks[j];
        // Synthesise the sub-claim's trace at offset 0 (block-local rows).
        let block_local_layout = MerkleSpongeLayout::new(
            claim.variant, sub.depth(), 0,
        );
        let (sub_trace, root) =
            synthesize_merkle_sponge_trace(sub, &block_local_layout)?;
        emitted_roots.push(root);

        // Copy sub_trace into composed at this block's absolute row offset.
        let dst_offset = block_layout.hop_starts[0];
        for sub_row in 0..sub_trace.n_rows {
            for col in 0..sub_trace.schema.width {
                let v = sub_trace.get(sub_row, col);
                composed.set(dst_offset + sub_row, col, v);
            }
        }
    }

    Ok((composed, emitted_roots))
}

/// Emit ALL cross-row binding constraints for every block in a batched
/// Merkle path layout.  Constraints address absolute rows (each block's
/// `MerkleSpongeLayout` was constructed at an absolute row offset), so
/// they compose into one combined constraint set without further
/// remapping.  Inter-block threading is INTENTIONALLY absent — each
/// path is a self-contained statement.
///
/// **Plain (no-DS) mode** — calls into
/// `batched_merkle_cross_row_constraints_with_ds` with the claim's
/// `ds_prefix_per_hop` taken into account per block.
pub fn batched_merkle_cross_row_constraints(
    layout: &BatchedMerklePathLayout,
) -> Vec<MerkleCrossRowConstraint> {
    layout.blocks.iter()
        .flat_map(merkle_cross_row_constraints)
        .collect()
}

/// **Phase 2.5**: Emit batched cross-row constraints with optional
/// per-block DS prefixes.  `claim.paths[j].ds_prefix_per_hop` is the
/// per-hop DS bytes for block j.  All blocks must agree on whether DS
/// is set: either ALL blocks carry DS prefixes (Phase 2.5 mode) or
/// NONE do (plain mode).  Mixed mode is rejected.
pub fn batched_merkle_cross_row_constraints_with_ds(
    claim: &BatchedMerklePathClaim,
    layout: &BatchedMerklePathLayout,
) -> Result<Vec<MerkleCrossRowConstraint>, String> {
    if claim.paths.len() != layout.blocks.len() {
        return Err(format!(
            "batched_merkle_cross_row_constraints_with_ds: \
             paths {} != blocks {}",
            claim.paths.len(), layout.blocks.len()
        ));
    }
    let any_ds = claim.paths.iter().any(|p| p.has_ds_prefix());
    let all_ds = claim.paths.iter().all(|p| p.has_ds_prefix());
    if any_ds && !all_ds {
        return Err(
            "batched_merkle_cross_row_constraints_with_ds: \
             mixed DS / no-DS blocks not supported (all-or-nothing)".into()
        );
    }
    let mut out = Vec::new();
    for (block, path) in layout.blocks.iter().zip(&claim.paths) {
        if path.has_ds_prefix() {
            out.extend(merkle_cross_row_constraints_with_ds(
                block, Some(&path.ds_prefix_per_hop),
            ));
        } else {
            out.extend(merkle_cross_row_constraints(block));
        }
    }
    Ok(out)
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
            ds_prefix_per_hop: Vec::new(),
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
            ds_prefix_per_hop: Vec::new(),
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
            ds_prefix_per_hop: Vec::new(),
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

    // ─── Multi-hop trace synthesiser tests ──────────────────────────

    use crate::bit_constraint::{MockTrace, TraceAccess};

    #[test]
    fn synthesized_trace_root_matches_native() {
        // Build a 4-leaf tree (depth=2), open leaf index 2, synthesise
        // the trace, verify the synthesiser's computed root matches
        // the claim's expected root.
        let variant = Sha3Variant::Sha3_256;
        let leaves: Vec<MerkleNode> = (0..4u8).map(|i| fake_leaf(variant, 0x40 + i)).collect();
        let claim = merkle_build_and_open(variant, &leaves, 2);
        let layout = MerklePathLayout::new(variant, claim.depth(), 0);

        let mut trace = MockTrace::zeros(layout.depth, layout.row_width());
        let computed_root = synthesize_merkle_path_trace(&claim, &layout, &mut trace)
            .expect("synthesise must succeed on a valid claim");
        assert_eq!(computed_root, claim.root,
            "synthesiser's computed root must match the claim's expected root");
    }

    #[test]
    fn synthesized_cells_satisfy_selection_constraints() {
        // Build trace + verify EVERY selection constraint at every hop
        // is satisfied with i128 arithmetic (matches Goldilocks for
        // boolean cell values).
        let variant = Sha3Variant::Sha3_256;
        let leaves: Vec<MerkleNode> = (0..8u8).map(|i| fake_leaf(variant, 0x70 + i)).collect();
        let claim = merkle_build_and_open(variant, &leaves, 5);
        let layout = MerklePathLayout::new(variant, claim.depth(), 0);

        let mut trace = MockTrace::zeros(layout.depth, layout.row_width());
        synthesize_merkle_path_trace(&claim, &layout, &mut trace).unwrap();

        let field_trace = crate::bit_constraint::lift_to_field::<Goldilocks>(&trace);
        for hop in &layout.hops {
            let (sel, bools) = merkle_hop_selection_constraints(hop);
            for op in &sel {
                assert!(op.satisfied_by_field::<Goldilocks>(&field_trace),
                    "hop row {} selection constraint failed", hop.row);
            }
            for b in &bools {
                assert!(b.satisfied_by_field(&field_trace),
                    "hop row {} booleanity failed", hop.row);
            }
        }
    }

    #[test]
    fn synthesized_trace_threading_holds() {
        // Cross-hop threading: parent[r] = current[r+1] for every
        // consecutive pair of rows.  Since parent isn't directly a
        // trace column in the current selection-only layout, we check
        // an equivalent property: at row r+1, current bits equal the
        // hash that the trace at row r commits to (the synthesiser's
        // native hash output between hops).
        let variant = Sha3Variant::Sha3_256;
        let leaves: Vec<MerkleNode> = (0..8u8).map(|i| fake_leaf(variant, 0x90 + i)).collect();
        let claim = merkle_build_and_open(variant, &leaves, 3);
        let layout = MerklePathLayout::new(variant, claim.depth(), 0);

        let mut trace = MockTrace::zeros(layout.depth, layout.row_width());
        synthesize_merkle_path_trace(&claim, &layout, &mut trace).unwrap();

        // The synthesiser computes parent natively and feeds it as
        // current at the next row.  Verify the chain by walking the
        // trace bit-by-bit + reading the current_bit pattern.
        use crate::sha3_absorb_air::hash;
        for r in 0..(layout.depth - 1) {
            // Reconstruct left + right bytes from this row's cells.
            let hop = &layout.hops[r];
            let mut left_bytes = vec![0u8; variant.output_bytes()];
            let mut right_bytes = vec![0u8; variant.output_bytes()];
            for i in 0..layout.n_hash_bits {
                let l = trace.get_cell(hop.left_bit(i)) as u8;
                let rv = trace.get_cell(hop.right_bit(i)) as u8;
                left_bytes[i / 8]  |= l << (i % 8);
                right_bytes[i / 8] |= rv << (i % 8);
            }
            let mut concat = Vec::new();
            concat.extend_from_slice(&left_bytes);
            concat.extend_from_slice(&right_bytes);
            let expected_parent = hash(variant, &concat);

            // Next row's current_bits should equal expected_parent bits.
            let next_hop = &layout.hops[r + 1];
            for i in 0..layout.n_hash_bits {
                let actual = trace.get_cell(next_hop.current_bit(i)) as u8;
                let expected = (expected_parent[i / 8] >> (i % 8)) & 1;
                assert_eq!(actual, expected,
                    "threading violated at hop {r}→{}, bit {i}", r + 1);
            }
        }
    }

    #[test]
    fn synthesizer_rejects_mismatched_depth() {
        let variant = Sha3Variant::Sha3_256;
        let leaves: Vec<MerkleNode> = (0..4u8).map(|i| fake_leaf(variant, 0xA0 + i)).collect();
        let claim = merkle_build_and_open(variant, &leaves, 1);  // depth 2
        let layout = MerklePathLayout::new(variant, 3, 0);       // mismatched depth

        let mut trace = MockTrace::zeros(layout.depth, layout.row_width());
        let result = synthesize_merkle_path_trace(&claim, &layout, &mut trace);
        assert!(result.is_err());
    }

    // ─── Composed Merkle + sponge_air tests ─────────────────────────

    use crate::row_uniform::{
        UniformAirConstraints, global_booleanity_constraints,
        state_threading_constraints, selector_pattern,
    };
    use crate::bit_constraint::FieldTraceAccess;

    #[test]
    fn composed_layout_total_rows() {
        let layout = MerkleSpongeLayout::new(Sha3Variant::Sha3_256, 3, 0);
        assert_eq!(MerkleSpongeLayout::ROWS_PER_HOP, 98);
        assert_eq!(layout.total_rows(), 3 * 98);
        assert_eq!(layout.hop_starts, vec![0, 98, 196]);
        assert_eq!(layout.sponge_absorb_row(0), 1);
        assert_eq!(layout.sponge_absorb_row(2), 197);
        assert_eq!(layout.sponge_final_iota_row(0), 97);
        assert_eq!(layout.sponge_final_iota_row(2), 293);
    }

    #[test]
    fn composed_synthesiser_root_matches_claim() {
        // Build a 4-leaf tree, open one, synthesise the composed
        // (Merkle + sponge_air) trace.  The synthesised root must
        // equal the claim's expected root.
        let variant = Sha3Variant::Sha3_256;
        let leaves: Vec<MerkleNode> = (0..4u8).map(|i| fake_leaf(variant, 0x50 + i)).collect();
        let claim = merkle_build_and_open(variant, &leaves, 2);
        let layout = MerkleSpongeLayout::new(variant, claim.depth(), 0);

        let (_trace, computed_root) = synthesize_merkle_sponge_trace(&claim, &layout)
            .expect("synthesise must succeed");
        assert_eq!(computed_root, claim.root);
    }

    #[test]
    fn composed_trace_has_correct_dimensions() {
        let variant = Sha3Variant::Sha3_256;
        let leaves: Vec<MerkleNode> = (0..8u8).map(|i| fake_leaf(variant, 0x60 + i)).collect();
        let claim = merkle_build_and_open(variant, &leaves, 5);
        let layout = MerkleSpongeLayout::new(variant, claim.depth(), 0);

        let (trace, _) = synthesize_merkle_sponge_trace(&claim, &layout).unwrap();
        assert_eq!(trace.n_rows, layout.total_rows());
        assert_eq!(trace.n_rows, 3 * 98);   // depth=3 × 98 rows
        assert_eq!(trace.width(), layout.row_width());
    }

    #[test]
    fn composed_trace_per_hop_sponge_satisfies_sponge_constraints() {
        // For each hop's sponge sub-trace (97 rows starting at
        // hop_starts[r]+1), the rows satisfy sponge_air's row-uniform
        // constraint set.  This is the soundness check that the
        // composed layout's sponge sub-region is a valid SHA-3
        // computation.
        let variant = Sha3Variant::Sha3_256;
        let leaves: Vec<MerkleNode> = (0..4u8).map(|i| fake_leaf(variant, 0xC0 + i)).collect();
        let claim = merkle_build_and_open(variant, &leaves, 3);
        let layout = MerkleSpongeLayout::new(variant, claim.depth(), 0);

        let (composed, _root) = synthesize_merkle_sponge_trace(&claim, &layout).unwrap();

        // Booleanity over the sponge sub-trace rows must hold (state
        // cells + helpers + selectors are boolean).  We only check
        // the cells that the sponge sub-trace populates — the
        // merkle-hop row (every 98 rows) is unfilled by THIS commit
        // and would fail booleanity if checked, so we skip those rows.
        let bools = global_booleanity_constraints(&layout.schema);
        for r in 0..layout.depth {
            let sub_start = layout.hop_starts[r] + 1;
            let sub_end   = sub_start + ROWS_PER_BLOCK;
            for row in sub_start..sub_end {
                for c in &bools {
                    match c.op {
                        crate::row_uniform::RowUniformOp::Boolean { b: col } => {
                            let v = composed.get(row, col.0);
                            assert!(v == 0 || v == 1,
                                "non-boolean cell at hop {r} sub-row {row} col {}: {v}",
                                col.0);
                        }
                        _ => {}
                    }
                }
            }
        }
    }

    #[test]
    fn composed_synthesiser_rejects_mismatched_depth() {
        let variant = Sha3Variant::Sha3_256;
        let leaves: Vec<MerkleNode> = (0..4u8).map(|i| fake_leaf(variant, 0xD0 + i)).collect();
        let claim = merkle_build_and_open(variant, &leaves, 1);   // depth 2
        let layout = MerkleSpongeLayout::new(variant, 4, 0);      // mismatched
        let result = synthesize_merkle_sponge_trace(&claim, &layout);
        assert!(result.is_err());
    }

    #[test]
    fn composed_works_at_l3_l5_variants() {
        // sha3-384 and sha3-512 — confirm the composed synthesiser
        // doesn't break on larger hash sizes.  At sha3-512 the
        // sponge input 2N = 128 bytes which still fits in one
        // 72-byte... wait, 128 > 72, so it would need 2 blocks.
        // Our current single-block assertion would reject; that's
        // expected and tested below.
        for variant in [Sha3Variant::Sha3_384] {
            let leaves: Vec<MerkleNode> = (0..4u8)
                .map(|i| fake_leaf(variant, 0xE0 + i))
                .collect();
            let claim = merkle_build_and_open(variant, &leaves, 1);
            let layout = MerkleSpongeLayout::new(variant, claim.depth(), 0);

            // For sha3-384: 2N = 96 bytes, block_bytes = 104 → fits in 1 block.
            let (_, root) = synthesize_merkle_sponge_trace(&claim, &layout)
                .expect("sha3-384 single-block hop must succeed");
            assert_eq!(root, claim.root);
        }
    }

    // ─── Merkle hop row + cross-row binding tests ──────────────────

    #[test]
    fn hop_row_cells_match_native_chain() {
        // The hop row's current/sibling/left/right cells must match
        // what the native Merkle chain produces at that hop.
        let variant = Sha3Variant::Sha3_256;
        let leaves: Vec<MerkleNode> = (0..4u8).map(|i| fake_leaf(variant, 0xA8 + i)).collect();
        let claim = merkle_build_and_open(variant, &leaves, 1);
        let layout = MerkleSpongeLayout::new(variant, claim.depth(), 0);
        let (trace, _root) = synthesize_merkle_sponge_trace(&claim, &layout).unwrap();

        let schema = &layout.schema;
        let n_bits = variant.output_bits();

        // Walk the chain natively + compare to hop row cells.
        let mut current = claim.leaf.0.clone();
        let mut idx = claim.leaf_index;
        for r in 0..claim.depth() {
            let bit = (idx & 1) as u8;
            let hop_row = layout.hop_starts[r];

            // current_bits must equal `current` byte-by-byte.
            for i in 0..n_bits {
                let expected = (current[i / 8] >> (i % 8)) & 1;
                let actual = trace.get(hop_row, hop_current_col(schema, i));
                assert_eq!(actual, expected,
                    "hop {r} bit {i}: hop-row current cell {actual} != native {expected}");
            }

            // bit cell matches.
            assert_eq!(trace.get(hop_row, hop_index_bit_col(schema)), bit,
                "hop {r}: bit cell mismatch");

            // Update for next hop.
            let sibling = &claim.path[r].0;
            let mut concat = Vec::with_capacity(current.len() + sibling.len());
            if bit == 0 {
                concat.extend_from_slice(&current);
                concat.extend_from_slice(sibling);
            } else {
                concat.extend_from_slice(sibling);
                concat.extend_from_slice(&current);
            }
            current = crate::sha3_absorb_air::hash(variant, &concat);
            idx >>= 1;
        }
    }

    #[test]
    fn hop_row_left_right_satisfy_selection_constraint() {
        // At each hop row, the left/right cells must satisfy the
        // selection constraint we documented in MerkleSelOp.
        let variant = Sha3Variant::Sha3_256;
        let leaves: Vec<MerkleNode> = (0..8u8).map(|i| fake_leaf(variant, 0xB0 + i)).collect();
        let claim = merkle_build_and_open(variant, &leaves, 5);
        let layout = MerkleSpongeLayout::new(variant, claim.depth(), 0);
        let (trace, _root) = synthesize_merkle_sponge_trace(&claim, &layout).unwrap();

        let schema = &layout.schema;
        let n_bits = variant.output_bits();
        let field_trace = crate::bit_constraint::lift_uniform_to_field::<Goldilocks>(&trace);

        for r in 0..claim.depth() {
            let hop_row = layout.hop_starts[r];
            // For every bit, verify left - current - bit·(sibling - current) = 0.
            for i in 0..n_bits {
                let op = MerkleSelOp::LeftSelect {
                    left:    CellRef::new(hop_row, hop_left_col(schema, i)),
                    current: CellRef::new(hop_row, hop_current_col(schema, i)),
                    sibling: CellRef::new(hop_row, hop_sibling_col(schema, i)),
                    bit:     CellRef::new(hop_row, hop_index_bit_col(schema)),
                };
                assert!(op.satisfied_by_field::<Goldilocks>(&field_trace),
                    "left-select fails at hop {r} bit {i}");

                let op = MerkleSelOp::RightSelect {
                    right:   CellRef::new(hop_row, hop_right_col(schema, n_bits, i)),
                    current: CellRef::new(hop_row, hop_current_col(schema, i)),
                    sibling: CellRef::new(hop_row, hop_sibling_col(schema, i)),
                    bit:     CellRef::new(hop_row, hop_index_bit_col(schema)),
                };
                assert!(op.satisfied_by_field::<Goldilocks>(&field_trace),
                    "right-select fails at hop {r} bit {i}");
            }
        }
    }

    #[test]
    fn cross_row_binding_holds_block_bits_match_left_right() {
        // The cross-row binding invariant: at the sponge absorb row
        // (hop_starts[r] + 1), block_bits[0..2N] must equal the
        // (left || right) bits from the merkle hop row.  This is
        // what the future polynomial constraint will enforce; this
        // test confirms the synthesiser produces a trace satisfying
        // the invariant.
        let variant = Sha3Variant::Sha3_256;
        let leaves: Vec<MerkleNode> = (0..4u8).map(|i| fake_leaf(variant, 0xC8 + i)).collect();
        let claim = merkle_build_and_open(variant, &leaves, 3);
        let layout = MerkleSpongeLayout::new(variant, claim.depth(), 0);
        let (trace, _root) = synthesize_merkle_sponge_trace(&claim, &layout).unwrap();

        let schema = &layout.schema;
        let n_bits = variant.output_bits();

        for r in 0..claim.depth() {
            let hop_row    = layout.hop_starts[r];
            let absorb_row = layout.sponge_absorb_row(r);

            // block_bits[0..N] should match left_bits.
            for i in 0..n_bits {
                let block_i = trace.get(absorb_row, schema.block_bit(i));
                let left_i  = trace.get(hop_row, hop_left_col(schema, i));
                assert_eq!(block_i, left_i,
                    "hop {r} bit {i}: block_bits[{i}] = {block_i} ≠ left[{i}] = {left_i}");
            }
            // block_bits[N..2N] should match right_bits.
            for i in 0..n_bits {
                let block_i = trace.get(absorb_row, schema.block_bit(n_bits + i));
                let right_i = trace.get(hop_row, hop_right_col(schema, n_bits, i));
                assert_eq!(block_i, right_i,
                    "hop {r} bit {i}: block_bits[{}] = {block_i} ≠ right[{i}] = {right_i}",
                    n_bits + i);
            }
        }
    }

    #[test]
    fn cross_row_binding_sponge_output_equals_next_hop_current() {
        // Threading: at the sponge's final ι row (hop_starts[r] + 97),
        // state_out's first N bits must equal the NEXT hop's current_bits.
        let variant = Sha3Variant::Sha3_256;
        let leaves: Vec<MerkleNode> = (0..8u8).map(|i| fake_leaf(variant, 0xD8 + i)).collect();
        let claim = merkle_build_and_open(variant, &leaves, 4);
        let layout = MerkleSpongeLayout::new(variant, claim.depth(), 0);
        let (trace, _root) = synthesize_merkle_sponge_trace(&claim, &layout).unwrap();

        let schema = &layout.schema;
        let n_bits = variant.output_bits();

        for r in 0..(claim.depth() - 1) {
            let sponge_final_row = layout.sponge_final_iota_row(r);
            let next_hop_row     = layout.hop_starts[r + 1];

            for i in 0..n_bits {
                let lane = i / 64;
                let bit_in_lane = i % 64;
                let state_out_bit = trace.get(sponge_final_row, schema.state_out_bit(lane, bit_in_lane));
                let next_current  = trace.get(next_hop_row, hop_current_col(schema, i));
                assert_eq!(state_out_bit, next_current,
                    "hop {}→{}: state_out[{i}] = {} ≠ next current[{i}] = {}",
                    r, r + 1, state_out_bit, next_current);
            }
        }
    }

    // ─── Cross-row binding polynomial constraint tests ─────────────

    #[test]
    fn merkle_cross_row_constraint_count_matches_design() {
        // Per hop: 2N input bindings + (between consecutive hops) N
        // threading bindings.  Total: d·2N + (d-1)·N = (3d-1)·N.
        let variant = Sha3Variant::Sha3_256;
        let layout = MerkleSpongeLayout::new(variant, 4, 0);  // d=4
        let constraints = merkle_cross_row_constraints(&layout);
        let n_bits = variant.output_bits();
        let expected = (3 * 4 - 1) * n_bits;  // (3d-1)·N
        assert_eq!(constraints.len(), expected);
    }

    #[test]
    fn cross_row_constraints_satisfied_on_synthesised_trace() {
        // The headline test: on a valid trace, every cross-row binding
        // constraint must satisfy.  This pins that the synthesiser
        // produces traces where the future polynomial constraints
        // (in the AIR-level prover) will all evaluate to zero.
        let variant = Sha3Variant::Sha3_256;
        let leaves: Vec<MerkleNode> = (0..4u8).map(|i| fake_leaf(variant, 0xE8 + i)).collect();
        let claim = merkle_build_and_open(variant, &leaves, 2);
        let layout = MerkleSpongeLayout::new(variant, claim.depth(), 0);
        let (trace, _root) = synthesize_merkle_sponge_trace(&claim, &layout).unwrap();
        let constraints = merkle_cross_row_constraints(&layout);

        for (i, c) in constraints.iter().enumerate() {
            assert!(c.satisfied_by(&trace),
                "cross-row constraint #{i} = {c:?} residue {}",
                c.eval(&trace));
        }
    }

    #[test]
    fn cross_row_input_tampering_breaks_constraint() {
        // Tamper one block_bits cell at a sponge absorb row.  At
        // least one SpongeInputLeft or SpongeInputRight constraint
        // must reject.
        let variant = Sha3Variant::Sha3_256;
        let leaves: Vec<MerkleNode> = (0..4u8).map(|i| fake_leaf(variant, 0xF1 + i)).collect();
        let claim = merkle_build_and_open(variant, &leaves, 1);
        let layout = MerkleSpongeLayout::new(variant, claim.depth(), 0);
        let (mut trace, _) = synthesize_merkle_sponge_trace(&claim, &layout).unwrap();

        // Flip a block_bits cell at the sponge absorb row of hop 0.
        let absorb_row = layout.sponge_absorb_row(0);
        let block_col  = layout.schema.block_bit(3);
        let original = trace.get(absorb_row, block_col);
        trace.set(absorb_row, block_col, 1 - original);

        let constraints = merkle_cross_row_constraints(&layout);
        let n_failing = constraints.iter().filter(|c| !c.satisfied_by(&trace)).count();
        assert!(n_failing >= 1,
            "input tampering must trip ≥ 1 cross-row constraint");
    }

    #[test]
    fn cross_row_threading_tampering_breaks_constraint() {
        // Tamper a state_out cell at a sponge final ι row.  At least
        // one SpongeOutputThreading constraint must reject.
        let variant = Sha3Variant::Sha3_256;
        let leaves: Vec<MerkleNode> = (0..8u8).map(|i| fake_leaf(variant, 0x14 + i)).collect();
        let claim = merkle_build_and_open(variant, &leaves, 3);
        let layout = MerkleSpongeLayout::new(variant, claim.depth(), 0);
        let (mut trace, _) = synthesize_merkle_sponge_trace(&claim, &layout).unwrap();

        // Flip a state_out cell at the final ι row of hop 0.
        let final_iota = layout.sponge_final_iota_row(0);
        let state_col = layout.schema.state_out_bit(0, 7);
        let original = trace.get(final_iota, state_col);
        trace.set(final_iota, state_col, 1 - original);

        let constraints = merkle_cross_row_constraints(&layout);
        let n_failing = constraints.iter().filter(|c| !c.satisfied_by(&trace)).count();
        assert!(n_failing >= 1,
            "threading tampering must trip ≥ 1 cross-row constraint");
    }

    #[test]
    fn cross_row_constraint_degrees_are_linear() {
        let layout = MerkleSpongeLayout::new(Sha3Variant::Sha3_256, 2, 0);
        for c in merkle_cross_row_constraints(&layout) {
            assert_eq!(c.degree(), 1,
                "all cross-row Merkle bindings are Copy-shaped (degree 1)");
        }
    }

    #[test]
    fn cross_row_constraints_at_l3_l5_variants() {
        // Confirm constraint counts scale with N for sha3-384/512.
        for variant in [Sha3Variant::Sha3_384] {
            let layout = MerkleSpongeLayout::new(variant, 3, 0);
            let constraints = merkle_cross_row_constraints(&layout);
            let n_bits = variant.output_bits();
            let expected = (3 * 3 - 1) * n_bits;
            assert_eq!(constraints.len(), expected,
                "variant {variant:?}");
        }
    }

    #[test]
    fn composed_synthesiser_supports_sha3_512_multi_block() {
        // sha3-512: 2N = 128 bytes > 72-byte block → 2 absorb blocks
        // per hop.  This used to error out with "single-block expected";
        // now supported.
        let variant = Sha3Variant::Sha3_512;
        let leaves: Vec<MerkleNode> = (0..2u8)
            .map(|i| fake_leaf(variant, 0xF0 + i))
            .collect();
        let claim = merkle_build_and_open(variant, &leaves, 0);
        let layout = MerkleSpongeLayout::new(variant, claim.depth(), 0);

        // Verify layout reflects the multi-block hop sizing.
        assert_eq!(
            MerkleSpongeLayout::sponge_blocks_per_hop(variant), 2,
            "sha3-512 should need 2 absorb blocks for 128-byte left||right"
        );
        let rows_per_hop = MerkleSpongeLayout::rows_per_hop(variant);
        assert_eq!(rows_per_hop, 1 + 2 * ROWS_PER_BLOCK,
            "rows_per_hop should be 1 + 2*97 = 195 for sha3-512");

        // Synthesise successfully + compute the right root.
        let (_, root) = synthesize_merkle_sponge_trace(&claim, &layout)
            .expect("sha3-512 multi-block hop must succeed");
        assert_eq!(root, claim.root);
    }

    #[test]
    fn sponge_blocks_per_hop_per_variant() {
        // L1 (sha3-256): 2N=64, rate=136 → 1 block (64 + 1 padding ≤ 136)
        // L3 (sha3-384): 2N=96, rate=104 → 1 block (96 + 1 padding ≤ 104)
        // L5 (sha3-512): 2N=128, rate=72 → 2 blocks (128+1 padding > 72)
        assert_eq!(MerkleSpongeLayout::sponge_blocks_per_hop(Sha3Variant::Sha3_256), 1);
        assert_eq!(MerkleSpongeLayout::sponge_blocks_per_hop(Sha3Variant::Sha3_384), 1);
        assert_eq!(MerkleSpongeLayout::sponge_blocks_per_hop(Sha3Variant::Sha3_512), 2);
    }

    #[test]
    fn rows_per_hop_per_variant() {
        assert_eq!(MerkleSpongeLayout::rows_per_hop(Sha3Variant::Sha3_256), 98);
        assert_eq!(MerkleSpongeLayout::rows_per_hop(Sha3Variant::Sha3_384), 98);
        assert_eq!(MerkleSpongeLayout::rows_per_hop(Sha3Variant::Sha3_512), 195);
    }

    // ─── Phase 1: BatchedMerklePathClaim structural tests ───────────

    #[test]
    fn batched_merkle_claim_empty_rejects() {
        let claim = BatchedMerklePathClaim {
            variant: Sha3Variant::Sha3_256,
            paths: vec![],
        };
        assert!(claim.check_shape().is_err(),
            "empty batched claim must fail shape check");
        assert!(!batched_merkle_verify_native(&claim),
            "empty batched claim cannot native-verify");
    }

    #[test]
    fn batched_merkle_claim_b2_native_verifies() {
        let variant = Sha3Variant::Sha3_256;
        let leaves_a = vec![fake_leaf(variant, 0xAA), fake_leaf(variant, 0xBB),
                            fake_leaf(variant, 0xCC), fake_leaf(variant, 0xDD)];
        let leaves_b = vec![fake_leaf(variant, 0x11), fake_leaf(variant, 0x22),
                            fake_leaf(variant, 0x33), fake_leaf(variant, 0x44)];
        let claim_a = merkle_build_and_open(variant, &leaves_a, 1);
        let claim_b = merkle_build_and_open(variant, &leaves_b, 3);
        let batched = BatchedMerklePathClaim {
            variant,
            paths: vec![claim_a, claim_b],
        };
        assert!(batched.check_shape().is_ok());
        assert_eq!(batched.batch_size(), 2);
        assert!(batched_merkle_verify_native(&batched),
            "B=2 batched claim must native-verify");
    }

    #[test]
    fn batched_merkle_claim_mixed_depth_native_verifies() {
        // Different depths in one batch: B=3 with depths 2, 3, 2.
        let variant = Sha3Variant::Sha3_256;
        let leaves_d2 = vec![fake_leaf(variant, 0x10), fake_leaf(variant, 0x20),
                             fake_leaf(variant, 0x30), fake_leaf(variant, 0x40)];
        let leaves_d3: Vec<MerkleNode> = (0..8)
            .map(|i| fake_leaf(variant, 0x80 | i as u8))
            .collect();
        let leaves_d2b = vec![fake_leaf(variant, 0xF1), fake_leaf(variant, 0xF2),
                              fake_leaf(variant, 0xF3), fake_leaf(variant, 0xF4)];

        let batched = BatchedMerklePathClaim {
            variant,
            paths: vec![
                merkle_build_and_open(variant, &leaves_d2,  0),  // depth 2
                merkle_build_and_open(variant, &leaves_d3,  5),  // depth 3
                merkle_build_and_open(variant, &leaves_d2b, 2),  // depth 2
            ],
        };
        assert_eq!(batched.paths[0].depth(), 2);
        assert_eq!(batched.paths[1].depth(), 3);
        assert_eq!(batched.paths[2].depth(), 2);
        assert!(batched_merkle_verify_native(&batched),
            "B=3 mixed-depth batched claim must native-verify");
    }

    #[test]
    fn batched_merkle_claim_mismatched_variant_rejects() {
        let claim_256 = merkle_build_and_open(
            Sha3Variant::Sha3_256,
            &[fake_leaf(Sha3Variant::Sha3_256, 1),
              fake_leaf(Sha3Variant::Sha3_256, 2)],
            0,
        );
        let claim_384 = merkle_build_and_open(
            Sha3Variant::Sha3_384,
            &[fake_leaf(Sha3Variant::Sha3_384, 1),
              fake_leaf(Sha3Variant::Sha3_384, 2)],
            0,
        );
        let batched = BatchedMerklePathClaim {
            variant: Sha3Variant::Sha3_256,
            paths: vec![claim_256, claim_384],
        };
        assert!(batched.check_shape().is_err(),
            "mixed-variant batched claim must fail shape check");
    }

    #[test]
    fn batched_merkle_layout_b2_geometry() {
        let variant = Sha3Variant::Sha3_256;
        let leaves_a = vec![fake_leaf(variant, 0xAA), fake_leaf(variant, 0xBB),
                            fake_leaf(variant, 0xCC), fake_leaf(variant, 0xDD)];
        let leaves_b = vec![fake_leaf(variant, 0x11), fake_leaf(variant, 0x22),
                            fake_leaf(variant, 0x33), fake_leaf(variant, 0x44)];
        let claim = BatchedMerklePathClaim {
            variant,
            paths: vec![
                merkle_build_and_open(variant, &leaves_a, 1),  // depth 2
                merkle_build_and_open(variant, &leaves_b, 3),  // depth 2
            ],
        };
        let layout = BatchedMerklePathLayout::new(&claim, /*row_offset=*/0);

        assert_eq!(layout.batch_size(), 2);
        // Each block at depth=2 occupies 2 × 98 = 196 rows.
        assert_eq!(layout.blocks[0].total_rows(), 196);
        assert_eq!(layout.blocks[1].total_rows(), 196);
        // Block 0 starts at row 0, block 1 at row 196.
        assert_eq!(layout.block_start_row(0), 0);
        assert_eq!(layout.block_start_row(1), 196);
        assert_eq!(layout.total_rows(), 392);
        // Shared schema → consistent row width.
        assert_eq!(layout.row_width(), layout.blocks[0].row_width());
    }

    #[test]
    fn batched_merkle_layout_mixed_depth_geometry() {
        // Depths 2 + 3 + 2 — total = 196 + 294 + 196 = 686 rows.
        let variant = Sha3Variant::Sha3_256;
        let leaves_d2 = vec![fake_leaf(variant, 0x10), fake_leaf(variant, 0x20),
                             fake_leaf(variant, 0x30), fake_leaf(variant, 0x40)];
        let leaves_d3: Vec<MerkleNode> = (0..8)
            .map(|i| fake_leaf(variant, 0x80 | i as u8))
            .collect();
        let leaves_d2b = vec![fake_leaf(variant, 0xF1), fake_leaf(variant, 0xF2),
                              fake_leaf(variant, 0xF3), fake_leaf(variant, 0xF4)];
        let claim = BatchedMerklePathClaim {
            variant,
            paths: vec![
                merkle_build_and_open(variant, &leaves_d2,  0),
                merkle_build_and_open(variant, &leaves_d3,  5),
                merkle_build_and_open(variant, &leaves_d2b, 2),
            ],
        };
        let layout = BatchedMerklePathLayout::new(&claim, /*row_offset=*/0);
        assert_eq!(layout.block_start_row(0), 0);
        assert_eq!(layout.block_start_row(1), 196);
        assert_eq!(layout.block_start_row(2), 196 + 294);
        assert_eq!(layout.total_rows(), 196 + 294 + 196);
    }

    #[test]
    fn batched_merkle_trace_b2_emits_correct_roots() {
        let variant = Sha3Variant::Sha3_256;
        let leaves_a = vec![fake_leaf(variant, 0xAA), fake_leaf(variant, 0xBB),
                            fake_leaf(variant, 0xCC), fake_leaf(variant, 0xDD)];
        let leaves_b = vec![fake_leaf(variant, 0x11), fake_leaf(variant, 0x22),
                            fake_leaf(variant, 0x33), fake_leaf(variant, 0x44)];
        let claim_a = merkle_build_and_open(variant, &leaves_a, 1);
        let claim_b = merkle_build_and_open(variant, &leaves_b, 3);
        let expected_root_a = claim_a.root.clone();
        let expected_root_b = claim_b.root.clone();
        let batched = BatchedMerklePathClaim {
            variant, paths: vec![claim_a, claim_b],
        };
        let layout = BatchedMerklePathLayout::new(&batched, 0);
        let (trace, roots) = synthesize_batched_merkle_sponge_trace(&batched, &layout)
            .expect("B=2 batched trace must synthesise");

        assert_eq!(roots.len(), 2);
        assert_eq!(roots[0], expected_root_a, "block 0 emitted root must match claim");
        assert_eq!(roots[1], expected_root_b, "block 1 emitted root must match claim");
        assert_eq!(trace.n_rows, layout.total_rows());
    }

    #[test]
    fn batched_merkle_cross_row_constraints_all_satisfied_on_honest_trace() {
        let variant = Sha3Variant::Sha3_256;
        let leaves_a = vec![fake_leaf(variant, 0xAA), fake_leaf(variant, 0xBB),
                            fake_leaf(variant, 0xCC), fake_leaf(variant, 0xDD)];
        let leaves_b = vec![fake_leaf(variant, 0x11), fake_leaf(variant, 0x22),
                            fake_leaf(variant, 0x33), fake_leaf(variant, 0x44)];
        let batched = BatchedMerklePathClaim {
            variant,
            paths: vec![
                merkle_build_and_open(variant, &leaves_a, 1),
                merkle_build_and_open(variant, &leaves_b, 3),
            ],
        };
        let layout = BatchedMerklePathLayout::new(&batched, 0);
        let (trace, _roots) = synthesize_batched_merkle_sponge_trace(&batched, &layout)
            .expect("trace must synthesise");
        let constraints = batched_merkle_cross_row_constraints(&layout);
        assert!(!constraints.is_empty(),
            "batched layout must emit at least some cross-row constraints");
        for (i, c) in constraints.iter().enumerate() {
            assert!(c.satisfied_by(&trace),
                "honest trace violates batched cross-row constraint {i}: {c:?}");
        }
    }

    // ─── Phase 2.5 Milestone 1: DS-aware native verify tests ──────

    fn fake_ds_bytes(arity: u64, level: u32, position: u64, tree_label: u64) -> Vec<u8> {
        let mut out = Vec::with_capacity(32);
        out.extend_from_slice(&arity.to_le_bytes());
        out.extend_from_slice(&(level as u64).to_le_bytes());
        out.extend_from_slice(&position.to_le_bytes());
        out.extend_from_slice(&tree_label.to_le_bytes());
        out
    }

    #[test]
    fn ds_aware_merkle_build_and_open_round_trip_depth_2() {
        let variant = Sha3Variant::Sha3_256;
        let leaves = vec![
            fake_leaf(variant, 0xAA), fake_leaf(variant, 0xBB),
            fake_leaf(variant, 0xCC), fake_leaf(variant, 0xDD),
        ];
        // 2 hops at arity-2 tree_label=7
        let ds_per_hop = vec![
            fake_ds_bytes(2, 1, 0, 7),
            fake_ds_bytes(2, 2, 0, 7),
        ];
        let claim = merkle_build_and_open_with_ds(variant, &leaves, 1, &ds_per_hop);
        assert_eq!(claim.depth(), 2);
        assert!(claim.has_ds_prefix());
        assert_eq!(claim.ds_prefix_bytes(), 32);
        assert!(claim.check_shape().is_ok());
        assert!(merkle_verify_native(&claim),
            "DS-aware native verify must accept honest claim");
    }

    #[test]
    fn ds_aware_merkle_build_and_open_round_trip_depth_3() {
        let variant = Sha3Variant::Sha3_256;
        let leaves: Vec<MerkleNode> = (0..8)
            .map(|i| fake_leaf(variant, 0x80 | i as u8))
            .collect();
        let ds_per_hop = vec![
            fake_ds_bytes(2, 1, 0, 42),
            fake_ds_bytes(2, 2, 0, 42),
            fake_ds_bytes(2, 3, 0, 42),
        ];
        let claim = merkle_build_and_open_with_ds(variant, &leaves, 5, &ds_per_hop);
        assert_eq!(claim.depth(), 3);
        assert!(merkle_verify_native(&claim));
    }

    #[test]
    fn ds_aware_native_verify_rejects_wrong_ds_prefix() {
        let variant = Sha3Variant::Sha3_256;
        let leaves = vec![
            fake_leaf(variant, 0xAA), fake_leaf(variant, 0xBB),
            fake_leaf(variant, 0xCC), fake_leaf(variant, 0xDD),
        ];
        let ds_per_hop = vec![
            fake_ds_bytes(2, 1, 0, 7),
            fake_ds_bytes(2, 2, 0, 7),
        ];
        let mut claim = merkle_build_and_open_with_ds(variant, &leaves, 1, &ds_per_hop);
        // Tamper one DS byte — verify must reject (root no longer matches).
        claim.ds_prefix_per_hop[0][0] ^= 0xFF;
        assert!(!merkle_verify_native(&claim),
            "tampered DS prefix must change derived parent → reject");
    }

    #[test]
    fn ds_aware_vs_plain_produce_different_roots() {
        let variant = Sha3Variant::Sha3_256;
        let leaves = vec![
            fake_leaf(variant, 0xAA), fake_leaf(variant, 0xBB),
            fake_leaf(variant, 0xCC), fake_leaf(variant, 0xDD),
        ];
        let plain = merkle_build_and_open(variant, &leaves, 1);
        let ds = merkle_build_and_open_with_ds(variant, &leaves, 1, &[
            fake_ds_bytes(2, 1, 0, 7),
            fake_ds_bytes(2, 2, 0, 7),
        ]);
        assert_ne!(plain.root, ds.root,
            "DS-prefixed hashing must produce a different root from plain");
        // Both verify natively against their own (different) protocols.
        assert!(merkle_verify_native(&plain));
        assert!(merkle_verify_native(&ds));
    }

    #[test]
    fn ds_aware_check_shape_rejects_mismatched_ds_lengths() {
        let variant = Sha3Variant::Sha3_256;
        let claim = MerklePathClaim {
            variant,
            root: fake_leaf(variant, 0xAA),
            leaf_index: 0,
            leaf: fake_leaf(variant, 0x11),
            path: vec![fake_leaf(variant, 0x22), fake_leaf(variant, 0x33)],
            ds_prefix_per_hop: vec![
                vec![0u8; 32],
                vec![0u8; 28],  // wrong length — uniform required
            ],
        };
        assert!(claim.check_shape().is_err(),
            "non-uniform DS-prefix lengths must fail shape check");
    }

    #[test]
    fn ds_aware_check_shape_rejects_wrong_ds_count() {
        let variant = Sha3Variant::Sha3_256;
        let claim = MerklePathClaim {
            variant,
            root: fake_leaf(variant, 0xAA),
            leaf_index: 0,
            leaf: fake_leaf(variant, 0x11),
            path: vec![fake_leaf(variant, 0x22), fake_leaf(variant, 0x33)],
            ds_prefix_per_hop: vec![vec![0u8; 32]],  // 1 entry; depth=2 → mismatch
        };
        assert!(claim.check_shape().is_err(),
            "DS-prefix count must equal depth");
    }

    #[test]
    fn batched_merkle_claim_tampered_root_rejects() {
        let variant = Sha3Variant::Sha3_256;
        let leaves = vec![fake_leaf(variant, 1), fake_leaf(variant, 2),
                          fake_leaf(variant, 3), fake_leaf(variant, 4)];
        let mut claim = merkle_build_and_open(variant, &leaves, 0);
        // Tamper: flip a byte in the root.
        claim.root.0[0] ^= 0xFF;
        let batched = BatchedMerklePathClaim {
            variant, paths: vec![claim],
        };
        assert!(batched.check_shape().is_ok(),
            "shape check is structural — tampered root passes shape");
        assert!(!batched_merkle_verify_native(&batched),
            "tampered root must fail native verify");
    }
}

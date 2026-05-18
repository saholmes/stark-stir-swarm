# FRI-Merkle binding for master / sharded-master recursion — Phase 0 design

## Goal

Close the prover-supplied-residue caveat documented at
`crates/wrapper-stark/src/master_recursion_bridge.rs:653–658` and
`crates/wrapper-stark/src/v2_recursion_bridge.rs:862–866`,`986–991`.

Sub-circuit 1 of the master STARK currently asserts the FRI DEEP-quotient
relation

```
residue = q_val · (x_i − z_ext) − (f_val − fz_per_layer[ell]) = 0
```

over `(f_val, q_val)` pulled from each inner `RecursiveStarkProof`'s
`fri_proof.queries[k].per_layer_payloads[ell]`. The `(f_val, q_val)`
values are **prover-supplied bytes** with no in-AIR re-binding to the
inner FRI proof's per-layer Merkle commitments
(`fri_proof.root_f0`, `fri_proof.roots[ell-1]`). A malicious prover
could substitute values that satisfy the algebraic relation without
ever committing them to the FRI Merkle root.

Phase 1+ closes this by adding, per (query, layer) opening, an in-AIR
SHA-3 Merkle-path STARK that proves the leaf
`leaf_ell = enc(f_val, s_val, q_val)` matches `roots[ell-1]` at index
`per_layer_refs[ell].i`.

## What needs to be bound

Per inner `RecursiveStarkProof` the master's sub-circuit 1 already
extracts (in `master_recursion_bridge.rs:123-167`):

| Source | Field | Used in residue |
|--------|-------|-----------------|
| `fri_proof.queries[k].per_layer_payloads[ell].f_val` | `Ext` | `f_val` |
| `fri_proof.queries[k].per_layer_payloads[ell].q_val` | `Ext` | `q_val` |
| `fri_proof.queries[k].per_layer_refs[ell].i` | `usize` | `x_i = ω_ell^i` |
| `fri_proof.fz_per_layer[ell]` | `Ext` | `fz` |

The Merkle authentication path bytes already live in:

| Layer | Path location | Root location |
|-------|---------------|---------------|
| 0 | `fri_proof.queries[k].f0_opening` (`MerkleOpening`) | `fri_proof.root_f0: [u8; 32]` |
| `ell ≥ 1` | `fri_proof.layer_proofs.layers[ell].openings[k]` | `fri_proof.roots[ell-1]: [u8; 32]` |

(Confirmed in `crates/deep_ali/src/fri.rs:1311-1326`.)

`MerkleOpening` (`crates/merkle/src/lib.rs:136-140`):

```rust
pub struct MerkleOpening {
    pub leaf: [u8; HASH_BYTES],
    pub path: Vec<Vec<[u8; HASH_BYTES]>>,
    pub index: usize,
}
```

Leaf encoding (`fri.rs:1382-1387`):

```rust
ext_leaf_fields(f, s, q) = f.to_fp_components() ++ s.to_fp_components() ++ q.to_fp_components()
```

= 3 × `EXT_DEGREE` Goldilocks elements = **18 × 8 = 144 B at L1/L3**
(`Fp⁶`), **24 × 8 = 192 B at L5** (`Fp⁸`).

The leaf is then SHA-3-compressed to `HASH_BYTES` bytes before insertion
into the Merkle tree (`crates/merkle/src/lib.rs::compress_leaf_standalone`,
`Sha3Variant` per NIST level).

## Sizing: M (openings per inner)

The inner `RecursiveStarkProof` FRI proof has:

- `n_trace_inner` = max of three sub-circuit accumulator traces (composition + OOD + perm-arg), each padded to next power of 2.
  **Anchored**: `scripts/results/sharded-master-architecture.md` measures the single-level master at N=16 with `n_trace = 262 144 = 16 × 16 K` and sharded at K=4 with `n_trace = 65 536 = 4 × 16 K` — i.e. every v2-driven recursive inner contributes **exactly 16 K rows** of master accumulator trace. So `n_trace_inner = 16 K` at L1/L3 production.  At L5 (Fp⁸, `EXT_DEGREE=8`), the per-inner column count is `n_queries × L × 8` vs `× 6` at L1/L3, so the master n_trace per inner ≈ `pow2(54 × L × 8 / 3)` ≈ **32 K** (vs 16 K) — kept consistent in the M_paths table below.
- `n_lde_inner = n_trace_inner × blowup` (production blowup=32, smoke blowup=4).
- `schedule = [2; log2(n_lde_inner)]` → **L = log2(n_lde_inner)** layers.
- `r` queries (paper Table 2: 54 / 79 / 105 at L1 / L3 / L5).

Per (query, layer) there is exactly **one** Merkle opening. Per layer
ell the opening depth is `log2(n_lde_inner / 2^ell)` = `L − ell`. So
per query the sum of opening depths is

```
Σ_{ell=0..L-1} (L − ell)  =  L(L+1)/2
```

and per inner

```
M_paths = r × L                              (paths to verify)
M_hashes = r × L(L+1)/2                      (total SHA-3 hashes)
```

**Anchored from `print_fri_merkle_binding_sizing` test** (2026-05-18,
sha3-256 blowup=4):

```
inner.n_trace             = 8 192    (= 2^13)
n_lde_inner               = 32 768   (= 2^15)
L (FRI layers)            = 15
r (queries)               = 54       (hardcoded in build_one_inner_recursive)
M_paths = r × L           = 810
M_hashes = r × Σ depth    = 6 480
per-layer depths          = [15, 14, 13, …, 2, 1]
fri_proof.roots.len       = 15       (one Merkle root per layer)
```

So at smoke blowup=4 the workload is **slightly smaller than
extrapolated**: M_paths=810 vs the doc's 864 (-6%); M_hashes=6 480 vs
7 344 (-12%). The inner recursive STARK's n_trace is **8 K** (not 16 K
as the design doc assumed), driven by max(comp, ood, perm) accumulator
traces, all of which fit within 8 K rows for v2 + composition.

Production scaling (inner blowup=32, same inner n_trace=8 K → n_lde_inner=256 K, L=18):

| Level | EXT_DEGREE | r (WIP num_queries_for_blowup) | M_paths | M_hashes | Hash bytes |
|-------|-----------:|-------------------------------:|--------:|---------:|-----------:|
| L1    | 6 (Fp⁶)   | 54                              |     972 |    9 234 | 32 (sha3-256) |
| L3    | 6 (Fp⁶)   | 79                              |   1 422 |   13 509 | 48 (sha3-384) |
| L5    | 8 (Fp⁸)   |105                              |   1 890 |   17 955 | 64 (sha3-512) |

**Note on r scaling (uncommitted WIP)**: `crates/deep_ali/src/lib.rs`'s
`num_queries_for_blowup(blowup)` makes r = ⌈TARGET_IT_BITS / (½·log₂ blowup)⌉ + 2.
At smoke blowup=4 this gives r=130 (NOT 54), which means the post-WIP
smoke M_paths at L1 would be **1 950** and M_hashes **15 600** (well
above the prod blowup=32 case because lower blowup demands more
queries for L1 soundness). The current `build_one_inner_recursive`
hard-codes r=54 and would need updating once `num_queries_for_blowup`
is fully wired through.

**At the master level**: one inner-binding bundle per inner, so total
hashes scale linearly in N.  At N=10 inners, smoke L1: ~73 K SHA-3
hashes; at N=100, ~734 K.

## Why per-path STARKs don't scale

The existing single-path `prove_merkle_path` STARK is anchored in
`scripts/results/merkle-stark-bench.md`:

- L1 sha3-256 blowup=32 depth=2 FRI: **8.12 s prove / 1.83 ms verify / 559 KiB**
- L1 sha3-256 blowup=32 depth=3 FRI: **17.08 s prove / 2.04 ms verify / 600 KiB**

Each depth doubles the trace; per-hop trace ≈ 98 rows.

At L=19 the average path depth is **~10 hops** = ~980 trace rows →
padded to 1 024 → n_trace ≈ 1 024 ≈ 2× the depth-3 case → ~30 s prove
per path STARK. At M_paths=1 026 per inner → **30 800 s = 8.5 hours per
inner** at prod blowup=32. Untenable.

The existing `v2_recursion_bridge.rs:738-742` comment estimates ~8 100
MerklePathProofs per v2 inner (slightly different framing) and explicitly
flags it for "batched Merkle AIR or recursive aggregation."

## Phase 1 primitive — shape decision

Four candidate shapes considered:

| Shape | Idea | Per-inner LDE | Verdict |
|-------|------|--------------:|---------|
| **A** Single big batched STARK over all M paths | One trace, M blocks stacked, one FRI | ~5.8 GB @ smoke / ~46 GB @ prod | **Rejected**: prod memory wall + single failure point |
| **B** Recursive aggregation of M single-path STARKs | M × `prove_merkle_path` then wrap | 8.5 h prove/inner (anchored) | **Rejected**: per-path STARK overhead dominates |
| **C** Coset/shared-sponge batching | Exploit shared subtrees across queries/layers | unclear; <10% saving | **Rejected**: FRI queries are random, sharing is negligible |
| **D** Small batched primitive + recursive wrap | Build batch-size B primitive (B≈64), wrap N_b = ⌈M/B⌉ via existing `prove_master_recursive` | ~370 MB/STARK × 17 STARKs/inner | **Recommended** |

**Why D wins**:

- The existing `prove_master_recursive` already aggregates `RecursiveStarkProof`s — Phase 1 just needs to make the batched-Merkle proof emit a `RecursiveStarkProof`-compatible shape.
- Each batched-Merkle STARK is bounded in size (B=64 paths × ~10 avg hops × 98 rows ≈ 63 K trace rows ≈ pow2 64 K). Working set ~370 MB at blowup=4. Easily fits.
- Per-inner cost: `M/B` STARKs of bounded size, sequential within an inner. At L1 smoke: 864/64 ≈ 14 batched-Merkle STARKs per inner.
- Testability: B=2 → B=16 → B=64 ladder is cheap to validate; failure mode is local to one block.
- Soundness: composes through the same FRI-quotient algebraic gadget the rest of the master pipeline uses. No new soundness primitive.

**Phase 1 = the batched primitive at fixed B**. Phase 3 = the recursive
wrap into a single `RecursiveStarkProof`-shaped per-inner binding artefact.

**Per-inner cost model (Shape D, L1 prod blowup=32)**:

| Quantity | Value |
|----------|------:|
| M_paths/inner | 1 026 |
| B (batch size) | 64 |
| N_b STARKs/inner | 17 |
| Per-STARK trace (pad) | 64 K rows |
| Per-STARK LDE @ blowup=32 | 2 M rows |
| Per-STARK working set | ~750 MB |
| Per-STARK prove (extrapolated from sha3-256 d=3 anchor) | ~30 s |
| Per-inner prove | ~510 s (17 × 30 s, sequential) |
| Per-inner wire | 17 × ~600 KiB ≈ ~10 MiB before recursive wrap |
| After Phase 3 recursive wrap | ~1 MiB per-inner constant |

This brings per-inner FRI-Merkle binding prove time into the same order
as the inner v2 proof itself (~5 minutes anchored at K=256 in
`scripts/results/se-zone-hnpl-demo.md`). Practical.

**Total wire cost projection (Phase 3 + Phase 4 with recursive wrap)**:

| Config | Master STARK | + N × per-inner wrap | Total L1 |
|--------|-------------:|---------------------:|--------:|
| Current (no binding) | 789 KiB | — | ~789 KiB |
| Phase 3 N=10 L1 prod | 789 KiB | 10 × ~1 MiB | ~11 MiB |
| Phase 3 N=10 L1 smoke | ~395 KiB | 10 × ~300 KiB | ~3.4 MiB |
| Phase 4 sharded N=1000 Ni=64 K=16 + recursive wrap | super: ~395 KiB | aggregated into 1 outer | ~3 MiB constant |

Phase 4 wire cost stays **constant in N** if Phase 4b (recursive
aggregation of per-inner binding wraps) lands together with Phase 4.

**Lower-r at the binding layer** — kept as an optional optimization.
The binding STARK attests only Merkle-path correctness; its own FRI
soundness margin is independent of the inner statement's bits-of-security
budget. Defer to bench phase.

## Phase 1 implementation sketch

Extend `crates/wrapper-stark/src/merkle_path_air.rs`:

```rust
pub struct BatchedMerklePathClaim {
    pub variant: Sha3Variant,
    /// EXACTLY B paths per claim (fixed at construction; default B = 64).
    /// Paths may have DIFFERENT (root, depth, leaf_index, leaf, path) —
    /// no shared subtree assumptions.
    pub paths: Vec<MerklePathClaim>,
}

pub struct BatchedMerklePathLayout {
    pub variant: Sha3Variant,
    /// One layout per path, vertically offset-stacked.
    pub blocks: Vec<MerklePathLayout>,
    /// pow2 padding of Σ blocks[i].trace_rows().
    pub n_trace: usize,
}

pub struct BatchedMerklePathPublicInputs {
    pub variant: Sha3Variant,
    /// Per-path (root, leaf_index, depth) — these are PUBLIC.
    /// Leaf + path bytes stay private.
    pub paths: Vec<(MerkleNode, u64, usize)>,
    /// SHA3-256("WRAPPER-BATCHED-MERKLE-V1" || variant_tag ||
    ///          B(LE) || depth_0(LE) || root_0 || leaf_index_0(LE) ||
    ///          ... || depth_{B-1}(LE) || root_{B-1} || leaf_index_{B-1}(LE))
    pub pi_hash: [u8; 32],
}
```

`prove_batched_merkle_paths`:

1. For each `path_j` (j = 0..B), synthesise its single-path trace
   block via the existing `synthesize_merkle_sponge_trace` at offset
   `blocks[j].row_offset`.
2. Concatenate vertically with idle-row padding (all selectors = 0,
   so no constraint fires).
3. Build the c_eval as Σ_j over per-block (selection + sponge sub-AIR +
   cross-row) constraints, with FS-derived α coefficients seeded from
   `pi_hash`.
4. ONE `deep_fri_prove` over the stacked LDE.

`verify_batched_merkle_paths`:

1. `deep_fri_verify` over the stacked c_eval / FRI proof against
   the same FS-derived alphas.
2. Per-block boundary checks: row 0 of each block has
   `current_node = leaf_j` (PRIVATE — encoded as opening at row 0
   committed via the FRI trace Merkle), row `depth_j − 1` of each
   block has `parent = root_j` (PUBLIC — boundary constraint reads
   from public inputs).

Tests at B ∈ {2, 8, 16, 64} smoke blowup=4: round-trip + tamper
(flip one sibling byte → must reject) → `merkle_prover.rs` test module.

## Soundness binding chain

The binding is a **three-piece** chain — all three pieces are needed
or the soundness gap stays open.

For each inner `i`:

### Piece 1 — Master STARK FS-absorbs the inner FRI Merkle roots

`build_master_composition`'s FS seed (currently `MASTER-RECURSION-COMP-V1`
+ each inner's `outer_pi_hash`) **must additionally absorb every inner's
`fri_proof.root_f0` and `fri_proof.roots[*]`**. Without this, a
malicious prover could swap a different inner FRI commitment in
between sub-circuit 1's residue extraction and the binding bundle's
public root — the FS-derived α coefficients would still match.

**Audit needed in Phase 3**: confirm whether `outer_pi_hash` (built in
`recursive_prover.rs::RecursiveStarkPublicInputs::for_claims`) already
transitively binds `root_f0` / `roots` through the sub-circuit pi_hashes.
If not, extend the master's FS seed to include them explicitly.

### Piece 2 — Per-inner binding bundle public roots match inner FRI roots

The `BatchedMerklePathPublicInputs.paths[j].0` (the public root for
path j) must equal the inner's actual FRI Merkle root for the layer
that opening j addresses. The verifier re-derives the expected
`(root, leaf_index, depth)` triple for every (query, layer) opening
from the inner's `fri_proof.{root_f0, roots, queries[k].per_layer_refs}`
and cross-checks against `binding_bundle.public.paths[j]`.

### Piece 3 — Per-inner binding bundle leaf encodings match inner FRI payloads

The leaf bytes opened by path j (committed inside the FRI proof of
the batched Merkle STARK at row 0 of block j) must equal
`SHA3(ext_leaf_fields(f_val, s_val, q_val))` for the matching inner
`(query k, layer ell)` payload. Since the leaf bytes are PRIVATE
witness, the binding bundle exposes only the FRI-committed leaf
opening — the verifier re-derives the expected leaf encoding from
`inner.fri_proof.queries[k].per_layer_payloads[ell]` and cross-checks
via a domain-separated SHA-3 commitment that the prover must include
in `BatchedMerklePathPublicInputs` (or equivalently, the master
STARK's sub-circuit 1 absorbs the SHA-3 of every leaf encoding into
its own FS transcript — symmetric formulation).

### Why all three are needed

- Drop Piece 1 → attacker swaps `roots[ell]`, binding bundle accepts
  the modified root, sub-circuit 1's α's are still legitimate, attack
  succeeds.
- Drop Piece 2 → attacker constructs a binding bundle attesting some
  Merkle tree (not the inner's) and supplies fake `(f, s, q)` values
  matching that tree; sub-circuit 1's residues sum to zero, attack
  succeeds.
- Drop Piece 3 → attacker presents a valid binding bundle for the
  inner's actual roots but the bundle's committed leaves are different
  from the `(f_val, s_val, q_val)` sub-circuit 1 actually consumed;
  the bundle accepts, sub-circuit 1 accepts, attack succeeds.

Together: any prover-supplied substitution of `(f_val, s_val, q_val)`
in sub-circuit 1 propagates to a leaf encoding that no longer matches
the inner's actual FRI Merkle tree — and the BatchedMerklePathProof
rejects. The three pieces tie the algebraic residue extraction,
the Merkle-path verification, and the inner FRI proof's identity into
one binding statement.

### Tamper tests required (Phase 5)

For each piece, at least one tamper case that flips state controlled
by that piece and confirms rejection:

| Piece | Tamper | Expected |
|-------|--------|---------|
| 1 | Modify `inner_i.fri_proof.root_f0` in the bundle public; leave bundle proof bytes intact | Master STARK FS mismatch → reject |
| 2 | Modify `binding_bundle.public.paths[j].0` (root) for one j | Verifier cross-check fails → reject |
| 3 | Modify one `per_layer_payloads[ell].f_val` in the inner FRI proof; regenerate sub-circuit 1 with the new value (zero residue still holds because we also chose the matching q_val); binding bundle still attests the OLD leaf | Leaf-encoding cross-check fails → reject |

## Scope decisions (refined)

### In-scope follow-ups (pulled forward from previously out-of-scope)

1. **Fold-relation in-AIR encoding** — moved into Phase 3 as
   *sub-circuit 1a*. With `(f, s, q)` now Merkle-bound (Pieces 2+3
   above), the algebraic FOLD relation `s_val[ell] ==
   f_val_at_next_layer[ell+1]` (at the index implied by FRI's
   position-halving) becomes meaningful to constrain — it ties the
   bound `s` at layer `ell` to the bound `f` at layer `ell+1`.
   Without this, a prover could provide consistent leaves at every
   layer that don't actually fold correctly. ~1-day extension to
   Phase 3.
2. **Recursive aggregation of per-inner binding bundles** — moved into
   Phase 4 as *Phase 4b*. Without it the sharded variant's L1 wire
   scales linearly in N (≈10 MiB/inner pre-wrap), defeating the
   sharded-master-architecture.md target of ~$56/batch constant. The
   wrap re-uses the existing `prove_master_recursive` aggregation
   pattern (the per-inner binding bundles emit a
   `RecursiveStarkProof`-shaped artefact by design).

### Genuinely out-of-scope (parking)

1. **STIR-mode binding** — current sub-circuit 1 only handles FRI
   mode (`master_recursion_bridge.rs:130-131`). STIR proximity is a
   fiber-fold-vs-z₀ check, structurally different from FRI's
   per-layer DEEP-quotient. The SHA-3 leaf-binding primitive built
   in Phase 1 reuses; the residue-extraction extractor and FS-binding
   shape differ. Separate effort.
2. **In-AIR FRI Merkle tree CONSTRUCTION** (vs. opening verification) —
   binding only the OPENINGS, not the construction. A prover with a
   malformed FRI Merkle tree but consistent openings at the queried
   positions could still pass. FRI soundness already covers the
   non-queried positions through the FRI low-degree test; the
   binding bundle inherits that soundness margin.
3. **Cross-inner leaf-encoding deduplication** — different inners'
   FRI proofs have independent FRI Merkle trees, so leaf-encoding
   sharing across inners has no soundness payoff. Skip.

## Sizing probe (deferred)

An inline `#[ignore]`'d test `print_fri_merkle_binding_sizing` was
added to `crates/wrapper-stark/src/master_recursion_bridge.rs`'s test
module to anchor the M_paths / M_hashes / L numbers above against a
live `RecursiveStarkProof`. Running it is blocked by the working
tree's WIP refactor of `v2_fri_params` (signature changed from
`(n0, blowup) → DeepFriParams` to `(n0, blowup, pi_hash)`, 32 call
sites not yet updated). Once that lands, run:

```bash
cargo test --release -p wrapper-stark \
  --features "sha3-256 mldsa-44 parallel" --no-default-features \
  print_fri_merkle_binding_sizing -- --ignored --nocapture
```

and fold measured numbers back into the worked-examples tables above.

## Phase 2.5 — DS-aware in-AIR Merkle gadget (2026-05-18)

**Closed soundness gap**: The original in-AIR Merkle gadget hashed plain
`SHA3(left || right)`, but FRI/STIR's `MerkleTreeChannel::verify_opening`
uses `SHA3(DsLabel.to_bytes() || child_0 || child_1)` per hop. DS
labels were a holdover from the dual-hash (Poseidon-algebraic + SHA3-FIPS)
architecture and aren't strictly needed in STIR-only mode, but keeping
them on the producer side and adding consumer-side support preserves
forward compatibility with potential future Poseidon acceleration.

The fix extends the in-AIR gadget with optional per-hop DS prefix
absorption:

| Component | Change |
|-----------|--------|
| `MerklePathClaim` | New `ds_prefix_per_hop: Vec<Vec<u8>>` field (empty = backward-compat plain mode) |
| `merkle_verify_native` | Absorbs DS at each hop when present |
| `synthesize_merkle_sponge_trace` | Builds sponge input as `ds || left || right` (96B at sha3-256, fits 1 block) |
| `MerkleCrossRowConstraint` | New `SpongeInputDsByte` variant binds public DS bit values |
| `merkle_cross_row_constraints_with_ds` | Emits DS bindings + shifts Left/Right by `ds_bits` |
| `prove_batched_merkle_paths` | c_eval handles `SpongeInputDsByte` via `lde[col] − constant` shape |
| `extract_fri_merkle_openings` | Populates DS bytes per FRI's `DsLabel{ arity=2, level=hop+1, position=idx>>1, tree_label=ell }` (mirrors `merkle/src/lib.rs:781`) |

**Integration test anchor** (`fri_merkle_binding_integration_b10_subset` ignored test):

```
1. build_one_inner_recursive(910)                  → real RecursiveStarkProof
2. extract_fri_merkle_openings(&inner)             → 810-path BatchedMerklePathClaim
3. subset to B=10 (spans multiple FRI layers)
4. batched_merkle_verify_native(&subset)           → ACCEPT (DS matches FRI)
5. prove_batched_merkle_paths(&subset, 4, 54, false)
   - prove time: 224 s (≈3.7 min) at blowup=4 r=54 smoke
   - mixed depths 15..1 across the 10 sampled paths
6. verify_batched_merkle_paths(&proof)             → ACCEPT
```

End-to-end binding pipeline (extract → DS-aware prove → verify) works
on **real cryptographic data**.

**Cost extrapolation** to B=810 (full per-inner binding):
- 224 s × (810/10) ≈ 5 hours per inner at smoke
- Sequential per inner; Phase 3 wraps as 1 STARK per inner
- At production blowup=32 r=54: ~5× slowdown (per FRI's typical scaling),
  so ~25 hours per inner — still infeasible on a single machine
- **Mitigation**: Shape D from Phase 0 design (B=64 small batches +
  recursive wrap) bounds per-batch cost to ~5 min, with 17 batches per
  inner = ~1.5 h sequential per inner.  Phase 4b's recursive aggregation
  brings this to ~1 STARK shape per inner on the L1 wire.

**Open scoping items for L3/L5**: DS bytes (32 B) push the sha3-384 input
to 128 B > 104 B rate (2 blocks instead of 1), and sha3-512 input to
160 B > 72 B rate (3 blocks instead of 2).  `MerkleSpongeLayout::sponge_blocks_per_hop`
needs awareness of DS-byte length to compute correct rows_per_hop at
L3/L5.  Documented; not blocking for L1.

## Phase 3 — Master-level FRI-Merkle binding (2026-05-18, commit f885ee8)

The 3-piece soundness chain landed end-to-end at the master STARK level:

- **Piece 1** — FS-seeds (`MASTER-RECURSION-{COMP,OOD,PI}-V2`) absorb
  every inner's `(root_f0, roots[*])` via new `absorb_inner_fri_roots`
  helper. Master STARK alphas now bound to the specific N-tuple of
  inner FRI commitments.
- **Piece 2** — `verify_master_with_fri_merkle_binding` re-extracts each
  inner's expected Merkle openings (via `extract_fri_merkle_openings`)
  and cross-checks per-block `(root, leaf_index, depth)` triples
  against the binding bundle's `BatchedMerklePathPublicInputs.paths`.
- **Piece 3** — Leaf encodings inherit from Phase 2.5's DS-aware
  extractor — bundle's committed leaves are
  `SHA3(DsLabel || ext_leaf_fields(f, s, q))` for the same inner
  `per_layer_payloads` the sub-circuit 1 residue extraction reads.

`MasterWithFriMerkleProof { master, fri_merkle_bindings: Vec<BatchedMerklePathProof> }`
is the proof artifact. `prove_master_with_fri_merkle_binding(...,
subset_paths: Option<&[usize]>)` allows tractable testing on subsets.

**Anchored**: `prove_master_with_fri_merkle_binding_n1_subset_b10`
ignored test verifies in 226 s end-to-end on a real inner v2 STARK.

## Phase 4a — Sharded master-level FRI-Merkle binding (this phase)

Applies the Phase 3 3-piece chain at BOTH levels of the sharded
recursion:

- N per-inner binding bundles (Phase 3 shape) — bind each inner's FRI
  Merkle openings.
- K per-shard binding bundles (new) — bind each first-level shard
  master's FRI Merkle openings.
- Super-master's V2 seed already absorbs shard masters' FRI roots via
  the V1→V2 extension from Phase 3 (called recursively when proving
  the super-master over shard_masters).

**Wire-cost note**: Linear in N+K until Phase 4b recursive aggregation
lands. The shard masters are carried in the proof artifact (Option A
from design) because the verifier needs them for the per-shard
binding's Piece 2 cross-check.

`TwoLevelShardedFriMerkleProof { super_master, shard_masters,
inner_fri_merkle_bindings, shard_fri_merkle_bindings, shard_size }` is
the proof artifact.

**Round-trip anchor** (`prove_sharded_with_fri_merkle_binding_n2_k1_subset_b10`,
ignored): 2 inners → 1 shard master → super-master + 2 inner bindings
+ 1 shard binding → 3-piece verify at BOTH levels.

## Phase 4b — Recursive aggregation wrap (2026-05-18)

Collapses N `BatchedMerklePathProof`s into ONE outer
`RecursiveStarkProof` via the same FRI-residue-extraction pattern the
master uses for inner recursive STARKs.

**Solution**: Option 1 from the prior design note — adapt
`BatchedMerklePathProof` to the `RecursiveStarkProof`-compatible
extraction pattern through new helpers:

- `batched_merkle_proof_params(bmp)` mirrors `recursive_proof_params`
  but reads `bmp.public.pi_hash` instead of `outer_pi_hash`.
- `extract_batched_merkle_fri_residues(bmp)` mirrors
  `extract_recursive_fri_residues`.
- `build_aggregator_{composition, ood_anchor, vestige_perm_arg}` use
  FS seeds `AGGREGATOR-FRI-MERKLE-{COMP,OOD,PI}-V1` over binding
  `public.pi_hash`es.  Since `BatchedMerklePathPublicInputs.pi_hash`
  already SHA-3-binds `(variant, B, per-path (depth, root, leaf_index))`,
  the aggregator's `outer_pi_hash` is transitively bound to every
  binding's complete public commitment.
- `aggregate_fri_merkle_bindings(bindings, ...)` runs the three
  sub-circuits through `prove_recursive_stark` to produce a
  `RecursiveStarkProof` whose FRI-quotient relation attests every
  binding's FRI-quotient relation.

**Compact API** (`CompactFriMerkleBundle`):

```rust
pub struct CompactFriMerkleBundle {
    pub master: RecursiveStarkProof,             // L1 wire
    pub binding_aggregator: RecursiveStarkProof, // L1 wire (constant in N)
    /// Per-binding public inputs needed for Piece 2 cross-check.
    /// Size ≈ N × (32 + B × 48) B; small compared to ~789 KiB STARKs.
    pub binding_publics: Vec<BatchedMerklePathPublicInputs>,
}
```

**`prove_master_with_fri_merkle_binding_aggregated`** orchestrates:

1. Run Phase 3 linear form (`prove_master_with_fri_merkle_binding`).
2. `aggregate_fri_merkle_bindings(&linear.fri_merkle_bindings, ...)`.
3. Strip binding `fri_proof`s from wire; keep only `binding_publics`.

**`verify_master_with_fri_merkle_binding_aggregated`** checks:

1. Master STARK FRI-verifies.
2. Binding aggregator FRI-verifies.
3. Each `binding_publics[i].pi_hash` deterministically re-derives from
   its `(variant, B, per-path triples)` (defense-in-depth against
   binding_publics tamper not actually consumed by the aggregator).
4. Per-inner Piece 2 cross-check (unchanged from Phase 3).

**Wire cost projection** (sha3-256 prod blowup=32, r=54):

| Component | Linear (Phase 3) | Compact (Phase 4b) | Δ |
|-----------|-----------------:|-------------------:|--:|
| Master | ~789 KiB | ~789 KiB | — |
| N bindings @ B=810 | N × ~500 KiB | — | removed |
| Aggregator | — | ~789 KiB | added (constant in N) |
| binding_publics | — | N × ~39 KiB | new (linear but tiny) |
| **Total at N=10** | ~5.7 MiB | ~1.97 MiB | **−65%** |
| **Total at N=100** | ~50 MiB | ~5.5 MiB | **−89%** |

Constant-in-N L1 wire achieved (modulo small per-inner publics
calldata which is much cheaper than full STARK).

**Anchored**: `prove_master_with_fri_merkle_binding_aggregated_n1_subset_b10`
ignored test verifies the full compact-form pipeline end-to-end on a
real inner v2 STARK at B=10 subset.  Tamper test
`prove_master_with_fri_merkle_binding_aggregated_rejects_tampered_publics`
confirms binding_publics tampering is detected.

**Known soundness gap (M6 follow-up)**: the compact form's current
verifier doesn't re-derive `aggregator.public.outer_pi_hash` from
`binding_publics` deterministically.  Without that link, a malicious
prover could submit a DEGENERATE aggregator (proven over residues all
set to zero) plus the real `binding_publics` — passing both the
aggregator FRI verify AND the Piece 2 cross-check.  The gap is closed
by adding `binding_meta: Vec<(n_trace, blowup, r, use_stir)>` (32 B
per binding) to `CompactFriMerkleBundle` so the verifier can
reconstruct each binding's `n_constraints = r × log2(n_trace × blowup)
× EXT_DEGREE`, re-derive the alphas from the FS-seed, rebuild the
sub-circuit pi_hashes, and confirm
`aggregator.public.outer_pi_hash` matches.  Documented as Phase 4b-2.

**Out-of-scope (next pickups)**:

- **Phase 4b-2 — soundness completion** — add binding_meta + verifier
  re-derivation of aggregator.outer_pi_hash from binding_publics.
  ~half-day; binding_meta is constant-in-binding wire (~32 B each).
- **Sharded compact form** — combine Phase 4a + 4b to aggregate
  inner+shard bindings into a single aggregator for the sharded
  variant (`CompactShardedFriMerkleBundle`).  Mechanical extension.
- **Multi-level aggregation** — for very large N, aggregate batches of
  bindings into mid-level aggregators, then super-aggregate.  Same
  shape as the existing sharded master at the aggregator layer.

## Phase 5 — Sub-circuit 1a (FRI fold relation) + Piece 2 tamper (2026-05-18)

### Sub-circuit 1a — FRI fold relation

Master sub-circuit 1 previously encoded only the DEEP-quotient
relation `q · (x − z) = f − fz` per (k, ell).  Phase 5 adds the
fold relation `s_val[ell] − f_val[ell+1] = 0` per (k, ell) for ell
in 0..L-1, making the master STARK's algebraic attestation of each
inner's FRI verify COMPLETE (DEEP-quotient ∧ fold) — previously the
fold check was implicit in the inner's own FRI verify, but with the
master sub-circuit 1 we want full algebraic encoding.

New helper `extract_recursive_fold_residues(rec)` returns
`n_queries × (L − 1)` Ext residues; appended to
`build_master_composition`'s column_values + IsZero constraints.

FS seeds bumped V2 → V3 (`MASTER-RECURSION-{COMP,OOD,PI}-V3`) to
reflect the new constraint set (otherwise unchanged byte format).

Total constraint count per master sub-circuit 1: previously
`N × n_queries × L × EXT_DEGREE`; now `N × n_queries × (2L − 1) × EXT_DEGREE`.
At smoke L1 r=54 L=15: 5184 → 10044 constraints per inner.

`extract_recursive_fold_residues_shape` ignored test confirms shape
and that honest fold residues are all zero in F_ext.

### Piece 2 tamper test

`fri_merkle_binding_piece_2_tamper_rejects` ignored test:
1. Honest end-to-end prove + verify (Phase 3 shape, N=1 B=10 subset)
2. Flip one byte in `binding.public.paths[3].0` (root)
3. Verifier MUST reject (Piece 2 cross-check against re-extracted
   inner FRI fails)

### Known soundness gaps (Phase 5-2 follow-up)

- **Piece 1 tamper** (swap `inner.fri_proof.root_f0` post-prove):
  current verifier reads `master.public.outer_pi_hash` at face value
  rather than re-deriving it from supplied `inner_proofs`.  Adversary
  could submit (master_real, inner_proofs_with_swapped_root_f0) — FRI
  verify still passes because outer_pi_hash is baked into the proof.
  Same structural issue as Phase 4b-2 (compact-aggregator gap).
- **Piece 3 tamper** (modify `per_layer_payloads[ell].f_val`): the
  binding bundle's committed leaf bytes are private witness inside
  the BMP FRI proof.  Without explicit leaf-encoding cross-check at
  verify time, an adversary modifying `per_layer_payloads[ell].f_val`
  in the supplied inner_proofs causes the re-derived expected leaf
  bytes to differ from the binding's committed leaves — but the
  current verifier only cross-checks public roots, not leaves.

Both close by adding `binding_meta` (or equivalent) to the proof
artifact + re-deriving the chain of pi_hashes from supplied inputs.
Phase 5-2 tracks this work alongside Phase 4b-2.

### Out-of-scope (next pickups)

- **Aggregator sub-circuit 1a** — extend the Phase 4b aggregator to
  also include fold residues over binding bundles' FRI proofs.
  Same shape extension as master sub-circuit 1a but at the aggregator
  layer.  Bump AGGREGATOR seeds V1 → V2.

## Status

- Phase 0 (this doc) — **done**.
- Phase 1 (batched Merkle AIR at fixed B) — pending; ~3-4 days.
- Phase 2 (FRI Merkle opening extractor) — pending; ~1 day.
- Phase 3 (Sub-circuits 1 + 1a + master-level wire) — pending; ~2-3 days.
- Phase 4 (Sharded variant + Phase 4b recursive wrap) — pending; ~2 days.
- Phase 5 (Round-trip + 3-piece tamper tests) — pending; ~1 day.
- Phase 6 (Bench + anchor) — pending; ~1 day.

**Total**: ~10-12 days end-to-end for the headline "true FRI-Merkle
binding at every recursion level" deliverable.

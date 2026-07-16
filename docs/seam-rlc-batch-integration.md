# Handoff: integrating the RLC seam batch into the shipped stranded-proof pipeline

**Status:** design complete and validated in examples; **shipped-lib integration NOT done.**
This is a soundness-critical change to the production G-way stranded prover/verifier
(`crates/deep_ali/src/ecdsa_verify_stranded_gway.rs`). Do it as a focused, reviewed
effort. Every mechanism below is already proven sound and measured in isolation.

**Branch:** `feature/accumulation-recursion`. **Field:** Goldilocks base `F`; extension
`ExtField` (`Fp6` at L1/L3, `Fp8` at L5), `EXT_DEGREE = d`.

---

## 1. Why

The reconstruction bottleneck (see `examples/gway_reconstruction.rs`) is the seam
verification: `verify_seams` runs one `verify_ood_consistency` **per seam column per
holder-pair** — for K=256/G=64 that is **M = 2622 checks = 5244 FRI verifies**, ~36.5 s
(6.9 s parallel), and the seam commitments dominate proof size at **~2.36 GiB** (each
`BindingCellsCommit` is a full FRI proof, ~0.9 MiB).

The RLC batch replaces all M checks with **d = EXT_DEGREE (6/8) FRI verifies total**,
at `α ∈ F_ext` (NIST) soundness, and replaces the per-column BCCs with raw seam-column
commitments (16 KiB each) + d small R proofs.

**Measured at real cut scale** (`examples/seam_rlc_coordinator.rs`, K=256/G=64/Fp6):
2622 checks → **6 FRI verifies, 170 ms, 41 MiB seam data** — 874× fewer verifies, 58×
smaller seam data; honest accepts (`R(z0)=0`), one-in-2622 tamper caught (`R(z0)≠0`).

## 2. The mechanism (all validated)

Let each seam-consistency obligation be `aₘ(z0) = bₘ(z0)` where `aₘ, bₘ` are two strands'
LDE columns for the same shared seam column, over the same `n_lde = n_trace·blowup`
domain, and `z0` is the FS-derived OOD point. Enumerate all M obligations; let
`dₘ = aₘ − bₘ` (honest ⇒ `dₘ ≡ 0`).

1. **Consistency (`examples/seam_rlc_batch.rs`, commit `bf94c69`).** Draw `α ∈ F_ext`
   (FS from `pi_hash`). `R(x) = Σₘ αᵐ·dₘ(x)`. `R ≡ 0` iff all `dₘ ≡ 0` (Schwartz–Zippel
   over α, ε ≤ M/|F_ext|); `R(z0)=0` iff `R ≡ 0` (ε ≤ n/|F_ext|).
   `R` is `F_ext`-valued and `deep_fri_prove` is base-F only, so **component-decompose**:
   `αᵐ = Σⱼ cₘⱼ·eⱼ` with `cₘⱼ = (αᵐ).to_fp_components()[j] ∈ F`, giving
   `R(x) = Σⱼ eⱼ·R⁽ʲ⁾(x)`, `R⁽ʲ⁾(x) = Σₘ cₘⱼ·dₘ(x)` **base-F**. Commit each of the
   `d` base-F codewords `R⁽ʲ⁾` with the existing `deep_fri_prove`, take
   `R⁽ʲ⁾(z0) = proof.fz_per_layer[0]`, recombine `R(z0) = Σⱼ eⱼ·R⁽ʲ⁾(z0)`, check `== 0`.
   One global RLC over ALL M works (shared domain) ⇒ `d` verifies regardless of M.

2. **Binding (`examples/seam_rlc_bound.rs`, commit `36be7c4`).** The consistency check
   alone lets a prover commit `R⁽ʲ⁾ = 0` to fake agreement. Bind `R⁽ʲ⁾` to the individual
   `aₘ, bₘ` (standard FRI batching): commit each `aₘ, bₘ` (Merkle roots); draw query
   positions `Q = FS(pi_hash ‖ all roots)`; at each `q ∈ Q` check
   `R⁽ʲ⁾(q) == Σₘ cₘⱼ·(aₘ(q) − bₘ(q))` with a Merkle-path verification of every opened
   value. A forged `R⁽ʲ⁾=0` fails this at some q.

Given (1)+(2) plus `aₘ, bₘ` low-degree (established by the **strand proofs**, already
verified) and `R⁽ʲ⁾` low-degree (its FRI), the batch is sound end-to-end.

## 3. Current (shipped) architecture — exact surface

`crates/deep_ali/src/ecdsa_verify_stranded_gway.rs`:

```rust
pub struct StrandedProofG {
    pub proofs: Vec<SubAirProofWithTrace>,
    pub seam_commits: Vec<Vec<(usize /*gid*/, Vec<BindingCellsCommit>)>>, // per strand, per held group, per column
}

pub fn prove_one_strand<P>(strand_trace, cut, s, layout, pubin, n_trace, blowup, pi_hash,
    domain_sep, params_fn) -> (SubAirProofWithTrace, Vec<(usize, Vec<BindingCellsCommit>)>)
// inside: has `lde` (the strand LDE). Seam cols are `lde[cut.local(s, c)]`.
// Commits each held group's cols individually via commit_binding_cells(&lde, &[cut.local(s,c)], …).

pub fn verify_stranded_g<P>(proof, cut, layout, pubin, n_trace, blowup, pi_hash, params_fn)
    -> Result<(),String>  // = for s in 0..g { verify_one_strand(…) } ; verify_seams(…)

pub fn verify_seams<P>(proof, cut, pi_hash, params_fn) -> Result<(),String>
// for (gid, sg) in cut.seams: refs=sg.holders[0]; for h in sg.holders[1..]:
//   for j,col: verify_ood_consistency(ref_commits[j], hc[j], pi_hash, params_fn)   // 2 FRI verifies each
```

Supporting (`binding_cells_commit.rs`): `commit_binding_cells(lde, cols, n_trace, blowup,
pi_hash, domain_sep, fri_params_fn) -> (BindingCellsCommit, packed_lde: Vec<F>)`;
`extract_ood_value(&BindingCellsCommit) -> ExtField` (= `fz_per_layer[0]`).
Cut (`ecdsa_verify_stranded_gway.rs`): `GwayCut { g, full_width, seams: Vec<SeamGroup>,
strand_cols, .. }`, `SeamGroup { holders: Vec<usize>, cols: Vec<usize> }`,
`cut.local(s, c) -> usize`.

## 4. Target architecture

Replace the per-column BCC seam sub-protocol with: **(P)** strands emit their raw seam
columns + a Merkle commitment; **(C)** a coordinator forms the global RLC; **(V)** the
verifier checks `d` FRI + the LC binding + `R(z0)=0`.

### 4.1 New types (in `ecdsa_verify_stranded_gway.rs` or a new `seam_rlc.rs` module)

```rust
use merkle::{MerkleChannelCfg, MerkleOpening, MerkleTreeChannel, compute_leaf_hash};
use crate::permutation_argument::{ExtField, EXT_DEGREE};
use crate::tower_field::TowerField;
use crate::fri::{deep_fri_prove, deep_fri_verify, DeepFriProof, FriDomain};

/// One strand's seam contribution: for each held (gid, col) the raw LDE column
/// values + a Merkle root committing them. Column key = (gid, col) global index.
pub struct StrandSeamColumns {
    pub cfg: MerkleChannelCfg,                       // shared, = seam_merkle_cfg(n_lde)
    pub columns: Vec<((usize /*gid*/, usize /*col*/), Vec<F> /*len n_lde*/, [u8;32] /*root*/)>,
}

/// The coordinator's global RLC seam proof (replaces StrandedProofG.seam_commits).
pub struct SeamRlcProof {
    pub component_proofs: Vec<DeepFriProof<ExtField>>,   // len d = EXT_DEGREE, each R^{(j)}
    /// Per query position q, per obligation m: the opened a_m(q), b_m(q) + Merkle openings.
    pub lc_openings: Vec<QueryLcOpening>,                // len r (= params.r)
}
pub struct QueryLcOpening {
    pub q: usize,
    pub rj_at_q: Vec<F>,                                  // R^{(j)}(q), len d  (from component_proofs' openings; see §5.3)
    pub a_vals: Vec<F>, pub a_ops: Vec<MerkleOpening>,    // per obligation m
    pub b_vals: Vec<F>, pub b_ops: Vec<MerkleOpening>,
}
```

`StrandedProofG` becomes `{ proofs: Vec<SubAirProofWithTrace>, seam_rlc: SeamRlcProof }`
(drop `seam_commits`). Keep the old field behind a feature or a sibling `StrandedProofGRlc`
if you want a non-breaking migration.

### 4.2 Prover — `prove_one_strand`

Return the strand's seam columns + roots instead of BCCs. Inside, the strand `lde` and
`cut.local(s, c)` are already available:

```rust
// after obtaining `lde`:
let cfg = seam_merkle_cfg(n_trace * blowup);   // MerkleChannelCfg::new(vec![2; log2(n_lde)], SEAM_TREE_LABEL)
let mut columns = Vec::new();
for (gid, sg) in cut.seams.iter().enumerate() {
    if !sg.holders.contains(&s) { continue; }
    for &c in &sg.cols {
        let col: Vec<F> = lde[cut.local(s, c)].clone();   // raw seam column (16 KiB), NOT a BCC
        let vals: Vec<Vec<F>> = col.iter().map(|&v| vec![v]).collect();
        let mut tree = MerkleTreeChannel::new(cfg.clone(), [0u8;32]);
        let root = tree.commit_compact(&vals);
        columns.push(((gid, c), col, root));
    }
}
(proof, StrandSeamColumns { cfg, columns })
```

Cost/size: emitting a raw column (16 KiB) is far cheaper than committing a BCC (FRI prove
+ ~0.9 MiB). This removes the dominant per-strand seam prove cost AND the 4.7 GiB seam
data. RSS per strand is unaffected (a column is a slice of the already-resident `lde`).

### 4.3 Coordinator — new `aggregate_seams_rlc`

```rust
pub fn aggregate_seams_rlc<P>(strand_seams: &[StrandSeamColumns], cut: &GwayCut,
    n_trace: usize, blowup: usize, pi_hash: [u8;32], params_fn: P) -> SeamRlcProof
where P: Fn(usize,[u8;32]) -> DeepFriParams + Copy
{
    let n_lde = n_trace * blowup;
    // 1. Enumerate obligations m = (gid, holder h, col c): a_m = column of holders[0],
    //    b_m = column of h. Look them up in strand_seams by (gid,col).
    //    Build diffs d_m = a_m − b_m (Vec<F> len n_lde) AND keep (a_m, b_m, roots) for binding.
    // 2. α = derive_alpha(pi_hash); c_{m,j} = (α^m).to_fp_components()[j].
    // 3. For j in 0..EXT_DEGREE: R^{(j)} = Σ_m c_{m,j}·d_m; proof_j = deep_fri_prove::<ExtField>(R^{(j)}, FriDomain::new_radix2(n_lde), &params_fn(n_lde,pi_hash)).
    // 4. Build lc_openings at the FRI query positions (see §5.3).
}
```

### 4.4 Verifier — replace `verify_seams`

```rust
pub fn verify_seams_rlc<P>(seam: &SeamRlcProof, strand_roots: &SeamRootIndex, cut, n_trace,
    blowup, pi_hash, params_fn) -> Result<(),String> {
    let params = params_fn(n_trace*blowup, pi_hash);
    // (a) d FRI verifies + recombine R(z0):
    let mut r_z0 = ExtField::zero();
    for (j, pj) in seam.component_proofs.iter().enumerate() {
        if !deep_fri_verify::<ExtField>(&params, pj) { return Err(format!("seam R[{j}] FRI reject")); }
        r_z0 += basis(j) * pj.fz_per_layer[0];
    }
    if !r_z0.is_zero() { return Err("seam RLC: R(z0) ≠ 0 (a seam differs)".into()); }
    // (b) per-query LC binding: recompute α^m/c_{m,j}; for each QueryLcOpening:
    //     verify a_m(q), b_m(q) Merkle openings against the strand roots;
    //     check rj_at_q[j] == Σ_m c_{m,j}(a_m(q) − b_m(q)) for every j;
    //     check rj_at_q[j] equals the value the component proof opens at q (§5.3).
    Ok(())
}
```

`verify_stranded_g` then calls `verify_seams_rlc` in place of `verify_seams`; the strand
loop is unchanged.

## 5. Precise details & gotchas

1. **α derivation.** `α = ExtField::from_fp_components([H(pi_hash‖"seam-rlc-alpha"‖j)]_{j<d})`.
   MUST be FS-derived from `pi_hash` (statement binding — see `docs/…` and the pi-binding
   discussion). Absorb the strand seam roots into the transcript too (adaptive soundness):
   `α = H(pi_hash ‖ all seam roots ‖ "alpha")`.
2. **Obligation order.** `m` must be enumerated identically by prover and verifier
   (iterate `cut.seams` in order; `holders[0]` = ref; `holders[1..]` in order; `cols` in
   order). `α^m` powers depend on this order.
3. **Query positions & `rj_at_q` (the real coupling).** For the tightest binding, use the
   component proofs' OWN FRI query positions rather than a fresh FS set: for `proof_j`,
   `proof_j.queries[qi].per_layer_refs[0].i` is the layer-0 index `q`, and
   `proof_j.queries[qi].per_layer_payloads[0].f_val` is `R^{(j)}(q)` (Ext; its base-F
   component is the value). Then open `a_m(q), b_m(q)` from the strand Merkle trees at those
   `q`. NB the d component proofs have DIFFERENT query sets; either (i) open `a_m, b_m` at
   each proof's own `q` set (d·r openings/column), or (ii) derive ONE shared `Q` from
   `H(pi_hash ‖ all roots ‖ all component roots)` and open all (a,b,R^{(j)}) at `Q` — simpler,
   still sound, but requires exposing R^{(j)}(q) for arbitrary q (commit R^{(j)} in a side
   Merkle tree like a_m, OR use option (i)). The `seam_rlc_bound.rs` prototype uses (ii)
   with side Merkle trees; production likely wants (i) to avoid extra commitments.
4. **Value binding.** verify `compute_leaf_hash(&cfg, q, &[v]) == opening.leaf` AND
   `MerkleTreeChannel::verify_opening(&cfg, root, &opening, &trace_hash)`.
5. **`n_lde` power-of-two.** Seam columns are single columns → `n_lde` is already a
   power of two (no padding, unlike the packing approach).
6. **Shared `z0`.** All R^{(j)} use the same `params` (same `seed_z`, `pi_hash`, `n0=n_lde`)
   so they share `z0` — required for the recombination and for comparability with the
   strands' OOD points. (This is the existing `verify_ood_consistency` precondition.)
7. **Holders > 2 / single-holder groups.** A group with `holders=[h0,h1,h2]` yields
   obligations `(h0−h1)` and `(h0−h2)` per column — fold both into the global RLC. A group
   with a single holder yields no obligation (skip).
8. **`a_m` vs `b_m` low-degree.** NOT re-tested by the seam batch — it is guaranteed by the
   strand sub-AIR proofs (`verify_one_strand`), which prove each strand's LDE (including its
   seam columns) is a valid low-degree extension. State this dependency explicitly.
9. **κ_sys.** `ε_seam ≤ (M+n)/|F_ext|` — at L1 Fp6 (`|F_ext| ≈ 2^378`, M≈2^12, n≈2^11)
   `≈ 2^-360 ≫ 2^-128`. So `κ_seam` is never the binding term;
   `κ_sys = min(κ_IT, κ_bind, κ_FS, κ_seam)` is unchanged. Assert this in a test at L1/L3/L5.

## 6. Test plan (port from the examples; add to lib `#[cfg(test)]`)

- **Honest** end-to-end stranded prove → verify accepts (small K, e.g. K=4, G=2/4).
- **Tampered strand** interior cell → strand FRI rejects (unchanged behaviour).
- **★ Tampered seam** (flip one seam column post-commit in one strand) → `R(z0) ≠ 0` reject.
- **★ Forged R=0** (coordinator commits R^{(j)}=0 while a seam differs) → LC binding reject.
- **Merkle tamper** (corrupt an `a_m`/`b_m` opening) → `verify_opening` reject.
- **Wrong pi_hash** at verify → reject (α/z0 re-derive; strand-proof pi binding).
- **κ_seam ≥ target** at L1/L3/L5 (build under sha3-256/384/512).
- **Re-measure** the full stranded prove+verify (`ecdsa_verify_stranded_gway_bench.rs` /
  `gway_reconstruction.rs`): expect seam-verify from ~36.5 s → sub-second, seam proof data
  ~2.36 GiB → tens of MiB, reconstruction RSS further reduced (raw cols + d proofs, no BCCs).

## 7. Migration

Additive-first is safest: add `StrandedProofGRlc` + `prove_one_strand_seam_columns` +
`aggregate_seams_rlc` + `verify_stranded_g_rlc` alongside the existing path; switch the
benches/harnesses; once green, retire `seam_commits` / `verify_seams` /
`verify_ood_consistency` from the stranded path (keep `verify_ood_consistency` — it may be
used elsewhere; grep before removing).

## 8. References

Examples (all on `feature/accumulation-recursion`, example/test-only):
- `crates/deep_ali/examples/seam_rlc_batch.rs` — component-decomposition reduction + consistency (`bf94c69`)
- `crates/deep_ali/examples/seam_rlc_bound.rs` — per-query LC binding, forgery caught (`36be7c4`)
- `crates/deep_ali/examples/seam_rlc_coordinator.rs` — real-cut global RLC, 874× / 58× (`8e0c201`)
- `crates/deep_ali/examples/seam_batch_bridge.rs` — packing (rejected: 1.2× wall / 8× RSS) (`9b08f8c`, `1968976`)
- Streaming reconstruction context: `crates/deep_ali/examples/gway_reconstruction.rs`

Key APIs: `merkle` crate (`MerkleTreeChannel`, `commit_compact`/`open_compact`/`verify_opening`,
`compute_leaf_hash`, `MerkleChannelCfg`, `MerkleOpening`); `deep_fri_prove`/`deep_fri_verify`,
`DeepFriProof.{fz_per_layer, queries, root_f0}`, `FriQueryPayload.{per_layer_refs,
per_layer_payloads}`, `LayerQueryRef.i`; `TowerField::{DEGREE, from_fp, to_fp_components,
from_fp_components}`, `ExtField`, `EXT_DEGREE`.

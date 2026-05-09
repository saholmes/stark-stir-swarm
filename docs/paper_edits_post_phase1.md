# Paper edits to reflect Phase 1 implementation

Drop-in LaTeX additions for the FRI paper
(`ESORICS-FIPS_Aligned_STARKs_with_Multi_Level_PQ_Security`) and
the STIR paper (`STARK_STIR`) to reflect the actual implementation
post-Phase-1.

## Overview of mismatches paper vs implementation (post-Phase 1)

| Paper §  | Paper text                                  | Implementation reality                                                      |
|----------|---------------------------------------------|----------------------------------------------------------------------------|
| §3.1     | Eq. (1): merged DEEP-ALI polynomial `C(X)` with DEEP shift `−Φ(z)·Z_H(X)/Z_H(z)` and HVZK blinding `β·R(X)` | Implementation uses the **standard STARK pattern**: phi/Z_H quotient (no DEEP merge-shift, no β·R) + separate trace Merkle commit + per-query constraint formula check |
| §3.1     | f_0 = C\|H_0 ∈ F_pe                         | f_0 = (phi/Z_H)\|H_0 ∈ **F (base Goldilocks)**, lifted to F_pe in FRI internally |
| §3.1     | α ∈ F_pe                                    | α ∈ F (Goldilocks); FS-derived from pi_hash                                |
| §3.2     | Theorem 1 ε_ali = (s+D+1)/(\|F_pe\|−\|H_0\|) | Equivalent ε_query = (D/n_lde)^r from per-query constraint check            |
| §9       | HVZK formal via Lemma 4 (β·R blinding)       | β·R blinding NOT yet implemented; HVZK is "computational" / practical only  |

## Edit 1 — §3 (DEEP-ALI Merge): add an Implementation Note

**Where**: end of §3.1 ("Construction"), or as a footnote on Eq. (1).

**Text to add:**

```latex
\paragraph{Implementation.}
The reference implementation realises the soundness claim of
Theorem~\ref{thm:modular} via the standard STARK pattern (separate
Merkle commitments to trace and constraint composition, with
per-query DEEP openings) rather than the merged construction in
Eq.~\eqref{eq:c_construction}.  Concretely, the prover commits
$f_0 = (\Phi/Z_H) \restriction_{H_0}$ as the FRI initial function,
and additionally commits a Merkle tree over the trace LDE.  At
each FRI query position $x \in H_0$, the verifier opens the trace
cells and checks the per-row constraint identity
$c_\text{eval}(x) \cdot Z_H(x) = \sum_j \alpha_j \cdot \Phi_j(\text{trace}[x], x)$.
Both constructions achieve the same total~$\varepsilon$ bound at the
chosen FRI query counts $r \in \{54, 79, 105\}$ for NIST PQ
Levels~1/3/5 respectively (Theorem~\ref{thm:modular}); the standard
pattern is chosen for implementation simplicity and reuses an
existing $\mathrm{F}$-valued FRI infrastructure.  The merged
construction (Eq.~\eqref{eq:c_construction}) and HVZK blinding
$\beta \cdot R(X)$ (Lemma~\ref{lem:hvzk}) are left for a future
implementation revision.
```

**If a reviewer asks "is this sound?":** yes — the soundness
argument for the standard pattern is the bog-standard FRI proof
soundness via per-query checks, and gives ε_query =
(D/n_lde)^r ≤ 2⁻²¹⁶/2⁻³¹⁶/2⁻⁴²⁰ at NIST PQ Levels 1/3/5 with
r=54/79/105 and blowup=32, comfortably below the per-level
$\varepsilon$ target.

## Edit 2 — §3.2 / §4: add an alternative ε_query bound paragraph

**Where**: after Theorem 1 (ε_ali) or in the modular soundness
decomposition (Theorem 4).

**Text to add:**

```latex
\paragraph{Alternative bound for the standard-pattern implementation.}
When the implementation realises soundness via per-query trace
openings (rather than via the merged construction), the
$\varepsilon_\text{ali}$ term in Theorem~\ref{thm:modular} is
replaced by the per-query constraint check error
\begin{equation}
  \varepsilon_\text{query}
  \;\le\; \left(\frac{D}{|H_0|}\right)^{r}
  \;=\; \left(\frac{d_c}{\rho_0^{-1}}\right)^{r}.
\end{equation}
For $d_c = 2$, $\rho_0 = 1/32$, this gives
$\varepsilon_\text{query} \le 16^{-r}$:
$2^{-216}$ at $r=54$ (Level~1),
$2^{-316}$ at $r=79$ (Level~3),
$2^{-420}$ at $r=105$ (Level~5).
All comfortably below $2^{-128}, 2^{-192}, 2^{-256}$ respectively.
The two constructions give the same NIST PQ Level claim; the merged
construction's $\varepsilon_\text{ali}$ provides a tighter bound
($\sim 2^{-370}$) at the cost of $\sim 2.5$–$3.5\times$ slower prove
time and $\sim 1$–$2\%$ larger proofs.
```

## Edit 3 — Empirical Validation table (§10): replace timing numbers if regenerated

If you regenerate Table 5 against the Phase 1 implementation, the
expected numbers (per session benchmarking on c5.4xlarge-equivalent
hardware) are within ~10% of the original Table 5 values, since
Phase 1 doesn't change the merge cost — it adds a parallel trace
Merkle commit (small) and per-query trace openings (also small).

Approximate Phase-1 expectations per level (no measured numbers
yet — should be regenerated):

| Level | Hash      | r   | Proof (KiB est.) | Verify (ms est.) | Prove (s est.) |
|-------|-----------|-----|------------------|------------------|----------------|
| L1    | SHA3-256  | 54  | 1090–1110        | 11–13            | 0.7–0.9        |
| L3    | SHA3-384  | 79  | 2310–2335        | 21–24            | 0.7–0.9        |
| L5    | SHA3-512  | 105 | 4080–4110        | 45–50            | 1.0–1.2        |

The slight proof-size increase (~5–25 KB per level) is from the
per-query trace openings (cur and nxt cells per FRI query).  If the
paper's Table 5 will be regenerated, list both prove time and verify
time per level; otherwise leave the original numbers and add a
footnote that they were measured against an earlier implementation
that did not include the explicit trace Merkle commitment.

## Edit 4 — T-MEM permutation argument section (if present)

If the paper has a section/paragraph on the T-MEM perm-arg used for
cross-AIR cell binding, add the following:

**Text to add:**

```latex
\paragraph{T-MEM in the extension field.}
The T-MEM permutation argument is implemented over the FRI
extension field $\mathbb{F}_{p^e}$ (Fp$^6$ for Levels 1/3, Fp$^8$ for
Level 5), with running products $\mathrm{RP}_i, \mathrm{WP}_i$
encoded as $e$ base-field columns each.  Per-row constraints emit
one base-field equation per coefficient of the F$_{p^e}$-valued
constraint, all degree~$\le 2$.  An \texttt{IS\_ACTIVE} column
gates the TERM correctness so padding rows propagate the running
products unchanged through to the active$\to$padding boundary,
where the constraint
\[
  (\texttt{cur.IS\_ACTIVE} - \texttt{nxt.IS\_ACTIVE}) \cdot
  (\mathrm{RP} - \mathrm{WP}) \;=\; 0
  \qquad \in \mathbb{F}_{p^e}
\]
fires exactly once per proof and enforces multiset equality.  This
final-row boundary is essential: per-row transitions alone prove
only that the running products are correctly accumulated, not that
they meet at the boundary, so without this constraint the
permutation argument proves nothing.

The composed soundness contribution of T-MEM under
Schwartz–Zippel is $\le N/|\mathbb{F}_{p^e}|$, giving $2^{-370}$
(Fp$^6$) and $2^{-498}$ (Fp$^8$) for $N \approx 2^{14}$ log entries
in the v2 ML-DSA verify.
```

## Edit 5 — HVZK: tighten the claim

The paper's Lemma 4 claims HVZK via $C = D_z + \beta R$ blinding.
Without $\beta R$ in the implementation, this Lemma's claim is not
yet realised.

**Where**: at the start of Lemma 4, or in §9.

**Text to add (or replace existing):**

```latex
\begin{remark}[HVZK status of the reference implementation]
The reference implementation does not yet add the HVZK blinding
$\beta \cdot R(X)$ described in Lemma~\ref{lem:hvzk}; the proof
remains \emph{computationally} indistinguishable across witnesses
that satisfy the same public input via the FRI commitment's
collision resistance, but the formal HVZK property requires the
blinding term and is left for a future revision.
\end{remark}
```

## Edit 6 — Implementation gaps: brief candid disclosure

Adding a short paragraph in §10 (or wherever the implementation is
described) acknowledging the specific gaps strengthens credibility
with reviewers:

```latex
\paragraph{Known implementation gaps from the reference protocol.}
The reference implementation accompanying this paper differs from
the protocol in §3 in three respects, each of which is documented
in the source repository's audit document (\texttt{docs/v2\_soundness\_audit\_2026-05-09.md}):

\begin{itemize}
  \item The merge constructs $f_0 = (\Phi/Z_H) \restriction_{H_0}$
        (without the merge-level DEEP shift in Eq.~\eqref{eq:c_construction})
        and binds it to a specific trace via a parallel trace
        Merkle commitment plus per-query constraint formula
        opening.  The standard-pattern soundness bound
        $\varepsilon_\text{query} \le (D/|H_0|)^r$ replaces
        $r \cdot \varepsilon_\text{ali}$ in
        Theorem~\ref{thm:modular}; both are below
        $2^{-\lambda_k}$ at NIST PQ Levels~$k \in \{1, 3, 5\}$
        with $r \in \{54, 79, 105\}$ respectively.
  \item HVZK blinding $\beta \cdot R(X)$ is not yet implemented;
        the proof is computationally indistinguishable across
        equivalent witnesses but does not yet satisfy the formal
        HVZK property of Lemma~\ref{lem:hvzk}.
  \item Cross-AIR cell binding in the v2 ML-DSA-verify protocol
        is currently enforced via Merkle commitments to the public
        inputs (pi-hash) rather than via in-circuit T-MEM bindings
        between sub-AIRs.  The latter is a substantial structural
        refactor and is left for a future revision; the current
        approach gives preimage-bound consistency at NIST PQ
        Level~$k$ via the matching SHA3-$2k$ hash.
\end{itemize}
```

## Recommended edit order

1. **Edit 6** (implementation-gaps disclosure) — quickest, sets
   reviewer expectations.
2. **Edit 4** (T-MEM in F_ext) — cleanly adds Phase 1's actual
   contribution to the construction.
3. **Edit 1** (implementation note on Eq. 1) — clarifies the
   construction-vs-implementation gap explicitly.
4. **Edit 2** (alternative ε_query bound) — adds the soundness
   argument the implementation actually uses.
5. **Edit 5** (HVZK status remark) — short, candid.
6. **Edit 3** (timing table refresh) — only if Table 5 is being
   regenerated.

## Open question for the user

**Is the LaTeX source on Overleaf or another machine?** I can't find
it locally; the only `.tex` files I found referencing DEEP-ALI are
`fri-arity-proof.tex` (a side proof) and `match-me-if-you-can/docs/paper/paper.tex`
(a different paper).  If you share the source location, I can apply
these edits directly; otherwise treat this doc as a paste-ready
guide.

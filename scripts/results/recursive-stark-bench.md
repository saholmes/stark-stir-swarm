# Recursive ML-DSA STARK Bench

**Host:** `192.168.1.152` · **Cores:** `10` · **Blowup:** `4` · **Git:** `2b2fa48`

Each row is one prove + verify of the **composed** recursive STARK statement (constraint composition ∧ binding-cells OOD ∧ perm-arg multiset equality), produced as a single outer DeepFriProof<SexticExt>.

| Variant | NIST L | Blowup | r | LDT | Prove (ms) | Verify (ms) | Proof (KiB) | n_trace | n_constraints | n_ood | n_perm |
|---|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| sha3-256 | L1 | 4 | 54 | fri | 1.7 | 1.00 | 200.5 | 8 | 6 | 7 | 5 |
| sha3-256 | L1 | 4 | 54 | stir | 0.5 | 0.20 | 46.3 | 8 | 6 | 7 | 5 |
| sha3-384 | L3 | 4 | 79 | fri | 1.5 | 1.66 | 394.4 | 8 | 6 | 7 | 5 |
| sha3-384 | L3 | 4 | 79 | stir | 0.6 | 0.36 | 93.2 | 8 | 6 | 7 | 5 |
| sha3-512 | L5 | 4 | 105 | fri | 1.6 | 2.90 | 658.7 | 8 | 6 | 7 | 5 |
| sha3-512 | L5 | 4 | 105 | stir | 0.7 | 0.69 | 158.0 | 8 | 6 | 7 | 5 |

## Notes
- Statement proven: "I know witnesses such that Σ α·Φ = expected (composition) ∧ Σ α·(f − g) = 0 (binding-cells OOD) ∧ ∏(γ + l) = ∏(γ + r) (perm-arg)".
- All three sub-circuits LDE'd on a shared domain of n_trace_max × blowup, summed with FS-derived outer α's into a single outer c_eval.
- Synthesised witnesses: 6 XOR constraints + 7 OOD binding-cells claims + 5-element multisets — these are the structural shapes of an inner ML-DSA-65 verification's three required sub-circuits.
- All measurements at `--features parallel` with RAYON_NUM_THREADS=`10` pinned.

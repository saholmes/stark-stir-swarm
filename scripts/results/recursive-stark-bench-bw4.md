# Recursive ML-DSA STARK Bench

**Host:** `192.168.1.152` · **Cores:** `10` · **Blowup:** `4` · **Git:** `c90b902`

Each row is one prove + verify of the **composed** recursive STARK statement (constraint composition ∧ binding-cells OOD ∧ perm-arg multiset equality), produced as a single outer DeepFriProof<SexticExt>.

| Variant | NIST L | Blowup | r | LDT | Prove (ms) | Verify (ms) | Proof (KiB) | n_trace | n_constraints | n_ood | n_perm |
|---|---|---:|---:|---|---:|---:|---:|---:|---:|---:|---:|
| sha3-256 | L1 | 4 | 135 | stir | 0.9 | 0.53 | 114.0 | 8 | 6 | 7 | 5 |
| sha3-384 | L3 | 4 | 198 | stir | 1.7 | 1.69 | 231.8 | 8 | 6 | 7 | 5 |
| sha3-512 | L5 | 4 | 263 | stir | 2.2 | 1.62 | 393.9 | 8 | 6 | 7 | 5 |

## Notes
- Statement proven: "I know witnesses such that Σ α·Φ = expected (composition) ∧ Σ α·(f − g) = 0 (binding-cells OOD) ∧ ∏(γ + l) = ∏(γ + r) (perm-arg)".
- All three sub-circuits LDE'd on a shared domain of n_trace_max × blowup, summed with FS-derived outer α's into a single outer c_eval.
- Synthesised witnesses: 6 XOR constraints + 7 OOD binding-cells claims + 5-element multisets — these are the structural shapes of an inner ML-DSA-65 verification's three required sub-circuits.
- All measurements at `--features parallel` with RAYON_NUM_THREADS=`10` pinned.

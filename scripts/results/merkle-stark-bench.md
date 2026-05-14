# Wrapper-STARK Merkle Path Bench

**Host:** `192.168.1.152` · **Cores:** `10` · **Blowup:** `4` · **Variant:** `SHA3-256` (L1, r=54)

Each row is one prove + verify of a Merkle authentication path STARK at the given depth, evaluated through deep_ali's deep_fri_prove.

| Depth (log₂) | Leaves | Blowup | r | LDT | Prove (ms) | Verify (ms) | Proof (KiB) | n_trace |
|---:|---:|---:|---:|---|---:|---:|---:|---:|
| 2 | 4 | 4 | 54 | fri | 764 | 1.25 | 395.9 | 256 |
| 2 | 4 | 4 | 54 | stir | 744 | 0.37 | 109.2 | 256 |
| 3 | 8 | 4 | 54 | fri | 1645 | 1.39 | 431.0 | 512 |
| 3 | 8 | 4 | 54 | stir | 1644 | 0.38 | 111.5 | 512 |
| 4 | 16 | 4 | 54 | fri | 1670 | 1.39 | 431.0 | 512 |
| 4 | 16 | 4 | 54 | stir | 1686 | 0.37 | 111.5 | 512 |

## Notes
- Statement proven: "I know a leaf + authentication path such that the Merkle chain hashes to the public root."
- Trace: `d × 98` rows (1 merkle hop + 97 sponge_air sub-rows per hop), padded to next power of 2.
- Constraints: selection (2N per hop) + sponge sub-AIR (~22k per absorb) + cross-row bindings (~2N per hop) + root boundary.
- All measurements at `--features parallel` with RAYON_NUM_THREADS=`10` pinned.

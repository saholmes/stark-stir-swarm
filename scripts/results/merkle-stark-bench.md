# Wrapper-STARK Merkle Path Bench

**Host:** `192.168.1.152` · **Cores:** `10` · **Blowup:** `4` · **Variant:** `SHA3-256` (L1, r=54)

Each row is one prove + verify of a Merkle authentication path STARK at the given depth, evaluated through deep_ali's deep_fri_prove.

| Depth (log₂) | Leaves | Blowup | r | LDT | Prove (ms) | Verify (ms) | Proof (KiB) | n_trace |
|---:|---:|---:|---:|---|---:|---:|---:|---:|
| 2 | 4 | 4 | 54 | fri | 820 | 1.23 | 395.9 | 256 |
| 2 | 4 | 4 | 54 | stir | 770 | 0.35 | 109.2 | 256 |
| 3 | 8 | 4 | 54 | fri | 1650 | 1.40 | 431.0 | 512 |
| 3 | 8 | 4 | 54 | stir | 1685 | 0.37 | 111.5 | 512 |
| 4 | 16 | 4 | 54 | fri | 1730 | 1.43 | 431.0 | 512 |
| 4 | 16 | 4 | 54 | stir | 1724 | 0.38 | 111.5 | 512 |
| 5 | 32 | 4 | 54 | fri | 1781 | 1.42 | 431.0 | 512 |
| 5 | 32 | 4 | 54 | stir | 1761 | 0.36 | 111.5 | 512 |
| 6 | 64 | 4 | 54 | fri | 3697 | 1.61 | 468.2 | 1024 |
| 6 | 64 | 4 | 54 | stir | 3691 | 0.41 | 113.7 | 1024 |
| 7 | 128 | 4 | 54 | fri | 3813 | 1.61 | 468.2 | 1024 |
| 7 | 128 | 4 | 54 | stir | 3825 | 0.42 | 113.7 | 1024 |

## Notes
- Statement proven: "I know a leaf + authentication path such that the Merkle chain hashes to the public root."
- Trace: `d × 98` rows (1 merkle hop + 97 sponge_air sub-rows per hop), padded to next power of 2.
- Constraints: selection (2N per hop) + sponge sub-AIR (~22k per absorb) + cross-row bindings (~2N per hop) + root boundary.
- All measurements at `--features parallel` with RAYON_NUM_THREADS=`10` pinned.

# Wrapper-STARK Merkle Path Bench

**Host:** `192.168.1.152` · **Cores:** `10` · **Blowup:** `4` · **Levels:** `L1 L3`

Each row is one prove + verify of a Merkle authentication path STARK at the given depth, evaluated through deep_ali's deep_fri_prove.

| Level | Hash | Depth | Leaves | Blowup | r | LDT | Prove (ms) | Verify (ms) | Proof (KiB) | n_trace |
|---|---|---:|---:|---:|---:|---|---:|---:|---:|---:|
| L1 | sha3-256 | 2 | 4 | 4 | 54 | fri | 810 | 1.30 | 395.9 | 256 |
| L1 | sha3-256 | 2 | 4 | 4 | 54 | stir | 744 | 0.36 | 109.2 | 256 |
| L1 | sha3-256 | 3 | 8 | 4 | 54 | fri | 1663 | 1.39 | 431.0 | 512 |
| L1 | sha3-256 | 3 | 8 | 4 | 54 | stir | 1666 | 0.37 | 111.5 | 512 |
| L1 | sha3-256 | 4 | 16 | 4 | 54 | fri | 1708 | 1.40 | 431.0 | 512 |
| L1 | sha3-256 | 4 | 16 | 4 | 54 | stir | 1699 | 0.36 | 111.5 | 512 |
| L3 | sha3-384 | 2 | 4 | 4 | 79 | fri | 756 | 2.47 | 772.7 | 256 |
| L3 | sha3-384 | 2 | 4 | 4 | 79 | stir | 743 | 0.70 | 228.1 | 256 |
| L3 | sha3-384 | 3 | 8 | 4 | 79 | fri | 1659 | 2.86 | 838.8 | 512 |
| L3 | sha3-384 | 3 | 8 | 4 | 79 | stir | 1667 | 0.74 | 232.6 | 512 |
| L3 | sha3-384 | 4 | 16 | 4 | 79 | fri | 1715 | 2.86 | 838.8 | 512 |
| L3 | sha3-384 | 4 | 16 | 4 | 79 | stir | 1707 | 0.73 | 232.6 | 512 |

## Notes
- Statement proven: "I know a leaf + authentication path such that the Merkle chain hashes to the public root."
- Trace: `d × 98` rows (1 merkle hop + 97 sponge_air sub-rows per hop), padded to next power of 2.
- Constraints: selection (2N per hop) + sponge sub-AIR (~22k per absorb) + cross-row bindings (~2N per hop) + root boundary.
- All measurements at `--features parallel` with RAYON_NUM_THREADS=`10` pinned.

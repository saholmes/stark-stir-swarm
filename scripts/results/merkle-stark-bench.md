# Wrapper-STARK Merkle Path Bench

**Host:** `192.168.1.152` · **Cores:** `10` · **Blowup:** `4` · **Levels:** `L1 L3 L5`

Each row is one prove + verify of a Merkle authentication path STARK at the given depth, evaluated through deep_ali's deep_fri_prove.

| Level | Hash | Depth | Leaves | Blowup | r | LDT | Prove (ms) | Verify (ms) | Proof (KiB) | n_trace |
|---|---|---:|---:|---:|---:|---|---:|---:|---:|---:|
| L1 | sha3-256 | 2 | 4 | 4 | 54 | fri | 833 | 1.36 | 395.9 | 256 |
| L1 | sha3-256 | 2 | 4 | 4 | 54 | stir | 767 | 0.37 | 109.2 | 256 |
| L1 | sha3-256 | 3 | 8 | 4 | 54 | fri | 1659 | 1.37 | 431.0 | 512 |
| L1 | sha3-256 | 3 | 8 | 4 | 54 | stir | 1633 | 0.40 | 111.5 | 512 |
| L1 | sha3-256 | 4 | 16 | 4 | 54 | fri | 1712 | 1.43 | 431.0 | 512 |
| L1 | sha3-256 | 4 | 16 | 4 | 54 | stir | 1693 | 0.38 | 111.5 | 512 |
| L3 | sha3-384 | 2 | 4 | 4 | 79 | fri | 789 | 2.51 | 772.7 | 256 |
| L3 | sha3-384 | 2 | 4 | 4 | 79 | stir | 774 | 0.69 | 228.1 | 256 |
| L3 | sha3-384 | 3 | 8 | 4 | 79 | fri | 1673 | 2.92 | 838.8 | 512 |
| L3 | sha3-384 | 3 | 8 | 4 | 79 | stir | 1679 | 0.74 | 232.6 | 512 |
| L3 | sha3-384 | 4 | 16 | 4 | 79 | fri | 1726 | 2.88 | 838.8 | 512 |
| L3 | sha3-384 | 4 | 16 | 4 | 79 | stir | 1719 | 0.74 | 232.6 | 512 |
| L5 | sha3-512 | 2 | 4 | 4 | 105 | fri | 786 | 4.66 | 1284.3 | 256 |
| L5 | sha3-512 | 2 | 4 | 4 | 105 | stir | 796 | 1.37 | 394.5 | 256 |
| L5 | sha3-512 | 3 | 8 | 4 | 105 | fri | 1715 | 5.50 | 1391.9 | 512 |
| L5 | sha3-512 | 3 | 8 | 4 | 105 | stir | 1680 | 1.50 | 402.1 | 512 |
| L5 | sha3-512 | 4 | 16 | 4 | 105 | fri | 1736 | 5.29 | 1391.9 | 512 |
| L5 | sha3-512 | 4 | 16 | 4 | 105 | stir | 1737 | 1.45 | 402.1 | 512 |

## Notes
- Statement proven: "I know a leaf + authentication path such that the Merkle chain hashes to the public root."
- Trace: `d × 98` rows (1 merkle hop + 97 sponge_air sub-rows per hop), padded to next power of 2.
- Constraints: selection (2N per hop) + sponge sub-AIR (~22k per absorb) + cross-row bindings (~2N per hop) + root boundary.
- All measurements at `--features parallel` with RAYON_NUM_THREADS=`10` pinned.

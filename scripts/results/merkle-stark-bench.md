# Wrapper-STARK Merkle Path Bench

**Host:** `192.168.1.152` · **Cores:** `10` · **Blowup:** `32` · **Levels:** `L1 L3 L5`

Each row is one prove + verify of a Merkle authentication path STARK at the given depth, evaluated through deep_ali's deep_fri_prove.

| Level | Hash | Depth | Leaves | Blowup | r | LDT | Prove (ms) | Verify (ms) | Proof (KiB) | n_trace |
|---|---|---:|---:|---:|---:|---|---:|---:|---:|---:|
| L1 | sha3-256 | 2 | 4 | 32 | 54 | fri | 8119 | 1.83 | 559.0 | 256 |
| L1 | sha3-256 | 2 | 4 | 32 | 54 | stir | 8070 | 0.42 | 116.0 | 256 |
| L1 | sha3-256 | 3 | 8 | 32 | 54 | fri | 17083 | 2.04 | 600.4 | 512 |
| L1 | sha3-256 | 3 | 8 | 32 | 54 | stir | 17079 | 0.49 | 144.1 | 512 |
| L3 | sha3-384 | 2 | 4 | 32 | 79 | fri | 8132 | 3.91 | 1096.4 | 256 |
| L3 | sha3-384 | 2 | 4 | 32 | 79 | stir | 8146 | 0.86 | 241.6 | 256 |
| L3 | sha3-384 | 3 | 8 | 32 | 79 | fri | 17214 | 4.33 | 1175.5 | 512 |
| L3 | sha3-384 | 3 | 8 | 32 | 79 | stir | 17162 | 0.97 | 302.3 | 512 |
| L5 | sha3-512 | 2 | 4 | 32 | 105 | fri | 8174 | 7.15 | 1827.7 | 256 |
| L5 | sha3-512 | 2 | 4 | 32 | 105 | stir | 8163 | 1.64 | 417.3 | 256 |
| L5 | sha3-512 | 3 | 8 | 32 | 105 | fri | 17208 | 8.04 | 1957.4 | 512 |
| L5 | sha3-512 | 3 | 8 | 32 | 105 | stir | 17201 | 1.90 | 524.1 | 512 |

## Notes
- Statement proven: "I know a leaf + authentication path such that the Merkle chain hashes to the public root."
- Trace: `d × 98` rows (1 merkle hop + 97 sponge_air sub-rows per hop), padded to next power of 2.
- Constraints: selection (2N per hop) + sponge sub-AIR (~22k per absorb) + cross-row bindings (~2N per hop) + root boundary.
- All measurements at `--features parallel` with RAYON_NUM_THREADS=`10` pinned.

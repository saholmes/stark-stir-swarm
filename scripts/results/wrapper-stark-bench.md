# Wrapper-STARK SHA-3 Bench

**Host:** `192.168.1.152` · **Cores:** `10` · **Blowup:** `4` · **Git:** `7f84890`

Each row is one prove + verify of SHA-3(message="abc") under the wrapper-stark row-uniform AIR, evaluated through deep_ali's deep_fri_prove.

| Variant | NIST L | Blowup | r | LDT | Prove (ms) | Verify (ms) | Proof (KiB) | n_trace |
|---|---|---:|---:|---|---:|---:|---:|---:|
| sha3-256 | L1 | 4 | 54 | fri | 336 | 1.05 | 362.9 | 128 |
| sha3-256 | L1 | 4 | 54 | stir | 344 | 0.34 | 81.1 | 128 |
| sha3-384 | L3 | 4 | 79 | fri | 317 | 2.11 | 710.8 | 128 |
| sha3-384 | L3 | 4 | 79 | stir | 318 | 0.57 | 167.4 | 128 |
| sha3-512 | L5 | 4 | 105 | fri | 325 | 3.87 | 1184.1 | 128 |
| sha3-512 | L5 | 4 | 105 | stir | 319 | 1.08 | 287.7 | 128 |

## Notes
- Row-uniform encoding per paper §3 + §5: 7 557-column schema (L1), 16 000 selected sub-step constraints per round + 5 957 always-active (booleanity + state threading).
- pi_hash binds (variant, message) into the FS transcript; verifier rejects on FS divergence (validated by tamper test).
- All measurements at `--features parallel` with RAYON_NUM_THREADS=`10` pinned.

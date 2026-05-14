# Wrapper-STARK SHA-3 Bench

**Host:** `192.168.1.152` · **Cores:** `10` · **Blowup:** `32` · **Git:** `80abdf4`

Each row is one prove + verify of SHA-3(message="abc") under the wrapper-stark row-uniform AIR, evaluated through deep_ali's deep_fri_prove.

| Variant | NIST L | Blowup | r | LDT | Prove (ms) | Verify (ms) | Proof (KiB) | n_trace |
|---|---|---:|---:|---|---:|---:|---:|---:|
| sha3-256 | L1 | 32 | 54 | fri | 3087 | 1.60 | 468.2 | 128 |
| sha3-256 | L1 | 32 | 54 | stir | 3068 | 0.41 | 113.7 | 128 |
| sha3-384 | L3 | 32 | 79 | fri | 2988 | 3.28 | 909.3 | 128 |
| sha3-384 | L3 | 32 | 79 | stir | 2963 | 0.78 | 237.1 | 128 |
| sha3-512 | L5 | 32 | 105 | fri | 2975 | 6.04 | 1506.9 | 128 |
| sha3-512 | L5 | 32 | 105 | stir | 2949 | 1.54 | 409.7 | 128 |

## Notes
- Row-uniform encoding per paper §3 + §5: 7 557-column schema (L1), 16 000 selected sub-step constraints per round + 5 957 always-active (booleanity + state threading).
- pi_hash binds (variant, message) into the FS transcript; verifier rejects on FS divergence (validated by tamper test).
- All measurements at `--features parallel` with RAYON_NUM_THREADS=`10` pinned.

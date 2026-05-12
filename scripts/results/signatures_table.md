# Signature STARK Benchmarks

**Host:** `192.168.1.152` · **Rust:** `1.86.0` · **Cores:** `10` · **Blowup:** `32` · **Git:** `f80ae27`

Each row reports a single signature-verification STARK round-trip (one signature, one full prove+verify) at the signature scheme's natural NIST PQ security level.

## STIR (default LDT)

| Scheme | NIST L | Hash | F_ext | Prove (ms) | Verify (ms) | Proof (KiB) |
|---|---|---|---|---:|---:|---:|
| RSA-2048 | L1 | sha3-256 | Fp6 | 157808 | 0.54 | 151.1 |
| Ed25519 | L1 | sha3-256 | Fp6 | 75000 | NA | 135 |
| ECDSA-p256 | L1 | sha3-256 | Fp6 | 167240 | NA | 138 |
| ML-DSA-44 | L1 | sha3-256 | Fp6 | 23727 | 83.42 | 10333.1 |
| ML-DSA-65 | L3 | sha3-384 | Fp6 | 29344 | 161.18 | 18412.0 |
| ML-DSA-87 | L5 | sha3-512 | Fp8 | 58219 | 351.98 | 29588.7 |

## FRI (`MMIYC_V2_USE_FRI=1` override)

| Scheme | NIST L | Hash | F_ext | Prove (ms) | Verify (ms) | Proof (KiB) |
|---|---|---|---|---:|---:|---:|
| RSA-2048 | L1 | sha3-256 | Fp6 | 158658 | 2.75 | 789.0 |
| Ed25519 | L1 | sha3-256 | Fp6 | 75000 | NA | 135 |
| ECDSA-p256 | L1 | sha3-256 | Fp6 | 167240 | NA | 138 |
| ML-DSA-44 | L1 | sha3-256 | Fp6 | 32310 | 182.31 | 15266.1 |
| ML-DSA-65 | L3 | sha3-384 | Fp6 | 40059 | 400.74 | 27820.8 |
| ML-DSA-87 | L5 | sha3-512 | Fp8 | 90796 | 925.74 | 49901.7 |

## Notes

- RSA-2048, Ed25519, ECDSA-p256 are NIST L1 signature primitives (~128-bit classical security). Running them with L3/L5 STARK soundness amplification is wasteful over-provisioning; the natural pairing is sha3-256 + Fp⁶.
- ML-DSA-{44,65,87} pair naturally with NIST L1/L3/L5 (sha3-{256,384,512} + Fp{6,6,8}).
- All cells use the same deep_ali_merge composition framework + STIR Theorem 1 / BCIKS Johnson-regime proximity bound. Soundness is unconditional at NIST PQ Levels 1/3/5 (no conjectures invoked).
- **REFERENCE rows** (Ed25519, ECDSA-P256) come from a 2026-05-01 warm Apple M4 Mac mini run that used the harness in `crossalg_three_signature_bench.rs` (no longer in this tree — see memory `project_crossalg_bench.md` / `project_ecdsa_status.md` for provenance).
- LIVE rows (RSA-2048, ML-DSA-44/65/87) are measured this run on the host listed at the top.
- Each LIVE measurement is a single run; for paper-grade numbers run 3+ times and take the median.

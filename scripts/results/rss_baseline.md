# Peak-RSS baseline — blowup=4, ldt=stir (arm64, 10 threads)

| Scheme | NIST | Peak RSS (MiB) | Prove (ms) | Proof (KiB) | Note |
|---|---|--:|--:|--:|---|
| rsa_bound | L1 | 272.1 | 836.0 | NA |  |
| ecdsa_bound | L1 | 5859.4 | 89742.1 | NA |  |
| ed25519_bound | L1 | 6189.3 | 10116.8 | NA |  |
| Ed25519 | L1 | — | — | — | full per-sig harness NOT in tree (see memory project_crossalg_bench) |
| ECDSA-P256 | L1 | — | — | — | AIR in sibling repo, NOT in tree (see memory project_ecdsa_status) |

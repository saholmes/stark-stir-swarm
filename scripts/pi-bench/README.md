# Raspberry Pi fleet-proving benchmark (DNS-STARK / S1d ML-DSA verify)

Measure end-to-end **throughput** and **wall time** of the fleet-sharded ML-DSA-44 verify on
Raspberry Pi (or any aarch64) compute — the low-cost proving fleet for DNS-STARK.

## Why a Pi fleet works

Every fleet strand is a **standalone low-RSS proof** (12–74 MiB/shard — measured on x86/Apple):
NTT butterfly, combine (finer: single-multiply), digit, z-norm, closing-hash. A Raspberry Pi 4/5
(4 cores, 4–8 GB) runs **many shards well within RAM** (25 MiB peak/shard). The whole ML-DSA-44
verify is ~640 shards; distributed across a fleet of Pis they prove in parallel, then a combiner
folds the outputs and the resolver verifies once (sub-ms to tens-of-ms — see the combiner flag).

## Quick start (on one Pi, 64-bit Pi OS)

```bash
# 1. toolchain (nightly per rust-toolchain.toml) + build deps
curl https://sh.rustup.rs -sSf | sh -s -- -y
sudo apt-get install -y build-essential pkg-config

# 2. clone the repo (with the binius sibling checkout — see repo root)
# 3. run the benchmark
cd stark-binius-swarm/scripts/pi-bench
SHARD_COEFFS=32 ./pi-fleet-bench.sh
```

It runs two steps and saves results under `results/pi-<stamp>/`:

1. **`single_device_rss_pipeline`** — the FIRST test: proves ONE shard of every strand type
   SEQUENTIALLY on this one Pi, sampling the process peak RSS (getrusage high-water) after each.
   It shows the peak **plateaus at ≈ one strand** (each shard freed before the next), not the sum —
   the low-RSS story on a single node. On an aarch64 M4 proxy (SHARD_COEFFS=16):

   ```
   after NTT-butterfly shard : 23 MiB
   after combine shard       : 24 MiB
   after digit shard         : 24 MiB
   after z-norm shard         : 24 MiB
   after closing-hash shard  : 25 MiB  ← PEAK across all 5 strands
   PEAK RSS whole pipeline    : 25 MiB  ⇒ 1 GB Pi headroom 40× ; < 500 MiB: YES
   combiner = trustless, verify 9 ms ; wall 7.8 s (sequential on one node)
   ```

   **This is the "one Pi to test the RSS pipeline" run.** Start here: it validates the whole
   ML-DSA-44 verify pipeline runs on one 1 GB Pi at ~25 MiB, then aggregate + verify locally.

2. **`fleet_throughput_model`** — per-strand unit shard cost (ms + RSS), then the end-to-end
   model: shards/signature, total shard-work, per-signature latency, and **throughput (sigs/hr)**
   at fleet sizes 1 / 4 / 16 / 64 / 256 Pis (sizes the fleet for a target rate).

`SHARD_COEFFS` tunes shard size (fewer coeffs/shard = smaller, faster, lower-RSS shards, more of
them). `PIN_CORE=0` pins to one core for a per-core baseline.

## Reference (aarch64 proxy, Apple M4 core, `--features parallel`, SHARD_COEFFS=32)

| strand | ms/shard | RSS |
|---|---|---|
| NTT butterfly | 3481 | 22 MiB |
| combine (×) | 3408 | 24 MiB |
| digit | 1546 | 24 MiB |
| z-norm | 186 | 25 MiB |
| closing-hash | 1685 | 25 MiB |

Per ML-DSA-44 verify: **641 shards, ~2050 s total shard-work single-core, 25 MiB peak RSS.**
Throughput scales ~linearly with the fleet: 256 Pis ⇒ ~8 s/signature latency, ~449 sigs/hr
(on M4-class cores). RSS stays 25 MiB regardless. For real low-end-Pi numbers see below — a
Cortex-A7 turned out ~40× slower than the M4, so scale throughput by core speed, not a small factor.

## Measured on a real Raspberry Pi 2 (2026-07-17) — the low-RSS claim on genuine 1 GB hardware

Mythic Beasts hosted Pi 2: **ARMv7 Cortex-A7, 4 cores, ~944 MB RAM (≈1 GB), 32-bit**, Raspbian
bookworm. Built with `TARGET=armv7-unknown-linux-musleabihf ./cross-build.sh` (static 16 MB ELF).
The binius stack compiles for 32-bit with **zero code changes**.

**STEP 1 — single-device RSS pipeline (`SHARD_COEFFS=8`):**

```
after NTT-butterfly shard : 29 MiB
after combine-multiply    : 30 MiB
after digit shard         : 30 MiB
after z-norm shard        : 30 MiB
after closing-hash shard  : 33 MiB  ← PEAK across all 5 strands
PEAK RSS whole pipeline   : 33 MiB  ⇒ 1 GB headroom 31× ; < 500 MiB: YES
combiner = trustless, verify 538 ms ; wall 227.7 s (sequential on one node)
```

The whole ML-DSA-44 verify pipeline runs at **33 MiB peak RSS on a real 1 GB device** — the
sub-500 MB IoT claim holds on genuine low-end silicon, not just the M4/x86 proxy. (At the larger
`SHARD_COEFFS=32` the peak is **35 MiB** — bigger shards, essentially the same footprint.)

**STEP 2 — fleet throughput model (`SHARD_COEFFS=32`, 4 cores):**

| strand | ms/shard | RSS |
|---|---:|---:|
| NTT butterfly | 136040 | 29 MiB |
| combine (×) | 130156 | 32 MiB |
| digit | 59894 | 32 MiB |
| z-norm | 8233 | 32 MiB |
| closing-hash | 67453 | 34 MiB |

Per ML-DSA-44 verify: **641 shards, ~79665 s total shard-work, 34 MiB peak RSS.** Fleet latency:
1 Pi → ~22 h, 64 → 1245 s, 256 → 311 s (~12 sigs/hr).

### Going further with the RAM headroom — 34 MiB of ~900 MiB is ~4%

The peak footprint is tiny relative to the 1 GB, so the spare RAM is budget to spend. Two
independent levers, both measured on this Pi 2, both far under 500 MiB, and they **compose**.

**Lever 1 — bigger shards (`SHARD_COEFFS` ↑, zero code change).** Larger shards amortise the
per-shard fixed cost (setup/commit), cutting total shard-work per ML-DSA-44 verify monotonically:

| `SHARD_COEFFS` | shards/sig | total shard-work | peak RSS | vs sc=8 |
|---:|---:|---:|---:|---:|
| 8 | 2,561 | 136,474 s | 33 MiB | 1.0× |
| 32 | 641 | 79,665 s | 34 MiB | 1.7× |
| 64 | 321 | 52,564 s | 33 MiB | 2.6× |
| 128 | 161 | 33,675 s | 37 MiB | 4.1× |
| **256** | **81** | **21,101 s** | **43 MiB** | **6.5×** |

`sc=256` (a whole polynomial per shard) does **6.5× less total work than `sc=8` for 43 MiB — 13% of
the budget**. (`closing-hash` stays ~67 s at every size: it is per-signature SHA-3 of the full
message, not coeff-sharded, so it is the critical-path floor.)

**Lever 2 — intra-node concurrency (`concurrent_shards_throughput`).** A single shard's intra-parallel
prove leaves ~⅔ of the 4 cores idle (Pi load ~1.9/4), so proving several independent shards *at once*
recovers it. Measured (combine shards, `sc=32`):

| CONC (shards at once) | sequential | concurrent | speedup | peak RSS |
|---:|---:|---:|---:|---:|
| 4 (= core count) | 518.5 s | 162.6 s | **3.19×** | 46 MiB |
| 8 (oversubscribed) | 1036.4 s | 319.6 s | 3.24× | 64 MiB |

**Rule: `CONC` = core count** — oversubscribing past 4 adds nothing (cores saturated) but more RAM.
The two levers stack: `sc=256` (6.5× less work) × `CONC=4` (~3.2× faster wall) still fits in ~64 MiB,
leaving ~850 MiB of the Pi's RAM untouched.

**The Cortex-A7 is the worst-case throughput floor** (a 2015-era in-order core, ~40× the M4). The
realistic fleet node is a Pi 4/5 (Cortex-A72/A76, 64-bit, 4–8× faster/core, runs the aarch64 static
binary). **The Pi 2 proves low-RSS + 32-bit portability at the bottom of the market; throughput
lives on faster nodes and scales ~linearly with core count and speed.**

## Running an actual distributed fleet

The single-Pi script measures the **per-strand unit cost + the model**. A real distributed run
assigns shards to Pis and folds:

1. **Prove (each Pi):** invoke the strand shard functions on assigned work — `run_stage_shard`
   (NTT), `run_mult_shard` (combine), `run_digit_shard`, `run_boundary_shard`,
   `run_closing_hash_shard` (all in `crates/binius-substrate/src/mldsa_ntt.rs`). Each returns
   `(proof_bytes, peak_rss)`; low RSS ⇒ any Pi. Shards are independent ⇒ embarrassingly parallel.
2. **Seam-bind:** shards carry their I/O + schedule as boundary flushes on the shared channels, so
   the combiner checks the seam tokens union to the whole record (positions are global).
3. **Combine + verify:** `accumulation_air::combine_and_verify(records, inner_vars)` folds the
   shard outputs and verifies. Trust model is a **compile flag**:
   - default → **trustless** (proves the fold tree; ~ms verify; a forged shard output is rejected).
   - `--features trusted-combiner` → **trusted aggregator** (model A; sub-ms verify).

The natural fleet controller: a coordinator hands each Pi a shard spec, collects `(proof, output)`,
and runs `combine_and_verify` once per epoch. The `fleet_throughput_model` numbers size the fleet
(how many Pis for a target sigs/hr) directly from the measured per-Pi unit costs.

## Cross-compile on a Mac (Apple Silicon) → deploy to the Pi ✅ recommended for 1 GB Pis

Yes — build on the Mac mini, ship a ~15 MB **fully static** binary to the Pi. `peak_rss_bytes`
already normalises Linux's kilobyte `ru_maxrss`, so it's a clean cross-compile. The crate is Rust
with one transitive C dep (`stackalloc`), so the only tool needed is **zig** (used as the cross
compiler + linker); `python3` (already on macOS) runs a tiny target shim.

```bash
# one-time, on the Mac:
brew install zig            # provides `zig cc` (cross cc + linker) and `zig ar`

# build + get the deployable binary (default = STATIC musl → runs on any 64-bit Pi OS):
cd scripts/pi-bench
./cross-build.sh
# TARGET=aarch64-unknown-linux-gnu.2.31 ./cross-build.sh   # Pi OS Bullseye glibc
# TARGET=aarch64-unknown-linux-gnu.2.36 ./cross-build.sh   # Pi OS Bookworm glibc

# deploy + run (no Rust toolchain on the Pi):
scp deploy/pi-bench pi@raspberrypi:~/
ssh pi@raspberrypi 'SHARD_COEFFS=16 ./pi-bench single_device_rss_pipeline --ignored --nocapture --test-threads=1'
```

> **Why not `cargo-zigbuild`?** It has no `test` subcommand, and the deployable is the *test*
> binary (the lib only builds under `cargo test`). So `cross-build.sh` drives `cargo test --no-run`
> and points `CC`/`AR`/linker at a small `zig cc` shim it generates. The shim (a) forces zig's
> `-target aarch64-linux-musl` and drops cc-rs's un-parseable rust-triple `--target=`, so C deps
> compile as ELF not Mach-O, and (b) at link time drops rust's self-contained `crt*.o` +
> `-nostartfiles` so only zig supplies the startup files (else `_start` is defined twice).

### One command: build → deploy → run → collect

`deploy.sh` does the whole Mac→Pi loop (cross-build, `scp` the binary, run both benchmarks on the
Pi, pull results back to the Mac):

```bash
cd scripts/pi-bench
PI_HOST=pi@raspberrypi.local ./deploy.sh
# or:  ./deploy.sh pi@192.168.1.50
# reuse a prior build:  SKIP_BUILD=1 ./deploy.sh pi@raspberrypi.local
# static musl binary:   TARGET=aarch64-unknown-linux-musl ./deploy.sh pi@raspberrypi.local
```

Results land on the Mac under `results/deploy-<stamp>/` (`host.txt`, `rss-pipeline.txt`,
`throughput.txt`). Needs SSH access to the Pi (key auth recommended); no toolchain on the Pi.

The lib builds only under `cargo test`, so `cross-build.sh` cross-compiles the **test binary** —
a standalone executable that carries the `single_device_rss_pipeline` / `fleet_throughput_model`
benchmarks. Pick **musl** for a fully static binary (no glibc-version matching); pick **glibc** (pin
the version to your Pi OS) for native-malloc benchmarking. Both are ~20 MB, need no toolchain on the
Pi, and fit the 8 GB-SD provisioning above.

## Notes

- Build **on the Pi** (native aarch64) is simplest; cross-compiling from x86 to
  `aarch64-unknown-linux-gnu` also works (the crate is pure Rust + the local `binius` checkout).
- Use `--features parallel` to use all Pi cores per shard, or pin one core per shard and run
  4 shards/Pi (4-core Pi) for max fleet parallelism at fixed RAM.
- The resolver (DNS-STARK verifier) verifies ONE aggregated proof — not the shards — so its cost
  is unchanged by the fleet (sub-ms trusted / ~ms trustless); the Pi fleet is purely prover-side.

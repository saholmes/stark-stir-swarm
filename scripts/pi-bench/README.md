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
(on M4-class cores; a Pi core is ~2–5× slower, so scale accordingly — run on the Pi for real
numbers). RSS stays 25 MiB regardless, so the fleet runs on the cheapest Pis.

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

Yes — build on the Mac mini, ship a ~20 MB binary to the Pi. The crate is **pure Rust** (no C
build deps) and `peak_rss_bytes` already normalises Linux's kilobyte `ru_maxrss`, so it's a clean
cross-compile. The only tool needed is a cross-linker, provided by **zig** via **cargo-zigbuild**.

```bash
# one-time, on the Mac:
brew install zig
cargo install cargo-zigbuild

# build + get the deployable binary:
cd scripts/pi-bench
./cross-build.sh                                   # glibc for Pi OS Bullseye (2.31)
# TARGET=aarch64-unknown-linux-gnu.2.36 ./cross-build.sh   # Pi OS Bookworm
# TARGET=aarch64-unknown-linux-musl     ./cross-build.sh   # STATIC — runs on any Pi OS

# deploy + run (no Rust toolchain on the Pi):
scp deploy/pi-bench pi@raspberrypi:~/
ssh pi@raspberrypi 'SHARD_COEFFS=16 ./pi-bench single_device_rss_pipeline --ignored --nocapture --test-threads=1'
```

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

# Constrained-edge decider/fold measurement on AWS a1.medium (Cortex-A72)

This runbook produces the **camera-ready constrained-edge numbers** for STARK-DNS:
the once-per-epoch **decider** verify time, the **hierarchical fold** verify-vs-leaves,
the **epoch-Π** L1/L3/L5 verify, and the **peak RSS** that answers "can a 2–4 GB edge
verify at all?" — on the Raspberry Pi 4's exact CPU core.

**Why a1.medium.** AWS EC2 `a1.*` instances use **Graviton1 = ARM Cortex-A72**, the same
microarchitecture as the Raspberry Pi 4 (`a1.medium` @ 2.3 GHz vs Pi 4 @ 1.8 GHz). One vCPU
matches the single-threaded verifier; 2 GiB matches the ceiling under test. The whole run
costs **~$0.05–0.10 on-demand** (~$0.0255/hr).

> ⚠️ **Check availability first.** A1 is AWS's oldest Graviton generation and may be retired
> in your region. If `a1.medium` is unavailable, use a **physical Raspberry Pi 4** (below) —
> do **not** substitute `t4g.*` for the headline number: its Graviton2 / Neoverse-N1 core is
> markedly faster than A72 and would *understate* the constrained-edge cost.

---

## 1. Launch the instance

- **Region:** one that still offers A1 (e.g. `us-east-1`, `us-east-2`, `us-west-2`, `eu-west-1` — verify).
- **AMI:** Ubuntu 22.04/24.04 **arm64**, or Amazon Linux 2023 **arm64**.
- **Instance type:** `a1.medium` (1 vCPU, 2 GiB). *(`a1.large` if you also want a 2-core check.)*
- **Storage:** **≥ 30 GiB gp3** — the Rust build + swapfile + target/ need room.
- **Security group:** inbound SSH (22) from your IP only.

CLI equivalent (adjust AMI id / key / SG):

```bash
aws ec2 run-instances --image-id ami-XXXXXXXX_arm64 --instance-type a1.medium \
  --key-name YOUR_KEY --security-group-ids sg-XXXX \
  --block-device-mappings '[{"DeviceName":"/dev/sda1","Ebs":{"VolumeSize":30,"VolumeType":"gp3"}}]' \
  --count 1
```

## 2. Get the code onto the box

From your workstation (double-blind: use the anonymised repo, or copy your local checkout):

```bash
# option A — copy your local checkout (no network deps on the instance)
rsync -az --exclude target/ ./stark-binius-swarm/ ubuntu@<IP>:~/stark-binius-swarm/
# option B — clone the (anonymised) artifact repo on the instance
# git clone <ANON_REPO_URL> ~/stark-binius-swarm
```

> **Long runs — survive SSH disconnects.** Both the setup build (30–90 min) and the decider
> bench (minutes on A72) outlive a typical SSH session. Run them detached so a dropped
> connection does not kill them. Two options:
>
> ```bash
> # (A) tmux — recommended: reattach later with `tmux attach -t bench`
> tmux new -s bench
> #   ...run the commands below inside tmux; detach with Ctrl-b then d...
>
> # (B) nohup — fire-and-forget with a log you can tail
> nohup CMD > CMD.log 2>&1 &        # returns immediately
> tail -f CMD.log                   # watch; Ctrl-c to stop watching (job keeps running)
> ```

## 3. Setup (installs deps + swap + builds — SLOW on A72)

```bash
ssh ubuntu@<IP>
cd ~/stark-binius-swarm
# detached (survives disconnect):
nohup ./scripts/aws-bench/edge-a1-setup.sh > ~/setup.log 2>&1 &
tail -f ~/setup.log                 # watch progress; the job runs even if you disconnect
```

This installs build tools + GNU `time` + `taskset`, adds a **6 GiB swapfile** (a 2 GiB box
cannot build this workspace or hold the N=8192 decider without it), installs Rust, and builds
the test binary **single-threaded** (`CARGO_BUILD_JOBS=1`) so the *compile* does not OOM.
**Expect 30–90 min** — Cortex-A72 compiling a large Rust workspace is slow; that is fine, it
is one-time. (`SWAP_GIB=8 nohup ./...` for more swap.) Wait for `=== setup complete ===` in
`~/setup.log` before step 4.

## 4. Run the benchmark

```bash
# detached (survives disconnect):
nohup ./scripts/aws-bench/edge-a1-bench.sh > ~/bench.log 2>&1 &
tail -f ~/bench.log                 # watch; the run continues if you disconnect
# knobs:  PIN_CORE=0  (default)   — pin to a single vCPU
```

It pins to one core, runs each bench under GNU `time -v` (accurate peak RSS, not cargo's),
and writes `scripts/aws-bench/results/edge-a1-<UTC>/`:

- `SUMMARY.md` — headline table (per-bench external peak RSS + status)
- `decider.out` — **the key file**: `N | PROVE ms | VERIFY ms | prove-peak-RSS GiB | proof KiB`
- `fold-hierarchical.out`, `epoch-pi-ladder.out`, `opening-leaves-indep.out`
- `*.time` — GNU `time -v` reports (external peak RSS)

## 5. Read the results

- **Edge decider cost** = the **VERIFY ms** column in `decider.out` (proving is publisher-side
  and only run here to produce the object; the peak RSS shown is prove-dominated, an *upper
  bound* on the verifier footprint).
- **2 GiB question** = the peak RSS. On M-series the decider peaks at 0.13/0.35/1.16 GiB for
  N=512/2048/8192; if the A72 run stays similar and the whole prove+verify fits, a 2 GiB edge
  verifies with headroom (the edge alone holds only the sub-MiB proof + constraint system).
- **Fold** = `fold-hierarchical.out` should show polylog verify (≪ 512× over a 512× leaf range).
- **Cadence floor** = the L1/L5 decider VERIFY ms sets the minimum epoch interval for the edge.

## 6. Put the numbers in the paper

In `STARK-DNS-ACNS.tex`:

1. Add a row to `tab:verify-costs` with **Node = `a1`/A72** for the decider + fold (the table
   already has a Node column for exactly this).
2. Replace the "Constrained-edge cadence" **extrapolation paragraph** with the measured
   VERIFY ms and verifier peak RSS; drop "extrapolated" from the paragraph header.
3. Keep the reproducibility pointer to these scripts.

---

## Alternative: physical Raspberry Pi 4 (most faithful, no cloud)

Same core, at the exact target clock (1.8 GHz — conservative vs A1's 2.3 GHz), ~$55 one-time,
and it is literally the device the paper motivates with:

```bash
# on a Pi 4 (64-bit Raspberry Pi OS / Ubuntu arm64), 4 GB model:
sudo apt-get update && sudo apt-get install -y build-essential clang pkg-config libssl-dev git time util-linux
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
source ~/.cargo/env
# copy/clone the repo, then:
cd stark-binius-swarm && SWAP_GIB=6 ./scripts/aws-bench/edge-a1-setup.sh   # adds swap; 4 GB Pi builds slowly
./scripts/aws-bench/edge-a1-bench.sh
```

The 4 GB Pi 4 has more RAM than a1.medium, so N=8192 fits comfortably; the scripts are
identical.

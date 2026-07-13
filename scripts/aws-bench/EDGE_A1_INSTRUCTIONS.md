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

## Quick start — existing instance with the repo already cloned (e.g. t4g)

Already have an ARM instance and cloned `stark-stir-swarm`? Two steps: add the binius fork
as a **sibling**, then run. `edge-a1-bench.sh` **auto-detects the core** and labels the
results honestly (A72 = faithful; N1/Graviton2 = *lower bound*), so nothing gets mislabeled.

```bash
# 1. clone the binius fork NEXT TO your existing clone (sibling, not inside it)
cd "$(dirname "$(pwd)")"            # move to the PARENT of your stark-stir-swarm/ dir
git clone -b feature/nist-tower-level-8-9-fext https://github.com/saholmes/binius.git binius
ls                                   # must show BOTH your repo dir AND binius/

# 2. from inside the repo, run setup + bench under nohup (survives disconnects)
cd stark-stir-swarm                  # (or whatever your clone dir is named)
nohup ./scripts/aws-bench/edge-a1-setup.sh > ~/setup.log 2>&1 &   # builds (30-90 min on ARM)
tail -f ~/setup.log                  # wait for  EDGE_A1_SETUP_COMPLETE
nohup ./scripts/aws-bench/edge-a1-bench.sh > ~/bench.log 2>&1 &
tail -f ~/bench.log                  # wait for  EDGE_A1_BENCH_COMPLETE ; read SUMMARY.md
```

> **t4g = Graviton2 / Neoverse-N1, NOT Cortex-A72.** The scripts run fine and will *print*
> `core: Neoverse-N1 … LOWER BOUND on the Pi-4/A72 cost`. Report it as such: *"measured on
> Graviton2/N1; a physical Cortex-A72 (Pi 4) is ~2–3× slower, so this is a lower bound."*
> Pair it with the M-series→A72 extrapolation (upper-ish bound) to give an honest **range**,
> or get one physical Pi-4 run for the definitive A72 number.
>
> **RAM:** `t4g.micro`=1 GiB (too small — build will fail even with swap), `t4g.small`=2 GiB
> (tight; `SWAP_GIB=10`), `t4g.medium`=4 GiB (fine). The build needs the memory; the *run*
> fits easily. If your t4g is 1–2 GiB, cross-compile elsewhere or use `t4g.medium`.

---

## 1. Launch the instance

- **Region:** one that still offers A1 (e.g. `us-east-1`, `us-east-2`, `us-west-2`, `eu-west-1` — verify).
- **AMI:** Ubuntu 22.04/24.04 **arm64**, or Amazon Linux 2023 **arm64**.
- **Instance type:** `a1.medium` (1 vCPU, **2 GiB**) works with swap, but the **build**
  is memory-hungry and slow on 2 GiB. **Prefer `a1.large`** (2 vCPU, **4 GiB**, *same
  Cortex-A72 core*, ~$0.051/hr) to make the build painless, then **pin to one vCPU**
  (`PIN_CORE=0`) so the edge measurement stays single-core. (Strict 2 GiB? use
  `SWAP_GIB=10`, or cross-compile the test binary elsewhere and only *run* here.)
- **Storage:** **50 GiB gp3** — `target/` alone is ~10–20 GiB for this workspace, plus
  the toolchain (~7 GiB), cargo cache (~2 GiB), and the swapfile (6–10 GiB). 30 GiB is
  not enough once all three land; 50 GiB is cheap insurance (~$4/mo, pennies for a run).
- **Security group:** inbound SSH (22) from your IP only.

CLI equivalent (adjust AMI id / key / SG):

```bash
aws ec2 run-instances --image-id ami-XXXXXXXX_arm64 --instance-type a1.medium \
  --key-name YOUR_KEY --security-group-ids sg-XXXX \
  --block-device-mappings '[{"DeviceName":"/dev/sda1","Ebs":{"VolumeSize":30,"VolumeType":"gp3"}}]' \
  --count 1
```

## 2. Get the code onto the box — TWO repos, side by side

The build has a **path dependency** on a **forked binius** (the binary-tower NIST
L8/9 extension: B256/B512, SHA-3-laddered commitments, in-circuit GF(2^512) multiply):
`crates/binius-substrate/Cargo.toml` → `../../../binius/crates/*`. So the two repos
must sit as **siblings** under one parent directory:

```
~/work/
  stark-binius-swarm/   branch feature/accumulation-recursion   (on GitHub, pushed)
  binius/               branch feature/nist-tower-level-8-9-fext (the FORK)
```

**Simplest (both repos are on GitHub now):**
```bash
ssh ubuntu@<IP>
mkdir -p ~/work && cd ~/work
git clone -b feature/accumulation-recursion   https://github.com/saholmes/stark-stir-swarm.git stark-binius-swarm
git clone -b feature/nist-tower-level-8-9-fext https://github.com/saholmes/binius.git          binius
ls ~/work   # must show BOTH stark-binius-swarm/ and binius/
```
(If you later set `saholmes/binius` to **private**, clone it with a token/deploy key, or use
the bundle Option D below.)

The remaining options are fallbacks (e.g. offline, or a private fork):

**Option A — rsync both local checkouts (simplest; no push needed).** A working-tree
copy builds fine — cargo does not need git history for path deps.

```bash
# from your workstation (run one level ABOVE both repos):
DEST=ubuntu@<IP>
ssh "$DEST" 'mkdir -p ~/work'
rsync -az --exclude target/ --exclude .git ./stark-binius-swarm/ "$DEST":~/work/stark-binius-swarm/
rsync -az --exclude target/ --exclude .git ./binius/             "$DEST":~/work/binius/
```

**Option B — clone the main repo (it IS pushed) + rsync only the fork.**

```bash
ssh ubuntu@<IP>
mkdir -p ~/work && cd ~/work
git clone -b feature/accumulation-recursion \
  https://github.com/saholmes/stark-stir-swarm.git stark-binius-swarm
# then, from your workstation, copy the fork (branch not on any remote):
#   rsync -az --exclude target/ --exclude .git ./binius/ ubuntu@<IP>:~/work/binius/
```

**Option C — push the fork branch to your own remote first** (needs write access to a
remote you own), then clone both:
```bash
# on your workstation, in ../binius:
#   git remote add mine https://github.com/saholmes/binius.git   # must exist + be writable
#   git push mine feature/nist-tower-level-8-9-fext
# then on the a1: git clone both into ~/work as siblings, on the branches above.
```

**Option D — carry the fork as a git BUNDLE (no remote / no write access needed).** A
`git bundle` is one self-contained file that clones like a repo:
```bash
# on your workstation, in ../binius (already done — see binius-fork-*.bundle):
#   git bundle create ~/binius-fork.bundle feature/nist-tower-level-8-9-fext
# copy it up and clone from it on the a1:
scp binius-fork-*.bundle ubuntu@<IP>:~/work/
ssh ubuntu@<IP> 'cd ~/work && git clone -b feature/nist-tower-level-8-9-fext binius-fork-*.bundle binius'
# main repo is on GitHub, so clone it normally alongside:
ssh ubuntu@<IP> 'cd ~/work && git clone -b feature/accumulation-recursion https://github.com/saholmes/stark-stir-swarm.git stark-binius-swarm'
```
This is the smallest transfer (a few MB) and yields a real git tree on the correct branch.

Verify the layout before setup: `ls ~/work` must show **both** `stark-binius-swarm/` and
`binius/`, and `~/work/stark-binius-swarm/crates/binius-substrate/Cargo.toml`'s
`../../../binius` must resolve to `~/work/binius`.

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

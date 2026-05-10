# Full instructions: AWS c5.4xlarge benchmark suite

End-to-end guide for reproducing the paper Table 6 (and FRI paper
Table 5) measurements on the canonical reference machine.

## Cost

c5.4xlarge is ~\$0.68/hour on-demand.  Full matrix run takes ~3-5
hours → **~\$3-4 total**.  Terminate the instance when done.

## Prerequisites

- AWS account with EC2 launch permissions.
- SSH key pair registered with EC2 (e.g., `~/.ssh/aws-stark.pem`).
- Repo URL + branch you want to benchmark.

---

## Step 1 — Launch the instance

```bash
aws ec2 run-instances \
    --image-id ami-0c7217cdde317cfec \
    --instance-type c5.4xlarge \
    --key-name aws-stark \
    --security-groups default \
    --block-device-mappings 'DeviceName=/dev/sda1,Ebs={VolumeSize=64,VolumeType=gp3}' \
    --tag-specifications 'ResourceType=instance,Tags=[{Key=Name,Value=stark-bench}]' \
    --region us-east-1
```

Notes:
- AMI is **Ubuntu 22.04 LTS** for `us-east-1`; in a different region,
  search for `ubuntu/images/hvm-ssd/ubuntu-jammy-22.04-amd64-server`.
- **64 GB EBS** required (deep_ali release-mode `target/` reaches ~30 GB).
- **c5.4xlarge** = 16 vCPU Intel Xeon Cascade Lake with AVX-512 — matches
  the FRI paper's reference hardware.

Wait for `running`, grab the public IP:

```bash
aws ec2 describe-instances --filters "Name=tag:Name,Values=stark-bench" \
    --query 'Reservations[*].Instances[*].[InstanceId,PublicIpAddress,State.Name]' \
    --output table
```

## Step 2 — Connect and start tmux

```bash
ssh -i ~/.ssh/aws-stark.pem ubuntu@<PUBLIC_IP>

# Inside instance:
sudo apt-get install -y tmux
tmux new -s bench
```

Detach with `Ctrl-b d`, reattach later with `tmux attach -t bench`.

## Step 3 — Get the code

```bash
git clone https://github.com/<YOUR_ORG>/stark-stir-swarm.git
cd stark-stir-swarm
git checkout main
git submodule update --init --recursive
```

(For a private repo: set up SSH key on the instance with `ssh-keygen`
and register it with GitHub.)

## Step 4 — Install dependencies

```bash
cd scripts/aws-bench
./setup.sh
```

Installs apt packages (build-essential, clang, lld, libssl-dev, time,
linux-tools-generic, git-lfs), Rust stable toolchain via rustup, and
pre-builds deep_ali / cairo-bench / swarm-dns in release mode.

Takes ~5 minutes; idempotent.

## Step 5 — Smoke test (recommended)

Single-cell sanity check (~10 minutes):

```bash
./run-all.sh
```

Runs every bench once at the default (L1, SHA3-256) cell.  If anything
fails here, fix before launching the full matrix.

## Step 6 — Full matrix run

```bash
export BENCH_RUNS=3                         # 3-run median (default)
# Optional: shorten trace-size sweep
# export BENCH_K_RANGE="11 14 18 22"
./run-matrix.sh 2>&1 | tee results/run-matrix.log
```

The matrix iterates **6 (level, hash) cells**, each requiring a
fresh deep_ali compile (~2-4 min per cell):

| Cell | Level | Ext. | Hash      | $q_{\max}$ |
|------|-------|------|-----------|-----------|
| 1    | L1    | Fp6  | SHA3-256  | $2^{40}$  |
| 2    | L1    | Fp6  | SHA3-384  | $2^{65}$  |
| 3    | L1    | Fp6  | SHA3-512  | $2^{90}$  |
| 4    | L3    | Fp6  | SHA3-384  | $2^{65}$  |
| 5    | L3    | Fp6  | SHA3-512  | $2^{90}$  |
| 6    | L5    | Fp8  | SHA3-512  | $2^{65}$ only (binding wall at $2^{90}$) |

At each cell:
- 3 simple AIRs (Fibonacci, PoseidonChain, RegisterMachine) swept
  across log₂(n_trace) = 11..24 (FRI-paper methodology).
- Cryptographic AIRs at the matching level (Ed25519, RSA-2048
  once per machine in cell 1; ML-DSA-{44,65,87} once per L1/L3/L5
  cell).

Total: 6 × 3 × 14 = **252 simple-AIR measurements** + cryptographic
AIRs, triplicated by `BENCH_RUNS`.

## Step 7 — Monitor (optional, second SSH session)

```bash
ssh -i ~/.ssh/aws-stark.pem ubuntu@<PUBLIC_IP>
cd stark-stir-swarm/scripts/aws-bench

tail -f results/$(ls -t results/*.log | head -1)
# or
watch -n 30 'wc -l results/*.csv'
# or
htop
```

The runner prints a banner at each cell transition:
```
════════════════════════════════════════════════════════════
Cell: L1 × Fp6 × sha3-256 × mldsa-44 (binding q=2^40)
════════════════════════════════════════════════════════════
```

## Step 8 — Collect results

```
results/
├── matrix-meta.txt              # host info, cell list
├── run-matrix.log               # full stdout/stderr capture
├── simple-scaling.csv           # 252 simple-AIR rows
├── cairo-suite.csv              # criterion bench rows
├── hash-rollup.csv
├── ed25519.csv
├── rsa2048.csv
├── mldsa-l{1,3,5}.csv
├── summary.csv                  # all rows concatenated
├── summary_median.csv           # 3-run medians
└── paper_table.tex              # LaTeX drop-in for Table 6
```

Pull to your laptop:

```bash
scp -i ~/.ssh/aws-stark.pem -r \
    ubuntu@<PUBLIC_IP>:stark-stir-swarm/scripts/aws-bench/results/ \
    ./aws-bench-results-$(date +%Y%m%d)/
```

Or push to S3 from the instance:

```bash
aws s3 sync results/ s3://your-bucket/stark-bench/$(date +%Y%m%d)/
```

## Step 9 — Update the paper

Open `paper_table.tex` — it's a complete `\begin{tabular}…\end{tabular}`
block formatted to match Table 6's columns:

```
AIR & Level & Ext. & Hash & r & Proof (KiB) & t_verify (ms) & t_prove (s)
```

Drop into `main-22.tex` (or Overleaf) replacing the existing
tabular block.

For the simple-AIR scaling data (line plots of prove_ms vs
log₂(n_trace) per (level, hash) cell), the data is in
`simple-scaling.csv`; produce a pgfplots / matplotlib figure with
your preferred tool.

## Step 10 — Terminate the instance

**Important** — terminate when done to avoid billing:

```bash
INSTANCE_ID=$(aws ec2 describe-instances --filters \
    "Name=tag:Name,Values=stark-bench" \
    "Name=instance-state-name,Values=running" \
    --query 'Reservations[*].Instances[*].InstanceId' --output text)

aws ec2 terminate-instances --instance-ids "$INSTANCE_ID"
```

---

## Troubleshooting

### "v2_bench failed: no v2_bench line in log"

The `v2_bench` test panicked.  Check `results/mldsa-l*.runN.log` for
the panic message.  Common cause: the bench script's feature pair
doesn't match the witness expectations.

### "rsa2048_bench: Example may not have compiled"

Check `results/rsa2048.run1.log` for the cargo build error.  Most
likely an API drift since the bench was last validated.

### Out of memory at k=24

Trace 2²⁴ × blowup 32 = 2²⁹ field elements per LDE column.  At
~16 columns × 8 bytes = 64 GiB peak working set.  **c5.4xlarge has
only 32 GiB RAM** — the highest practical k is ~22.

```bash
export BENCH_K_RANGE="11 12 13 14 15 16 17 18 19 20 21 22"
./run-matrix.sh
```

For full k=24 measurements, use c5.9xlarge (72 GiB) or c5n.9xlarge.

### "FRI verify rejected" in any bench

Indicates a real soundness regression — file a bug.  Bench harnesses
are written so honest provers always pass; rejection means a drift.

### Builds taking >10 minutes per cell

Ensure cargo uses all 16 cores:

```bash
export CARGO_BUILD_JOBS=16
```

Verify `target-cpu=native` is in effect (check `.cargo/config.toml`
for `rustflags = ["-C", "target-cpu=native"]`).

### FRI vs STIR mode

Default is `BENCH_LDT=fri` (matches Phase 1; `stir: false` in
`DeepFriParams`).  To run STIR mode:

```bash
export BENCH_LDT=stir
./run-matrix.sh
```

Note: STIR mode currently relies on Phase 2 of the soundness fix
(eq. 1 lift); for Phase 1 the FRI mode is canonical.

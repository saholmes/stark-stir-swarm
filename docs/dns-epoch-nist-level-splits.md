# DNS-Epoch Demo — NIST-Level Prove/Verify/RSS Splits

Measured cost of the **per-record in-circuit DNSSEC-digest proof** in the
end-to-end DNS-epoch demonstration
([`crates/binius-substrate/src/dns_epoch_demo.rs`](../crates/binius-substrate/src/dns_epoch_demo.rs)),
broken out by NIST security level with **prove time, verify time, and peak
RSS reported separately**.

The point of the split: for a FIPS-hash proved *inside* a Binius circuit the
**verifier**, not the prover, is the cost center — and the gap widens with the
security level. This is the "FIPS-width tension" quantified, and the motivation
for the O(1)-verify accumulation route.

## TL;DR

* **Verify dominates prove at every level** — 3.8× at L1/L3, **8.1× at L5** —
  because Binius verify is *linear in the committed hash width* and FIPS SHA-3
  is the widest thing in-circuit.
* **L1 → L3 is nearly free**: same field (B256), same circuit width; SHA3-384
  only changes the sponge rate and output length. 128- → 192-bit soundness
  costs ~0 here because B256 already carries the 192-bit Fiat–Shamir floor.
* **L5 is the real jump**: the 256-bit floor forces the field B256 → B512,
  which ~2× prove, ~4.4× verify, ~1.6× RSS.
* The **aggregation / epoch layer is unaffected** — it edge-verifies in **18 ms,
  O(1) in the record count**, at every level. The per-record hash cost is a
  first-contact cost, amortized away in steady state.

## Level instantiation

Each level uses the correct field + FIPS-202 variant + Fiat–Shamir/commitment
target so **no soundness term drops below the level**:
`min(κ_IT, κ_bind, κ_FS)` reaches the category.

| Level | Variant  | Field | Target (κ) | Sponge rate r |
|:-----:|:---------|:-----:|:----------:|:-------------:|
| **L1** | SHA3-256 | B256  | 128-bit    | 136 B         |
| **L3** | SHA3-384 | B256  | 192-bit    | 104 B         |
| **L5** | SHA3-512 | B512  | 256-bit    | 72 B          |

B256 holds the 128/192-bit FS floor (Binius accepts `security_bits ≤ 192` on
B256); L5's 256-bit floor requires B512. The commitment/FS hash is laddered to
the variant so `κ_bind = κ_FS = digest_bits/2` also reaches the target. The FRI
query count `r` is auto-derived by Binius `make_commit_params` to meet
`security_bits`.

## Measured splits

Real per-record in-circuit DNSSEC-digest proof over the 8-record `example.com`
zone (batch padded to 512 single-Keccak-block messages; `log_inv_rate = 1`,
blowup = 2). Digest gated bit-for-bit against the native `sha3` crate.

| Level | Proof   | **Prove** | **Verify** | Verify / Prove | **Peak RSS** |
|:-----:|:-------:|:---------:|:----------:|:--------------:|:------------:|
| **L1** | 608 KiB  | 2455 ms  | 9318 ms   | 3.8×           | 0.12 GiB     |
| **L3** | 844 KiB  | 2448 ms  | 9316 ms   | 3.8×           | 0.12 GiB     |
| **L5** | 1943 KiB | 5062 ms  | 40952 ms  | 8.1×           | 0.19 GiB     |

For contrast, the **aggregation / epoch layer** (one recursive STARK binding
all N records, edge-verified) is level-independent in the demo:

| Stage             | Value                    |
|:------------------|:-------------------------|
| Epoch proof size  | 339 KiB                  |
| Epoch prove       | ~77 ms (aggregator, O(N))|
| **Edge verify**   | **~18 ms, O(1) in N**    |
| Steady-state lookup | ~1.3 µs (local SHA3 Merkle path) |

## Reading the numbers

* **The verifier is the bottleneck, not the prover.** Binius verify is polylog
  in trace *rows* but *linear* in committed *width*. FIPS SHA-3 is the widest
  gadget in the circuit, so per-record FIPS-hash-in-circuit verify is seconds,
  and it worsens with the level (SHA3-512-over-B512 at L5 is the widest config →
  41 s verify).
* **L1 ≈ L3.** SHA3-384 vs SHA3-256 changes only the sponge rate / output
  length; both commit over B256 at the same width. The 192-bit floor is free
  because B256 already reaches it.
* **L5 pays the field tax.** B256 → B512 doubles the base field. Prove roughly
  doubles (2.1×), verify jumps 4.4×, RSS climbs 1.6×. The 256-bit category is
  where the width tax actually bites.
* **RSS is modest here** (0.12–0.19 GiB) because these are single-Keccak-block
  batches (small traces). RSS scales with trace size, not security level; see
  [`docs/scaling-analysis.md`](./scaling-analysis.md) and
  [`docs/iot-memory-bounded-prover.md`](./iot-memory-bounded-prover.md) for the
  memory-bounded prover path at production trace sizes.

## Why this motivates accumulation — the two layers

There are **two distinct "verify times"** in this system, and the accumulator
only fixes one of them. Keeping them separate is what keeps the claim honest.

### Layer 1 — the per-record FIPS-hash in-circuit verify (this table)

Verifying one record's DNSSEC-digest proof is *seconds* (9 s at L1, 41 s at L5),
because Binius verify is linear in committed hash width and FIPS SHA-3 is the
widest gadget in the circuit. **The accumulator does NOT make this
sub-second.** This cost is paid **once, prover-side / at first contact**, and
then amortized away. It is not on the steady-state path.

### Layer 2 — the epoch verify over N records (accumulation)

What the accumulator buys is that the **edge verifier's work is O(1) in the
number of records N**, not O(N):

* **Without accumulation**, verifying an epoch of N records recursively means
  re-verifying N per-record proofs — N × (Layer-1 seconds) ⇒ minutes-to-hours
  for a real zone.
* **With accumulation**, the N per-record proofs are *folded into one
  accumulator instance during proving*. The edge verifier checks **one**
  aggregated proof against the interleaved-commit Merkle root `R*` — constant
  in N (~18 ms in this demo, tied to the Merkle lookup tree). Any individual
  record then resolves via a ~1.3 µs Merkle path against the verified root.

This works precisely because accumulation arithmetizes the **narrow fold-verify
(~48 ms)**, *not* the wide FRI/hash-verify.

> **Caveat — don't over-read the ~18 ms.** That figure is the aggregation /
> fold layer, *not* a from-scratch in-circuit re-verification of the FIPS-hash
> op-table. A fully assembled recursive verify that re-checks the wide FIPS hash
> in-circuit is still seconds (~12 s Keccak / ~minute SHA-256 at recursion
> scale). "ms verify" holds for the fold layer and the steady-state Merkle
> lookups — not for re-proving the FIPS hashes from scratch.

### Net effect

* The win is **never first-contact** (fetch + verify) — that regime is a
  wash-to-loss vs a warm DNS cache.
* The win is **(a) O(1) scaling in N** — adding more DNS records to the epoch
  costs the edge verifier nothing extra — **and (b) steady-state amortization**
  — verify the epoch once, then serve every record with a ~1.3 µs local
  Merkle-path check.

In one line: the accumulator means *"more records cost the verifier nothing
extra, and after the first verify every lookup is µs"* — **not** *"the FIPS-hash
proof now verifies in milliseconds."* See
[`docs/accumulation-recursion.md`](./accumulation-recursion.md).

## Reproducing

The demo defaults to L1. Flip `let level = Sha3Level::L1;` in the
`dns_epoch_end_to_end` test to `L3` / `L5` for the other categories:

```bash
cargo test --release --lib dns_epoch_end_to_end -- --ignored --nocapture
```

The prove/verify split and peak RSS come from the timed gadget entries
(`prove_verify_sha3_b256_timed` / `prove_verify_sha3_b512_timed`), which wrap
the Binius `prove` and `verify` calls in separate timers and sample process
peak RSS (`getrusage` `ru_maxrss`) right after prove — the memory-dominant
phase.

Measurement host: Apple M-series (`darwin`), release profile, single machine.
Timings are wall-clock; treat ±10% as run-to-run noise.

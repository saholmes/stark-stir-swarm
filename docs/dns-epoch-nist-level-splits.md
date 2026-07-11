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

## Flow model & security

**Actors:** the zone *publisher* (prover — does the expensive work once per
epoch), the *edge resolver* (verifier — O(1) work), the *client* (µs lookups).

```
PUBLISH  (prover, once per epoch)
  each DNS record  r_i
    │  canonical wire form   (name ‖ type ‖ rdata)
    ▼
  S-layer AIR: proves in-circuit  "RRSIG(r_i) verifies under alg A_i, key K_i"
               + FIPS SHA-3 digest over the canonical form           ← Layer 1
    │  per-record proof π_i  +  commitment c_i
    ▼
  interleave {r_i} → one polynomial P → streaming interleaved commit
    │  Merkle root  R*   (byte-exact == binius commit_interleaved)   ← the lookup tree
    ▼
  ACCUMULATOR: fold {π_i} into ONE accumulator instance; arithmetize the
               narrow fold-verify (~48 ms), NOT the wide FRI/hash-verify
    │  one epoch proof  Π  binding all N records to R*               ← Layer 2
    ▼
  artifact = (R*, Π)      [+ the record set / Merkle leaves]

VERIFY   (edge resolver, once)
  check Π against R*         → O(1) in N,  ~18 ms (fold layer)

SERVE    (client, every lookup after the first)
  record r_i  +  Merkle path to R*   → ~1.3 µs SHA-3 path check
```

Layer 1 and Layer 2 below are exactly the two stages of this flow: Layer 1 is
the per-record S-layer proof (seconds, paid once at publish — the table above);
Layer 2 is the accumulator + epoch verify (O(1) in N).

### Why it is secure — three independent guarantees

**1. Proof-system soundness — unconditional / post-quantum.**
End-to-end soundness is `κ_sys = min(κ_IT, κ_bind, κ_FS)`, every term laddered
to the target (L1/L3/L5 = 128/192/256):

* `κ_IT` — STARK/FRI interactive-oracle soundness from field size + query count
  `r` (auto-derived by Binius). Information-theoretic; no computational
  assumption.
* `κ_bind` — Merkle commitment binding = SHA-3 collision resistance
  (`digest_bits / 2`).
* `κ_FS` — Fiat–Shamir, same SHA-3.

Resting only on **STARK IT-soundness + SHA-3 collision resistance**, this layer
is post-quantum *unconditionally* — no algebraic hash, no number-theoretic
assumption on the soundness path. No adversary (classical or quantum) can forge
a valid epoch proof `Π`, make `Π` attest to a record not in the epoch, or tamper
a witness (the corrupted-lane / flipped-transcript soundness tests gate exactly
this).

**2. Aggregation & lookup integrity — unconditional / PQ.**
`R*` is a collision-resistant SHA-3 commitment to the *entire* interleaved
record set, and `Π` proves the accumulator was folded correctly (the fold-verify
is itself in-circuit, so a dishonest fold is caught). Once a resolver has
verified `Π` against `R*`, **no record can be substituted, added, or dropped**
in steady state — every µs lookup is a SHA-3 Merkle path back to the *proven*
root. Adding records changes `R*` and needs a new `Π`; it cannot be forged onto
an existing verified root. This is the O(1)-in-N win *and* the anti-substitution
guarantee, PQ for the same reason as (1).

**3. Signature trust — algorithm-dependent (the honest caveat).**
The STARK proves *"this RRSIG verified under algorithm A"*; it does **not**
upgrade the signature's own security:

* **ML-DSA-signed records → post-quantum end to end.** A CRQC cannot forge the
  RRSIG, so it cannot produce a record the S-layer accepts. (This is what the
  quantum-MITM demo shows: the CRQC forgery classical DNSSEC accepts is rejected
  on the ML-DSA path.)
* **RSA / ECDSA / Ed25519 records → classical trust root.** The STARK faithfully
  proves a *classical* signature check; a CRQC that forges the underlying RRSIG
  yields a proof that honestly verifies. The proof system is still PQ-sound
  about the *statement* — the trust root is only as quantum-safe as the
  signature algorithm.

> **Precise statement.** The **transport, aggregation, and lookup integrity are
> post-quantum unconditional** (STARK + SHA-3): you cannot forge the epoch
> proof, substitute records, or tamper the witness, even with a quantum
> computer. **End-to-end trust is post-quantum only for records signed with a PQ
> algorithm (ML-DSA);** for classical algorithms the STARK inherits the
> signature's classical security — it makes DNSSEC *verifiable and aggregatable
> at µs cost*, not *quantum-safe by itself*. The distinction is a PQ-sound
> *envelope* vs. an algorithm-bound *trust root*.

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

## Projection: `.se` TLD epoch

**A projection**, extrapolated from the measured 512-record batch unit above plus
the accumulation model — *not* a measured full-`.se` run (that needs the prover
fleet). It answers "what would prove/verify cost for a whole TLD epoch?"

### Assumptions

* **Scale:** `.se` ≈ **1.5 M signed delegation records** (~1.4–1.5 M registered,
  fully DNSSEC-signed; the TLD-zone epoch is the NS / DS / NSEC3 RRsets under
  `.se`'s own ZSK). Use `N = 1.5 M`, **L1 (128-bit)**.
* **Measured unit** (L1 split above): a 512-record single-block SHA3-256 batch =
  one Binius proof, prove 2455 ms, verify 9318 ms, 608 KiB. Amortized prove =
  **4.79 ms/record**.
* **Granularity caveat:** 4.79 ms/record is the SHA3 *digest* proof, not the full
  RRSIG *signature* verify. The full S-layer sig-AIR (`.se` ZSK = ECDSA-P256 or
  RSA) is heavier — RSA-2048 ModMul is seconds/record, ECDSA lighter — and pushes
  the prove side up proportionally (still fleet-parallel). Nail this down with a
  real ZSK-algorithm measurement before quoting full-signature numbers.
* Anchor: the real `.se` HNPL sample (857 records → 207 KiB package, **1.36 ms
  edge verify**) supports the O(1) ms edge-verify at the leaf model.

### Prove — fleet-parallel, publisher-side (once per epoch)

Slivers/batches are embarrassingly parallel (independent proofs); wall-clock =
(2.0 core-hours)/P + one accumulation tree.

| Provers P | Wall-clock prove for N = 1.5 M |
|:---------:|:------------------------------:|
| 1 core    | 2930 batches × 2.455 s ≈ **2.0 h** |
| 100       | ≈ **72 s** |
| 1000      | ≈ **7.2 s** |

Folding 2930 batch-instances is a ~log₂(2930) ≈ 11.5-deep narrow-fold tree
(~48 ms arithmetized fold-verify per node) → **adds seconds, not hours**; one
epoch proof `Π` out the end.

### Verify — O(1) in N, edge-side (does not scale with 1.5 M)

| Quantity | Value | Note |
|:---------|:------|:-----|
| Epoch verify (fold layer)         | **~18 ms** | O(1) in N; consistent with the 1.36 ms HNPL edge package |
| Epoch verify (assembled, in-circuit hash re-check) | **seconds** (~12 s Keccak) | the honest caveat — see the two-layer framing |
| Per-record lookup                 | **~3 µs**  | Merkle path, depth ≈ log₂(2¹⁰·1.5 M) ≈ 30 SHA-3 hashes |

A resolver verifies the **entire `.se` epoch once** in ms (fold layer) —
*independent of whether it is 857 records or 1.5 M* — then answers any of the
1.5 M delegations in ~3 µs.

### L5 multiplier

Prove ×2.1, Layer-1 verify ×4.4, RSS ×1.6 (B256 → B512). The edge/epoch verify
stays **O(1) in N** regardless of level.

### Bottom line

* **Prove:** ~2 core-hours at digest granularity for full `.se`, collapsing to
  **seconds on a ~1000-prover fleet** — the decentralised, censorship-resistant
  proving path. (Full-signature granularity is heavier; needs the ZSK-algo
  S-layer number.)
* **Verify:** **~18 ms once, O(1) in N**, then ~3 µs/lookup — the 1.5 M scale is
  invisible to the verifier.

Two reviewer caveats restated: (1) the ~18 ms is the fold layer, not assembled
in-circuit hash re-verification (seconds); (2) 4.79 ms/record is the SHA3 digest,
not the full RRSIG signature verify.

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

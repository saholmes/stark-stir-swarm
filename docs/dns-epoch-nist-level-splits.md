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
* The **aggregation / epoch layer edge-verifies in two checks, both O(1) in N,
  once per epoch**: a **~18 ms fold check** (distribution integrity — anti-substitution
  vs `R*`) and a **full decider** (statement validity — pays record-AIR width:
  ~0.8 s Keccak floor / ~6.6–10 s measured assembled). The 18 ms alone does **not**
  enforce the per-record constraints (width law: 18 ms ⇒ near-zero width = fold table
  only); the security section claims validity only for the decider layer. Both amortize
  into background per-epoch cost.
* **Open (headline-deciding):** the full-decider verify with the width term is the one
  measurement that settles "sound O(1)-in-N aggregation at sub-second edge" vs "efficient
  proof distribution"; and the epoch proof's FS/Merkle + EC/ECDSA challenger are `Sha256`
  (128-bit), so **L3/L5 pin at 128 for the combined artifact** until they ladder (see the
  component×level×hash table). The streaming interleaved-commit RSS is the residual that
  couples low-RSS proving to sound O(1) aggregation.

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
  RRSIG(r_i) VERIFIED  [demo: NATIVELY, p256 crate]  +  FIPS SHA-3 digest of the
               canonical form proved IN-CIRCUIT                      ← Layer 1
    │  (in-circuit RRSIG verify = the offline two-tier "owner proves once"
    │   path; ~99 core-hours/sig — see ecdsa-in-circuit-strand-cost.md)
    │  per-record proof π_i  +  commitment c_i
    ▼
  interleave {r_i} → one polynomial P → streaming interleaved commit
    │  Merkle root  R*   (byte-exact == binius commit_interleaved)   ← the lookup tree
    ▼
  ACCUMULATOR: fold {π_i} into ONE accumulator instance
    │  one epoch proof  Π  binding all N records to R*               ← Layer 2
    ▼
  artifact = (R*, Π)      [+ the record set / Merkle leaves]

VERIFY   (edge resolver, once per epoch — TWO distinct checks)
  (a) FOLD layer:    check Π's fold-correctness   → ~18 ms, O(1) in N
                     ⇒ distribution integrity (anti-substitution vs R*)
  (b) FULL DECIDER:  check the accumulated record-AIR instance  → O(record-AIR
                     width) + polylog(N), O(1) in N, SUB-SECOND–SECONDS (see below)
                     ⇒ statement validity ("the records' constraints hold")

SERVE    (client, every lookup after the first)
  record r_i  +  Merkle path to R*   → ~1.3 µs SHA-3 path check
```

**The two verify checks are not interchangeable** (this is the accumulation-soundness
structure — fold-correctness + a decider): the **~18 ms fold check** establishes that the
accumulator was folded correctly and binds the lookups to `R*` — *distribution integrity*,
i.e. anti-substitution relative to a publisher-constructed `R*`. It does **not** by itself
enforce the per-record digest/AIR constraints, because by the width law
(`verify ≈ 20 + 1.3·width ms`) an 18 ms verify is only reachable at near-zero width — the
fold table alone. **Statement validity** ("no adversary can make `Π` attest to a record whose
constraints don't hold") requires the **full decider**, which checks the accumulated instance
at record-AIR width — Keccak ~575 cols ⇒ ~0.8 s floor / measured assembled ~6.6–10 s
(trace-opening-dominated), SHA-256 ~2000 cols ⇒ ~2.6 s. Crucially the decider is **O(1) in N**
and runs **once per epoch**, so it amortizes into the background exactly like the 18 ms — but
the security section must claim only what the layer it describes checks.

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
assumption on the soundness path.

> **Which check earns which claim (the fold/decider distinction).** *Statement
> validity* — "no adversary can make `Π` attest to a record whose AIR constraints
> don't hold" — is earned only by the **full decider** (verify (b): pays record-AIR
> width, O(1) in N, sub-second–seconds). The **~18 ms fold check** (verify (a))
> earns only *distribution integrity* (fold-correctness + anti-substitution vs a
> publisher-constructed `R*`). Do not attribute validity to the 18 ms layer, and do
> not treat "Layer-1 verified prover-side" as repair — a prover checking its own
> proof is not a soundness event for the edge. An edge that runs (a) only gets a
> *correctly-folded commitment to a publisher-chosen record set*; an edge that also
> runs (b) gets *the records' constraints actually hold*.

> **Epoch-layer hash must ladder for L3/L5 to be real.** `κ_sys = min(record-layer,
> epoch-layer, decider)`. The record layer ladders its FS/commitment SHA-3 to the
> variant (§Level instantiation), **but the epoch proof `Π` and the EC/ECDSA gadgets
> use a `Sha256` challenger (128-bit FS)**. Unless the epoch proof's own FS + Merkle
> hash also ladder, `κ_sys` pins at **128 at L3/L5** regardless of Layer-1 laddering —
> so "18 ms at every level" is level-independence of *cost*, not of *security*. See
> the component×level×hash table below; every row must reach the category for the
> label to hold.

**2. Aggregation & lookup integrity — unconditional / PQ (distribution integrity).**
`R*` is a collision-resistant SHA-3 commitment to the *entire* interleaved
record set, and the fold check proves the accumulator was folded correctly.
Once a resolver has run **both** verify checks against `R*`, **no record can be
substituted, added, or dropped**, *and* the surviving records' constraints hold;
running the fold check **alone** gives the first (anti-substitution) but **not**
the second — that is the decider's job. Every µs lookup is a SHA-3 Merkle path back
to the *proven* root; adding records changes `R*` and needs a new `Π`. This is the
O(1)-in-N win; it is PQ for the same reason as (1).

**Component × level × hash (the single source of truth for κ_sys).**

| Component | Hash today | L1 (128) | L3 (192) | L5 (256) |
|-----------|-----------|:--------:|:--------:|:--------:|
| Record proof FS/commitment | SHA3-256/384/512 (laddered) | ✓ | ✓ | ✓ |
| Record digest AIR (in-circuit) | SHA3-N | ✓ | ✓ | ✓ |
| **Epoch proof `Π` FS** | SHA-256 today → **SHA3-N (mechanism proven)** | ✓ | ◐ | ◐ |
| **Epoch/EC-ECDSA challenger** | SHA-256 today → **SHA3-N (mechanism proven)** | ✓ | ◐ | ◐ |
| Lookup-tree Merkle | SHA3-N (leveled) | ✓ | ✓ | ✓ |

The two ◐ rows: the **laddering mechanism is now proven** — `ec_field_op_challenger_ladders_over_b256`
proves the EC field-op over B256 with `HasherChallenger<Sha3_N>` + `Sha3Compression<Sha3_N>` at
SHA3-256@128 **and SHA3-384@192** (so `κ_FS = κ_bind` ladders; L5 SHA3-512@256 needs B512 for
`κ_IT`). What remains is the **mechanical rollout**: swapping the type params on the ~33
EC/ECDSA/epoch prove/verify call sites (they hard-code `Sha256`). Until that rollout lands in
the *shipped* epoch prover, the combined artifact's L3/L5 label is still 128-epoch-pinned *in
the current binaries*, but the soundness path to real L3/L5 is demonstrated, not conjectural.

**Edge protocol (three tiers — the amortization shape).** On fetching the epoch package the
resolver runs, **once per epoch**: (1) the **decider** (statement validity, ~seconds, O(1) in N)
and (2) the **fold** (distribution integrity, ~18 ms, O(1) in N). Thereafter, **per DNS request**,
(3) a **µs SHA-3 Merkle-path** check of the record against the already-verified `R*` — not a
proof re-verification. So the expensive validity proof is paid once; every lookup in the epoch is
a µs membership check.

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

## Runnable `.se` epoch demo (real ECDSA-P256 RRSIGs + Merkle + proofs)

The projection below is anchored by a **complete, runnable `.se` TLD epoch** —
[`crates/binius-substrate/src/se_tld_epoch_demo.rs`](../crates/binius-substrate/src/se_tld_epoch_demo.rs),
test `se_tld_epoch_end_to_end`. It runs on **real Tranco `.se` names** and drives
the full DNSSEC delegation unit:

* per delegation: canonical RFC-4034 DS RRset → RRSIG signing input → **real
  ECDSA-P256 / SHA-256 signature** (DNSSEC algorithm 13 — the real `.se` ZSK),
  `m32 = SHA-256(signing_input)`, `leaf = SHA3-N(m32)`;
* **hybrid** (per the design decision): the ECDSA RRSIG is verified **natively**
  (`p256` crate — the reference the in-circuit S2 gadget is gated against; the
  assembled in-circuit ECDSA verify is not yet wired), the FIPS commitment
  `leaf` is proved **fully in-circuit** (b256/b512 SHA3 gadget, gated == native),
  and all N leaves feed the **SHA-3 Merkle lookup tree** + interleaved epoch
  commitment + aggregated epoch proof.

Measured green (256 real delegations, L1): all 256 RRSIGs verify + a tampered
signing input rejected; every in-circuit digest == the native Merkle leaf;
sampled membership auth-paths verify + a record-not-in-epoch rejected;
per-record in-circuit proof 608 KiB / prove 2456 ms / verify 9317 ms / RSS
0.13 GiB; Merkle tree depth 8; epoch proof 588 KiB / prove 921 ms / **edge
verify 81 ms, O(1) in N**; steady-state lookup ~1.8 µs. Flip `Sha3Level` for
L3 / L5.

> The signature check is **native-pending-in-circuit**; everything downstream of
> the signed message (commitment, aggregation, lookup) is in-circuit /
> cryptographic. Swapping the native ECDSA verify for the assembled S2 gadget is
> the only remaining upgrade.

## Projection: full `.se` TLD epoch

**A projection to full `.se`**, extrapolated from the measured 512-record batch
unit above plus the accumulation model — *not* a measured full-`.se` run (that
needs the prover fleet). It answers "what would prove/verify cost for the whole
TLD epoch?"

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

| Quantity | Value | What it earns |
|:---------|:------|:-----|
| Epoch verify — **fold check** | **~18 ms**, O(1) in N | distribution integrity (anti-substitution vs `R*`); consistent with the 1.36 ms HNPL edge package |
| Epoch verify — **full decider** (record-AIR width) | **~0.8 s Keccak floor / ~6.6–10 s measured**, O(1) in N | **statement validity** (the records' constraints hold) — REQUIRED for security-claim 1 |
| Per-record lookup                 | **~3 µs**  | Merkle path, depth ≈ log₂(2¹⁰·1.5 M) ≈ 30 SHA-3 hashes |

A resolver runs **both** checks on the **entire `.se` epoch once** — both O(1) in N
(*independent of whether it is 857 records or 1.5 M*), amortized per-epoch background
cost — then answers any of the 1.5 M delegations in ~3 µs. The decider is the number
that decides the headline: with it, the claim is "sound O(1)-in-N aggregation at
sub-second–seconds edge cost, once per epoch"; without it, only "efficient distribution."

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

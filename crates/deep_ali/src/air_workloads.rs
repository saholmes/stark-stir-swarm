//! air_workloads.rs
//!
//! Three AIR workloads for benchmarking DEEP-ALI + MF-FRI across
//! varying trace widths and constraint structures.
//!
//!   AIR                  | w   | constraints | degree | blowup
//!   ---------------------|-----|-------------|--------|-------
//!   Fibonacci            |  2  |     1       |   2    |   4
//!   Poseidon hash chain  | 16  |    16       |   2    |   4
//!   Register machine     |  8  |     8       |   2    |   4
//!
//! All AIRs produce genuine execution traces that satisfy their
//! transition constraints, so the composition quotient polynomial
//! is well-defined and low-degree.

use ark_ff::{Field, Zero, One, UniformRand};
use ark_goldilocks::Goldilocks as F;
use rand::{rngs::StdRng, SeedableRng};

// ═══════════════════════════════════════════════════════════════════
//  AIR type enumeration
// ═══════════════════════════════════════════════════════════════════

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AirType {
    /// Fibonacci recurrence  f(i+2) = f(i+1) + f(i).
    /// w = 2 trace columns, 1 degree-2 transition constraint.
    Fibonacci,

    /// Poseidon-like hash chain with state width t = 4.
    /// S-box x^7 decomposed: sq = x², cu = x³, fo = x⁴
    ///   → sbox_out = fo · cu = x⁷  (each step is degree 2).
    /// w = 16 columns  (4 state + 4 sq + 4 cu + 4 fo).
    /// 16 degree-2 transition constraints.
    PoseidonChain,

    /// Eight-register arithmetic machine with cross-coupled
    /// bilinear (degree-2) transition constraints.
    /// w = 8 columns, 8 degree-2 transition constraints.
    RegisterMachine,

    /// Simplified Cairo CPU AIR compatible with ethSTARK trace input format.
    ///
    /// Columns (w = 8):
    ///   [0] pc  — program counter
    ///   [1] ap  — allocation pointer
    ///   [2] fp  — frame pointer
    ///   [3] op0 — first operand
    ///   [4] op1 — second operand
    ///   [5] res — op0 * op1  (multiplication gate)
    ///   [6] dst — copy of res
    ///   [7] flags — instruction flags (reserved, always 0 in this AIR)
    ///
    /// Transition constraints (4, max degree 2):
    ///   C0: pc'  − pc  − 1 = 0   (PC advances by 1 per step)
    ///   C1: ap'  − ap  − 1 = 0   (AP advances by 1 per step)
    ///   C2: fp'  − fp      = 0   (FP is constant)
    ///   C3: dst  − op0 * op1 = 0  (multiplication gate, degree 2)
    ///
    /// Public inputs define boundary constraints on (pc, ap, fp) at
    /// row 0 and row n-1, verified by the API before proving.
    CairoSimple,

    /// 32-bit range check via two parallel bit-decomposition columns.
    ///
    /// Columns (w = 2):
    ///   [0] b_lo  — bit i of (witness - lower_bound)
    ///   [1] b_hi  — bit i of (upper_bound - witness)
    ///
    /// Per-row constraints (k = 2, max degree 2):
    ///   C0:  b_lo * (1 - b_lo) = 0
    ///   C1:  b_hi * (1 - b_hi) = 0
    ///
    /// (Implemented as transition constraints reading only `cur`,
    /// so they fire on every row of the trace.)
    ///
    /// Boundary constraints (carried via public_inputs_hash, evaluated
    /// at a single point and therefore essentially free):
    ///   Σ_i b_lo[i] · 2^i  =  witness - lower_bound
    ///   Σ_i b_hi[i] · 2^i  =  upper_bound - witness
    ///
    /// Backs the age-range predicate in the "Match Me If You Can"
    /// paper (Holmes 2026) and any other 32-bit two-sided range
    /// check (income brackets, postcode numeric ranges, etc.).
    AgeRange32,

    /// Poseidon Merkle inclusion path (w = 16).
    ///
    /// Identical constraint set to `PoseidonChain` — a Poseidon
    /// round-function chain — but with a distinct enum identity so
    /// the prover/verifier can dispatch on the country / e-mail
    /// set-membership predicate from the "Match Me If You Can" paper
    /// (Holmes 2026) without aliasing PoseidonChain in calling code.
    ///
    /// **Cryptographic note.**  This variant currently emits a real
    /// STARK proof at Poseidon-Merkle-equivalent cost, bound to the
    /// public set root via `public_inputs_hash`, but the constraint
    /// system does NOT enforce per-layer hash chaining or
    /// sibling-swap selection in-circuit; the witness's Merkle
    /// inclusion is checked at the application layer (mmiyc-air's
    /// `country::Witness::prove` membership gate) until a dedicated
    /// constraint set lands as a follow-up.  Storage and prove-time
    /// figures match a full in-circuit Merkle path because the
    /// PoseidonChain constraint set is what dominates both.
    MerklePath,

    /// Hash-chain rollup aggregator (w = 4).
    ///
    /// Absorbs a stream of leaf values into a running hash, used to
    /// aggregate commitments from multiple inner STARK proofs into a
    /// single rolled-up commitment.
    ///
    /// Columns (w = 4):
    ///   [0] idx       — row counter (0, 1, 2, …, n-1)
    ///   [1] leaf_val  — value being absorbed at this row
    ///   [2] state     — running hash accumulator
    ///   [3] state_sq  — auxiliary equal to state² (degree-1 reduction)
    ///
    /// Transition constraints (3, max degree 2):
    ///   C0: idx'      − idx − 1                = 0   (counter)
    ///   C1: state_sq  − state · state           = 0   (auxiliary squaring)
    ///   C2: state'    − state_sq − leaf_val     = 0   (absorb step: s' = s² + leaf)
    ///
    /// The leaf_val sequence in rollup demos contains the bytes of each
    /// inner proof's `public_inputs_hash`, packed 8 bytes per row.
    HashRollup,

    /// NSEC3 chain-completeness AIR (w = 8).
    ///
    /// Each row commits to one NSEC3 record's (owner_hash, next_hash)
    /// pair, packed as 4 little-endian u64 limbs each.  The chain-link
    /// invariant `next_hash[i] == owner_hash[i+1]` (with cyclic wrap
    /// row n-1 → row 0) is enforced by 4 transition constraints — one
    /// per limb.  Because the trace domain is cyclic in the FRI sense,
    /// the row n-1 → row 0 wrap fires the same constraint and so the
    /// "closed-cycle" property required for NSEC3 completeness is
    /// established by the same mechanism that enforces every other
    /// link.
    ///
    /// What this proves:  the committed sequence of NSEC3 records
    /// forms a closed cyclic chain on the 256-bit hash space, i.e. the
    /// intervals `[owner_i, next_i)` (with wrap-around) tile the full
    /// hash range with no gaps and no overlaps.  Combined with the
    /// `pi_hash` binding that enumerates the records' contents, this
    /// gives the global completeness property a bare Merkle commitment
    /// over the same records cannot.
    ///
    /// Columns (w = 8):
    ///   [0..3] owner_hash limbs  (4 × u64, little-endian on 32 bytes)
    ///   [4..7] next_hash limbs   (4 × u64)
    ///
    /// Transition constraints (4, all degree 1):
    ///   C0: nxt[0] − cur[4] = 0   (next_hash[i].limb0 == owner_hash[i+1].limb0)
    ///   C1: nxt[1] − cur[5] = 0
    ///   C2: nxt[2] − cur[6] = 0
    ///   C3: nxt[3] − cur[7] = 0
    ///
    /// The wrap row n-1 → row 0 enforces `next_hash[n-1] == owner_hash[0]`,
    /// which is the NSEC3 cyclic closure.
    Nsec3Chain,

    /// Single-block SHA-256 AIR for DS→KSK binding (FIPS 180-4 §6.2.2).
    ///
    /// Proves `SHA-256(message_block) == digest` over Goldilocks with
    /// the full message schedule and compression function in-circuit.
    /// w = 756 columns, 766 transition constraints, all degree ≤ 2.
    /// Trace height for one block: 128.  Multi-block messages are
    /// supported via `crate::sha256_air::build_sha256_trace_multi`,
    /// which returns `(trace, n_blocks)` and is invoked directly by
    /// `swarm-dns` rather than through this registry path.  This
    /// registry variant exposes only the single-block default trace
    /// (empty message → one padded block) for benchmarking against
    /// the other AIRs in `Self::all()`.
    Sha256DsKsk,
    /// Ed25519ZskKsk — full RFC 8032 §5.1.7 cofactored signature
    /// verification AIR (composed in `crate::ed25519_verify_air`).
    ///
    /// Proves `[8]·([s]·B − R − [k]·A) = O` end-to-end given public
    /// inputs `(M, R_compressed, A_compressed, s_bits, k_bits)`.  The
    /// underlying composition is parametric in `K_scalar` (the scalar
    /// bit-length); this registry variant exposes the **K=8** test
    /// configuration with the RFC 8032 TEST 1 vectors, which
    /// exercises every sub-phase (SHA-512 + scalar reduce + 2
    /// decompositions + 2 ladders + cofactor check + identity verdict)
    /// at a tractable trace size.  Production usage (K=256) calls
    /// `verify_air_layout_v16` / `fill_verify_air_v16` /
    /// `eval_verify_air_v16_per_row` directly from `swarm-dns`.
    Ed25519ZskKsk,

    /// NSEC3 NODATA type-bitmap non-coverage AIR (N2 gadget).
    ///
    /// Companion to `Nsec3Chain`.  Where the chain AIR proves the zone's
    /// NSEC3 records tile the namespace with no gaps (so a *name* either
    /// exists or is provably absent — NXDOMAIN), this AIR proves the
    /// complementary NODATA fact: a name that *does* exist has a queried
    /// RR type *absent* from its NSEC3 type bitmap (RFC 4034 §4.1.2,
    /// window 0, types 0..255).
    ///
    /// Columns (w = 3):
    ///   [0] bit   — bit `j` of the committed type bitmap (1 ⇔ type `j`
    ///               present at the name)
    ///   [1] sel   — selector, 1 at exactly the queried type row, else 0
    ///   [2] prod  — bit·sel (auxiliary, holds the product at degree 2)
    ///
    /// Transition constraints (4, all read the current row only, so they
    /// are trivially cyclic-safe over the FRI domain — same per-row style
    /// as `AgeRange32`):
    ///   C0: bit·(1−bit)  = 0        (bitmap entries are Boolean)
    ///   C1: sel·(1−sel)  = 0        (selector is Boolean)
    ///   C2: prod − bit·sel = 0      (product well-formed)
    ///   C3: prod          = 0       (NON-COVERAGE: wherever sel=1, bit=0)
    ///
    /// The full 32-byte bitmap, the queried type code, and the record's
    /// owner-hash are bound into `pi_hash` by the caller
    /// (`swarm_dns::prover::prove_nsec3_nodata`), which is where the
    /// selector position (= queried type) and the name-exists check
    /// (owner_hash == H(qname)) are pinned to public inputs — the same
    /// in-circuit-core + pi_hash-bound-public-values split used by the
    /// DS→KSK and RSA/ECDSA verifiers.
    Nsec3NoData,

    /// NSEC3 Opt-Out flag AIR (N3 gadget).
    ///
    /// Proves that a covering NSEC3 record carries the Opt-Out flag set
    /// (RFC 5155 §3.1.2.1), which authorises the legitimate elision of an
    /// unsigned (insecure) delegation from the iterated-hash chain: inside
    /// an Opt-Out span, the absence of an NSEC3 RR for an insecure
    /// delegation is correct, not an attack.
    ///
    /// Columns (w = 3) — the 8 bits of the NSEC3 Flags octet, LSB-first:
    ///   [0] bit   — bit `j` of the Flags octet (`(flags >> j) & 1`)
    ///   [1] sel   — selector, 1 at the Opt-Out bit row (bit 0), else 0
    ///   [2] prod  — bit·sel
    ///
    /// Transition constraints (4, cyclic-safe per-row, same style as N2):
    ///   C0: bit·(1−bit)  = 0     (Flags bits are Boolean)
    ///   C1: sel·(1−sel)  = 0     (selector is Boolean)
    ///   C2: prod − bit·sel = 0   (product well-formed)
    ///   C3: prod − sel     = 0   (OPT-OUT SET: wherever sel=1, bit=1)
    ///
    /// Note C3 is `prod − sel` (the SET polarity), versus N2's `prod`
    /// (the CLEAR polarity).  The Flags octet, the covering record's
    /// owner/next hashes, and the elided delegation's hash are bound into
    /// `pi_hash` by `swarm_dns::prover::prove_nsec3_optout`.
    Nsec3OptOut,

    /// Lexicographic strict-less-than over 256-bit values (F1 gadget).
    ///
    /// Proves `a < b` for two 256-bit integers (the big-endian
    /// interpretation of two 32-byte hashes — so integer order equals
    /// lexicographic byte order) entirely in-circuit, via
    /// subtraction-with-borrow: `a + 1 + δ = b` with `δ` a 256-bit
    /// value and no final carry-out.  This is the core primitive for the
    /// fully in-circuit NSEC3 interval cover (`prove_nsec3_cover`),
    /// removing the native lexicographic comparison from the
    /// denial-of-existence path.
    ///
    /// Single meaningful row (all rows hold the same comparison), so
    /// every constraint reads only the current row and is trivially
    /// cyclic-safe — no reliance on the wrap-row / release-skip pattern.
    ///
    /// Columns (w = 776):
    ///   [0..256)   abit  — bits of `a` (limb k = bits[k·32 .. k·32+32),
    ///                      LSB-first within the limb; value
    ///                      Σ_k limb_k·2^{32k})
    ///   [256..512) bbit  — bits of `b`
    ///   [512..768) dbit  — bits of `δ = b − a − 1`
    ///   [768..776) carry — per-limb carry-out of `a + 1 + δ` (Boolean)
    ///
    /// Constraints (785, degree ≤ 2):
    ///   * abit / bbit / dbit Boolean (768) — also range-checks every
    ///     32-bit limb for free (a limb is a sum of 32 committed bits)
    ///   * carry Boolean (8)
    ///   * per-limb addition `a_k + δ_k + carry_{k−1} + [k=0] −
    ///     b_k − carry_k·2^{32} = 0` (8), limb values recomposed inline
    ///   * final carry-out `carry_7 = 0` (1) — the strict-less-than verdict
    ///
    /// Operands `a`, `b` are bound into `pi_hash` by the caller
    /// (`swarm_dns::prover::prove_lex_lt`); the comparison *logic* is what
    /// this AIR proves (enforced by the low-degree test on the
    /// composition), versus the previous native `nsec3_covers`.
    LexLt,
}

impl AirType {
    /// Short label for CSV / filenames.
    pub fn label(self) -> &'static str {
        match self {
            AirType::Fibonacci       => "fib_w2_d2",
            AirType::PoseidonChain   => "poseidon_w16_d2",
            AirType::RegisterMachine => "regmach_w8_d2",
            AirType::CairoSimple     => "cairo_simple_w8_d2",
            AirType::AgeRange32      => "age_range32_w2_d2",
            AirType::MerklePath      => "merkle_path_w16_d2",
            AirType::HashRollup      => "hash_rollup_w4_d2",
            AirType::Nsec3Chain      => "nsec3_chain_w8_d1",
            AirType::Sha256DsKsk     => "sha256_dsksk_w756_d2",
            AirType::Ed25519ZskKsk   => "ed25519_zskksk_v16_k8",
            AirType::Nsec3NoData     => "nsec3_nodata_w3_d2",
            AirType::Nsec3OptOut     => "nsec3_optout_w3_d2",
            AirType::LexLt           => "lex_lt_w776_d2",
        }
    }

    /// Number of trace columns.
    pub fn width(self) -> usize {
        match self {
            AirType::Fibonacci       => 2,
            AirType::PoseidonChain   => 16,
            AirType::RegisterMachine => 8,
            AirType::CairoSimple     => 8,
            AirType::AgeRange32      => 2,
            AirType::MerklePath      => 16,
            AirType::HashRollup      => 4,
            AirType::Nsec3Chain      => 8,
            AirType::Sha256DsKsk     => crate::sha256_air::WIDTH,
            AirType::Ed25519ZskKsk   => ed25519_zsk_ksk_default_layout().width,
            AirType::Nsec3NoData     => 3,
            AirType::Nsec3OptOut     => 3,
            AirType::LexLt           => 776,
        }
    }

    /// Maximum individual constraint degree.
    pub fn max_constraint_degree(self) -> usize {
        2
    }

    /// Number of transition constraints.
    pub fn num_constraints(self) -> usize {
        match self {
            AirType::Fibonacci       => 1,
            AirType::PoseidonChain   => 16,
            AirType::RegisterMachine => 8,
            AirType::CairoSimple     => 4,
            AirType::AgeRange32      => 2,
            AirType::MerklePath      => 16,
            AirType::HashRollup      => 3,
            AirType::Nsec3Chain      => 4,
            AirType::Sha256DsKsk     => crate::sha256_air::NUM_CONSTRAINTS,
            AirType::Ed25519ZskKsk   =>
                crate::ed25519_verify_air::verify_v16_per_row_constraints(8),
            AirType::Nsec3NoData     => 4,
            AirType::Nsec3OptOut     => 4,
            AirType::LexLt           => 785,
        }
    }

    /// Convenience: all defined workloads.
    pub fn all() -> &'static [AirType] {
        &[
            AirType::Fibonacci,
            AirType::PoseidonChain,
            AirType::RegisterMachine,
            AirType::CairoSimple,
            AirType::AgeRange32,
            AirType::MerklePath,
            AirType::HashRollup,
            AirType::Nsec3Chain,
            AirType::Sha256DsKsk,
            AirType::Ed25519ZskKsk,
        ]
    }
}

// ═══════════════════════════════════════════════════════════════════
//  Top-level dispatcher
// ═══════════════════════════════════════════════════════════════════

/// Build a raw execution trace (w columns × n_trace rows) for the
/// given AIR.  Every row genuinely satisfies the transition
/// constraints so that the composition quotient is low-degree.
pub fn build_execution_trace(air: AirType, n_trace: usize) -> Vec<Vec<F>> {
    assert!(n_trace >= 2, "trace must have at least 2 rows");
    match air {
        AirType::Fibonacci       => build_fibonacci_trace(n_trace),
        AirType::PoseidonChain   => build_poseidon_chain_trace(n_trace),
        AirType::RegisterMachine => build_register_machine_trace(n_trace),
        AirType::CairoSimple     => build_cairo_simple_trace(n_trace),
        AirType::AgeRange32      => build_age_range_trace(n_trace),
        // MerklePath shares the PoseidonChain constraint set; the
        // trace builder is shared too.  See enum-variant doc for
        // the cryptographic boundary on what this currently proves.
        AirType::MerklePath      => build_poseidon_chain_trace(n_trace),
        AirType::HashRollup      => build_hash_rollup_trace(n_trace, &default_rollup_leaves(n_trace)),
        AirType::Nsec3Chain      => build_nsec3_chain_trace(n_trace, &default_nsec3_chain(n_trace)),
        AirType::Sha256DsKsk     => build_sha256_dsksk_trace(n_trace),
        AirType::Ed25519ZskKsk   => build_ed25519_zsk_ksk_default_trace(n_trace),
        // Registry default: an all-zero bitmap (no types present) with the
        // selector on the AAAA row (type 28).  Every bit is 0, so the
        // non-coverage product is trivially 0 — a valid NODATA trace.
        AirType::Nsec3NoData     => build_nsec3_nodata_trace(n_trace, 28, &[0u8; 32]),
        // Registry default: Flags octet = 0x01 (Opt-Out set), selector on
        // bit 0 — a valid Opt-Out trace.
        AirType::Nsec3OptOut     => build_nsec3_optout_trace(n_trace, 0, 0x01),
        // Registry default: prove 0 < 1.
        AirType::LexLt           => build_lex_lt_trace(n_trace, [0; 8], { let mut b = [0u64; 8]; b[0] = 1; b }),
    }
}

/// Evaluate the transition constraints for AIR type `air` given
/// the current row values `cur` and the next row values `nxt`.
/// Returns a vector of length `air.num_constraints()`.
/// On a valid trace every entry is zero.
pub fn evaluate_constraints(
    air: AirType,
    cur: &[F],
    nxt: &[F],
    // Poseidon needs round constants per row; pass row index
    row: usize,
) -> Vec<F> {
    match air {
        AirType::Fibonacci       => eval_fibonacci_constraints(cur, nxt),
        AirType::PoseidonChain   => eval_poseidon_constraints(cur, nxt, row),
        AirType::RegisterMachine => eval_register_constraints(cur, nxt),
        AirType::CairoSimple     => eval_cairo_simple_constraints(cur, nxt),
        AirType::AgeRange32      => eval_age_range_constraints(cur),
        AirType::MerklePath      => eval_poseidon_constraints(cur, nxt, row),
        AirType::HashRollup      => eval_hash_rollup_constraints(cur, nxt),
        AirType::Nsec3Chain      => eval_nsec3_chain_constraints(cur, nxt),
        AirType::Sha256DsKsk     => crate::sha256_air::eval_sha256_constraints(
            cur, nxt, row, /* n_blocks = */ 1,
        ),
        AirType::Ed25519ZskKsk   => crate::ed25519_verify_air::eval_verify_air_v16_per_row(
            cur, nxt, row, ed25519_zsk_ksk_default_layout(),
        ),
        AirType::Nsec3NoData     => eval_nsec3_nodata_constraints(cur),
        AirType::Nsec3OptOut     => eval_nsec3_optout_constraints(cur),
        AirType::LexLt           => eval_lex_lt_constraints(cur),
    }
}

// ═══════════════════════════════════════════════════════════════════
//  AIR 1 — Fibonacci  (w = 2)
// ═══════════════════════════════════════════════════════════════════

fn build_fibonacci_trace(n: usize) -> Vec<Vec<F>> {
    let mut c0 = vec![F::zero(); n];
    let mut c1 = vec![F::zero(); n];
    c0[0] = F::one();
    c1[0] = F::one();
    for i in 0..n - 1 {
        // transition: c0' = c1,  c1' = c0 + c1
        let next_c0 = c1[i];
        let next_c1 = c0[i] + c1[i];
        if i + 1 < n {
            c0[i + 1] = next_c0;
            c1[i + 1] = next_c1;
        }
    }
    vec![c0, c1]
}

fn eval_fibonacci_constraints(cur: &[F], nxt: &[F]) -> Vec<F> {
    // constraint:  nxt[1] - cur[0] - cur[1] = 0
    vec![nxt[1] - cur[0] - cur[1]]
}

// ═══════════════════════════════════════════════════════════════════
//  AIR — AgeRange32 (w = 2, k = 2, deg 2)
//
//  Per-row Boolean check on two parallel bit-decomposition columns.
//  Backs the age-range / income-bracket / postcode-prefix predicates
//  in the Match-Me-If-You-Can paper (Holmes 2026).
// ═══════════════════════════════════════════════════════════════════

fn build_age_range_trace(n: usize) -> Vec<Vec<F>> {
    // Deterministic well-formed trace: alternating bits in column 0,
    // every-other-row bits in column 1.  Exact pattern doesn't matter
    // for prove-time benchmarks; the only invariant the framework
    // enforces is that each cell satisfies the per-row Boolean.
    let mut b_lo = vec![F::zero(); n];
    let mut b_hi = vec![F::zero(); n];
    for i in 0..n {
        if (i & 1) != 0        { b_lo[i] = F::one(); }
        if ((i >> 1) & 1) != 0 { b_hi[i] = F::one(); }
    }
    vec![b_lo, b_hi]
}

fn eval_age_range_constraints(cur: &[F]) -> Vec<F> {
    // Per-row Boolean: cur[i] * (1 - cur[i]) = 0  for i ∈ {0, 1}.
    // Reads only the current row; the same constraint is enforced
    // on every trace row via the standard transition mechanism.
    let one = F::one();
    vec![
        cur[0] * (one - cur[0]),
        cur[1] * (one - cur[1]),
    ]
}

// ═══════════════════════════════════════════════════════════════════
//  AIR 2 — Poseidon-like hash chain  (w = 16)
// ═══════════════════════════════════════════════════════════════════
//
//  State width t = 4.
//  Columns layout:
//     [0..4)   state   s_j
//     [4..8)   sq_j  = (s_j + rc_j)²
//     [8..12)  cu_j  = sq_j · (s_j + rc_j)     = (s_j + rc_j)³
//     [12..16) fo_j  = sq_j²                    = (s_j + rc_j)⁴
//
//  sbox_out_j = fo_j · cu_j  = (s_j + rc_j)⁷
//
//  Transition constraints (all degree ≤ 2):
//    C_{4+j}:  sq_j  - (s_j + rc_j)²                     = 0
//    C_{8+j}:  cu_j  - sq_j · (s_j + rc_j)               = 0
//    C_{12+j}: fo_j  - sq_j²                              = 0
//    C_j:      s_j'  - Σ_k mds[j][k] · (fo_k · cu_k)     = 0
//
//  Round constants are derived deterministically from a fixed seed.

/// Deterministic round constants.  Cached via a simple closure;
/// the benchmark calls `build_execution_trace` which generates them
/// inline. For constraint evaluation we regenerate from the same seed.
fn poseidon_round_constant(row: usize, col: usize) -> F {
    // Fast deterministic derivation — not cryptographically strong,
    // but sufficient for a benchmark trace.
    let seed = (row as u64)
        .wrapping_mul(0x9E37_79B9_7F4A_7C15)
        .wrapping_add(col as u64)
        .wrapping_mul(0x6C62_272E_07BB_0142);
    F::from(seed)
}

fn build_mds_4x4() -> [[F; 4]; 4] {
    // Cauchy matrix:  M[i][j] = 1 / (x_i + y_j)
    // with x_i = i+1, y_j = t+j+1,  t = 4.
    let mut m = [[F::zero(); 4]; 4];
    for i in 0..4u64 {
        for j in 0..4u64 {
            let denom = F::from(i + 1) + F::from(4 + j + 1);
            m[i as usize][j as usize] =
                denom.inverse().expect("Cauchy denominator is nonzero");
        }
    }
    m
}

fn build_poseidon_chain_trace(n: usize) -> Vec<Vec<F>> {
    let t = 4usize;
    let w = 4 * t; // 16
    let mut trace = vec![vec![F::zero(); n]; w];
    let mds = build_mds_4x4();

    let mut state: [F; 4] = [
        F::from(1u64),
        F::from(2u64),
        F::from(3u64),
        F::from(4u64),
    ];

    for row in 0..n {
        // ---- write state columns 0..4 ----
        for j in 0..t {
            trace[j][row] = state[j];
        }

        // ---- S-box decomposition ----
        let mut sbox_out = [F::zero(); 4];
        for j in 0..t {
            let rc = poseidon_round_constant(row, j);
            let s  = state[j] + rc;
            let sq = s * s;        // s²
            let cu = sq * s;       // s³
            let fo = sq * sq;      // s⁴
            sbox_out[j] = fo * cu; // s⁷

            trace[t     + j][row] = sq; // cols  4..8
            trace[2 * t + j][row] = cu; // cols  8..12
            trace[3 * t + j][row] = fo; // cols 12..16
        }

        // ---- MDS → next state ----
        if row + 1 < n {
            for j in 0..t {
                let mut acc = F::zero();
                for k in 0..t {
                    acc += mds[j][k] * sbox_out[k];
                }
                state[j] = acc;
            }
        }
    }

    trace
}

fn eval_poseidon_constraints(cur: &[F], nxt: &[F], row: usize) -> Vec<F> {
    let t = 4usize;
    let mds = build_mds_4x4(); // cheap for t = 4
    let mut out = vec![F::zero(); 16];

    // ---- auxiliary column constraints ----
    for j in 0..t {
        let rc = poseidon_round_constant(row, j);
        let s  = cur[j] + rc;         // state + round constant
        let sq = cur[t + j];          // sq column
        let cu = cur[2 * t + j];      // cu column
        let fo = cur[3 * t + j];      // fo column

        out[t     + j] = sq - s * s;         // sq  = s²
        out[2 * t + j] = cu - sq * s;        // cu  = s³
        out[3 * t + j] = fo - sq * sq;       // fo  = s⁴
    }

    // ---- state transition constraints ----
    for j in 0..t {
        let mut expected = F::zero();
        for k in 0..t {
            let fo = cur[3 * t + k];
            let cu = cur[2 * t + k];
            expected += mds[j][k] * fo * cu; // fo · cu = s⁷
        }
        out[j] = nxt[j] - expected;
    }

    out
}

// ═══════════════════════════════════════════════════════════════════
//  AIR 3 — Eight-register arithmetic machine  (w = 8)
// ═══════════════════════════════════════════════════════════════════
//
//  Transitions (all degree-2, bilinear cross-coupling):
//    r0' = r0 · r1 + r2
//    r1' = r1 · r2 + r3
//    r2' = r2 · r3 + r4
//    r3' = r3 · r4 + r5
//    r4' = r4 · r5 + r6
//    r5' = r5 · r6 + r7
//    r6' = r6 · r7 + r0
//    r7' = r0 · r4 + r1 · r5 + r2 · r6 + r3 · r7
//
//  The last constraint couples all 8 registers via an inner-product
//  structure, making the constraint system non-separable.

fn build_register_machine_trace(n: usize) -> Vec<Vec<F>> {
    let w = 8usize;
    let mut trace = vec![vec![F::zero(); n]; w];

    let mut r: [F; 8] = core::array::from_fn(|i| F::from((i + 1) as u64));

    for row in 0..n {
        for j in 0..w {
            trace[j][row] = r[j];
        }
        if row + 1 < n {
            let p = r; // snapshot
            r[0] = p[0] * p[1] + p[2];
            r[1] = p[1] * p[2] + p[3];
            r[2] = p[2] * p[3] + p[4];
            r[3] = p[3] * p[4] + p[5];
            r[4] = p[4] * p[5] + p[6];
            r[5] = p[5] * p[6] + p[7];
            r[6] = p[6] * p[7] + p[0];
            r[7] = p[0] * p[4] + p[1] * p[5] + p[2] * p[6] + p[3] * p[7];
        }
    }

    trace
}

fn eval_register_constraints(cur: &[F], nxt: &[F]) -> Vec<F> {
    let r = cur;
    vec![
        nxt[0] - (r[0] * r[1] + r[2]),
        nxt[1] - (r[1] * r[2] + r[3]),
        nxt[2] - (r[2] * r[3] + r[4]),
        nxt[3] - (r[3] * r[4] + r[5]),
        nxt[4] - (r[4] * r[5] + r[6]),
        nxt[5] - (r[5] * r[6] + r[7]),
        nxt[6] - (r[6] * r[7] + r[0]),
        nxt[7] - (r[0] * r[4] + r[1] * r[5] + r[2] * r[6] + r[3] * r[7]),
    ]
}

// ═══════════════════════════════════════════════════════════════════
//  AIR 4 — Simplified Cairo CPU  (w = 8)
// ═══════════════════════════════════════════════════════════════════
//
//  Columns:
//    [0] pc    — program counter  (starts at initial_pc, increments by 1)
//    [1] ap    — allocation ptr   (starts at initial_ap, increments by 1)
//    [2] fp    — frame pointer    (constant throughout execution)
//    [3] op0   — first operand    (row+1, the natural sequence)
//    [4] op1   — second operand   (row+2)
//    [5] res   — op0 * op1        (multiplication gate)
//    [6] dst   — copy of res
//    [7] flags — reserved (zero)
//
//  Transition constraints (4 constraints, max degree 2):
//    C0: pc'  - pc  - 1 = 0             (PC increments)
//    C1: ap'  - ap  - 1 = 0             (AP increments)
//    C2: fp'  - fp      = 0             (FP constant)
//    C3: dst  - op0 * op1 = 0           (MUL gate, degree 2)
//
//  Public inputs set boundary values for (pc, ap, fp) at row 0 and row n-1.

/// Default initial PC and AP for CairoSimple traces.
pub const CAIRO_SIMPLE_INITIAL_PC: u64 = 0;
pub const CAIRO_SIMPLE_INITIAL_AP: u64 = 100;

fn build_cairo_simple_trace(n: usize) -> Vec<Vec<F>> {
    let mut pc   = vec![F::zero(); n];
    let mut ap   = vec![F::zero(); n];
    let mut fp   = vec![F::zero(); n];
    let mut op0  = vec![F::zero(); n];
    let mut op1  = vec![F::zero(); n];
    let mut res  = vec![F::zero(); n];
    let mut dst  = vec![F::zero(); n];
    let mut flags = vec![F::zero(); n];

    let init_pc = F::from(CAIRO_SIMPLE_INITIAL_PC);
    let init_ap = F::from(CAIRO_SIMPLE_INITIAL_AP);

    for i in 0..n {
        let row = i as u64;
        pc[i]   = init_pc + F::from(row);
        ap[i]   = init_ap + F::from(row);
        fp[i]   = init_ap; // constant
        op0[i]  = F::from(row + 1);
        op1[i]  = F::from(row + 2);
        res[i]  = op0[i] * op1[i];
        dst[i]  = res[i];
        flags[i] = F::zero();
    }

    vec![pc, ap, fp, op0, op1, res, dst, flags]
}

fn eval_cairo_simple_constraints(cur: &[F], nxt: &[F]) -> Vec<F> {
    // C0: pc' - pc - 1 = 0
    let c0 = nxt[0] - cur[0] - F::one();
    // C1: ap' - ap - 1 = 0
    let c1 = nxt[1] - cur[1] - F::one();
    // C2: fp' - fp = 0
    let c2 = nxt[2] - cur[2];
    // C3: dst - op0 * op1 = 0  (uses current row only, degree 2)
    let c3 = cur[6] - cur[3] * cur[4];
    vec![c0, c1, c2, c3]
}

// ═══════════════════════════════════════════════════════════════════
//  AIR 5 — HashRollup aggregator  (w = 4)
// ═══════════════════════════════════════════════════════════════════
//
//  A streaming hash that absorbs a sequence of leaf values into a
//  running accumulator.  Used as the outer "rollup" AIR over a sequence
//  of inner-proof commitments.
//
//  Columns:
//    [0] idx       — counter, 0, 1, …, n-1
//    [1] leaf_val  — value being absorbed at this row
//    [2] state     — running hash accumulator (state' = state² + leaf)
//    [3] state_sq  — auxiliary equal to state²
//
//  Transition constraints (3, max degree 2):
//    C0: idx'      − idx − 1                = 0
//    C1: state_sq  − state · state           = 0
//    C2: state'    − state_sq − leaf_val     = 0
//
//  Boundary semantics (under the existing `validate_trace_boundaries`):
//    initial_pc → idx[0]      = 0
//    initial_ap → leaf_val[0] = first absorbed value
//    initial_fp → state[0]    = 0   (running hash starts at zero)
//    final_pc   → idx[n-1]    = n-1
//    final_ap   → leaf_val[n-1] = last absorbed value
//
//  The rolled-up commitment is `state[n-1]` — the verifier learns this
//  from the public-inputs commitment (carried through the FS transcript)
//  and from `public_memory` entries if those are populated.

/// Build a HashRollup trace from an explicit sequence of leaf values.
/// `leaves.len()` must equal `n_trace`; if not, leaves are padded with
/// zeros / truncated.
pub fn build_hash_rollup_trace(n_trace: usize, leaves: &[u64]) -> Vec<Vec<F>> {
    let mut idx      = vec![F::zero(); n_trace];
    let mut leaf_col = vec![F::zero(); n_trace];
    let mut state    = vec![F::zero(); n_trace];
    let mut state_sq = vec![F::zero(); n_trace];

    let mut s = F::zero();
    for i in 0..n_trace {
        let leaf = if i < leaves.len() { F::from(leaves[i]) } else { F::zero() };
        idx[i]      = F::from(i as u64);
        leaf_col[i] = leaf;
        state[i]    = s;
        state_sq[i] = s * s;
        // Advance for the next row.
        s = state_sq[i] + leaf;
    }

    vec![idx, leaf_col, state, state_sq]
}

fn eval_hash_rollup_constraints(cur: &[F], nxt: &[F]) -> Vec<F> {
    // C0: idx' - idx - 1 = 0
    let c0 = nxt[0] - cur[0] - F::one();
    // C1: state_sq - state * state = 0
    let c1 = cur[3] - cur[2] * cur[2];
    // C2: state' - state_sq - leaf_val = 0
    let c2 = nxt[2] - cur[3] - cur[1];
    vec![c0, c1, c2]
}

/// Default leaf sequence for `build_execution_trace(HashRollup, n)`.
/// Used by benchmarks and the AIR self-tests; rollup demos build their
/// own leaf vector from inner proof commitments.
fn default_rollup_leaves(n: usize) -> Vec<u64> {
    (0..n as u64).map(|i| i.wrapping_mul(0x9E37_79B9_7F4A_7C15)).collect()
}

/// Pack a 32-byte hash into 4 little-endian u64 leaves.  Used by rollup
/// demos to absorb each inner proof's `public_inputs_hash` into the
/// outer HashRollup trace.
pub fn pack_hash_to_leaves(hash: &[u8; 32]) -> [u64; 4] {
    let mut out = [0u64; 4];
    for (i, chunk) in hash.chunks_exact(8).enumerate() {
        let mut buf = [0u8; 8];
        buf.copy_from_slice(chunk);
        out[i] = u64::from_le_bytes(buf);
    }
    out
}

/// Compute the same rollup state[n-1] that `build_hash_rollup_trace`
/// would produce, in pure host arithmetic (for verifier-side consistency
/// checks against the public-inputs commitment).
pub fn compute_hash_rollup_final_state(n_trace: usize, leaves: &[u64]) -> u64 {
    use ark_ff::PrimeField;
    let mut s = F::zero();
    for i in 0..n_trace {
        let leaf = if i < leaves.len() { F::from(leaves[i]) } else { F::zero() };
        s = s * s + leaf;
    }
    s.into_bigint().0[0]
}

// ═══════════════════════════════════════════════════════════════════
//  Sanity check (debug builds / tests)
// ═══════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ff::PrimeField;

    fn verify_trace(air: AirType, n: usize) {
        let trace = build_execution_trace(air, n);
        assert_eq!(trace.len(), air.width());
        for col in &trace {
            assert_eq!(col.len(), n);
        }
        // Check constraints on interior rows
        for row in 0..n - 1 {
            let cur: Vec<F> = trace.iter().map(|c| c[row]).collect();
            let nxt: Vec<F> = trace.iter().map(|c| c[row + 1]).collect();
            let cv = evaluate_constraints(air, &cur, &nxt, row);
            for (ci, val) in cv.iter().enumerate() {
                assert!(
                    val.is_zero(),
                    "AIR {:?}  row {}  constraint {} != 0",
                    air, row, ci
                );
            }
        }
    }

    #[test]
    fn fibonacci_trace_valid()    { verify_trace(AirType::Fibonacci, 1024); }

    #[test]
    fn poseidon_trace_valid()     { verify_trace(AirType::PoseidonChain, 1024); }

    #[test]
    fn register_trace_valid()     { verify_trace(AirType::RegisterMachine, 1024); }

    #[test]
    fn cairo_simple_trace_valid() { verify_trace(AirType::CairoSimple, 1024); }

    #[test]
    fn hash_rollup_trace_valid()  { verify_trace(AirType::HashRollup, 1024); }

    #[test]
    fn sha256_dsksk_registry_trace_valid() {
        // Single-block default trace via the registry (n_blocks = 1
        // baked in by the dispatcher).  Uses the empty-message padded
        // block.
        verify_trace(AirType::Sha256DsKsk, crate::sha256_air::N_TRACE);
    }

    #[test]
    fn sha256_dsksk_registry_trace_padded_to_larger_height() {
        // Larger n_trace (256) — registry pads by replicating the last
        // row of the 128-row single-block trace.
        verify_trace(AirType::Sha256DsKsk, 256);
    }

    #[test]
    fn ed25519_zskksk_registry_trace_valid() {
        // K=8 stub from `air_workloads.rs`'s registry: a zero-scalar
        // identity-R configuration making `[8]·([0]·B − R_id − [0]·A)
        // = O` hold, exercising every sub-phase of the v16 verify AIR.
        let h = super::ed25519_zsk_ksk_default_layout().height;
        verify_trace(AirType::Ed25519ZskKsk, h);
    }

    #[test]
    fn hash_rollup_aggregates_two_proof_hashes() {
        // Pack two 32-byte SHA3-256 commitments into 8 leaves and roll them up.
        let h_a: [u8; 32] = *b"INNER_PROOF_A_PUBLIC_INPUTS_HASH";
        let h_b: [u8; 32] = *b"INNER_PROOF_B_PUBLIC_INPUTS_HASH";
        let mut leaves = pack_hash_to_leaves(&h_a).to_vec();
        leaves.extend_from_slice(&pack_hash_to_leaves(&h_b));

        let n = 16usize;                   // power of 2 >= leaves.len()
        let trace = build_hash_rollup_trace(n, &leaves);
        assert_eq!(trace.len(), 4);
        assert_eq!(trace[0].len(), n);

        // All transition constraints must be satisfied.
        for row in 0..n - 1 {
            let cur: Vec<F> = trace.iter().map(|c| c[row]).collect();
            let nxt: Vec<F> = trace.iter().map(|c| c[row + 1]).collect();
            let cv = eval_hash_rollup_constraints(&cur, &nxt);
            for (i, v) in cv.iter().enumerate() {
                assert!(v.is_zero(), "row {row} constraint {i} != 0");
            }
        }

        // The host-side closed-form must match the trace's final state.
        let expected = compute_hash_rollup_final_state(n, &leaves);
        let trace_final: u64 =
            <F as ark_ff::PrimeField>::into_bigint(trace[2][n - 1]).0[0];
        // After the last row's update would have happened, but the trace stores
        // state[i] BEFORE absorbing leaf[i], so the closed-form for `n`
        // absorbs corresponds to `compute_hash_rollup_final_state(n, leaves)`
        // computed AFTER the loop.  The trace[2][n-1] equals state before the
        // n-th absorb step.  So compare to compute(n-1, leaves).
        let prefinal = compute_hash_rollup_final_state(n - 1, &leaves);
        assert_eq!(trace_final, prefinal);
        // And the n-th step value (what state[n] would be if the trace had one
        // more row) equals expected.
        let _ = expected;
    }

    #[test]
    fn cairo_simple_boundary_values() {
        use super::{CAIRO_SIMPLE_INITIAL_AP, CAIRO_SIMPLE_INITIAL_PC};
        let n = 64usize;
        let trace = build_execution_trace(AirType::CairoSimple, n);
        assert_eq!(trace.len(), 8);
        // PC starts at initial_pc, ends at initial_pc + n - 1
        let pc_u64: u64 = trace[0][0].into_bigint().0[0];
        assert_eq!(pc_u64, CAIRO_SIMPLE_INITIAL_PC);
        let pc_final: u64 = trace[0][n - 1].into_bigint().0[0];
        assert_eq!(pc_final, CAIRO_SIMPLE_INITIAL_PC + n as u64 - 1);
        // AP starts at initial_ap
        let ap_u64: u64 = trace[1][0].into_bigint().0[0];
        assert_eq!(ap_u64, CAIRO_SIMPLE_INITIAL_AP);
        // FP is constant
        assert_eq!(trace[2][0], trace[2][n - 1]);
    }

    #[test]
    fn nsec3_chain_constraints_zero_on_valid_trace() {
        // Build a closed cyclic chain of n_trace records and check that
        // the transition constraints evaluate to zero on every row,
        // including the wrap row n-1 → 0.
        let n_trace = 16;
        let mut chain: Vec<([u64; 4], [u64; 4])> = Vec::with_capacity(n_trace);
        // Pick n_trace distinct "owner" hashes; the next_hash of each is
        // the owner of the next record (cyclically).
        let owners: Vec<[u64; 4]> = (0..n_trace as u64)
            .map(|i| [i, i.wrapping_mul(31), i.wrapping_mul(17), i.wrapping_mul(7)])
            .collect();
        for i in 0..n_trace {
            let next = owners[(i + 1) % n_trace];
            chain.push((owners[i], next));
        }
        let trace = build_nsec3_chain_trace(n_trace, &chain);
        for i in 0..n_trace {
            let cur: Vec<F> = (0..8).map(|c| trace[c][i]).collect();
            let nxt: Vec<F> = (0..8).map(|c| trace[c][(i + 1) % n_trace]).collect();
            let cs = eval_nsec3_chain_constraints(&cur, &nxt);
            for (k, c) in cs.iter().enumerate() {
                assert!(c.is_zero(),
                    "row {i} constraint {k} non-zero: {c:?}");
            }
        }
    }

    #[test]
    fn nsec3_type_present_matches_rfc4034_window0() {
        // Set bits for A(1), AAAA(28), RRSIG(46), NSEC3(50).
        let mut bm = [0u8; 32];
        for t in [1u8, 28, 46, 50] {
            bm[(t >> 3) as usize] |= 1 << (7 - (t & 7));
        }
        for t in 0u8..=255 {
            let want = matches!(t, 1 | 28 | 46 | 50);
            assert_eq!(super::nsec3_type_present(&bm, t), want,
                "type {t} presence mismatch");
        }
    }

    #[test]
    fn nsec3_nodata_constraints_zero_on_valid_nodata() {
        // Name has A(1), RRSIG(46), NSEC3(50) but NOT AAAA(28).
        // Query AAAA → NODATA.  Every per-row constraint must be zero.
        let mut bm = [0u8; 32];
        for t in [1u8, 46, 50] {
            bm[(t >> 3) as usize] |= 1 << (7 - (t & 7));
        }
        let n_trace = 256;
        let trace = build_nsec3_nodata_trace(n_trace, 28, &bm);
        assert_eq!(trace.len(), 3);
        for j in 0..n_trace {
            let cur: Vec<F> = (0..3).map(|c| trace[c][j]).collect();
            let cs = super::eval_nsec3_nodata_constraints(&cur);
            for (k, c) in cs.iter().enumerate() {
                assert!(c.is_zero(),
                    "row {j} constraint {k} non-zero: {c:?}");
            }
        }
    }

    #[test]
    fn nsec3_nodata_constraints_catch_present_type() {
        // Adversary selects a type whose bit IS set (A=1 is present).
        // The C3 non-coverage constraint must fire at the selector row.
        let mut bm = [0u8; 32];
        bm[0] |= 1 << (7 - 1); // type A = 1 present
        let qtype = 1usize;
        // Hand-build the malicious trace: bit=1, sel=1 at the A row.
        let n_trace = 256;
        let mut bit = vec![F::zero(); n_trace];
        let mut sel = vec![F::zero(); n_trace];
        let mut prod = vec![F::zero(); n_trace];
        for j in 0..256usize {
            bit[j] = if super::nsec3_type_present(&bm, j as u8) { F::one() } else { F::zero() };
            sel[j] = if j == qtype { F::one() } else { F::zero() };
            prod[j] = bit[j] * sel[j]; // honestly computed product (= 1 at A row)
        }
        let cur: Vec<F> = vec![bit[qtype], sel[qtype], prod[qtype]];
        let cs = super::eval_nsec3_nodata_constraints(&cur);
        // C0,C1,C2 still hold; C3 (prod==0) must be violated.
        assert!(cs[0].is_zero() && cs[1].is_zero() && cs[2].is_zero());
        assert!(!cs[3].is_zero(),
            "non-coverage constraint failed to catch a present type");
    }

    #[test]
    fn nsec3_optout_constraints_zero_on_set_flag() {
        // Flags = 0x01 (Opt-Out set), selector on bit 0 → all constraints 0.
        let n_trace = 8;
        let trace = build_nsec3_optout_trace(n_trace, 0, 0x01);
        assert_eq!(trace.len(), 3);
        for j in 0..n_trace {
            let cur: Vec<F> = (0..3).map(|c| trace[c][j]).collect();
            let cs = super::eval_nsec3_optout_constraints(&cur);
            for (k, c) in cs.iter().enumerate() {
                assert!(c.is_zero(), "row {j} constraint {k} non-zero: {c:?}");
            }
        }
    }

    #[test]
    fn nsec3_optout_constraints_catch_clear_flag() {
        // Flags = 0x00 (Opt-Out CLEAR): at the selector row bit=0, sel=1,
        // so C3 (prod − sel) = −1 ≠ 0 — the gadget rejects a non-opt-out
        // record being passed off as opt-out.
        let n_trace = 8;
        let trace = build_nsec3_optout_trace(n_trace, 0, 0x00);
        let cur: Vec<F> = (0..3).map(|c| trace[c][0]).collect();
        let cs = super::eval_nsec3_optout_constraints(&cur);
        assert!(cs[0].is_zero() && cs[1].is_zero() && cs[2].is_zero());
        assert!(!cs[3].is_zero(),
            "opt-out constraint failed to catch a cleared flag");
    }

    fn lexlt_all_zero(trace: &[Vec<F>], n_trace: usize) -> bool {
        (0..n_trace).all(|row| {
            let cur: Vec<F> = (0..super::LEXLT_WIDTH).map(|c| trace[c][row]).collect();
            super::eval_lex_lt_constraints(&cur).iter().all(|v| v.is_zero())
        })
    }

    #[test]
    fn lexlt_constraints_zero_on_valid_less_than() {
        let n_trace = 8;
        // a few a < b cases including limb-boundary carries
        let cases: &[([u64; 8], [u64; 8])] = &[
            ([0; 8], { let mut b = [0u64; 8]; b[0] = 1; b }),
            ([1, 0, 0, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 0, 0]),
            ([0xFFFF_FFFF, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0]),
            ([5, 5, 5, 5, 5, 5, 5, 5], [5, 5, 5, 5, 5, 5, 5, 6]),
        ];
        for (a, b) in cases {
            let trace = build_lex_lt_trace(n_trace, *a, *b);
            assert!(lexlt_all_zero(&trace, n_trace), "valid a<b {a:?}<{b:?} must satisfy");
        }
    }

    #[test]
    #[should_panic(expected = "requires a < b")]
    fn lexlt_build_panics_on_not_less() {
        // a == b is not a < b — builder must refuse (final borrow != 0).
        let _ = build_lex_lt_trace(8, [7; 8], [7; 8]);
    }

    #[test]
    fn lexlt_constraints_catch_forged_carry() {
        // Take a valid a<b trace, then forge the final carry to 1 (as a
        // cheater would to fake a "no-overflow" verdict for a >= b).  The
        // final-carry constraint must fire.
        let n_trace = 8;
        let mut trace = build_lex_lt_trace(n_trace, [1, 0, 0, 0, 0, 0, 0, 0], [3, 0, 0, 0, 0, 0, 0, 0]);
        trace[super::LEXLT_CARRY0 + 7][0] = F::one(); // forge
        let cur: Vec<F> = (0..super::LEXLT_WIDTH).map(|c| trace[c][0]).collect();
        let cs = super::eval_lex_lt_constraints(&cur);
        assert!(cs.iter().any(|v| !v.is_zero()),
            "forging the final carry must break some constraint");
    }
}

// ═══════════════════════════════════════════════════════════════════
//  AIR 6 — NSEC3 chain completeness  (w = 8)
// ═══════════════════════════════════════════════════════════════════
//
//  Each row commits to one NSEC3 record's (owner_hash, next_hash) pair,
//  packed as 4 little-endian u64 limbs each.  Consecutive rows are
//  linked: row_i's next_hash limbs equal row_{i+1}'s owner_hash limbs.
//  The transition constraint applies cyclically over the FRI domain,
//  so the wrap row n-1 → row 0 enforces `next[n-1] == owner[0]` —
//  the closed-cycle property required for NSEC3 completeness.
//
//  Columns (w = 8):
//    [0..3] owner_hash (4 × u64 limbs)
//    [4..7] next_hash  (4 × u64 limbs)
//
//  Transition constraints (4, all degree 1):
//    C0..C3:  nxt[k] − cur[4 + k] = 0   for k ∈ {0, 1, 2, 3}

/// Build an NSEC3 chain trace.  `chain[i]` = (owner_hash_limbs, next_hash_limbs)
/// for record i.  `chain.len()` should equal `n_trace`; if shorter, the
/// trace is padded with a self-cycling all-zero record (which still
/// satisfies the chain-link constraint), if longer it is truncated.
pub fn build_nsec3_chain_trace(
    n_trace: usize,
    chain: &[([u64; 4], [u64; 4])],
) -> Vec<Vec<F>> {
    assert!(n_trace.is_power_of_two(), "n_trace must be a power of 2");
    let mut cols: Vec<Vec<F>> = (0..8).map(|_| vec![F::zero(); n_trace]).collect();
    // First, copy the input chain into the first chain.len() rows.
    for (i, (owner, next)) in chain.iter().take(n_trace).enumerate() {
        for k in 0..4 {
            cols[k][i]     = F::from(owner[k]);
            cols[4 + k][i] = F::from(next[k]);
        }
    }
    // Padding: if there are unused rows beyond `chain.len()`, fill them
    // with self-cycling zero records (owner = next = 0). The chain link
    // from the last real record's next must equal the next padding row's
    // owner; we set the padding's owner to whatever the previous row's
    // next was so the constraint is locally satisfied.
    if chain.len() < n_trace {
        // The wrap from the last real row → first padding row needs
        // owner[chain.len()] = next[chain.len()-1].
        let mut prev_next = if !chain.is_empty() {
            let last = &chain[chain.len() - 1];
            [last.1[0], last.1[1], last.1[2], last.1[3]]
        } else {
            [0u64; 4]
        };
        for i in chain.len()..n_trace {
            for k in 0..4 {
                cols[k][i]     = F::from(prev_next[k]);
                cols[4 + k][i] = F::from(prev_next[k]); // self-cycle on padding
            }
            // next padding row's owner should equal this padding row's next,
            // and our self-cycle keeps `next == owner` so that's `prev_next`.
            prev_next = prev_next;
        }
        // Final fix: the wrap row n-1 → row 0 needs next[n-1] = owner[0].
        // Force the last padding row's next to equal owner[0] of the trace.
        for k in 0..4 {
            cols[4 + k][n_trace - 1] = cols[k][0];
        }
    } else {
        // Exactly n_trace records: the wrap closure is the user's
        // responsibility (they should pass a closed chain). We do NOT
        // mutate trace[7][n-1] etc., so the constraint will FAIL at
        // wrap if the user passed a non-closed chain — surfacing the
        // bug.
    }
    cols
}

fn eval_nsec3_chain_constraints(cur: &[F], nxt: &[F]) -> Vec<F> {
    // C0..C3:  nxt[k] − cur[4 + k] = 0
    vec![
        nxt[0] - cur[4],
        nxt[1] - cur[5],
        nxt[2] - cur[6],
        nxt[3] - cur[7],
    ]
}

/// Default NSEC3 chain for `build_execution_trace(Nsec3Chain, n)`.
/// Generates a sequence of n distinct owner hashes (just `i`-derived
/// values), with each record's next equal to the next record's owner
/// and the last wrapping to the first.  Used by the AIR self-tests
/// and the `build_execution_trace` dispatcher.
fn default_nsec3_chain(n: usize) -> Vec<([u64; 4], [u64; 4])> {
    let owners: Vec<[u64; 4]> = (0..n as u64)
        .map(|i| [
            i.wrapping_mul(0x0123_4567_89AB_CDEF),
            i.wrapping_mul(0xFEDC_BA98_7654_3210),
            i.wrapping_mul(0xDEAD_BEEF_CAFE_BABE),
            i.wrapping_mul(0x9E37_79B9_7F4A_7C15),
        ])
        .collect();
    (0..n).map(|i| (owners[i], owners[(i + 1) % n])).collect()
}

/// Pack a 32-byte hash into 4 little-endian u64 limbs.  Re-export of
/// the same function used for HashRollup — included here for clarity
/// at the NSEC3 call sites.
pub fn pack_nsec3_hash(hash: &[u8; 32]) -> [u64; 4] {
    pack_hash_to_leaves(hash)
}

// ═══════════════════════════════════════════════════════════════════
//  AIR 6b — NSEC3 NODATA type-bitmap non-coverage  (w = 3)  [N2 gadget]
// ═══════════════════════════════════════════════════════════════════
//
//  Proves the NODATA half of authenticated denial-of-existence: a name
//  that EXISTS has a queried RR type ABSENT from its NSEC3 type bitmap.
//  See the `AirType::Nsec3NoData` doc comment for the column layout and
//  constraint set.

/// RFC 4034 §4.1.2 window-0 bit test: is RR type `t` (0..255) present in
/// the 32-byte type bitmap?  Type `t` lives in byte `t >> 3`, bit
/// `7 − (t & 7)` (MSB-first within the byte).
#[inline]
pub fn nsec3_type_present(bitmap: &[u8; 32], t: u8) -> bool {
    let byte = bitmap[(t >> 3) as usize];
    ((byte >> (7 - (t & 7))) & 1) == 1
}

/// Build a NODATA non-coverage trace.
///
/// `qtype` is the queried RR type code (window 0, 0..255); `bitmap` is the
/// committed 32-byte NSEC3 type bitmap.  Row `j` carries bit `j` of the
/// bitmap and a selector that is 1 only at `j == qtype`.  Rows beyond 256
/// (if `n_trace > 256`) are zero-padded; all-zero rows satisfy every
/// per-row constraint.
///
/// The caller (`swarm_dns::prover::prove_nsec3_nodata`) must ensure the
/// queried type's bit is 0 — otherwise the C3 (`prod == 0`) constraint
/// fails at the selector row and the proof is rejected.
pub fn build_nsec3_nodata_trace(
    n_trace: usize,
    qtype:   u16,
    bitmap:  &[u8; 32],
) -> Vec<Vec<F>> {
    assert!(n_trace.is_power_of_two(), "n_trace must be a power of 2");
    assert!(n_trace >= 2, "trace must have at least 2 rows");
    let mut bit = vec![F::zero(); n_trace];
    let mut sel = vec![F::zero(); n_trace];
    let mut prod = vec![F::zero(); n_trace];
    let limit = n_trace.min(256);
    for j in 0..limit {
        let b = if nsec3_type_present(bitmap, j as u8) { F::one() } else { F::zero() };
        let s = if (qtype as usize) == j { F::one() } else { F::zero() };
        bit[j]  = b;
        sel[j]  = s;
        prod[j] = b * s;
    }
    vec![bit, sel, prod]
}

/// Transition (per-row) constraints for the NODATA non-coverage AIR.
/// Reads only the current row; returns 4 values, all zero on a valid
/// trace.
fn eval_nsec3_nodata_constraints(cur: &[F]) -> Vec<F> {
    let one = F::one();
    vec![
        cur[0] * (one - cur[0]),       // C0: bit Boolean
        cur[1] * (one - cur[1]),       // C1: sel Boolean
        cur[2] - cur[0] * cur[1],      // C2: prod = bit·sel
        cur[2],                        // C3: prod = 0  (non-coverage)
    ]
}

// ═══════════════════════════════════════════════════════════════════
//  AIR 6c — NSEC3 Opt-Out flag  (w = 3)  [N3 gadget]
// ═══════════════════════════════════════════════════════════════════
//
//  Proves a covering NSEC3 record's Flags octet has the Opt-Out bit SET
//  (RFC 5155 §3.1.2.1).  See the `AirType::Nsec3OptOut` doc comment.

/// Build an Opt-Out flag trace.  `flags` is the NSEC3 Flags octet; row `j`
/// (`j < 8`) carries its bit `j` (LSB-first), and the selector marks the
/// Opt-Out bit row `optout_bit` (bit 0 per RFC 5155).  Rows beyond 8 are
/// zero-padded (Boolean-valid, sel=0).
///
/// The caller (`swarm_dns::prover::prove_nsec3_optout`) must pass a `flags`
/// octet whose Opt-Out bit is 1 — otherwise the C3 (`prod == sel`)
/// constraint fails at the selector row and the proof is rejected.
pub fn build_nsec3_optout_trace(
    n_trace:    usize,
    optout_bit: usize,
    flags:      u8,
) -> Vec<Vec<F>> {
    assert!(n_trace.is_power_of_two(), "n_trace must be a power of 2");
    assert!(n_trace >= 2, "trace must have at least 2 rows");
    let mut bit = vec![F::zero(); n_trace];
    let mut sel = vec![F::zero(); n_trace];
    let mut prod = vec![F::zero(); n_trace];
    let limit = n_trace.min(8);
    for j in 0..limit {
        let b = if ((flags >> j) & 1) == 1 { F::one() } else { F::zero() };
        let s = if optout_bit == j { F::one() } else { F::zero() };
        bit[j]  = b;
        sel[j]  = s;
        prod[j] = b * s;
    }
    vec![bit, sel, prod]
}

/// Transition constraints for the Opt-Out AIR.  Identical to the NODATA
/// AIR except C3 enforces the SET polarity (`prod = sel`, i.e. the
/// selected bit is 1) rather than the CLEAR polarity.
fn eval_nsec3_optout_constraints(cur: &[F]) -> Vec<F> {
    let one = F::one();
    vec![
        cur[0] * (one - cur[0]),       // C0: bit Boolean
        cur[1] * (one - cur[1]),       // C1: sel Boolean
        cur[2] - cur[0] * cur[1],      // C2: prod = bit·sel
        cur[2] - cur[1],               // C3: prod = sel (Opt-Out SET)
    ]
}

// ═══════════════════════════════════════════════════════════════════
//  AIR — Lexicographic strict-less-than  (w = 776)  [F1 gadget]
// ═══════════════════════════════════════════════════════════════════
//
//  Proves a < b for two 256-bit integers via subtraction-with-borrow.
//  See the `AirType::LexLt` doc comment for layout + constraints.

/// Column-range constants for the LexLt AIR.
pub const LEXLT_ABIT0:  usize = 0;
pub const LEXLT_BBIT0:  usize = 256;
pub const LEXLT_DBIT0:  usize = 512;
pub const LEXLT_CARRY0: usize = 768;
pub const LEXLT_WIDTH:  usize = 776;

/// Recompose 32-bit limb `k` (LSB-first) from a bit column slice rooted
/// at `base` in row `cur`.
#[inline]
fn lexlt_limb(cur: &[F], base: usize, k: usize) -> F {
    let mut acc = F::zero();
    let mut pow = F::one();
    let two = F::from(2u64);
    for j in 0..32 {
        acc += cur[base + k * 32 + j] * pow;
        pow *= two;
    }
    acc
}

/// Bit `j` of 32-bit limb value `v`.
#[inline]
fn bit_of(v: u64, j: usize) -> u64 { (v >> j) & 1 }

/// Build a LexLt trace proving `a < b` (both as 8 little-endian 32-bit
/// limbs of a 256-bit integer; limb 0 is least significant).  All
/// `n_trace` rows hold the same comparison.  Panics if `a >= b`.
pub fn build_lex_lt_trace(
    n_trace: usize,
    a: [u64; 8],
    b: [u64; 8],
) -> Vec<Vec<F>> {
    assert!(n_trace.is_power_of_two() && n_trace >= 2, "n_trace pow2 ≥ 2");
    // δ = b − a − 1, by borrow subtraction over 32-bit limbs.
    let mut delta = [0u64; 8];
    let mut borrow: i64 = 0;
    for k in 0..8 {
        let sub = if k == 0 { 1i64 } else { 0 };
        let mut v = b[k] as i64 - a[k] as i64 - sub - borrow;
        if v < 0 { v += 1i64 << 32; borrow = 1; } else { borrow = 0; }
        delta[k] = v as u64;
    }
    assert_eq!(borrow, 0, "build_lex_lt_trace requires a < b (final borrow != 0)");

    // Forward carries of a + 1 + δ = b.
    let mut carry = [0u64; 8];
    let mut cin: u64 = 0;
    for k in 0..8 {
        let add = if k == 0 { 1u64 } else { 0 };
        let s = a[k] + delta[k] + cin + add;
        carry[k] = s >> 32;
        cin = carry[k];
    }
    debug_assert_eq!(carry[7], 0, "no final carry for a < b");

    let mut cols: Vec<Vec<F>> = (0..LEXLT_WIDTH).map(|_| vec![F::zero(); n_trace]).collect();
    for row in 0..n_trace {
        for k in 0..8 {
            for j in 0..32 {
                cols[LEXLT_ABIT0 + k * 32 + j][row] = F::from(bit_of(a[k], j));
                cols[LEXLT_BBIT0 + k * 32 + j][row] = F::from(bit_of(b[k], j));
                cols[LEXLT_DBIT0 + k * 32 + j][row] = F::from(bit_of(delta[k], j));
            }
            cols[LEXLT_CARRY0 + k][row] = F::from(carry[k]);
        }
    }
    cols
}

/// Per-row constraints for the LexLt AIR (785 values, all zero on a valid
/// `a < b` trace).
fn eval_lex_lt_constraints(cur: &[F]) -> Vec<F> {
    let one = F::one();
    let two32 = F::from(1u64 << 32);
    let mut out = Vec::with_capacity(LEXLT_WIDTH + 9);

    // Booleanity of all bit columns (768) — also range-checks each limb.
    for i in 0..256 { out.push(cur[LEXLT_ABIT0 + i] * (one - cur[LEXLT_ABIT0 + i])); }
    for i in 0..256 { out.push(cur[LEXLT_BBIT0 + i] * (one - cur[LEXLT_BBIT0 + i])); }
    for i in 0..256 { out.push(cur[LEXLT_DBIT0 + i] * (one - cur[LEXLT_DBIT0 + i])); }
    // Carry booleanity (8).
    for k in 0..8 { out.push(cur[LEXLT_CARRY0 + k] * (one - cur[LEXLT_CARRY0 + k])); }

    // Per-limb addition a_k + δ_k + carry_{k-1} + [k=0] − b_k − carry_k·2^32 = 0 (8).
    for k in 0..8 {
        let a_k = lexlt_limb(cur, LEXLT_ABIT0, k);
        let b_k = lexlt_limb(cur, LEXLT_BBIT0, k);
        let d_k = lexlt_limb(cur, LEXLT_DBIT0, k);
        let cin = if k == 0 { F::zero() } else { cur[LEXLT_CARRY0 + k - 1] };
        let add = if k == 0 { one } else { F::zero() };
        out.push(a_k + d_k + cin + add - b_k - cur[LEXLT_CARRY0 + k] * two32);
    }

    // Final carry-out must be 0 ⟺ a < b (1).
    out.push(cur[LEXLT_CARRY0 + 7]);

    out
}

// ═══════════════════════════════════════════════════════════════════
//  AIR 7 — Single-block SHA-256 (DS→KSK binding)
// ═══════════════════════════════════════════════════════════════════
//
// Registry-path trace builder: produces a default single-block trace
// for the empty message (one padded block).  Real DS→KSK proving is
// driven by `crate::sha256_air::build_sha256_trace_multi` directly
// from `swarm-dns`, with the actual DNSKEY RDATA bytes.

fn build_sha256_dsksk_trace(n_trace: usize) -> Vec<Vec<F>> {
    assert!(n_trace >= crate::sha256_air::N_TRACE,
        "Sha256DsKsk requires n_trace >= {} (single block)",
        crate::sha256_air::N_TRACE);
    assert!(n_trace.is_power_of_two(), "n_trace must be a power of 2");

    // Pad an empty message ("") into one canonical SHA-256 block.
    let blocks = crate::sha256_air::pad_message_to_blocks(b"");
    debug_assert_eq!(blocks.len(), 1);

    // Build the single-block trace at default height (128).
    let mut single = crate::sha256_air::build_sha256_trace(&blocks[0]);

    // If the registry asked for a larger trace (e.g. for benchmarking
    // at higher LDE blowup), pad each column by replicating row
    // (N_TRACE - 1).  That row is in the post-finalisation idle
    // region of the single-block trace, where every transition
    // constraint is satisfied by `nxt = cur`.
    if n_trace > crate::sha256_air::N_TRACE {
        for col in single.iter_mut() {
            let last = *col.last().expect("non-empty column");
            col.resize(n_trace, last);
        }
    }

    debug_assert_eq!(single.len(), crate::sha256_air::WIDTH);
    debug_assert_eq!(single[0].len(), n_trace);
    single
}

// ═══════════════════════════════════════════════════════════════════
//  AIR 8 — Ed25519ZskKsk  (RFC 8032 §5.1.7 cofactored verify, K=8)
// ═══════════════════════════════════════════════════════════════════
//
// Registry stub for the composed Ed25519 verify AIR (v16 of
// `crate::ed25519_verify_air`).  The AIR is parametric in `K_scalar`;
// production usage at K=256 calls `verify_air_layout_v16` /
// `fill_verify_air_v16` / `eval_verify_air_v16_per_row` directly with
// per-signature inputs.  For the registry we expose a fixed-size K=8
// stub initialised from the RFC 8032 TEST 1 vectors so that
// `AirType::all()` enumerates a self-contained, end-to-end-sound AIR
// usable by benchmarks and self-checks.
//
// All inputs (R, A, signature scalar s, derived k bits) are baked into
// a `OnceLock` layout; the trace builder regenerates the trace each
// call from these constants.

use std::sync::OnceLock;

/// RFC 8032 TEST 1 fixtures used by the registry stub.
fn rfc8032_test1_pubkey() -> [u8; 32] {
    let bytes = hex::decode(
        "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a",
    ).unwrap();
    let mut a = [0u8; 32]; a.copy_from_slice(&bytes); a
}
fn rfc8032_test1_sig() -> [u8; 64] {
    let bytes = hex::decode(
        "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555f\
         b8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b",
    ).unwrap();
    let mut a = [0u8; 64]; a.copy_from_slice(&bytes); a
}

/// Static defaults for the K=8 registry stub.  Computed once on first
/// access.  Kept in module-private statics so the layout's `Vec<bool>`
/// fields don't have to be reconstructed per call.
///
/// Configuration: zero-scalar identity case (R = compressed identity,
/// any A, s_bits = k_bits = 0).  This makes the cofactored predicate
/// `[8]·(O − R_id − O) = O` hold trivially while still exercising
/// every sub-phase of the AIR (SHA-512, scalar reduce, both
/// decompositions, both ladders, the residual chain, the doubling
/// chain, and the identity verdict).  The k_scalar = 8 truncation of
/// real signature bits would generally fail the verdict, so we use a
/// configuration that's mathematically valid at any K.
fn ed25519_zsk_ksk_defaults() -> &'static (
    Vec<u8>,                 // sha512_input = R || A || M
    [u8; 32],                // r_compressed (= compressed identity)
    [u8; 32],                // a_compressed
    Vec<bool>,               // s_bits (all zeros)
    Vec<bool>,               // k_bits (all zeros — also = canonical-r-low-8)
) {
    static D: OnceLock<(Vec<u8>, [u8; 32], [u8; 32], Vec<bool>, Vec<bool>)>
        = OnceLock::new();
    D.get_or_init(|| {
        // R = identity, compressed: y = 1 (= [0x01, 0, ..., 0]), sign = 0.
        let mut r_compressed = [0u8; 32];
        r_compressed[0] = 0x01;
        // A = RFC 8032 TEST 1 pubkey (any valid encoding works).
        let a_compressed = rfc8032_test1_pubkey();

        // The k_bits binding (v7) requires k_bits[i] = bit (K−1−i) of the
        // canonical r derived from SHA-512(R || A || M).  Since we want
        // k_bits = 0 (so [k]·A = identity), we MUST pick a (R, A, M) such
        // that the LOW 8 BITS of canonical-r are all zero.  Search a
        // small message space until we find one.
        let mut sha_input = Vec::with_capacity(64);
        sha_input.extend_from_slice(&r_compressed);
        sha_input.extend_from_slice(&a_compressed);
        let mut k_bits = vec![false; 8];
        let mut tweak: u32 = 0;
        loop {
            let mut probe = sha_input.clone();
            probe.extend_from_slice(&tweak.to_le_bytes());
            let digest = crate::sha512_air::sha512_native(&probe);
            let mut digest_arr = [0u8; 64];
            digest_arr.copy_from_slice(&digest);
            let k_canonical = crate::ed25519_scalar::reduce_mod_l_wide(&digest_arr);
            let candidate = crate::ed25519_verify_air::r_thread_bits_for_kA(
                &k_canonical, 8,
            );
            if candidate.iter().all(|&b| !b) {
                k_bits = candidate;
                sha_input = probe;
                break;
            }
            tweak = tweak.wrapping_add(1);
            assert!(tweak < 1 << 20,
                "registry default search failed to find low-8-bits-zero r");
        }

        let s_bits = vec![false; 8];
        (sha_input, r_compressed, a_compressed, s_bits, k_bits)
    })
}

/// Static default layout for `AirType::Ed25519ZskKsk`.
pub fn ed25519_zsk_ksk_default_layout()
    -> &'static crate::ed25519_verify_air::VerifyAirLayoutV16
{
    static L: OnceLock<crate::ed25519_verify_air::VerifyAirLayoutV16>
        = OnceLock::new();
    L.get_or_init(|| {
        let (sha_input, r, a, s_bits, k_bits) = ed25519_zsk_ksk_defaults();
        crate::ed25519_verify_air::verify_air_layout_v16(
            sha_input.len(), s_bits, k_bits, r, a,
        ).expect("RFC 8032 TEST 1 vectors must yield a valid v16 layout")
    })
}

/// Build the registry's default Ed25519ZskKsk trace.  `n_trace` is the
/// caller-requested trace height; if it exceeds the natural v16 height,
/// the trace is row-replicated past the last useful row (consistent
/// with `Sha256DsKsk`'s padding scheme).
fn build_ed25519_zsk_ksk_default_trace(n_trace: usize) -> Vec<Vec<F>> {
    let (sha_input, r, a, s_bits, k_bits) = ed25519_zsk_ksk_defaults();
    let (mut trace, layout, _) =
        crate::ed25519_verify_air::fill_verify_air_v16(
            sha_input, r, a, s_bits, k_bits,
        ).expect("registry stub trace builder must succeed");

    assert!(n_trace.is_power_of_two(), "n_trace must be a power of 2");
    assert!(
        n_trace >= layout.height,
        "Ed25519ZskKsk requires n_trace >= {} (k_scalar=8 height)",
        layout.height,
    );

    if n_trace > layout.height {
        for col in trace.iter_mut() {
            let last = *col.last().expect("non-empty column");
            col.resize(n_trace, last);
        }
    }

    debug_assert_eq!(trace.len(), layout.width);
    debug_assert_eq!(trace[0].len(), n_trace);
    trace
}

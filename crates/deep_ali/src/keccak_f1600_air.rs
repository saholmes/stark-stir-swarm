//! AIR for Keccak-f[1600] — phase-4 complete (one-row-per-round form).
//!
//! ## Design choices
//!
//! - **Bit-decomposed lanes.**  Each of the 25 lanes is held as
//!   64 boolean cells.  This is mandatory: χ's nonlinearity is
//!   bitwise (`a ⊕ ((¬b) · c)`), so packing lanes into Goldilocks
//!   field elements would force degree-64 constraints.  All
//!   constraints below are degree ≤ 2.
//!
//! - **One round per row.**  Each row holds the full witness for
//!   one Keccak round: state-in (1 600 bits), θ-correction (C, D),
//!   post-θ, post-ρπ, χ-aux, post-χ, post-ι.  Round-to-round
//!   chaining is a transition constraint: post-ι of row r equals
//!   state-in of row r+1.  Total 24 active rows per Keccak-f
//!   permutation; pad up to a power-of-two trace height.
//!
//! - **Aux witnesses for non-deg-2 logic.**  The 5-input XOR in θ
//!   (C[x] = ⊕_y A[x,y]) and the χ inner product
//!   ((¬b) · c) both reduce to deg-2 with explicit auxiliary
//!   columns.  Cost: ~2 880 extra cells/row.
//!
//! - **ρ + π combined.**  The bit positions in `post_rho_pi[]`
//!   are determined by FIPS 202 Table 2 + the (y, 2x+3y mod 5)
//!   permutation.  Constraints assert deg-1 cell equalities.
//!
//! - **ι row-dependent.**  The round constant XORed at the top of
//!   the (0,0) lane changes per round.  We pass `row` into
//!   `eval_per_row` and gate the ι constraints with it.  Other
//!   lanes pass through (post_iota = post_chi).
//!
//! ## Per-round constraint budget (all degree ≤ 2)
//!
//! | Step                              | Count |
//! |-----------------------------------|-------|
//! | bit-boolean range (every cell)    | varies; ~10k |
//! | θ 5-input XOR (C[x] via 4 aux)    | 5 × 64 × 4 = 1 280 |
//! | θ rotation D[x] = C[x-1] ⊕ rot(C[x+1],1) | 5 × 64 = 320 |
//! | θ apply: post_theta = A ⊕ D       | 25 × 64 = 1 600 |
//! | ρ + π cell-equality               | 25 × 64 = 1 600 |
//! | χ aux: t = (1−b)·c                | 25 × 64 = 1 600 |
//! | χ apply: post_chi = a ⊕ t         | 25 × 64 = 1 600 |
//! | ι: post_iota = post_chi ⊕ RC      | 1 × 64 = 64  (lane (0,0) only) |
//! | ι identity for other lanes        | 24 × 64 = 1 536 |
//! | chain (transition)                | 25 × 64 = 1 600 |
//!
//! Bit-boolean range checks dominate; total ~12k constraints/row,
//! which the `deep_ali_merge_general` pipeline handles fine.

#![allow(non_snake_case, dead_code)]

use ark_ff::{One, Zero};
use ark_goldilocks::Goldilocks as F;

use crate::keccak_f1600::{idx, NUM_LANES, RC, RHO_OFFSETS, ROUNDS};

/// Bits per lane.
pub const LANE_BITS: usize = 64;

/// Total state bits.
pub const STATE_BITS: usize = NUM_LANES * LANE_BITS; // 1600

/// θ aux: 4 intermediate XOR bits per (x, b) — tree-reduce a 5-input
/// XOR into four 2-input XORs.
pub const THETA_AUX_PER_X: usize = 4 * LANE_BITS;
pub const THETA_AUX_TOTAL: usize = 5 * THETA_AUX_PER_X;

/// χ aux: one (1-b)·c product per output bit.
pub const CHI_AUX_TOTAL: usize = STATE_BITS;

// ─── Column ranges within a single round's row ─────────────────────

pub mod cols {
    use super::*;

    pub const STATE_IN_BASE:    usize = 0;
    pub const THETA_AUX_BASE:   usize = STATE_IN_BASE   + STATE_BITS;
    pub const C_BASE:           usize = THETA_AUX_BASE  + THETA_AUX_TOTAL;
    pub const D_BASE:           usize = C_BASE          + 5 * LANE_BITS;
    pub const POST_THETA_BASE:  usize = D_BASE          + 5 * LANE_BITS;
    pub const POST_RHO_PI_BASE: usize = POST_THETA_BASE + STATE_BITS;
    pub const CHI_AUX_BASE:     usize = POST_RHO_PI_BASE + STATE_BITS;
    pub const POST_CHI_BASE:    usize = CHI_AUX_BASE    + CHI_AUX_TOTAL;
    pub const POST_IOTA_BASE:   usize = POST_CHI_BASE   + STATE_BITS;
}

/// Total width of one round's row.
pub const ROUND_WIDTH: usize =
    STATE_BITS                  // state in
  + THETA_AUX_TOTAL             // θ tree-reduce intermediates
  + 5 * LANE_BITS               // C
  + 5 * LANE_BITS               // D
  + STATE_BITS                  // post-θ
  + STATE_BITS                  // post-ρπ
  + CHI_AUX_TOTAL               // χ aux
  + STATE_BITS                  // post-χ
  + STATE_BITS;                 // post-ι

// ─── Column accessors ──────────────────────────────────────────────

#[inline] pub fn state_in_col(x: usize, y: usize, b: usize) -> usize {
    cols::STATE_IN_BASE + idx(x, y) * LANE_BITS + b
}
/// θ tree-reduce intermediate: t_lvl(x, b) for lvl ∈ {0..3}.
/// t0 = A[x,0]⊕A[x,1]; t1 = t0⊕A[x,2]; t2 = t1⊕A[x,3]; C[x] = t2⊕A[x,4].
#[inline] pub fn theta_aux_col(x: usize, lvl: usize, b: usize) -> usize {
    cols::THETA_AUX_BASE + x * THETA_AUX_PER_X + lvl * LANE_BITS + b
}
#[inline] pub fn c_col(x: usize, b: usize) -> usize {
    cols::C_BASE + x * LANE_BITS + b
}
#[inline] pub fn d_col(x: usize, b: usize) -> usize {
    cols::D_BASE + x * LANE_BITS + b
}
#[inline] pub fn post_theta_col(x: usize, y: usize, b: usize) -> usize {
    cols::POST_THETA_BASE + idx(x, y) * LANE_BITS + b
}
#[inline] pub fn post_rho_pi_col(x: usize, y: usize, b: usize) -> usize {
    cols::POST_RHO_PI_BASE + idx(x, y) * LANE_BITS + b
}
#[inline] pub fn chi_aux_col(x: usize, y: usize, b: usize) -> usize {
    cols::CHI_AUX_BASE + idx(x, y) * LANE_BITS + b
}
#[inline] pub fn post_chi_col(x: usize, y: usize, b: usize) -> usize {
    cols::POST_CHI_BASE + idx(x, y) * LANE_BITS + b
}
#[inline] pub fn post_iota_col(x: usize, y: usize, b: usize) -> usize {
    cols::POST_IOTA_BASE + idx(x, y) * LANE_BITS + b
}

/// Total bit cells (any cell that should satisfy a 0/1 boolean constraint).
fn all_bit_cols() -> impl Iterator<Item = usize> {
    (0..ROUND_WIDTH)
}

// ─── XOR polynomial helpers ─────────────────────────────────────────
//
// For a, b ∈ {0, 1}: XOR(a, b) = a + b − 2ab.
// Constraint:  a + b − 2ab − c = 0  expresses c = a ⊕ b given the
// inputs are boolean.

#[inline]
fn xor_constraint(a: F, b: F, c: F) -> F {
    let two = F::from(2u64);
    a + b - two * a * b - c
}

#[inline]
fn xor_with_constant_bit(a: F, k: u64, c: F) -> F {
    // If k=0: c = a;        constraint c − a = 0
    // If k=1: c = 1 − a;    constraint c − (1 − a) = c + a − 1
    if k == 0 { c - a } else { c + a - F::one() }
}

// ─── fill_trace: drive one Keccak-f permutation through 24 rows ────

pub fn fill_trace(trace: &mut [Vec<F>], n_trace: usize, initial_state: &[u64; NUM_LANES]) {
    assert_eq!(trace.len(), ROUND_WIDTH);
    assert!(n_trace >= ROUNDS, "trace must have at least 24 rows");
    for col in trace.iter() { assert_eq!(col.len(), n_trace); }

    let mut state = *initial_state;

    for round in 0..ROUNDS {
        write_state_bits(trace, round, cols::STATE_IN_BASE, &state);

        // θ — column parities (5-input XOR) tree-reduced
        let mut c = [0u64; 5];
        for x in 0..5 {
            // Levels 0..3 progressively XOR in lanes 1..4
            let mut acc = state[idx(x, 0)];
            for lvl in 0..4 {
                acc ^= state[idx(x, lvl + 1)];
                write_lane_bits(trace, round, theta_aux_col(x, lvl, 0), acc);
            }
            c[x] = acc;
            write_lane_bits(trace, round, c_col(x, 0), c[x]);
        }
        let mut d = [0u64; 5];
        for x in 0..5 {
            d[x] = c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1);
            write_lane_bits(trace, round, d_col(x, 0), d[x]);
        }
        let mut post_theta = state;
        for x in 0..5 {
            for y in 0..5 {
                post_theta[idx(x, y)] ^= d[x];
            }
        }
        write_state_bits(trace, round, cols::POST_THETA_BASE, &post_theta);

        // ρ + π combined
        let mut post_rho_pi = [0u64; NUM_LANES];
        for x in 0..5 {
            for y in 0..5 {
                let new_x = y;
                let new_y = (2 * x + 3 * y) % 5;
                post_rho_pi[idx(new_x, new_y)] =
                    post_theta[idx(x, y)].rotate_left(RHO_OFFSETS[x][y]);
            }
        }
        write_state_bits(trace, round, cols::POST_RHO_PI_BASE, &post_rho_pi);

        // χ — bitwise nonlinearity with aux witness
        let mut post_chi = [0u64; NUM_LANES];
        let mut chi_aux = [0u64; NUM_LANES];
        for y in 0..5 {
            for x in 0..5 {
                let a = post_rho_pi[idx(x, y)];
                let b = post_rho_pi[idx((x + 1) % 5, y)];
                let cc = post_rho_pi[idx((x + 2) % 5, y)];
                let t = (!b) & cc;
                chi_aux[idx(x, y)] = t;
                post_chi[idx(x, y)] = a ^ t;
            }
        }
        write_state_bits(trace, round, cols::CHI_AUX_BASE, &chi_aux);
        write_state_bits(trace, round, cols::POST_CHI_BASE, &post_chi);

        // ι — XOR round constant into lane (0,0)
        let mut post_iota = post_chi;
        post_iota[idx(0, 0)] ^= RC[round];
        write_state_bits(trace, round, cols::POST_IOTA_BASE, &post_iota);

        state = post_iota;
    }
}

fn write_state_bits(trace: &mut [Vec<F>], row: usize, base: usize, st: &[u64; NUM_LANES]) {
    for lane in 0..NUM_LANES {
        write_lane_bits(trace, row, base + lane * LANE_BITS, st[lane]);
    }
}

fn write_lane_bits(trace: &mut [Vec<F>], row: usize, base: usize, lane: u64) {
    for b in 0..LANE_BITS {
        trace[base + b][row] = F::from(((lane >> b) & 1) as u64);
    }
}

// ─── Constraints ───────────────────────────────────────────────────

/// Evaluate every per-row Keccak round constraint.  Returns the
/// vector of constraint values; on a satisfying trace each entry
/// is zero.
///
/// `cur` is the current row's column vector; `nxt` is the next
/// row's (used for the inter-round chaining transition); `row` is
/// the row index in [0, 24) — used to gate the ι round constant.
pub fn eval_per_row(cur: &[F], nxt: &[F], row: usize) -> Vec<F> {
    let mut out = Vec::new();

    // 1. Bit-boolean range checks on every bit cell.
    for c in 0..ROUND_WIDTH {
        let v = cur[c];
        out.push(v * (v - F::one()));
    }

    // 2. θ tree-reduce: 4 levels × 5 columns × 64 bits.
    //    t0 = A[x,0,b] ⊕ A[x,1,b]
    //    t1 = t0 ⊕ A[x,2,b]
    //    t2 = t1 ⊕ A[x,3,b]
    //    C[x][b] = t2 ⊕ A[x,4,b]
    for x in 0..5 {
        for b in 0..LANE_BITS {
            let a0 = cur[state_in_col(x, 0, b)];
            let a1 = cur[state_in_col(x, 1, b)];
            let a2 = cur[state_in_col(x, 2, b)];
            let a3 = cur[state_in_col(x, 3, b)];
            let a4 = cur[state_in_col(x, 4, b)];
            let t0 = cur[theta_aux_col(x, 0, b)];
            let t1 = cur[theta_aux_col(x, 1, b)];
            let t2 = cur[theta_aux_col(x, 2, b)];
            let cv = cur[c_col(x, b)];
            out.push(xor_constraint(a0, a1, t0));
            out.push(xor_constraint(t0, a2, t1));
            out.push(xor_constraint(t1, a3, t2));
            out.push(xor_constraint(t2, a4, cv));
        }
    }

    // 3. θ rotation: D[x][b] = C[(x-1) mod 5][b] ⊕ C[(x+1) mod 5][(b-1) mod 64].
    for x in 0..5 {
        let xm = (x + 4) % 5;
        let xp = (x + 1) % 5;
        for b in 0..LANE_BITS {
            let bm = (b + LANE_BITS - 1) % LANE_BITS;
            let cm = cur[c_col(xm, b)];
            let cp = cur[c_col(xp, bm)];   // rotate_left(C[x+1], 1) means bit b comes from bit (b-1)
            let dv = cur[d_col(x, b)];
            out.push(xor_constraint(cm, cp, dv));
        }
    }

    // 4. θ apply: post_theta[(x,y)][b] = state_in[(x,y)][b] ⊕ D[x][b].
    for x in 0..5 {
        for y in 0..5 {
            for b in 0..LANE_BITS {
                let a  = cur[state_in_col(x, y, b)];
                let dv = cur[d_col(x, b)];
                let p  = cur[post_theta_col(x, y, b)];
                out.push(xor_constraint(a, dv, p));
            }
        }
    }

    // 5. ρ + π cell-equality: post_rho_pi[(y, 2x+3y mod 5)][(b + RHO[x][y]) mod 64]
    //    = post_theta[(x, y)][b].  Degree-1 constraints.
    for x in 0..5 {
        for y in 0..5 {
            let new_x = y;
            let new_y = (2 * x + 3 * y) % 5;
            let off = RHO_OFFSETS[x][y] as usize;
            for b in 0..LANE_BITS {
                let bp = (b + off) % LANE_BITS;
                let src  = cur[post_theta_col(x, y, b)];
                let dst  = cur[post_rho_pi_col(new_x, new_y, bp)];
                out.push(dst - src);
            }
        }
    }

    // 6. χ aux: chi_aux[(x,y)][b] = (1 − post_rho_pi[(x+1,y)][b]) · post_rho_pi[(x+2,y)][b].
    for x in 0..5 {
        for y in 0..5 {
            let xp1 = (x + 1) % 5;
            let xp2 = (x + 2) % 5;
            for b in 0..LANE_BITS {
                let bb = cur[post_rho_pi_col(xp1, y, b)];
                let cc = cur[post_rho_pi_col(xp2, y, b)];
                let t  = cur[chi_aux_col(x, y, b)];
                out.push((F::one() - bb) * cc - t);
            }
        }
    }

    // 7. χ apply: post_chi[(x,y)][b] = post_rho_pi[(x,y)][b] ⊕ chi_aux[(x,y)][b].
    for x in 0..5 {
        for y in 0..5 {
            for b in 0..LANE_BITS {
                let a = cur[post_rho_pi_col(x, y, b)];
                let t = cur[chi_aux_col(x, y, b)];
                let p = cur[post_chi_col(x, y, b)];
                out.push(xor_constraint(a, t, p));
            }
        }
    }

    // 8. ι: post_iota[(0,0)][b] = post_chi[(0,0)][b] ⊕ RC[row][b];
    //    other lanes: post_iota = post_chi.
    let rc = if row < ROUNDS { RC[row] } else { 0u64 };
    for b in 0..LANE_BITS {
        let pc = cur[post_chi_col(0, 0, b)];
        let pi = cur[post_iota_col(0, 0, b)];
        let rcb = (rc >> b) & 1;
        out.push(xor_with_constant_bit(pc, rcb, pi));
    }
    for x in 0..5 {
        for y in 0..5 {
            if x == 0 && y == 0 { continue; }
            for b in 0..LANE_BITS {
                let pc = cur[post_chi_col(x, y, b)];
                let pi = cur[post_iota_col(x, y, b)];
                out.push(pi - pc);
            }
        }
    }

    // 9. Inter-round chaining: state_in of next row equals post_iota
    //    of current row.  Skipped on the last active round; the
    //    deep_ali pipeline's wrap-around is handled by the caller
    //    via the trace boundary (we pad with zeros after row 23,
    //    and gate this constraint with `row < ROUNDS - 1`).
    if row + 1 < ROUNDS {
        for c_off in 0..STATE_BITS {
            let pi = cur[cols::POST_IOTA_BASE + c_off];
            let nx = nxt[cols::STATE_IN_BASE + c_off];
            out.push(nx - pi);
        }
    }

    out
}

// ─── Tests ─────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::keccak_f1600::keccak_f;

    fn fresh_trace(n_trace: usize) -> Vec<Vec<F>> {
        (0..ROUND_WIDTH).map(|_| vec![F::zero(); n_trace]).collect()
    }

    /// Honest trace from a known-good input: every constraint must hold.
    /// The 24-round Keccak-f permutation drives the trace; we then
    /// run `eval_per_row` for every row and assert all entries are zero.
    #[test]
    fn honest_trace_satisfies_all_constraints() {
        // Pick an arbitrary state.  Using the simple "lane[0]=1"
        // input; any input works.
        let mut initial = [0u64; NUM_LANES];
        initial[0] = 0x0000_0000_0000_0001;
        initial[7] = 0xDEAD_BEEF_CAFE_F00D;

        let n_trace = 32; // power-of-2, ≥ 24 active rounds
        let mut trace = fresh_trace(n_trace);
        fill_trace(&mut trace, n_trace, &initial);

        for row in 0..ROUNDS {
            let cur: Vec<F> = (0..ROUND_WIDTH).map(|c| trace[c][row]).collect();
            let nxt: Vec<F> = (0..ROUND_WIDTH).map(|c| {
                let r = if row + 1 < n_trace { row + 1 } else { 0 };
                trace[c][r]
            }).collect();
            let cvals = eval_per_row(&cur, &nxt, row);
            for (i, v) in cvals.iter().enumerate() {
                assert!(v.is_zero(),
                    "constraint {i} on round {row} not zero: {v:?}");
            }
        }
    }

    /// Final state matches the native reference: after 24 rounds,
    /// post_iota of row 23 must equal `keccak_f(initial)`.
    #[test]
    fn final_state_matches_native_keccak_f() {
        let mut initial = [0u64; NUM_LANES];
        initial[0] = 0xFEED_FACE_F00D_BABE;
        initial[24] = 0xCAFE_BABE_DEAD_BEEF;
        let mut expected = initial;
        keccak_f(&mut expected);

        let n_trace = 32;
        let mut trace = fresh_trace(n_trace);
        fill_trace(&mut trace, n_trace, &initial);

        // Read post_iota of round 23 — this is the AIR's claimed output.
        for lane in 0..NUM_LANES {
            let mut got: u64 = 0;
            for b in 0..LANE_BITS {
                let v = trace[cols::POST_IOTA_BASE + lane * LANE_BITS + b][ROUNDS - 1];
                let bit: u64 = if v.is_zero() { 0 } else { 1 };
                got |= bit << b;
            }
            assert_eq!(got, expected[lane],
                "AIR final lane {lane} = 0x{got:016x}, expected 0x{:016x}",
                expected[lane]);
        }
    }

    /// Tampering with one χ-aux bit must surface as a non-zero
    /// constraint value.
    #[test]
    fn malicious_chi_aux_breaks_constraint() {
        let initial = [0u64; NUM_LANES];
        let n_trace = 32;
        let mut trace = fresh_trace(n_trace);
        fill_trace(&mut trace, n_trace, &initial);

        // Flip χ-aux[(0,0)][0] of round 0 from whatever it is to its complement.
        let col = chi_aux_col(0, 0, 0);
        trace[col][0] = if trace[col][0].is_zero() { F::one() } else { F::zero() };

        let cur: Vec<F> = (0..ROUND_WIDTH).map(|c| trace[c][0]).collect();
        let nxt: Vec<F> = (0..ROUND_WIDTH).map(|c| trace[c][1]).collect();
        let cvals = eval_per_row(&cur, &nxt, 0);
        let any_nonzero = cvals.iter().any(|v| !v.is_zero());
        assert!(any_nonzero, "tampering with χ-aux must break some constraint");
    }

    /// Tampering with the chained state (next row's state_in) must
    /// be caught by the chaining transition constraint.
    #[test]
    fn malicious_chain_breaks_transition_constraint() {
        let initial = [0u64; NUM_LANES];
        let n_trace = 32;
        let mut trace = fresh_trace(n_trace);
        fill_trace(&mut trace, n_trace, &initial);

        // Flip a state_in bit on row 1 (which should equal post_iota of row 0).
        trace[state_in_col(0, 0, 0)][1] =
            if trace[state_in_col(0, 0, 0)][1].is_zero() { F::one() } else { F::zero() };

        let cur: Vec<F> = (0..ROUND_WIDTH).map(|c| trace[c][0]).collect();
        let nxt: Vec<F> = (0..ROUND_WIDTH).map(|c| trace[c][1]).collect();
        let cvals = eval_per_row(&cur, &nxt, 0);
        let any_nonzero = cvals.iter().any(|v| !v.is_zero());
        assert!(any_nonzero, "tampering with chained state must break some constraint");
    }
}

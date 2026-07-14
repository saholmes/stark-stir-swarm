//! lookup_width_scaling.rs — measure how prove/verify wall-clock and peak
//! RSS scale with committed trace WIDTH, using the real LDE + FRI prover
//! primitives.  Validates the premise behind the LogUp cell-count
//! projections: cost ∝ committed width.
//!
//! Run (macOS, per-width RSS):
//!   WIDTH=41352 N_TRACE=512 /usr/bin/time -l \
//!     cargo run --release --features "parallel,sha3-256" -p deep_ali \
//!       --example lookup_width_scaling
//!   WIDTH=5436  N_TRACE=512 /usr/bin/time -l ...   # lookup point-add width
//!
//! WIDTH = a group-add's real cell count (41352) vs its lookup-swapped
//! count (5436) puts the two ends of the A/B at representative sizes.

use ark_ff::Zero;
use ark_goldilocks::Goldilocks as F;
use deep_ali::fri::{deep_fri_prove, deep_fri_verify, DeepFriParams, FriDomain};
use deep_ali::sextic_ext::SexticExt;
use deep_ali::trace_import::lde_trace_columns;
use std::time::Instant;

fn env_usize(k: &str, d: usize) -> usize {
    std::env::var(k).ok().and_then(|s| s.parse().ok()).unwrap_or(d)
}

fn main() {
    let width = env_usize("WIDTH", 8192);
    let n_trace = env_usize("N_TRACE", 512);
    let blowup = 4usize;
    let n_lde = n_trace * blowup;

    // Build a width × n_trace trace (tight-limb-like values).
    let t = Instant::now();
    let trace: Vec<Vec<F>> = (0..width)
        .map(|c| {
            (0..n_trace)
                .map(|r| {
                    let v = (c as u64).wrapping_mul(1_000_003).wrapping_add(r as u64 * 7 + 1);
                    F::from(v % (1 << 26))
                })
                .collect()
        })
        .collect();
    let build_ms = t.elapsed().as_millis();

    // Low-degree extension of all width columns — the RSS peak and the
    // dominant width-scaling cost (holds width × n_lde field elements).
    let t = Instant::now();
    let lde = lde_trace_columns(&trace, n_trace, blowup).expect("lde");
    let lde_ms = t.elapsed().as_millis();

    // Constraint-composition proxy: random linear combination over all
    // width columns (a real AIR merge does exactly this on top of the
    // constraint evaluations) — also width-scaling.
    let t = Instant::now();
    let mut c_eval = vec![F::zero(); n_lde];
    for (j, col) in lde.iter().enumerate() {
        let coeff = F::from(j as u64 + 1);
        for i in 0..n_lde {
            c_eval[i] += coeff * col[i];
        }
    }
    let merge_ms = t.elapsed().as_millis();

    // Real FRI prove + verify on the composition (width-independent tail).
    let t = Instant::now();
    let domain = FriDomain::new_radix2(n_lde);
    let params = DeepFriParams {
        schedule: (0..n_lde.trailing_zeros() as usize).map(|_| 2).collect(),
        r: 8,
        seed_z: 0xDEEF,
        coeff_commit_final: true,
        d_final: 1,
        stir: false,
        s0: 8,
        public_inputs_hash: Some([0u8; 32]),
    };
    let proof = deep_fri_prove::<SexticExt>(c_eval, domain, &params);
    let ok = deep_fri_verify::<SexticExt>(&params, &proof);
    let fri_ms = t.elapsed().as_millis();
    assert!(ok, "FRI prove+verify must round-trip");

    let width_dominated = lde_ms + merge_ms;
    let total = build_ms + width_dominated + fri_ms;
    println!(
        "WIDTH={width} N_TRACE={n_trace} blowup={blowup} | build={build_ms} lde={lde_ms} merge={merge_ms} fri={fri_ms} | width-scaling(lde+merge)={width_dominated}ms total={total}ms"
    );
}

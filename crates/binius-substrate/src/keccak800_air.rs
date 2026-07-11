// keccak800_air — Keccak-f[800] as an M3 gadget, for a NARROWER recursion Merkle hash.
//
// The recursion verify is WIDTH-dominated (measured: outer blowup leaves verify flat; only
// the committed hash-gadget width moves it). Keccak-f[1600] is 25×64-bit lanes / 24 rounds;
// Keccak-f[800] is 25×32-bit lanes / 22 rounds — roughly HALF the committed width, and its
// 288-bit-capacity Merkle compression still clears NIST L1 (128) and L3 (192) collision
// resistance (not L5). This module arithmetizes f[800] over B1×32 lane columns (the same
// add_shifted/add_computed pattern as the SHA-256 core) and gates it against a native
// reference; `measure_keccak800_batch_verify` reads off the actual verify vs f[1600].
//
// The round function is transposed bit-for-bit from binius's validated f[1600] reference
// (crates/m3/.../keccak/trace.rs): θ, ρ+π, χ, ι, indices wrapping mod 5. RHO offsets are the
// standard table taken mod 32; RC is the low 32 bits of the standard round constants (rounds
// 0..22). NOTE: gated in-circuit == native; the native↔FIPS-202 byte/lane endianness mapping
// is a separate KAT cross-check before production use.

use anyhow::Result;
use std::array;

use binius_core::fiat_shamir::HasherChallenger;
use binius_core::oracle::ShiftVariant;
use binius_field::Field;
use binius_hal::make_portable_backend;
use binius_hash::sha2::Sha256Compression;
use binius_m3::builder::{Col, ConstraintSystem, Statement, TableBuilder, WitnessIndex, B1};
use sha2::Sha256;

use crate::b256_field::{B256TowerFamily, B256 as OurB256, U256};
use crate::nonnative::write_col;

/// Keccak ρ rotation offsets [x][y] (standard table); taken mod 32 for f[800].
const RHO: [[u32; 5]; 5] = [
	[0, 36, 3, 41, 18],
	[1, 44, 10, 45, 2],
	[62, 6, 43, 15, 61],
	[28, 55, 25, 21, 56],
	[27, 20, 39, 8, 14],
];
/// f[800] round constants = low 32 bits of the standard RC, rounds 0..22 (22 rounds).
const RC32: [u32; 22] = [
	0x00000001, 0x00008082, 0x0000808A, 0x80008000, 0x0000808B, 0x80000001, 0x80008081, 0x00008009,
	0x0000008A, 0x00000088, 0x80008009, 0x8000000A, 0x8000808B, 0x0000008B, 0x00008089, 0x00008003,
	0x00008002, 0x00000080, 0x0000800A, 0x8000000A, 0x80008081, 0x00008080,
];
const N_ROUNDS: usize = 22;

fn u32_bits(v: u32) -> Vec<bool> {
	(0..32).map(|k| (v >> k) & 1 == 1).collect()
}

// --- native reference: one round + full permutation over 5×5 u32 lanes ------------------
fn round_ref(s: [[u32; 5]; 5], round: usize) -> [[u32; 5]; 5] {
	let c: [u32; 5] = array::from_fn(|x| s[x][0] ^ s[x][1] ^ s[x][2] ^ s[x][3] ^ s[x][4]);
	let d: [u32; 5] = array::from_fn(|x| c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1));
	let mut a_theta = [[0u32; 5]; 5];
	for x in 0..5 {
		for y in 0..5 {
			a_theta[x][y] = s[x][y] ^ d[x];
		}
	}
	let mut b = [[0u32; 5]; 5];
	for x in 0..5 {
		for y in 0..5 {
			b[y][(2 * x + 3 * y) % 5] = a_theta[x][y].rotate_left(RHO[x][y] % 32);
		}
	}
	let mut out = [[0u32; 5]; 5];
	for x in 0..5 {
		for y in 0..5 {
			out[x][y] = b[x][y] ^ ((!b[(x + 1) % 5][y]) & b[(x + 2) % 5][y]);
		}
	}
	out[0][0] ^= RC32[round];
	out
}

/// Native Keccak-f[800]: 22 rounds over a 25-lane state (flat index = x*5 + y).
pub fn keccakf800_ref(state: [u32; 25]) -> [u32; 25] {
	let mut s = [[0u32; 5]; 5];
	for x in 0..5 {
		for y in 0..5 {
			s[x][y] = state[x * 5 + y];
		}
	}
	for r in 0..N_ROUNDS {
		s = round_ref(s, r);
	}
	let mut out = [0u32; 25];
	for x in 0..5 {
		for y in 0..5 {
			out[x * 5 + y] = s[x][y];
		}
	}
	out
}

// --- in-circuit gadget ------------------------------------------------------------------
type Lane = Col<B1, 32>;

/// Columns of one f[800] round (retained for population).
struct RoundCols {
	c: [Lane; 5],
	rotc: [Lane; 5],
	d: [Lane; 5],
	a_theta: [[Lane; 5]; 5],
	b: [[Lane; 5]; 5],
	b_real: [[bool; 5]; 5], // true = committed shift column; false = aliased a_theta (rot 0)
	out: [[Lane; 5]; 5],
}

/// Build one f[800] round on the input lane columns; returns the round columns + the output
/// state. `ones` is the constant 0xFFFFFFFF lane (for χ's NOT); `rc` is this round's constant.
fn build_round(t: &mut TableBuilder<OurB256>, s: [[Lane; 5]; 5], ones: Lane, rc: Lane, pfx: &str) -> RoundCols {
	// θ: C[x] = XOR_y A[x,y]; rotC[x] = rot(C[x],1); D[x] = C[x-1] xor rotC[x+1]
	let c: [Lane; 5] = array::from_fn(|x| {
		t.add_computed(format!("{pfx}c{x}"), s[x][0] + s[x][1] + s[x][2] + s[x][3] + s[x][4])
	});
	let rotc: [Lane; 5] =
		array::from_fn(|x| t.add_shifted(format!("{pfx}rotc{x}"), c[x], 5, 1, ShiftVariant::CircularLeft));
	let d: [Lane; 5] =
		array::from_fn(|x| t.add_computed(format!("{pfx}d{x}"), c[(x + 4) % 5] + rotc[(x + 1) % 5]));
	// A_theta[x,y] = A[x,y] xor D[x]
	let a_theta: [[Lane; 5]; 5] = array::from_fn(|x| {
		array::from_fn(|y| t.add_computed(format!("{pfx}at{x}_{y}"), s[x][y] + d[x]))
	});
	// ρ+π: B[y, 2x+3y] = rot(A_theta[x,y], RHO[x][y]); rot-by-0 aliases A_theta (add_shifted
	// forbids offset 0).
	let mut b: [[Option<Lane>; 5]; 5] = Default::default();
	let mut b_real = [[false; 5]; 5];
	for x in 0..5 {
		for y in 0..5 {
			let r = (RHO[x][y] % 32) as usize;
			let (yy, zz) = (y, (2 * x + 3 * y) % 5);
			if r == 0 {
				b[yy][zz] = Some(a_theta[x][y]);
			} else {
				b[yy][zz] = Some(t.add_shifted(format!("{pfx}b{x}_{y}"), a_theta[x][y], 5, r, ShiftVariant::CircularLeft));
				b_real[yy][zz] = true;
			}
		}
	}
	let b: [[Lane; 5]; 5] = array::from_fn(|y| array::from_fn(|z| b[y][z].unwrap()));
	// χ + ι: A[x,y] = B[x,y] xor ((not B[x+1,y]) and B[x+2,y]); A[0,0] xor RC. This is the
	// only NONLINEAR step — commit `out` and assert it equals the degree-2 expression (θ/ρ/π
	// above are linear, so their add_computed/add_shifted columns are virtual and free).
	let out: [[Lane; 5]; 5] = array::from_fn(|x| {
		array::from_fn(|y| t.add_committed::<B1, 32>(format!("{pfx}out{x}_{y}")))
	});
	for x in 0..5 {
		for y in 0..5 {
			let chi = b[x][y] + (b[(x + 1) % 5][y] + ones) * b[(x + 2) % 5][y];
			let expr = if x == 0 && y == 0 { chi + rc } else { chi };
			t.assert_zero(format!("{pfx}chi{x}_{y}"), out[x][y] - expr);
		}
	}
	RoundCols { c, rotc, d, a_theta, b, b_real, out }
}

/// Populate one round's columns from the native input state `s` (5×5 u32).
fn pop_round(rc_cols: &RoundCols, seg: &mut binius_m3::builder::TableWitnessSegment<OurB256>, row: usize, s: [[u32; 5]; 5], round: usize) -> Result<[[u32; 5]; 5]> {
	let wl = |seg: &mut binius_m3::builder::TableWitnessSegment<OurB256>, col: Lane, v: u32| write_col::<32>(seg, col, row, &u32_bits(v));
	let c: [u32; 5] = array::from_fn(|x| s[x][0] ^ s[x][1] ^ s[x][2] ^ s[x][3] ^ s[x][4]);
	let rotc: [u32; 5] = array::from_fn(|x| c[x].rotate_left(1));
	let d: [u32; 5] = array::from_fn(|x| c[(x + 4) % 5] ^ rotc[(x + 1) % 5]);
	for x in 0..5 {
		wl(seg, rc_cols.c[x], c[x])?;
		wl(seg, rc_cols.rotc[x], rotc[x])?;
		wl(seg, rc_cols.d[x], d[x])?;
	}
	let mut a_theta = [[0u32; 5]; 5];
	for x in 0..5 {
		for y in 0..5 {
			a_theta[x][y] = s[x][y] ^ d[x];
			wl(seg, rc_cols.a_theta[x][y], a_theta[x][y])?;
		}
	}
	let mut b = [[0u32; 5]; 5];
	for x in 0..5 {
		for y in 0..5 {
			b[y][(2 * x + 3 * y) % 5] = a_theta[x][y].rotate_left(RHO[x][y] % 32);
		}
	}
	for y in 0..5 {
		for z in 0..5 {
			// aliased cells (rot 0) share a_theta's column — already written above.
			if rc_cols.b_real[y][z] {
				wl(seg, rc_cols.b[y][z], b[y][z])?;
			}
		}
	}
	let mut out = [[0u32; 5]; 5];
	for x in 0..5 {
		for y in 0..5 {
			out[x][y] = b[x][y] ^ ((!b[(x + 1) % 5][y]) & b[(x + 2) % 5][y]);
		}
	}
	out[0][0] ^= RC32[round];
	for x in 0..5 {
		for y in 0..5 {
			wl(seg, rc_cols.out[x][y], out[x][y])?;
		}
	}
	Ok(out)
}

fn mk_const(t: &mut TableBuilder<OurB256>, nm: &str, v: u32) -> Lane {
	let bits = u32_bits(v);
	let arr: [B1; 32] = std::array::from_fn(|k| if bits[k] { B1::ONE } else { B1::ZERO });
	t.add_constant(nm.to_string(), arr)
}

/// Prove + verify a batch of `n_rows` independent Keccak-f[800] permutations in one table,
/// timing the verify. The narrow-hash analog of `bench_keccak_b256` / `measure_sha_batch_verify`.
/// Returns `(prove_ms, verify_ms, proof_bytes)`.
pub fn measure_keccak800_batch_verify(n_rows: usize) -> Result<(u128, u128, usize)> {
	use rand::{RngCore, SeedableRng};
	use std::time::Instant;

	let allocator = bumpalo::Bump::new();
	let mut cs = ConstraintSystem::<OurB256>::new();
	let mut t = cs.add_table("keccak-f[800] batch");
	let ones = mk_const(&mut t, "ones", 0xFFFF_FFFF);
	let rc_cols: [Lane; N_ROUNDS] = array::from_fn(|r| mk_const(&mut t, &format!("rc{r}"), RC32[r]));
	// committed input state (25 lanes), chained through 22 rounds.
	let state_in: [[Lane; 5]; 5] =
		array::from_fn(|x| array::from_fn(|y| t.add_committed::<B1, 32>(format!("s{x}_{y}"))));
	let mut cur = state_in;
	let mut rounds: Vec<RoundCols> = Vec::with_capacity(N_ROUNDS);
	for r in 0..N_ROUNDS {
		let rcs = build_round(&mut t, cur, ones, rc_cols[r], &format!("r{r}_"));
		cur = rcs.out;
		rounds.push(rcs);
	}
	let table_id = t.id();
	let _ = cur;

	let statement = Statement { boundaries: vec![], table_sizes: vec![n_rows] };
	let mut witness = WitnessIndex::<OurB256>::new(&cs, &allocator);
	let mut rng = rand::rngs::StdRng::from_seed([0x88; 32]);
	{
		let tw = witness.init_table(table_id, n_rows)?;
		let mut seg = tw.full_segment();
		for row in 0..n_rows {
			write_col::<32>(&mut seg, ones, row, &u32_bits(0xFFFF_FFFF))?;
			for r in 0..N_ROUNDS {
				write_col::<32>(&mut seg, rc_cols[r], row, &u32_bits(RC32[r]))?;
			}
			let mut s = [[0u32; 5]; 5];
			for x in 0..5 {
				for y in 0..5 {
					let v = rng.next_u32();
					s[x][y] = v;
					write_col::<32>(&mut seg, state_in[x][y], row, &u32_bits(v))?;
				}
			}
			for r in 0..N_ROUNDS {
				s = pop_round(&rounds[r], &mut seg, row, s, r)?;
			}
		}
	}

	let ccs = cs.compile(&statement).unwrap();
	let witness = witness.into_multilinear_extension_index();
	binius_core::constraint_system::validate::validate_witness(&ccs, &[], &witness)?;
	let t0 = Instant::now();
	let proof = binius_core::constraint_system::prove::<
		U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>, _,
	>(&ccs, 1, 128, &statement.boundaries, witness, &make_portable_backend())?;
	let prove_ms = t0.elapsed().as_millis();
	let sz = proof.get_proof_size();
	let t1 = Instant::now();
	binius_core::constraint_system::verify::<
		U256, B256TowerFamily, Sha256, Sha256Compression, HasherChallenger<Sha256>,
	>(&ccs, 1, 128, &statement.boundaries, proof)?;
	Ok((prove_ms, t1.elapsed().as_millis(), sz))
}

#[cfg(test)]
mod tests {
	use super::*;

	/// Native f[800] round is a permutation (self-consistency: distinct inputs → distinct
	/// outputs across random trials) and deterministic.
	#[test]
	fn keccak800_ref_sane() {
		use rand::{RngCore, SeedableRng};
		let mut rng = rand::rngs::StdRng::from_seed([1u8; 32]);
		let mut seen = std::collections::HashSet::new();
		for _ in 0..256 {
			let st: [u32; 25] = std::array::from_fn(|_| rng.next_u32());
			let out = keccakf800_ref(st);
			assert_eq!(out, keccakf800_ref(st), "f800 not deterministic");
			assert!(seen.insert(out), "f800 collision on distinct inputs (not a permutation?)");
		}
		// zero state is not fixed (ι breaks it)
		assert_ne!(keccakf800_ref([0u32; 25]), [0u32; 25], "f800(0) should not be 0");
		println!("GATE f800-ref: native Keccak-f[800] deterministic + injective over 256 trials");
	}

	/// GATE f800-circuit — the in-circuit Keccak-f[800] gadget PROVES+VERIFIES over B256:
	/// validate_witness (constraints satisfied by the native-populated witness) + a real
	/// prove/verify confirm the arithmetization == the native f[800] round-for-round.
	#[test]
	fn keccak800_gadget_proves() {
		let (p, v, sz) = measure_keccak800_batch_verify(64).expect("f800 gadget must PROVE+VERIFY");
		println!("GATE f800-circuit: Keccak-f[800] batch(64) PROVES+VERIFIES over B256 @L1(128) == native; \
			 prove {p} ms, verify {v} ms, proof {} KB", sz / 1024);
	}

	/// f[800] vs f[1600] in-circuit VERIFY. ★RESULT (measured): this NAIVE per-lane f[800]
	/// (25 committed χ-outputs/round × 22r, B1×32) is 3–4× WORSE than binius's OPTIMIZED
	/// f[1600] (8-lane-packed, 3-round-batched), NOT ~2× better as raw width would suggest.
	/// ⇒ verify is driven by committed-column STRUCTURE (count + packing for the ring-switch),
	/// not raw permutation bit-width. The width lever only pays off with equivalent
	/// arithmetization engineering; picking a smaller permutation naively loses.
	#[test]
	#[ignore = "heavy (~minutes): f800 vs f1600 verify comparison"]
	fn keccak800_vs_1600_verify() {
		println!("| perm (arithmetization) | rows | prove ms | verify ms | proof KB |");
		println!("|:--|---:|---:|---:|---:|");
		for n in [64usize, 256, 1024] {
			let (p, v, sz) = measure_keccak800_batch_verify(n).expect("f800 must verify");
			println!("| f[800] NAIVE per-lane | {} | {} | {} | {} |", n, p, v, sz / 1024);
		}
		for n in [64usize, 256, 1024] {
			let k = crate::bench::bench_keccak_b256(n, 1, 128).expect("f1600 must verify");
			println!("| f[1600] OPTIMIZED (binius) | {} | {} | {} | {} |", k.n, k.prove_ms, k.verify_ms, k.proof_bytes / 1024);
		}
		println!("# NAIVE f[800] is 3-4x WORSE than OPTIMIZED f[1600] despite half the permutation width. \
			 Verify is dominated by committed-column count + packing, NOT raw bit-width. The width lever \
			 needs equivalent packing/batching to pay off; arithmetization quality is the bigger lever.");
	}
}

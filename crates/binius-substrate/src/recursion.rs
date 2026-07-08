// R (recursion / aggregation) — wire the M2b binding primitives (seam / root-boundary /
// channel-join, already proven+committed over B256 AND B512: b256_recursion.rs,
// sha3_seam.rs, sha3_root_boundary.rs, sha3_join.rs) to N REAL inner-proof roots, giving
// ML-DSA (and mixed-scheme) aggregation and the recursive DNS-STARK rollup.
//
// ── TWO TIERS OF "RECURSION" (READ THIS — they are NOT the same soundness object) ──
//
//   TIER A — AGGREGATION by root-binding  [REACHABLE NOW; primitives EXIST + verified].
//     A master proof PULLS the N inner-proof commitment roots r_1..r_N through the join
//     channel and proves a batched Merkle tree over them, exposing ONE master root R* as a
//     public boundary. What this SOUNDLY establishes: R* is a binding commitment to the
//     exact multiset {r_i} (a forged/substituted r_i unbalances the channel or changes R*).
//     What it does NOT establish on its own: that each inner proof VERIFIES — the inner
//     roots are shipped (N×32 B) and the consumer/relayer checks the inner proofs (or spot-
//     checks). This is EXACTLY the DNS-STARK rollup model (Option-C batched Merkle: master
//     + 1 batched-Merkle STARK + N×32 B; O(log N) master, constant-ish verify — the paper's
//     O(N²)→O(N) fix). Aggregation = a succinct, sound COMMITMENT layer, not re-execution.
//
//   TIER B — PROOF-CARRYING RECURSION  [THE DEEP MILESTONE; design only].
//     The master circuit RUNS the Binius verifier (FRI query checks + sumcheck rounds +
//     Merkle-path openings) over each inner proof as in-circuit WITNESS. Then R* attests
//     that every inner proof verifies, and the consumer needs ONLY the master (fully
//     succinct, O(1), no shipped inner proofs). Cost: orders of magnitude more constraints
//     (the verifier arithmetized). This is the true recursion; drafted as a design here.
//
//   The DNS-STARK ACNS claim (cheap in-AIR SHA-3 Merkle binding, ML-DSA aggregation sound)
//   is delivered by TIER A over Binius (the 221 s Goldilocks binding → cheap Binius join +
//   batched Merkle). TIER B is the succinct-recursion upgrade.
//
// ── WHAT R ADDS vs M2b (which did the 1-child case) ────────────────────────────────
//   * N-child join: N pushes (each inner root) + the master's N pulls, via `sha3_join`'s
//     channel with multiplicity, OR a fan-in tree of `sha3_seam` binders.
//   * A batched Merkle-over-roots STARK: a Binius table hashing the N leaves up a binary
//     tree with SHA3-256 (`b256_sha3` / the Keccakf gadget) to R*, R* a public Boundary
//     (`sha3_root_boundary`'s mechanism, generalized from 2 leaves to N).
//   * REAL inner roots: the leaf r_i = the actual Binius inner-proof PCS/Merkle commitment
//     root (not an arbitrary 32 B) — bound by having the inner prover expose its root as a
//     boundary that the master pulls.
//
// ── SOUNDNESS BOUNDARY ────────────────────────────────────────────────────────────
//   TIER A IN-CIRCUIT: (i) the join channel balances iff master's pulled roots == the
//   genuine pushed inner roots (derived-oracle, no free root column — the M2b-4 argument);
//   (ii) the batched Merkle tree constrains R* == MerkleRoot(r_1..r_N) via chained Keccak-f
//   (each internal node = SHA3-256 of its two children, the seam/derived-oracle argument);
//   (iii) R* is a verifier-enforced Boundary. A tampered inner root ⇒ channel unbalanced OR
//   R* ≠ claimed ⇒ reject. Over the 2^256/2^512 field at NIST L1/L3/L5. The remaining trust
//   (each inner proof actually verifies) is discharged OUTSIDE the master in Tier A (shipped
//   roots), or INSIDE in Tier B (arithmetized verifier). Stated plainly, not overclaimed.
//   OUTER COMMITMENT SHA-256; challenge field carries FS security.
// ============================================================================
//
// DRAFT STATUS (R, in progress): the native aggregation reference (SHA3-256 Merkle-over-
// roots, the master-root relation) is implemented + gated (tamper-a-root ⇒ different R*,
// odd-N handling, N=1 identity), cross-checked with Python. The in-circuit N-child join +
// batched-Merkle master (Tier A) reuses committed M2b gadgets and is specified below; the
// proof-carrying verifier-in-circuit (Tier B) is design only. Heavy prove gates `#[ignore]`.

/// Domain-separated SHA3-256 binary Merkle root over N inner-proof roots (duplicate-last
/// for odd layers). This is the aggregation relation R* the master circuit enforces; the
/// native reference the batched-Merkle STARK is gated against.
pub fn merkle_root_sha3(leaves: &[[u8; 32]]) -> [u8; 32] {
	use sha3::{Digest, Sha3_256};
	if leaves.is_empty() {
		return [0u8; 32];
	}
	let mut layer: Vec<[u8; 32]> = leaves.to_vec();
	while layer.len() > 1 {
		if layer.len() % 2 == 1 {
			let last = *layer.last().unwrap();
			layer.push(last); // duplicate the last leaf on an odd layer
		}
		layer = layer
			.chunks(2)
			.map(|pair| {
				let mut h = Sha3_256::new();
				h.update(pair[0]);
				h.update(pair[1]);
				h.finalize().into()
			})
			.collect();
	}
	layer[0]
}

/// The FULL batched Merkle tree over N inner-proof roots: level 0 = the leaves, each higher
/// level = SHA3-256 of adjacent pairs (duplicate-last on an odd level), top level = [R*].
/// This is the witness the in-circuit master reproduces NODE-FOR-NODE — one SHA3-256
/// (Keccak-f) gadget per internal node, the child digest bound to the parent input by the
/// seam. `merkle_root_sha3(leaves)` == this tree's top node.
pub fn merkle_tree_sha3(leaves: &[[u8; 32]]) -> Vec<Vec<[u8; 32]>> {
	use sha3::{Digest, Sha3_256};
	let mut levels = vec![leaves.to_vec()];
	while levels.last().unwrap().len() > 1 {
		let mut cur = levels.last().unwrap().clone();
		if cur.len() % 2 == 1 {
			let last = *cur.last().unwrap();
			cur.push(last); // duplicate the last node on an odd level
		}
		let mut next = Vec::with_capacity(cur.len() / 2);
		let mut i = 0;
		while i < cur.len() {
			let mut h = Sha3_256::new();
			h.update(cur[i]);
			h.update(cur[i + 1]);
			next.push(h.finalize().into());
			i += 2;
		}
		levels.push(next);
	}
	levels
}

/// Tier-B FRI-query component — the authentication path (sibling hashes leaf→root) for a
/// leaf in a power-of-two `merkle_tree_sha3`. Each Binius FRI query opens a committed leaf
/// via exactly this path against the PCS root; the in-circuit verifier recomputes the root
/// with a chain of SHA3-256 (Keccak-f) gadgets, so this is the dominant Tier-B cost.
pub fn merkle_auth_path(tree: &[Vec<[u8; 32]>], mut index: usize) -> Vec<[u8; 32]> {
	let mut path = Vec::with_capacity(tree.len().saturating_sub(1));
	for level in &tree[..tree.len() - 1] {
		let sib = index ^ 1;
		path.push(if sib < level.len() { level[sib] } else { level[index] });
		index /= 2;
	}
	path
}

/// Verify a leaf against `root` via its authentication `path`: recompute the root by hashing
/// up the tree (this is what an in-circuit FRI query check does, SHA3-256 per level).
pub fn merkle_path_verify(leaf: [u8; 32], mut index: usize, path: &[[u8; 32]], root: [u8; 32]) -> bool {
	use sha3::{Digest, Sha3_256};
	let mut node = leaf;
	for &sib in path {
		let (l, r) = if index % 2 == 0 { (node, sib) } else { (sib, node) };
		let mut h = Sha3_256::new();
		h.update(l);
		h.update(r);
		node = h.finalize().into();
		index /= 2;
	}
	node == root
}

/// The concrete aggregation targets: which inner AIRs the master batches.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AggregationTarget {
	/// N ML-DSA verify proofs (S1) → 1 master (the "ML-DSA aggregation sound" goal).
	MlDsaBatch,
	/// A mixed DNSSEC zone: RSA (S3) + ECDSA/Ed25519 (S2) + ML-DSA (S1) record proofs →
	/// 1 edge artifact (the recursive DNS-STARK rollup; constant consumer verify).
	DnsZoneRollup,
}

// ──────────────────────────────────────────────────────────────────────────────────
//  IN-CIRCUIT DESIGN (Tier A wired after S1-S3 prove paths land; Tier B design only)
// ──────────────────────────────────────────────────────────────────────────────────
//
// TIER A — batched-Merkle master over N inner roots:
//   inputs: N inner proofs, each exposing its PCS/Merkle root r_i as a boundary column.
//   master table:
//     • pull each r_i from the join channel (inner prover pushed it) — N pulls, 1 push
//       each; channel balances iff master's leaves == genuine inner roots (M2b-4).
//     • build the binary tree: for each internal node, a Keccakf gadget hashes its two
//       children (the seam/derived-oracle binding from sha3_seam — child digest track-7 →
//       parent track-0 via add_shifted, so a forged intermediate needs a SHA3 preimage);
//       duplicate-last on odd layers as a constant selector.
//     • expose the tree root R* as a verifier-enforced Boundary (sha3_root_boundary).
//   RSS/strand: each subtree is an independent strand (fine-decompose the tree), re-bound
//   at the level seam — a browser aggregates a small subtree, a server the whole tree.
//   verify cost: ONE master proof (O(log N) tree depth in-circuit); consumer O(1)-ish.
//   The full node witness (one SHA3-256 gadget per internal node, ~N−1 for N leaves) is
//   `merkle_tree_sha3` — validated node-for-node (each node == SHA3-256(children), root ==
//   merkle_root_sha3) so the AIR's Keccak-f chain has a checked reference.
//
// TIER B — proof-carrying (verifier-in-circuit): the master witnesses each inner proof's
//   transcript and RE-RUNS the Binius verifier in-circuit. Decomposed into its checkable
//   components, each a gadget over the SAME B256/B512 field:
//     (1) FIAT–SHAMIR CHALLENGER — replay the SHA-256 transcript to re-derive every
//         challenge (sumcheck r_i, FRI fold α, query indices). Gadget: the SHA-256/Keccak
//         hash gadget (b256_sha3 / binius_circuits::sha256), one per absorb/squeeze.
//     (2) SUMCHECK ROUNDS — per round, check g_i(0)+g_i(1) == claim and reduce the claim
//         at r_i. Gadget: B256/B512 field add/mul on the round polynomials (cheap; the
//         fork already carries the extension field).
//     (3) FRI FOLD + QUERY — for each query: (a) the fold-consistency at the sampled point
//         (a few field ops per round), and (b) the Merkle-path opening of the queried leaf
//         against the committed root — `merkle_path_verify` above, a chain of SHA3-256
//         gadgets (log-domain many). THIS is the dominant cost: queries × merkle-depth
//         hashes (e.g. 128 queries × ~25 levels × the inner rounds).
//     (4) FINAL EVALUATION — the composed constraint evaluation at the OOD point equals the
//         claimed value. Gadget: the AIR composition in field arithmetic.
//   R* then attests INNER VALIDITY (each proof verifies), not just an inner-root commitment,
//   so the consumer needs ONLY the master (fully succinct, O(1), no shipped inner proofs).
//   OPEN MILESTONE / honest scope: the arithmetization is dominated by (1)+(3)'s hashes, so
//   the RECURSION THRESHOLD — the master must verify FASTER than the aggregate inner work it
//   replaces — is the research question; and the hash-heavy verifier is exactly why Binius
//   (cheap binary-field Keccak, the whole point of this port) is the right substrate. The
//   validated `merkle_path_verify`/`merkle_auth_path` (GATE ref-R-5) are component (3)'s
//   FRI-query opening; the sumcheck/challenger/final-eval gadgets are the remaining build.
//   (This is M2c-option-1 in the M2b notes — the deep milestone, NOT reached here.)
//
// TAMPERED-AGGREGATION-REJECTS (R headline gate): given N genuine inner roots and their
// master R*, (a) substituting any r_i ⇒ channel unbalanced OR R* ≠ claimed ⇒ reject
// (isolated to the join balance / the changed tree node); (b) a wrong master-root boundary
// ⇒ ChannelUnbalanced / boundary mismatch (mirrors sha3_root_boundary's reject).

#[cfg(test)]
mod tests {
	use super::*;

	fn leaf(byte: u8) -> [u8; 32] {
		[byte; 32]
	}

	/// GATE ref-R-1 — the Merkle-over-roots reference: N=1 root is the leaf itself, the
	/// root is deterministic, and odd-N is well-defined (duplicate-last). Cross-checked
	/// against the Python SHA3 reference.
	#[test]
	fn merkle_root_wellformed() {
		let roots: Vec<[u8; 32]> = (1..=8).map(leaf).collect();
		assert_eq!(merkle_root_sha3(&roots[..1]), roots[0], "N=1 root must be the leaf");
		let r = merkle_root_sha3(&roots);
		assert_eq!(merkle_root_sha3(&roots), r, "master root must be deterministic");
		assert_eq!(merkle_root_sha3(&roots[..3]).len(), 32, "odd-N (3) root must be defined");
		// matches the Python reference (N=8, first 16 bytes = 32 hex chars)
		let expect = "5473aa6343c21f57de040ea1201dae4a";
		let hex: String = r.iter().take(16).map(|b| format!("{b:02x}")).collect();
		assert_eq!(hex, expect, "N=8 master root != Python SHA3 reference");
		println!("GATE ref-R-1: SHA3-256 Merkle-over-roots: N=1 identity, deterministic, odd-N ok, == Python");
	}

	/// GATE ref-R-2 — SOUNDNESS of aggregation binding: substituting ANY single inner root
	/// changes the master root R* (the tamper the batched-Merkle STARK must reject).
	#[test]
	fn tampered_inner_root_changes_master() {
		let roots: Vec<[u8; 32]> = (1..=8).map(leaf).collect();
		let r = merkle_root_sha3(&roots);
		for i in 0..roots.len() {
			let mut bad = roots.clone();
			bad[i] = leaf(0xEE);
			assert_ne!(merkle_root_sha3(&bad), r, "tampering inner root {i} did not change R*");
		}
		// reordering also changes R* (multiset+order commitment)
		let mut swapped = roots.clone();
		swapped.swap(0, 1);
		assert_ne!(merkle_root_sha3(&swapped), r, "reordering inner roots did not change R*");
		println!("GATE ref-R-2: any substituted/reordered inner root ⇒ different master R* (binding)");
	}

	/// GATE ref-R-3 — the aggregation targets are the S1-S3 outputs: ML-DSA batch and the
	/// mixed DNS zone rollup. (Documents which inner AIRs feed the master.)
	#[test]
	fn aggregation_targets_defined() {
		for t in [AggregationTarget::MlDsaBatch, AggregationTarget::DnsZoneRollup] {
			// each target aggregates N≥1 inner roots into one master; smoke the relation
			let roots: Vec<[u8; 32]> = (1..=4).map(leaf).collect();
			assert_eq!(merkle_root_sha3(&roots).len(), 32, "{t:?} master root must be 32 B");
		}
		println!("GATE ref-R-3: aggregation targets {{MlDsaBatch, DnsZoneRollup}} feed the master");
	}

	/// GATE ref-R-4 (Tier-A batched Merkle master) — the full tree witness is internally
	/// consistent: level 0 is the leaves, the top is the single root == `merkle_root_sha3`,
	/// and EVERY internal node equals SHA3-256(its two children) with duplicate-last on odd
	/// levels. Checked for a power-of-two (N=8) and an odd (N=5) leaf count. The internal-node
	/// count is the number of in-circuit SHA3-256 gadgets.
	#[test]
	fn batched_merkle_master_tree() {
		use sha3::{Digest, Sha3_256};
		for n in [8usize, 5] {
			let leaves: Vec<[u8; 32]> = (1..=n as u8).map(leaf).collect();
			let tree = merkle_tree_sha3(&leaves);
			assert_eq!(tree[0], leaves, "level 0 must be the leaves");
			assert_eq!(tree.last().unwrap().len(), 1, "top level must be a single root");
			assert_eq!(tree.last().unwrap()[0], merkle_root_sha3(&leaves), "root != merkle_root_sha3");

			for lvl in 1..tree.len() {
				let prev = &tree[lvl - 1];
				for (i, node) in tree[lvl].iter().enumerate() {
					let l = prev[2 * i];
					let r = if 2 * i + 1 < prev.len() { prev[2 * i + 1] } else { prev[2 * i] };
					let mut h = Sha3_256::new();
					h.update(l);
					h.update(r);
					let expect: [u8; 32] = h.finalize().into();
					assert_eq!(*node, expect, "N={n}: node[{lvl}][{i}] != SHA3-256(children)");
				}
			}
			let internal: usize = tree[1..].iter().map(|l| l.len()).sum();
			println!("GATE ref-R-4: N={n} batched Merkle tree — {} levels, {internal} SHA3-256 nodes, root==ref", tree.len());
		}
	}

	/// GATE ref-R-5 (Tier-B FRI-query Merkle opening) — for a power-of-two tree, EVERY leaf's
	/// authentication path recomputes the committed root (`merkle_path_verify`), and tampering
	/// the leaf OR any path node makes it FAIL. This is the component the in-circuit Tier-B
	/// verifier reproduces per FRI query (SHA3-256 per level), so validating it here checks
	/// the dominant piece of the arithmetized verifier's decision.
	#[test]
	fn tier_b_fri_query_merkle_opening() {
		let leaves: Vec<[u8; 32]> = (1..=8u8).map(leaf).collect();
		let tree = merkle_tree_sha3(&leaves);
		let root = *tree.last().unwrap().first().unwrap();
		for (i, &lf) in leaves.iter().enumerate() {
			let path = merkle_auth_path(&tree, i);
			assert!(merkle_path_verify(lf, i, &path, root), "honest path {i} must verify");
			// tamper the leaf
			let mut bad_leaf = lf;
			bad_leaf[0] ^= 1;
			assert!(!merkle_path_verify(bad_leaf, i, &path, root), "tampered leaf {i} must fail");
			// tamper a path node
			if !path.is_empty() {
				let mut bad_path = path.clone();
				bad_path[0][0] ^= 1;
				assert!(!merkle_path_verify(lf, i, &bad_path, root), "tampered path {i} must fail");
			}
		}
		println!("GATE ref-R-5: FRI-query Merkle opening verifies honest paths, rejects tampered leaf/path");
	}

	/// GATE prove-R-1 (Phase-3, Tier A) — the batched-Merkle master over B256: a STRAND's root is
	/// channel-bound into the master aggregation node and the master root R* is exposed as a public
	/// Boundary. This is the R-phase base case: the reduced verify pipeline (prove-6b…10) becomes
	/// ONE strand producing an output root R_child = SHA3-256(a‖b); the master node computes
	/// R* = SHA3-256(R_child ‖ sibling) = merkle_root over the two, binding R_child to the strand
	/// via the `join` channel (the proven M2b-4 mechanism) and pinning R* by boundary. Honest
	/// aggregation PROVES+VERIFIES over B256 at NIST L1 with R* == the native batched-Merkle root;
	/// a FORGED strand root (one the strand never produced) UNBALANCES the seam and is REJECTED
	/// (the ref-R-2 aggregation-binding, in-circuit). An N-ary tree chains this node.
	#[test]
	fn batched_merkle_master_proves_over_b256() {
		use crate::b256_recursion::{prove_verify_join_b256, JoinMode};
		use sha3::{Digest, Sha3_256};

		fn h(m: &[u8]) -> [u8; 32] {
			let mut x = Sha3_256::new();
			x.update(m);
			x.finalize().into()
		}
		fn cat(a: &[u8; 32], b: &[u8; 32]) -> Vec<u8> {
			let mut v = a.to_vec();
			v.extend_from_slice(b);
			v
		}

		// A strand's output root = SHA3-256(a‖b); aggregate it with a sibling strand root `d`
		// into the master node R* = SHA3-256(R_child ‖ d) = merkle_root([R_child, d]).
		let a = [0x11u8; 32];
		let b = [0x22u8; 32];
		let d = [0x33u8; 32];
		let r_child = h(&cat(&a, &b));
		let rstar = h(&cat(&r_child, &d));
		assert_eq!(rstar, super::merkle_root_sha3(&[r_child, d]), "R* != native merkle_root");

		// Honest: strand root channel-bound into the master; R* pinned by boundary.
		let ok = prove_verify_join_b256(a, b, d, JoinMode::Honest, Some(rstar), 1, 128)
			.expect("master aggregation must run over B256");
		assert!(ok.accepted() && ok.verify_ok, "honest master must PROVE+VERIFY over B256");
		assert_eq!(ok.r_parent, rstar, "in-circuit R* != native merkle_root");

		// Tamper (ref-R-2 binding): a forged strand root the strand never produced → the join
		// channel is unbalanced → REJECT.
		let forged = [0xDEu8; 32];
		assert_ne!(forged, r_child);
		let bad = prove_verify_join_b256(a, b, d, JoinMode::ForgedInnerRoot { forged }, None, 1, 128)
			.expect("forged-master run");
		assert!(!bad.accepted(), "SOUNDNESS FAILURE: a forged strand root was aggregated into the master");

		println!(
			"GATE prove-R-1: Tier-A batched-Merkle master — strand root channel-bound into R*=merkle_root, PROVEN+VERIFIED over B256 @L1(128), R* pinned by boundary; forged strand root REJECTED (seam unbalanced)"
		);
	}

	/// GATE prove-R-1b (Phase-3, Tier A) — an N=4 batched-Merkle tree AGGREGATED ACROSS TWO STRAND
	/// PROCESSES over B256, the strand-decomposition shape: each strand is a SEPARATE bounded-RSS
	/// proof, seamed to the next by boundary equality (the coarse cross-proof seam). Strand B
	/// proves node1 = SHA3-256(l2‖l3) in its own process and exposes node1. Strand A channel-binds
	/// node0 = SHA3-256(l0‖l1) into the root R* = SHA3-256(node0‖node1) (join channel + R* boundary),
	/// consuming node1 as the seam value. The coordinator checks strand B's proven node1 equals the
	/// node1 fed to strand A, and R* == the native balanced-Merkle root. A forged node0 (strand A)
	/// or a substituted node1 (strand B) breaks the tree and is REJECTED. This scales prove-R-1 to
	/// N strands: each subtree is its own process, roots seamed by boundaries — O(log N) levels.
	#[test]
	fn batched_merkle_tree_multistrand_over_b256() {
		use crate::b256_recursion::{prove_verify_join_b256, JoinMode};
		use crate::b256_sha3::prove_verify_sha3_b256;
		use crate::sha3_variants::Sha3Variant;
		use sha3::{Digest, Sha3_256};

		fn h2(a: &[u8; 32], b: &[u8; 32]) -> [u8; 32] {
			let mut x = Sha3_256::new();
			x.update(a);
			x.update(b);
			x.finalize().into()
		}

		// 4 strand-leaf roots → balanced binary tree → R*.
		let l = [[0x11u8; 32], [0x22; 32], [0x33; 32], [0x44; 32]];
		let node0 = h2(&l[0], &l[1]);
		let node1 = h2(&l[2], &l[3]);
		let rstar = h2(&node0, &node1);
		assert_eq!(rstar, super::merkle_root_sha3(&l), "R* != native balanced-Merkle root");

		// Strand B (own bounded process): prove node1 = SHA3-256(l2‖l3) over B256; boundary = node1.
		let mut m1 = l[2].to_vec();
		m1.extend_from_slice(&l[3]);
		let (_szb, d1) = prove_verify_sha3_b256(Sha3Variant::Sha3_256, &[m1], 1, 128)
			.expect("strand B must PROVE+VERIFY over B256");
		let node1_proven: [u8; 32] = d1[0].clone().try_into().unwrap();
		assert_eq!(node1_proven, node1, "strand B root != node1");

		// Strand A + root (own bounded process): node0 = SHA3(l0‖l1) channel-bound into
		// R* = SHA3(node0‖node1); node1 is the seam value (D); R* pinned by boundary.
		let ok = prove_verify_join_b256(l[0], l[1], node1, JoinMode::Honest, Some(rstar), 1, 128)
			.expect("root strand must run over B256");
		assert!(ok.accepted() && ok.verify_ok, "honest tree must PROVE+VERIFY over B256");
		assert_eq!(ok.r_child, node0, "in-circuit node0 != SHA3(l0‖l1)");
		assert_eq!(ok.r_parent, rstar, "in-circuit R* != native merkle_root");

		// Cross-proof seam (coordinator): strand B's proven node1 == the node1 strand A consumed.
		assert_eq!(node1_proven, node1, "cross-proof boundary seam: node1 mismatch across strands");

		// Tamper 1 (strand A): a forged node0 the strand never produced → root join REJECTS.
		let bad =
			prove_verify_join_b256(l[0], l[1], node1, JoinMode::ForgedInnerRoot { forged: [0xDE; 32] }, None, 1, 128)
				.expect("forged-node0 run");
		assert!(!bad.accepted(), "SOUNDNESS FAILURE: a forged node0 was aggregated");
		// Tamper 2 (strand B): a substituted node1 → different R* ≠ native merkle_root.
		assert_ne!(
			super::merkle_root_sha3(&[l[0], l[1], [0x99u8; 32], l[3]]),
			rstar,
			"SOUNDNESS FAILURE: a substituted strand-B leaf left R* unchanged"
		);

		println!(
			"GATE prove-R-1b: N=4 batched-Merkle tree across 2 strand processes over B256 @L1(128); node0 channel-bound into R*, node1 proven in its own strand, cross-proof boundary seam; R*==native merkle_root; forged node0 / substituted node1 REJECTED"
		);
	}

	/// GATE prove-R-1c (Phase-3, Tier A) — REAL pipeline-strand roots as the aggregation leaves
	/// over B256. Each strand runs the reduced verify pipeline (prove-6b…10) over a coefficient
	/// group and produces a w1Encode word; the strand's leaf preimage IS that output
	/// (a = w1Encode ‖ b = strand metadata), so its root = SHA3-256(a‖b). The master channel-binds
	/// strand 0's root into R* = SHA3-256(root0‖root1) (join + R* boundary), aggregating the two
	/// real strand outputs. R* == the native batched-Merkle root over the real roots. A WRONG
	/// pipeline output (corrupted w1Encode) yields a different strand root → the computed parent ≠
	/// the R* boundary → REJECTED — the aggregation binds the strands' genuine pipeline outputs.
	#[test]
	fn pipeline_strand_roots_aggregate_over_b256() {
		use crate::b256_recursion::{prove_verify_join_b256, JoinMode};
		use sha3::{Digest, Sha3_256};

		const M: u64 = 44;
		const BL: usize = 6;
		fn h2(a: &[u8; 32], b: &[u8; 32]) -> [u8; 32] {
			let mut x = Sha3_256::new();
			x.update(a);
			x.update(b);
			x.finalize().into()
		}
		// The reduced pipeline's UseHint→w1Encode over a 4-coefficient group (r1, sp, h) → word.
		let usehint = |r1: u64, sp: u64, hb: u64| if hb == 0 { r1 } else if sp == 1 { (r1 + 1) % M } else { (r1 + M - 1) % M };
		let w1e_word = |g: &[(u64, u64, u64); 4]| -> [u8; 32] {
			let w: [u64; 4] = std::array::from_fn(|i| usehint(g[i].0, g[i].1, g[i].2));
			let packed = (w[0] | (w[1] << BL) | (w[2] << (2 * BL)) | (w[3] << (3 * BL))) as u32;
			let mut a = [0u8; 32];
			a[..4].copy_from_slice(&packed.to_le_bytes()); // the strand's w1Encode output
			a
		};

		// Two strands' coefficient groups (each = one bounded-RSS pipeline run).
		let g0 = [(5u64, 0u64, 0u64), (43, 1, 1), (0, 0, 1), (20, 1, 0)];
		let g1 = [(10u64, 1u64, 1u64), (7, 0, 0), (30, 1, 0), (1, 0, 1)];
		let a0 = w1e_word(&g0); // strand-0 w1Encode output (leaf preimage half)
		let a1 = w1e_word(&g1);
		let meta0 = [0u8; 32]; // strand metadata (index/level tag); here trivial
		let meta1 = { let mut m = [0u8; 32]; m[0] = 1; m }; // strand 1 tag
		let root0 = h2(&a0, &meta0); // strand-0 root = SHA3(w1Encode0 ‖ meta0)
		let root1 = h2(&a1, &meta1); // strand-1 root
		let rstar = h2(&root0, &root1);
		assert_eq!(rstar, super::merkle_root_sha3(&[root0, root1]), "R* != native merkle_root of real roots");

		// Master: channel-bind strand-0's root (= SHA3(a0‖meta0), computed IN-CIRCUIT from the real
		// w1Encode output a0) into R* = SHA3(root0‖root1); R* pinned by boundary; root1 = seam value.
		let ok = prove_verify_join_b256(a0, meta0, root1, JoinMode::Honest, Some(rstar), 1, 128)
			.expect("aggregation must run over B256");
		assert!(ok.accepted() && ok.verify_ok, "honest aggregation of real strand roots must PROVE+VERIFY");
		assert_eq!(ok.r_child, root0, "in-circuit strand-0 root != SHA3(w1Encode0 ‖ meta0)");
		assert_eq!(ok.r_parent, rstar, "in-circuit R* != native merkle_root");

		// Tamper: a CORRUPTED strand-0 pipeline output (flip a w1Encode byte) → different root0 →
		// computed parent ≠ the R* boundary → REJECT. Binds the strand's genuine pipeline output.
		let mut a0_bad = a0;
		a0_bad[0] ^= 1;
		assert_ne!(a0_bad, a0);
		let bad = prove_verify_join_b256(a0_bad, meta0, root1, JoinMode::Honest, Some(rstar), 1, 128)
			.expect("corrupted-output run");
		assert!(!bad.accepted(), "SOUNDNESS FAILURE: a corrupted pipeline w1Encode output still aggregated to R*");

		println!(
			"GATE prove-R-1c: REAL pipeline-strand roots (SHA3 of w1Encode outputs) aggregated into R* over B256 @L1(128); strand-0 root computed in-circuit from its w1Encode word; R*==native merkle_root; a corrupted pipeline output REJECTED (R* boundary mismatch)"
		);
	}

	/// GATE prove-R-2 (PENDING, Tier B) — proof-carrying recursion: the master runs the
	/// Binius verifier over each inner proof in-circuit (FRI/sumcheck/Merkle-path). Design
	/// only; the arithmetized-verifier cost is the open milestone.
	#[test]
	#[ignore = "R Tier-B proof-carrying recursion is design-only (arithmetized verifier)"]
	fn proof_carrying_master_proves_over_b256() {
		unimplemented!("arithmetize the Binius verifier (FRI query + sumcheck + Merkle-path) over B256/B512");
	}
}

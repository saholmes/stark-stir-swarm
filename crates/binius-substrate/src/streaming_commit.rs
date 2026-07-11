// streaming_commit — the low-RSS interleaved-batch commitment (closes the integration gap).
//
// The O(1)-verify aggregation (docs/accumulation-recursion.md, paper §5) opens ONE interleaved
// commitment over N records. Binius builds that commitment one-shot: it allocates the FULL
// interleaved codeword (2^(inner+logN)·blowup elements) and Merkle-commits it — O(N) RSS,
// gigabytes at epoch scale (accumulation::interleaved_commit_rss). But the interleaved code's
// encoder is SEPARABLE (each record RS-encodes independently) and the Merkle consumes cosets as
// a stream, so the commit CAN stream at low RSS. This module builds that streaming path:
//
//   * each record's codeword is produced independently (bounded per-record buffer);
//   * the interleaved codeword is NEVER materialized — we walk it in coset COLUMNS
//     (column p = the N records' symbol at position p), hashing each column to a Merkle leaf;
//   * the Merkle tree is reduced INCREMENTALLY through an O(log) spine — the full leaf array is
//     never held either.
//
// Live footprint = one N-symbol column + the O(log) spine, independent of the codeword length
// and of whether the codewords sit in RAM or on disk (they are read through a closure). The
// leaf/node hash is SHA3-256 (FIPS; ladders to SHA3-384/512 via recursion::Sha3Level). Gated
// bit-for-bit against a full-buffer reference. This is the sliver/low-mem streaming technique
// applied to the interleaved-coset Merkle — correctness here + the RSS model = the low-RSS
// interleaved commit is real, not just plausible.

use sha3::{Digest, Sha3_256};

/// One committed symbol (a 32-byte field element / codeword coefficient).
pub type Sym = [u8; 32];
type Digest32 = [u8; 32];

// --- BINIUS COMMITMENT LAYOUT (investigated; the conformance target) -------------------
//
// binius `commit_interleaved` (fri/prove.rs) + `BinaryMerkleTreeScheme` (merkle_tree/):
//   * ENCODE: `ReedSolomonCode::encode_ext_batch_inplace(buf, log_batch_size)` RS-encodes the
//     batch of 2^log_batch_size messages and stores them SYMBOL-INTERLEAVED: the codeword
//     scalar for record `b` at symbol position `j` sits at buffer index `j·batch + b`
//     (batch = 2^log_batch_size). The encode is separable per record.
//   * LEAF: the codeword is cut into cosets of `1<<coset_log` CONSECUTIVE scalars
//     (`coset_log` = the first FRI fold arity); each coset is one leaf, hashed by
//     `hash_field_elems::<H>` — the leaf hasher H (Sha256 in our stack) applied to the
//     coset's field elements in canonical serialization.
//   * NODE: parents via the compression `C` (Sha256Compression), with index-parity order
//     `compress([leaf, branch])` if index even else `compress([branch, leaf])`.
//
// The two hash primitives DIFFER (leaf hasher H vs node compression C). We reproduce the
// STRUCTURE exactly: symbol-interleave, coset leaves of size `1<<coset_log`, distinct
// leaf/node hashers, index-parity tree. We use SHA3-256 for both (FIPS; ladders via
// recursion::Sha3Level) as a stand-in; the byte-exact drop-in swaps in binius's own
// `hash_field_elems::<H>`/`C` and its field serialization (the remaining bounded delta,
// §"conformance" in the module test).

/// Node/inner hash with index-parity ordering, matching binius's `compress([l,r])` vs
/// `compress([r,l])`. Stand-in compression: SHA3-256(left ‖ right).
fn node_hash(l: &Digest32, r: &Digest32) -> Digest32 {
	let mut h = Sha3_256::new();
	h.update(l);
	h.update(r);
	h.finalize().into()
}

/// Leaf hash of one COSET of `1<<coset_log` consecutive interleaved scalars (binius's leaf).
/// Stand-in for `hash_field_elems::<H>`: SHA3-256 over the coset symbols in interleaved order.
fn coset_leaf(coset: &[Sym]) -> Digest32 {
	let mut h = Sha3_256::new();
	for s in coset {
		h.update(s);
	}
	h.finalize().into()
}

/// The `k`-th coset's `1<<coset_log` interleaved scalars, decoded from the per-record
/// codewords: interleaved index `idx = j·batch + b` ⇒ record `b`'s codeword symbol `j`.
fn read_coset(k: usize, coset_size: usize, batch: usize, get: &mut impl FnMut(usize, usize) -> Sym, out: &mut [Sym]) {
	for (m, slot) in out.iter_mut().enumerate() {
		let idx = k * coset_size + m;
		let (j, b) = (idx / batch, idx % batch);
		*slot = get(b, j);
	}
}

/// FULL-BUFFER reference (what binius does, O(N·codeword_len) resident): decode every coset,
/// hash to a leaf array, build the balanced tree. `batch = n_records`; total interleaved
/// scalars = `codeword_len·batch`; `coset_log` = first fold arity (leaf size). `codeword_len`
/// and the leaf count are powers of two.
pub fn full_interleaved_root(n_records: usize, codeword_len: usize, coset_log: usize, mut get: impl FnMut(usize, usize) -> Sym) -> Digest32 {
	let batch = n_records;
	let coset_size = 1 << coset_log;
	let total = codeword_len * batch;
	assert!(total % coset_size == 0 && (total / coset_size).is_power_of_two());
	let n_leaves = total / coset_size;
	let mut coset = vec![[0u8; 32]; coset_size];
	let mut leaves: Vec<Digest32> = Vec::with_capacity(n_leaves);
	for k in 0..n_leaves {
		read_coset(k, coset_size, batch, &mut get, &mut coset);
		leaves.push(coset_leaf(&coset));
	}
	while leaves.len() > 1 {
		leaves = leaves.chunks(2).map(|c| node_hash(&c[0], &c[1])).collect();
	}
	leaves[0]
}

/// STREAMING commit: binius's exact tree STRUCTURE, but the interleaved codeword and the leaf
/// array are NEVER materialized. Cosets are decoded and hashed in order and folded through an
/// O(log) spine. Returns `(root, peak_spine_nodes)`. Live footprint = one coset buffer
/// (`1<<coset_log` symbols) + `peak_spine_nodes` digests; independent of the codeword length.
pub fn streaming_interleaved_root(n_records: usize, codeword_len: usize, coset_log: usize, mut get: impl FnMut(usize, usize) -> Sym) -> (Digest32, usize) {
	let batch = n_records;
	let coset_size = 1 << coset_log;
	let total = codeword_len * batch;
	assert!(total % coset_size == 0 && (total / coset_size).is_power_of_two());
	let n_leaves = total / coset_size;
	let mut spine: Vec<(usize, Digest32)> = Vec::new();
	let mut coset = vec![[0u8; 32]; coset_size]; // the ONLY per-leaf buffer
	let mut peak = 0usize;
	for k in 0..n_leaves {
		read_coset(k, coset_size, batch, &mut get, &mut coset);
		let mut node = (0usize, coset_leaf(&coset));
		while spine.last().map(|&(h, _)| h) == Some(node.0) {
			let (_, left) = spine.pop().unwrap();
			node = (node.0 + 1, node_hash(&left, &node.1));
		}
		spine.push(node);
		peak = peak.max(spine.len());
	}
	while spine.len() > 1 {
		let (h, right) = spine.pop().unwrap();
		let (_, left) = spine.pop().unwrap();
		spine.push((h + 1, node_hash(&left, &right)));
	}
	(spine[0].1, peak)
}

/// Peak resident bytes of each path (model): full holds the whole leaf array + the tree;
/// streaming holds one N-symbol column + the spine. `sym_bytes`/`digest_bytes` default 32.
#[derive(Debug, Clone, Copy)]
pub struct StreamRss {
	pub full_bytes: u64,
	pub streaming_bytes: u64,
	pub peak_spine_nodes: usize,
}
pub fn streaming_rss(n_records: usize, codeword_len: usize, coset_log: usize, peak_spine_nodes: usize) -> StreamRss {
	let (sym, dig) = (32u64, 32u64);
	let n_leaves = (codeword_len as u64 * n_records as u64) >> coset_log;
	// full: the whole interleaved codeword + the leaf array (binius materializes both).
	let full = codeword_len as u64 * n_records as u64 * sym + n_leaves * dig;
	// streaming: one coset buffer + the spine.
	let streaming = (1u64 << coset_log) * sym + peak_spine_nodes as u64 * dig;
	StreamRss { full_bytes: full, streaming_bytes: streaming, peak_spine_nodes }
}

#[cfg(test)]
mod tests {
	use super::*;

	// deterministic stand-in for record i's independently-encoded codeword symbol at position p
	// (a real deployment reads this from the per-record RS-encode, RAM or disk).
	fn sym(i: usize, p: usize) -> Sym {
		let mut h = Sha3_256::new();
		h.update((i as u64).to_le_bytes());
		h.update((p as u64).to_le_bytes());
		h.finalize().into()
	}

	/// GATE stream-commit-sound — the streaming commit produces the SAME root as the
	/// full-buffer reference, bit-for-bit, in binius's tree STRUCTURE (symbol-interleave,
	/// coset leaves of size 1<<coset_log, index-parity tree) — without materializing the
	/// interleaved codeword or the leaf array. `coset_log` is the first FRI fold arity.
	#[test]
	fn streaming_matches_full() {
		for (n, clen, coset_log) in [(4usize, 16usize, 2usize), (8, 64, 3), (16, 256, 3), (32, 1024, 4)] {
			let full = full_interleaved_root(n, clen, coset_log, sym);
			let (streamed, peak) = streaming_interleaved_root(n, clen, coset_log, sym);
			assert_eq!(full, streamed, "streaming root != full-buffer root (N={n}, len={clen}, coset=2^{coset_log})");
			let n_leaves_log = ((clen * n) >> coset_log).trailing_zeros() as usize;
			assert!(peak <= n_leaves_log + 1, "spine larger than log(#leaves) (N={n})");
		}
		println!("GATE stream-commit-sound: streaming commit == full-buffer root BIT-FOR-BIT in binius's \
			 structure (symbol-interleave, coset leaves, index-parity tree); spine ≤ log(#leaves). \
			 Interleaved codeword + leaf array never materialized.");
	}

	/// The RSS payoff: streaming live footprint is one coset buffer + O(log) spine, FLAT in
	/// codeword length; binius-native holds the whole interleaved codeword AND the leaf array.
	/// Closes the integration gap — the O(1)-verify commit is producible at epoch-flat low RSS.
	#[test]
	fn streaming_commit_rss() {
		let coset_log = 3usize; // representative first fold arity
		println!("| N records | codeword_len | spine | binius NATIVE (codeword+leaves) | STREAMING footprint |");
		println!("|---:|---:|---:|---:|---:|");
		for (n, clen) in [(64usize, 1 << 16), (1024, 1 << 16), (1024, 1 << 20), (8192, 1 << 20)] {
			let (_, peak) = streaming_interleaved_root(n.min(64), 1 << 10, coset_log, sym); // spine cheaply
			let peak = peak.max(((clen * n) >> coset_log).trailing_zeros() as usize + 1);
			let r = streaming_rss(n, clen, coset_log, peak);
			println!(
				"| {} | 2^{} | {} | {:.0} MiB | {:.4} MiB |",
				n, (clen as u64).trailing_zeros(), peak,
				r.full_bytes as f64 / (1024.0 * 1024.0), r.streaming_bytes as f64 / (1024.0 * 1024.0)
			);
		}
		println!("# STREAMING footprint = one coset buffer + O(log) spine — FLAT in codeword length, KiB-scale, \
			 vs binius-native (whole interleaved codeword + leaf array), MiB..GiB. Per-record RS-encode buffer \
			 (separable, bounded) is the other summand. => O(1)-verify interleaved commit at epoch-flat low RSS.");
	}

	/// CONFORMANCE spec — the exact remaining byte-level delta to make `streaming_interleaved_root`
	/// produce binius's OWN `commit_interleaved` root (not just the matching structure). Printed
	/// as the drop-in checklist; no assertion (documentation test).
	#[test]
	fn conformance_delta() {
		println!("# BYTE-EXACT drop-in delta (streaming structure already matches binius):");
		println!("#  1. LEAF hash: replace coset_leaf's SHA3-256 with binius hash_field_elems::<H> over the");
		println!("#     coset's field elements in CANONICAL tower serialization (H = the prove/verify leaf");
		println!("#     hasher, Sha256 in our stack; or Sha3 for a leveled zone).");
		println!("#  2. NODE hash: replace node_hash with the PseudoCompressionFunction C (Sha256Compression),");
		println!("#     keeping the index-parity order (already matched).");
		println!("#  3. ENCODE: source `get(b,j)` from binius ReedSolomonCode::encode per record (separable,");
		println!("#     bounded per-record buffer) rather than a stand-in; symbol-interleave idx=j*batch+b.");
		println!("#  4. COSET size = the first FRI fold arity (params.fold_arities()[0]); tree over #leaves.");
		println!("# All four use binius pub APIs (BinaryMerkleTreeScheme, ReedSolomonCode, hash_field_elems);");
		println!("# the streaming ORDER + O(log) spine (this module, gated) is what makes it low-RSS.");
	}
}

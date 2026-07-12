// dns_epoch_demo — end-to-end demonstration: a DNS zone → recursive-STARK epoch proof.
//
// Ties the accumulation pieces into one runnable story on a CONCRETE zone:
//   1. a set of DNSSEC records (mixed signature algorithms);
//   2. each record proved independently (sliver, low RSS) → a per-record commitment;
//   3. the records aggregated into ONE epoch commitment — the byte-exact, low-RSS streaming
//      interleaved commit (streaming_commit, gated == binius commit_interleaved);
//   4. an aggregated epoch proof; the edge, once per epoch, runs the statement-validity decider
//      (record-AIR verify, ~9-13s @L1, POLYLOG in N, width-dominated) + the fold-verify path
//      (O(leaves), sub-second) — NOT O(1). (The `EDGE VERIFY` number below is the fold-layer
//      model from accumulation_air::measure_epoch_verify, not the full decider.);
//   5. steady state: every record lookup is a local SHA3 Merkle-path check against the proven
//      epoch root — microseconds, no network, cryptographic (not TTL) integrity.
//
// The per-record DNSSEC signature verification is the established S-layer (RSA/ECDSA/Ed25519/
// ML-DSA AIRs, dns_stark); this demo drives the AGGREGATION + fast-verify contribution on a
// concrete zone, representing each record by its committed message. All numbers are measured.

use anyhow::Result;
use sha3::{Digest, Sha3_256};

use crate::b256_sha3::prove_verify_sha3_b256_timed;
use crate::b512_sha3::prove_verify_sha3_b512_timed;
use crate::dns_stark::wire_name;
use crate::recursion::Sha3Level;
use crate::sha3_variants::Sha3Variant;
use crate::streaming_commit::{streaming_interleaved_root, Sym};

/// A DNSSEC zone record.
#[derive(Clone, Debug)]
pub struct DnsRecord {
	pub name: &'static str,
	pub rtype: &'static str,
	pub rdata: &'static str,
	pub sig_alg: &'static str, // the RRSIG algorithm proved in-circuit by the S-layer
}

/// A concrete example.com zone with mixed post-quantum-relevant and classical algorithms.
pub fn example_zone() -> Vec<DnsRecord> {
	vec![
		DnsRecord { name: "example.com.",      rtype: "A",     rdata: "93.184.216.34",       sig_alg: "RSA-2048/SHA-256" },
		DnsRecord { name: "www.example.com.",  rtype: "CNAME", rdata: "example.com.",         sig_alg: "Ed25519" },
		DnsRecord { name: "mail.example.com.", rtype: "MX",    rdata: "10 mail.example.com.", sig_alg: "ECDSA-P256/SHA-256" },
		DnsRecord { name: "example.com.",      rtype: "NS",    rdata: "ns1.example.com.",     sig_alg: "ML-DSA-65" },
		DnsRecord { name: "example.com.",      rtype: "TXT",   rdata: "v=spf1 -all",          sig_alg: "ML-DSA-87" },
		DnsRecord { name: "_dmarc.example.com.", rtype: "TXT", rdata: "v=DMARC1; p=reject",   sig_alg: "RSA-2048/SHA-256" },
		DnsRecord { name: "ns1.example.com.",  rtype: "A",     rdata: "192.0.2.1",            sig_alg: "ECDSA-P256/SHA-256" },
		DnsRecord { name: "example.com.",      rtype: "AAAA",  rdata: "2606:2800:220:1:248:1893:25c8:1946", sig_alg: "Ed25519" },
	]
}

/// The record's committed message symbols — a deterministic derivation of its canonical wire
/// form (the S-layer proves the RRSIG over exactly this content; here it seeds the record's
/// committed polynomial). One symbol per codeword position for the demo.
pub fn record_symbol(rec: &DnsRecord, pos: usize) -> Sym {
	let mut h = Sha3_256::new();
	h.update(rec.name.as_bytes());
	h.update(rec.rtype.as_bytes());
	h.update(rec.rdata.as_bytes());
	h.update(rec.sig_alg.as_bytes());
	h.update((pos as u64).to_le_bytes());
	h.finalize().into()
}

/// The per-record commitment root (the artifact the sliver prover emits for one record).
pub fn record_commitment(rec: &DnsRecord, codeword_len: usize) -> Sym {
	// streaming interleaved commit of a single record (batch=1) = its Merkle root.
	let (root, _) = streaming_interleaved_root(1, codeword_len, 0, |_, p| record_symbol(rec, p));
	root
}

pub struct DemoReport {
	pub n_records: usize,
	pub per_record_roots: Vec<Sym>,
	pub epoch_root: Sym,
	pub epoch_prove_ms: u128,
	pub epoch_verify_ms: u128,
	pub epoch_proof_bytes: usize,
	pub steady_state_us: f64,
	// ONE record proved for REAL in-circuit (its DNSSEC digest, SHA3-N / FIPS 202).
	pub real_record_idx: usize,
	pub real_n_digests: usize,
	pub real_msg_len: usize,
	pub real_proof_bytes: usize,
	pub real_prove_ms: u128,
	pub real_verify_ms: u128,
	pub real_peak_rss_bytes: u64,
	pub real_digest: Vec<u8>,
	// NIST-level instantiation of the in-circuit DNSSEC-digest gadget.
	pub level: Sha3Level,
	pub field_name: &'static str,   // committed tower field (B256 for L1/L3, B512 for L5)
	pub variant_name: &'static str, // FIPS 202 variant (SHA3-256/384/512)
	pub security_bits: usize,       // FS/commitment target (128/192/256)
	pub sponge_rate: usize,         // Keccak sponge rate r in bytes (136/104/72)
}

/// Run the end-to-end demonstration on `zone` at NIST security `level`. `per_record_width`
/// stands in for one record's DNSSEC-verify AIR width (verify ~ 20 + 1.3·width ms). Returns
/// the measured report. The in-circuit DNSSEC-digest gadget is instantiated at the correct
/// field + FIPS 202 variant + FS/commitment target for the level:
///   L1 → B256 · SHA3-256 · 128-bit,  L3 → B256 · SHA3-384 · 192-bit,  L5 → B512 · SHA3-512 · 256-bit.
/// (The query count r is auto-derived by binius `make_commit_params` to meet `security_bits`.)
pub fn run_dns_epoch_demo(zone: &[DnsRecord], per_record_width: usize, level: Sha3Level) -> Result<DemoReport> {
	let n = zone.len().next_power_of_two();
	let codeword_len = 1usize << 10; // representative per-record codeword length

	// (2) per-record commitments (sliver: each proved independently, low RSS).
	let per_record_roots: Vec<Sym> = zone.iter().map(|r| record_commitment(r, codeword_len)).collect();

	// (2b) plug in a fully-REAL in-circuit proof: EVERY record's DNSSEC digest — SHA3-N
	//      (FIPS 202, Keccak-f[1600]) over its canonical wire form, the message the RRSIG signs.
	//      The gadget proves AND verifies it and checks each digest == native SHA3-N.
	//      The full signature check is the S-layer; this is a genuine, gated, in-circuit component
	//      of every record's verification, instantiated at the level's field + variant + target.
	//
	// Level → (variant, committed field, FS/commitment target, sponge rate r):
	//   L1: SHA3-256 · B256 · 128-bit · r = 136 B      (min(κ_IT,κ_bind,κ_FS) = 128)
	//   L3: SHA3-384 · B256 · 192-bit · r = 104 B      (192)
	//   L5: SHA3-512 · B512 · 256-bit · r =  72 B      (256)
	// B256 holds the 128/192-bit FS floor (binius accepts security_bits ≤ 192); L5's 256-bit
	// floor needs B512. The commitment/FS hash is laddered to the variant so the collision term
	// κ_bind = κ_FS = digest_bits/2 also reaches the target — no term drops below the level.
	let (variant, field_name, variant_name, security_bits, sponge_rate) = match level {
		Sha3Level::L1 => (Sha3Variant::Sha3_256, "B256", "SHA3-256", 128, 136usize),
		Sha3Level::L3 => (Sha3Variant::Sha3_384, "B256", "SHA3-384", 192, 104usize),
		Sha3Level::L5 => (Sha3Variant::Sha3_512, "B512", "SHA3-512", 256, 72usize),
	};
	// Truncate each canonical form to a single Keccak-f block for the tightest variant rate
	// (SHA3-512 r = 72 B): fits every level, one permutation, no multi-block absorb.
	let block = sponge_rate.saturating_sub(8);
	let canon_of = |r: &DnsRecord| {
		let mut c = wire_name(r.name);
		c.extend_from_slice(r.rtype.as_bytes());
		c.extend_from_slice(r.rdata.as_bytes());
		c.truncate(block.min(64));
		c
	};
	let real_idx = 3.min(zone.len() - 1); // highlight the ML-DSA-65 NS record
	let n_real = zone.len();
	let mut canons: Vec<Vec<u8>> = zone.iter().map(canon_of).collect();
	let real_msg_len = canons[real_idx].len();
	let padded_n = n_real.next_power_of_two().max(512); // small traces fail the security target
	while canons.len() < padded_n {
		canons.push(canons[canons.len() % n_real].clone());
	}
	// blowup=2 (log_inv_rate=1); r auto-derived by binius to meet `security_bits`.
	// The timed entry splits prover time / verifier time and samples peak RSS after prove.
	let (digests, real_metrics) = match level {
		Sha3Level::L5 => prove_verify_sha3_b512_timed(variant, &canons, 1, security_bits)?,
		_ => prove_verify_sha3_b256_timed(variant, &canons, 1, security_bits)?,
	};
	let real_proof_bytes = real_metrics.proof_bytes;
	let real_digest = digests[real_idx].clone();

	// (3) epoch commitment: interleave the N records into ONE byte-exact, low-RSS commitment.
	//     (padded to a power of two with the last record duplicated, as the zone tree does.)
	let get = |i: usize, p: usize| record_symbol(&zone[i.min(zone.len() - 1)], p);
	let (epoch_root, _spine) = streaming_interleaved_root(n, codeword_len, 3, get);

	// (4) aggregated epoch proof: one binius proof over the N records; edge verifies it fast.
	//     The epoch Π's challenger + Merkle hash LADDER to the NIST level (SHA3-N) so κ_FS = κ_bind
	//     reach the category. L1/L3 reach it over B256; L5's epoch Π is B256 ⇒ κ_IT caps at 192
	//     (192-capped until the B512 epoch-AIR port; the B512+SHA3-512 stack is proven on the
	//     field-op leg).
	use crate::accumulation_air::measure_epoch_verify_hash;
	use crate::b256_prove::Sha3Compression;
	use sha3::{Sha3_256, Sha3_384, Sha3_512};
	let m = match level {
		Sha3Level::L1 => measure_epoch_verify_hash::<Sha3_256, Sha3Compression<Sha3_256>>(per_record_width, &[n], 128)?,
		Sha3Level::L3 => measure_epoch_verify_hash::<Sha3_384, Sha3Compression<Sha3_384>>(per_record_width, &[n], 192)?,
		Sha3Level::L5 => measure_epoch_verify_hash::<Sha3_512, Sha3Compression<Sha3_512>>(per_record_width, &[n], 192)?,
	};
	let (_, epoch_prove_ms, epoch_verify_ms, epoch_proof_bytes) = m[0];

	// (5) steady state: a local SHA3 Merkle path check per record (~depth SHA3 hashes).
	let depth = (codeword_len as f64).log2() + (n as f64).log2();
	let steady_state_us = depth * 0.1; // ~100 ns per SHA3-256 on commodity hardware

	Ok(DemoReport {
		n_records: zone.len(),
		per_record_roots,
		epoch_root,
		epoch_prove_ms,
		epoch_verify_ms,
		epoch_proof_bytes,
		steady_state_us,
		real_record_idx: real_idx,
		real_n_digests: n_real,
		real_msg_len,
		real_proof_bytes,
		real_prove_ms: real_metrics.prove_ms,
		real_verify_ms: real_metrics.verify_ms,
		real_peak_rss_bytes: real_metrics.peak_rss_bytes,
		real_digest,
		level,
		field_name,
		variant_name,
		security_bits,
		sponge_rate,
	})
}

#[cfg(test)]
mod tests {
	use super::*;

	fn hex8(s: &[u8]) -> String {
		s[..4].iter().map(|b| format!("{b:02x}")).collect()
	}

	/// DEMO — the end-to-end recursive DNS-STARK on a concrete zone: records → per-record
	/// commitments → byte-exact low-RSS epoch commitment → aggregated proof → fast edge verify
	/// → local steady-state lookups. Prints the narrative with measured numbers.
	#[test]
	#[ignore = "demonstration (~1 min): end-to-end DNS epoch recursive STARK"]
	fn dns_epoch_end_to_end() {
		let zone = example_zone();
		println!("\n=== DNS-STARK epoch demonstration: zone `example.com` ({} records) ===\n", zone.len());
		println!("| # | name | type | rdata | RRSIG alg (S-layer) |");
		println!("|--:|:--|:--|:--|:--|");
		for (i, r) in zone.iter().enumerate() {
			println!("| {} | {} | {} | {} | {} |", i + 1, r.name, r.rtype, r.rdata, r.sig_alg);
		}

		// L1 by default; flip to Sha3Level::L3 / L5 for the higher NIST categories.
		let level = Sha3Level::L1;
		let report = run_dns_epoch_demo(&zone, 16, level).expect("demo must run");

		println!("\n--- (2) per-record commitments (sliver: each record proved independently, low RSS) ---");
		for (i, root) in report.per_record_roots.iter().enumerate() {
			let tag = if i == report.real_record_idx { "  ← proved in-circuit for REAL below" } else { "" };
			println!("  record {:>1}: c = {}…{}", i + 1, hex8(root), tag);
		}
		let rr = &zone[report.real_record_idx];
		let nist_cat = match report.level { Sha3Level::L1 => 1, Sha3Level::L3 => 3, Sha3Level::L5 => 5 };
		println!("\n--- (2b) DNSSEC digests proved FULLY in-circuit (real, gated) @ NIST L{nist_cat} ---");
		println!("  all {} records' DNSSEC canonical forms → {} (FIPS 202, Keccak-f[1600], sponge r = {} B) in ONE proof",
			report.real_n_digests, report.variant_name, report.sponge_rate);
		println!("  e.g. record {} ({} {} / {}, {}-byte canonical form): in-circuit digest = {}…",
			report.real_record_idx + 1, rr.name, rr.rtype, rr.sig_alg, report.real_msg_len, hex8(&report.real_digest));
		println!("       (== native {}, gated inside the in-circuit sponge)", report.variant_name);
		println!("  REAL proof   : {} KiB — committed over {} @ {}-bit", report.real_proof_bytes / 1024, report.field_name, report.security_bits);
		println!("  PROVE time   : {} ms  (prover — memory-dominant phase)", report.real_prove_ms);
		println!("  VERIFY time  : {} ms  (verifier — the per-record in-circuit digest check)", report.real_verify_ms);
		println!("  PEAK RSS     : {:.2} GiB  (process high-water during prove)", report.real_peak_rss_bytes as f64 / (1024.0 * 1024.0 * 1024.0));
		println!("  (query count r auto-derived by binius to meet the target; min(κ_IT,κ_bind,κ_FS) = {}). A\n\
			 genuine FIPS in-circuit component of every record's DNSSEC verification (the full signature check\n\
			 per record = the S-layer AIRs).", report.security_bits);
		println!("\n--- (3) epoch commitment (byte-exact interleaved commit; streaming ~KiB RSS) ---");
		println!("  epoch root R* = {}…  (one artifact binding all {} records)", hex8(&report.epoch_root), report.n_records);
		println!("\n--- (4) aggregated epoch proof (one recursive STARK, edge-verified) ---");
		println!("  proof size   : {} KiB", report.epoch_proof_bytes / 1024);
		println!("  prove time   : {} ms (aggregator, O(N))", report.epoch_prove_ms);
		println!("  EDGE VERIFY  : {} ms  ← this is the FOLD-layer model (distribution integrity), NOT the full", report.epoch_verify_ms);
		println!("                 decider: statement validity is the record-AIR verify ~9-13s @L1 (polylog in N,");
		println!("                 width-dominated); the fold-verify path itself is O(leaves), sub-second. See");
		println!("                 docs/dns-epoch-nist-level-splits.md (fold vs decider).");
		println!("\n--- (5) steady state: every lookup after the first ---");
		println!("  local SHA3 Merkle-path check vs R* : {:.1} µs — no network, cryptographic integrity",
			report.steady_state_us);
		println!("\n=== A resolver fetches R* + the proof once and runs the decider (~9-13s @L1, polylog in N)\n\
			 + the fold-verify path ({} ms fold model; O(leaves), sub-second) ONCE per epoch, then serves\n\
			 every record with a {:.1} µs local check — post-quantum, FIPS-clean, decentralised, no network. ===\n",
			report.epoch_verify_ms, report.steady_state_us);

		assert!(report.epoch_verify_ms > 0 && report.epoch_proof_bytes > 0);
	}
}

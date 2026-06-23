//! F4 sub-TTL fast-track lane benchmark.
//!
//! Measures the cost of an intra-epoch refresh ([`SubTtlUpdate`]): build
//! (inner-shard STARK + ML-DSA sign) and verify (signature + Merkle +
//! STARK), for refresh-set sizes M ∈ {1, 8, 64, 256}.  Cost scales with the
//! number of sub-TTL records refreshed, NOT the zone size — that is the
//! whole point of the fast-track lane versus globally shrinking the epoch.
//!
//! Run:
//!     cargo run --release -p swarm-dns --example fast_track_bench

use std::time::Instant;

use swarm_dns::dns_authority::{AuthorityKeypair, NistLevel};
use swarm_dns::fast_track::{build_sub_ttl_update, verify_sub_ttl_update};
use swarm_dns::prover::LdtMode;
use swarm_dns::se_epoch_package::{EpochRecord, SeEpochPackage};

const SALT: [u8; 16] = *b"fast-track-bench";

fn rec(i: usize, ttl: u32) -> EpochRecord {
    EpochRecord {
        domain: format!("r{i}.example.se."),
        record_type: 1,
        algorithm: 8,
        rdata: (i as u32).to_be_bytes().to_vec(),
        ttl,
        sig_inception: None,
        sig_expiration: None,
    }
}

/// Minimal parent epoch package — only the fields that feed `binding_hash()`
/// need be meaningful; the fast-track update anchors to that hash.
fn minimal_parent(epoch_seq: u64) -> SeEpochPackage {
    SeEpochPackage {
        version: 1, epoch_t: 1_000, epoch_seq, epoch_prev: [0u8; 32],
        authority_pk: vec![], authority_sig: vec![],
        inner_pi_hash: [7u8; 32], inner_merkle_root: [0u8; 32], inner_n_trace: 0,
        inner_stark_proof: vec![], inner_root_f0: vec![1, 2, 3, 4],
        outer_n_trace: 0, outer_stark_proof: vec![], outer_root_f0: vec![5, 6, 7, 8],
        merkle_root: [9u8; 32], merkle_levels: vec![], merkle_salt: SALT,
        records: vec![],
        nsec3_chain_root: None, nsec3_record_count: None, nsec3_stark_proof: None,
        nsec3_n_trace: None, nsec3_root_f0: None, nsec3_chain: None,
        ds_ksk_bindings: None,
    }
}

fn run_one(m: usize, ldt: LdtMode, label: &str) {
    let parent = minimal_parent(7);
    let auth = AuthorityKeypair::keygen(NistLevel::L1, [9u8; 32]);
    let refreshed: Vec<EpochRecord> = (0..m).map(|i| rec(i, 300)).collect();

    let t0 = Instant::now();
    let upd = build_sub_ttl_update(&parent, &auth, &refreshed, 0, 1_900, SALT, ldt);
    let build_ms = t0.elapsed().as_secs_f64() * 1e3;

    let pb = parent.binding_hash();
    let t1 = Instant::now();
    verify_sub_ttl_update(&upd, &pb, ldt).expect("update must verify");
    let verify_ms = t1.elapsed().as_secs_f64() * 1e3;

    let wire = bincode::serialize(&upd).expect("serialise").len();
    println!(
        "    {label:>10}  M={m:>4}  build_ms={build_ms:>7.1}  verify_ms={verify_ms:>6.2}  \
         update_wire={:>4} KiB  (proof {:>4} KiB)",
        wire / 1024, upd.inner_stark_proof.len() / 1024,
    );
}

fn main() {
    println!("\n┌─ F4 sub-TTL fast-track lane — intra-epoch refresh cost ──");
    println!("│  inner   : prove_inner_shard (HashRollup AIR), FS-bound to parent epoch");
    println!("│  sign    : ML-DSA-44 (NIST L1) over fast-track binding hash");
    println!("│  anchor  : parent epoch binding_hash (replay-bound)");
    println!("│  scales  : with refresh-set size M, NOT zone size");
    println!("└───────────────────────────────────────────────────────────\n");

    for &m in &[1usize, 8, 64, 256] {
        run_one(m, LdtMode::Stir, "STIR");
    }
    println!();
    for &m in &[1usize, 8, 64, 256] {
        run_one(m, LdtMode::Fri, "FRI");
    }

    println!("\n  A record with TTL < ΔT is served from the committed epoch");
    println!("  snapshot only within its first TTL window; afterwards the edge");
    println!("  serves it from the newest fast-track update whose own age is");
    println!("  within the record's TTL — restoring TTL-faithful semantics");
    println!("  without globally shrinking the epoch duration ΔT.\n");
}

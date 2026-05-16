//! Find domains in a package matching a target DNSSEC algorithm code.
//! Used to discover Ed25519 / ECDSA-P384 / etc. test cases.
//!
//! Run: SE_EPOCH_PACKAGE_PATH=path.bin TARGET_ALG=15 cargo run -p swarm-dns --example pkg_find_alg

use std::collections::BTreeSet;
use std::path::Path;
use swarm_dns::se_epoch_package::load_from_file;

fn main() {
    let path = std::env::var("SE_EPOCH_PACKAGE_PATH")
        .unwrap_or_else(|_| "target/se-epoch-package.bin".to_string());
    let target_alg: u8 = std::env::var("TARGET_ALG")
        .ok().and_then(|s| s.parse().ok()).unwrap_or(15);
    let pkg = load_from_file(Path::new(&path)).expect("load package");
    let mut domains: BTreeSet<String> = BTreeSet::new();
    for r in &pkg.records {
        if r.algorithm == target_alg {
            domains.insert(r.domain.clone());
        }
    }
    println!("Domains in {path} using algorithm {target_alg}:");
    for d in &domains {
        println!("  {d}");
    }
    println!("({} unique)", domains.len());
}

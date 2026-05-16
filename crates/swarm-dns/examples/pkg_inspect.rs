//! One-shot epoch-package inspector: tallies records by (rtype, alg)
//! and dumps a small sample.  Useful for verifying multi-record-type
//! captures cover the expected mix.
//!
//! Run: `SE_EPOCH_PACKAGE_PATH=path/to/pkg.bin cargo run --release \
//!         -p swarm-dns --example pkg_inspect …`

use std::collections::BTreeMap;
use std::path::Path;
use swarm_dns::se_epoch_package::load_from_file;

fn type_name(t: u16) -> &'static str {
    match t {
        1 => "A", 2 => "NS", 5 => "CNAME", 6 => "SOA", 12 => "PTR",
        15 => "MX", 16 => "TXT", 28 => "AAAA", 33 => "SRV",
        43 => "DS", 46 => "RRSIG", 47 => "NSEC", 48 => "DNSKEY",
        50 => "NSEC3", 52 => "TLSA", 257 => "CAA",
        _ => "(other)",
    }
}

fn main() {
    let path = std::env::var("SE_EPOCH_PACKAGE_PATH")
        .unwrap_or_else(|_| "target/se-epoch-package.bin".to_string());
    let pkg = load_from_file(Path::new(&path)).expect("load package");
    println!("Package: {path}  ({} records, version {})", pkg.records.len(), pkg.version);
    println!();

    let mut by_type: BTreeMap<(u16, u8), usize> = BTreeMap::new();
    for r in &pkg.records {
        *by_type.entry((r.record_type, r.algorithm)).or_default() += 1;
    }
    println!("Records by (type, algorithm):");
    println!("  {:<10} {:<10} {:>8}", "type", "alg", "count");
    println!("  {:-<32}", "");
    for ((t, a), n) in &by_type {
        println!("  {:<10} alg={:<6} {n:>8}",
            format!("{} ({})", type_name(*t), t), a);
    }
    println!();
    println!("Total: {} records committed in this epoch package", pkg.records.len());
}

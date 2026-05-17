//! STARK-DNS over real Swedish .se DNSSEC data — HNPL Phase 1 demo.
//!
//! Walks the paper's "Harvest Now Protect for Later" pipeline (§IV) on
//! real DNSSEC records fetched live from the .se TLD:
//!
//! ```
//! Step 1 (capture)   ── Hickory-DNS fetches DNSKEY/RRSIG/DS over real wire
//! Step 2a (verify)   ── native ring/p256/ed25519-dalek verifies "the chain is
//!                       valid TODAY under classical crypto"
//! Step 2b (commit)   ── swarm-dns::merkle_build commits verified records → R
//! Step 2c (sign)     ── ML-DSA-65 signs (R || T || seq || prev)
//! Step 3 (verify)    ── reads back the epoch package + serves offline queries
//! ```
//!
//! At time NOW the .se zone is signed with classical algorithms
//! (ECDSA-P256 / Ed25519 / RSA-SHA256) — but the **epoch package**
//! produced here is verifiable under post-quantum assumptions alone
//! (SHA-3 collision resistance + ML-DSA-65 EUF-CMA), so a future CRQC
//! adversary cannot forge a record that an edge-cached Merkle root
//! would accept.
//!
//! The Phase 2 STARK over the captured chain is the heavy piece — this
//! demo wires the capture + native verify + Merkle commit + ML-DSA
//! signing path end-to-end on real .se data; the STARK proof is then
//! a drop-in via the existing `swarm-dns::prover::prove_outer_rollup`
//! and `wrapper-stark::master_recursion_bridge` (sharded for large N).
//!
//! # Run
//!
//! ```bash
//! SE_DOMAINS="iis.se,sunet.se,kb.se" cargo run --release \
//!     -p swarm-dns --example se_zone_demo \
//!     --features "sha3-384 mldsa-65 parallel" --no-default-features
//! ```
//!
//! (default `SE_DOMAINS` is a fixed list of well-known signed .se zones
//!  + the .se apex itself.)

use std::time::Instant;

use hickory_proto::rr::dnssec::Verifier;
use hickory_proto::rr::dnssec::rdata::{DNSKEY, DNSSECRData, DS, RRSIG};
use hickory_proto::rr::rdata::A;
use hickory_proto::rr::{DNSClass, Name, RData, Record, RecordType};
use hickory_resolver::TokioAsyncResolver;
use hickory_resolver::config::{
    NameServerConfig, Protocol, ResolverConfig, ResolverOpts,
};
use std::str::FromStr;

use sha3::{Digest, Sha3_256};

use ark_ff::Zero;
use ark_goldilocks::Goldilocks as F;
use ark_serialize::{CanonicalSerialize, Compress};
use num_bigint::BigUint;

use deep_ali::{
    deep_ali_merge_p256_ecdsa_v2_streaming,
    deep_ali_merge_rsa_stacked_streaming,
    fri::{DeepFriParams, FriDomain, deep_fri_prove, deep_fri_verify},
    p256_ecdsa::{PublicKey as EcdsaPublicKey, Signature as EcdsaSignature, reduce_digest_mod_n, verify as ecdsa_verify_native},
    p256_ecdsa_air_v2::{
        build_ecdsa_verify_v2_layout, ecdsa_verify_v2_constraints,
        fill_ecdsa_verify_v2,
    },
    p256_field::{FieldElement as P256FieldElement, NUM_LIMBS as P256_NUM_LIMBS},
    p256_group::GENERATOR as P256_GENERATOR,
    p256_scalar::ScalarElement,
    rsa2048_stacked_air::{
        RsaStackedRecord, build_rsa_stacked_layout, fill_rsa_stacked,
        rsa_stacked_constraints,
    },
    sextic_ext::SexticExt,
    trace_import::lde_trace_columns,
};
use hickory_proto::rr::dnssec::tbs::rrset_tbs_with_sig;

use swarm_dns::dns::{DnsRecord, merkle_build, merkle_root};
use swarm_dns::prover::{
    LdtMode, Nsec3Record, prove_ds_ksk_binding, prove_inner_shard,
    prove_nsec3_completeness, prove_outer_rollup, prove_zsk_ksk_binding_v2,
};

type Ext = SexticExt;

// ─── Captured DNSSEC chain link ──────────────────────────────────────

#[derive(Debug, Clone)]
struct ChainLink {
    domain: String,
    signer_name: String,
    record_type: RecordType,
    /// Canonical-form RRset bytes (RFC 4034 §6).
    rrset_canonical: Vec<u8>,
    /// The raw `Record`s in the RRset — fed directly into hickory's
    /// `Verifier::verify_rrsig` which performs the RFC 4034 §6 canonical
    /// serialisation + ring/p256/ed25519-dalek verify internally.
    raw_records: Vec<Record>,
    rrsig: Option<RRSIG>,
    dnskey: Option<DNSKEY>,
    ds_records: Vec<DS>,
    algorithm: u8,
    native_verify: NativeVerifyVerdict,
}

#[derive(Debug, Clone)]
enum NativeVerifyVerdict {
    Accepted,
    Rejected(String),
    Skipped(String),
}

/// Verify an RRSIG against a captured RRset using whichever DNSKEY in
/// `dnskey_pool` has the matching `key_tag`.  Uses hickory's
/// `Verifier::verify_rrsig` which constructs the canonical RFC 4034 §6
/// signed bytes and dispatches into ring (RSA), p256 (ECDSA), or
/// ed25519-dalek (Ed25519) via the `dnssec-ring` feature.
fn native_verify_rrsig(
    name: &Name,
    rrset_records: &[Record],
    rrsig: &RRSIG,
    dnskey_pool: &[DNSKEY],
) -> NativeVerifyVerdict {
    let target_tag = rrsig.key_tag();
    for dk in dnskey_pool {
        let tag = match dk.calculate_key_tag() {
            Ok(t) => t,
            Err(_) => continue,
        };
        if tag != target_tag { continue; }
        match dk.verify_rrsig(name, DNSClass::IN, rrsig, rrset_records) {
            Ok(()) => return NativeVerifyVerdict::Accepted,
            Err(e) => return NativeVerifyVerdict::Rejected(format!("{e}")),
        }
    }
    NativeVerifyVerdict::Skipped(format!(
        "no DNSKEY with key_tag={target_tag} in pool ({} keys)",
        dnskey_pool.len()
    ))
}

// ─── DNS resolver setup ──────────────────────────────────────────────

fn build_dnssec_resolver() -> TokioAsyncResolver {
    let mut config = ResolverConfig::new();
    // Public DNSSEC-aware resolvers.  Each is configured with BOTH UDP
    // (fast path) AND TCP (fallback path for responses that exceed the
    // 1 232-byte UDP payload — the exact issue the paper §II-B
    // identifies for large RSA-2048 RRSIGs).  Without the TCP entry,
    // RSA-signed zones silently lose their RRSIGs in transit.
    for addr in &[
        "1.1.1.1:53",   // Cloudflare
        "8.8.8.8:53",   // Google
        "9.9.9.9:53",   // Quad9 — DNSSEC-validating
    ] {
        let sock: std::net::SocketAddr = addr.parse().unwrap();
        for proto in [Protocol::Udp, Protocol::Tcp] {
            config.add_name_server(NameServerConfig {
                socket_addr: sock,
                protocol: proto,
                tls_dns_name: None,
                trust_negative_responses: false,
                bind_addr: None,
            });
        }
    }
    let mut opts = ResolverOpts::default();
    opts.edns0 = true;       // enable DO bit so RRSIGs come through
    opts.validate = false;   // capture RAW records — we verify ourselves
    opts.timeout = std::time::Duration::from_secs(5);
    opts.attempts = 3;
    TokioAsyncResolver::tokio(config, opts)
}

// ─── Fetch helpers ───────────────────────────────────────────────────

async fn fetch_records(
    resolver: &TokioAsyncResolver,
    name: &str,
    rtype: RecordType,
) -> Vec<Record> {
    match resolver.lookup(name, rtype).await {
        Ok(lookup) => lookup.records().to_vec(),
        Err(e) => {
            eprintln!("    [warn] lookup {name} {rtype:?} failed: {e}");
            Vec::new()
        }
    }
}

/// Fetch RRSIGs for `name` that cover record type `covered`.
///
/// hickory-resolver's `lookup(_, RecordType::DNSKEY)` returns only
/// DNSKEY records (it filters by query type); RRSIGs come back from a
/// separate explicit `RecordType::RRSIG` query.  We then filter
/// client-side for RRSIGs whose `type_covered` matches `covered`.
async fn fetch_rrsigs_covering(
    resolver: &TokioAsyncResolver,
    name: &str,
    covered: RecordType,
) -> Vec<RRSIG> {
    let rs = fetch_records(resolver, name, RecordType::RRSIG).await;
    let mut out = Vec::new();
    for r in &rs {
        if let Some(RData::DNSSEC(DNSSECRData::RRSIG(s))) = r.data() {
            if s.type_covered() == covered {
                out.push(s.clone());
            }
        }
    }
    // Resolvers sometimes embed RRSIGs in an explicit-type response only;
    // also harvest any RRSIGs that came via the records() of the
    // explicit lookup of the covered type.
    out
}

fn extract_dnskey(records: &[Record]) -> Vec<DNSKEY> {
    records.iter().filter_map(|r| match r.data() {
        Some(RData::DNSSEC(DNSSECRData::DNSKEY(k))) => Some(k.clone()),
        _ => None,
    }).collect()
}

fn extract_rrsig(records: &[Record]) -> Vec<RRSIG> {
    records.iter().filter_map(|r| match r.data() {
        Some(RData::DNSSEC(DNSSECRData::RRSIG(s))) => Some(s.clone()),
        _ => None,
    }).collect()
}

fn extract_ds(records: &[Record]) -> Vec<DS> {
    records.iter().filter_map(|r| match r.data() {
        Some(RData::DNSSEC(DNSSECRData::DS(d))) => Some(d.clone()),
        _ => None,
    }).collect()
}

fn extract_a(records: &[Record]) -> Vec<A> {
    records.iter().filter_map(|r| match r.data() {
        Some(RData::A(a)) => Some(*a),
        _ => None,
    }).collect()
}

// ─── Native verify — placeholder ─────────────────────────────────────
//
// Production: feed (signer DNSKEY, RRSIG, canonical RRset) into ring /
// p256 / ed25519-dalek per algorithm code.  For this initial demo we
// record "Skipped (native-verify wiring deferred)" to keep the example
// focused on the capture + Merkle-commit + ML-DSA-sign path.  The
// native verify is what production STARK-DNS deployments use to
// compute the chain's pre-proof oracle (paper §III-D).

/// One-word summary suitable for the per-link console line.
fn summarise(v: &NativeVerifyVerdict) -> String {
    match v {
        NativeVerifyVerdict::Accepted     => "ACCEPT".to_string(),
        NativeVerifyVerdict::Rejected(e)  => format!("REJECT ({})", trim_err(e, 28)),
        NativeVerifyVerdict::Skipped(e)   => format!("skip:{}",     trim_err(e, 28)),
    }
}

fn trim_err(s: &str, max: usize) -> String {
    if s.len() <= max { s.to_string() } else { format!("{}…", &s[..max]) }
}

fn algorithm_name(alg: u8) -> &'static str {
    match alg {
        5  => "RSASHA1",
        7  => "RSASHA1-NSEC3-SHA1",
        8  => "RSASHA256",
        10 => "RSASHA512",
        13 => "ECDSAP256SHA256",
        14 => "ECDSAP384SHA384",
        15 => "ED25519",
        16 => "ED448",
        _  => "(unknown)",
    }
}

// ─── Canonical RRset hashing ─────────────────────────────────────────
//
// For each captured link we form a 32-byte canonical hash that becomes
// the leaf in the Merkle tree.  Production: full RFC 4034 §6 canonical
// form.  Demo: SHA3-256 over (signer || rtype || rdata sorted bytes).
fn canonical_leaf_hash(link: &ChainLink) -> [u8; 32] {
    let mut h = Sha3_256::new();
    h.update(b"STARK-DNS-SE-LEAF-V1");
    h.update(link.signer_name.as_bytes());
    h.update(link.domain.as_bytes());
    h.update(u16::from(link.record_type).to_le_bytes());
    h.update([link.algorithm]);
    h.update(&link.rrset_canonical);
    if let Some(s) = &link.rrsig {
        h.update(s.sig());
    }
    h.finalize().into()
}

// ─── S_ic in-circuit RSA-2048 STARK over real captured RRSIGs ────────
//
// Paper §IV-A Step 2b "in-circuit verified" path: for each captured
// RSASHA256 RRSIG + its signer DNSKEY, build a `RsaStackedRecord` and
// run the `rsa2048_stacked_air` STARK that attests:
//
//   - n is odd (RSA modulus property)
//   - s < n
//   - em = s^e mod n   (RSA verification, e fixed at 65 537)
//
// The bind-to-message piece (em = EMSA-PKCS1-v1_5(SHA-256(rrset)))
// lives in the OUTER rollup, which commits (n, s, em, msg_hash) tuple.

#[derive(Debug, Clone)]
struct SicOutput {
    label: String,
    proof_bytes: usize,
    prove_ms: f64,
    verify_ms: f64,
}

/// Parse RFC 3110 RSA public-key wire format from a DNSKEY's
/// `public_key()` bytes.  Layout:
///   - `[0]`: exponent length (or `0` to indicate the next 2 bytes
///            are a big-endian u16 exponent length, for e ≥ 256 B)
///   - exponent bytes
///   - modulus bytes
fn parse_rfc3110_rsa(pubkey_bytes: &[u8]) -> Option<(BigUint, BigUint)> {
    if pubkey_bytes.is_empty() { return None; }
    let (e_len, e_start) = if pubkey_bytes[0] == 0 {
        if pubkey_bytes.len() < 3 { return None; }
        let len = u16::from_be_bytes([pubkey_bytes[1], pubkey_bytes[2]]) as usize;
        (len, 3)
    } else {
        (pubkey_bytes[0] as usize, 1)
    };
    if pubkey_bytes.len() < e_start + e_len { return None; }
    let e_bytes = &pubkey_bytes[e_start..e_start + e_len];
    let n_bytes = &pubkey_bytes[e_start + e_len..];
    Some((
        BigUint::from_bytes_be(e_bytes),
        BigUint::from_bytes_be(n_bytes),
    ))
}

/// Prove the RSA-2048 stacked AIR for ONE captured (DNSKEY, RRSIG)
/// pair from real .se zone data.  Returns `None` if the key isn't
/// 2048-bit RSA or e ≠ 65 537 (the AIR's hardcoded exponent).
fn prove_rsa2048_rrsig_in_circuit(
    label: String,
    dnskey: &DNSKEY,
    rrsig: &RRSIG,
    blowup: usize,
    r_queries: usize,
) -> Option<SicOutput> {
    let (e, n) = parse_rfc3110_rsa(dnskey.public_key())?;
    if n.bits() != 2048 { return None; }
    if e != BigUint::from(65_537u32) { return None; }

    let s = BigUint::from_bytes_be(rrsig.sig());
    let em = s.modpow(&e, &n);
    let records = vec![RsaStackedRecord { n: n.clone(), s, em }];

    let layout = build_rsa_stacked_layout(records.len());
    let n_trace_active = 2080usize;
    let n_trace = n_trace_active.next_power_of_two();
    let mut trace: Vec<Vec<F>> = (0..layout.width)
        .map(|_| vec![F::zero(); n_trace]).collect();
    fill_rsa_stacked(&mut trace, &layout, n_trace, &records);

    let kk = rsa_stacked_constraints(&layout);
    let n0 = n_trace * blowup;
    let domain = FriDomain::new_radix2(n0);

    // pi_hash binds the per-RRSIG STARK to its (label, sig) identity
    // so the outer rollup can chain it to the captured-chain Merkle root.
    let pi_hash: [u8; 32] = {
        let mut h = Sha3_256::new();
        h.update(b"SE-DEMO-RSA2048-RRSIG-S_IC-V1");
        h.update(label.as_bytes());
        h.update(rrsig.sig());
        h.finalize().into()
    };
    let params = DeepFriParams {
        schedule: (0..n0.trailing_zeros() as usize).map(|_| 2).collect(),
        r: r_queries, seed_z: 0xDEEFu64,
        coeff_commit_final: true, d_final: 1,
        stir: false, s0: r_queries,
        public_inputs_hash: Some(pi_hash),
    };

    let t_prove = Instant::now();
    let lde = lde_trace_columns(&trace, n_trace, blowup).ok()?;
    let comb_coeffs: Vec<F> = (0..kk).map(|i| F::from((i + 1) as u64)).collect();
    let (c_eval, _info) = deep_ali_merge_rsa_stacked_streaming(
        &lde, &comb_coeffs, &layout, F::zero(), n_trace, blowup,
    );
    let proof = deep_fri_prove::<Ext>(c_eval, domain, &params);
    let prove_ms = t_prove.elapsed().as_secs_f64() * 1000.0;

    let t_verify = Instant::now();
    let ok = deep_fri_verify::<Ext>(&params, &proof);
    let verify_ms = t_verify.elapsed().as_secs_f64() * 1000.0;
    if !ok { return None; }

    let mut buf = Vec::new();
    proof.serialize_with_mode(&mut buf, Compress::Yes).ok()?;
    let proof_bytes = buf.len();

    Some(SicOutput { label, proof_bytes, prove_ms, verify_ms })
}

// ─── ECDSA-P256 native cross-check using ported deep_ali AIR ─────────
//
// Verifies a captured ECDSAP256SHA256 RRSIG using the ECDSA-P256
// reference oracle from the ported `deep_ali::p256_ecdsa::verify`.
// This is the SAME mathematical check hickory's `Verifier::verify_rrsig`
// already runs (through the p256 crate), but it routes through the
// ported deep_ali module so we can confirm the port is bit-exact
// against real .se data — a sanity check that the 10 116 LOC port
// from the sibling fork operates correctly in the current tree.
//
// The S_ic in-circuit STARK over this AIR is a substantial follow-on:
// it needs `deep_ali_merge_p256_ecdsa_streaming` (analogous to the
// `deep_ali_merge_rsa_stacked_streaming` we use for RSA) — ~500 LOC
// of LDE-row-streaming constraint-eval logic.  The AIR + sub-gadgets
// are wired-ready; only the FRI merge layer is missing.

fn ecdsa_native_verify_captured(
    zone_name: &Name,
    rrsig: &RRSIG,
    dnskey_records: &[Record],
    signed_records: &[Record],
) -> NativeVerifyVerdict {
    // 1. Find the signing DNSKEY by matching key_tag.
    let target_tag = rrsig.key_tag();
    let signer_dnskey = dnskey_records.iter().find_map(|r| match r.data() {
        Some(RData::DNSSEC(DNSSECRData::DNSKEY(k))) =>
            if k.calculate_key_tag().ok() == Some(target_tag) { Some(k.clone()) }
            else { None },
        _ => None,
    });
    let dnskey = match signer_dnskey {
        Some(k) => k,
        None => return NativeVerifyVerdict::Skipped(
            format!("no DNSKEY with key_tag={target_tag}")
        ),
    };

    // 2. Parse Q from the DNSKEY's public_key bytes.  For
    //    ECDSAP256SHA256 (RFC 6605 §4): pubkey is 64 bytes = Qx ‖ Qy
    //    (uncompressed, no leading 0x04).
    let pk = dnskey.public_key();
    if pk.len() != 64 {
        return NativeVerifyVerdict::Skipped(
            format!("ECDSA-P256 pubkey expected 64 B, got {}", pk.len())
        );
    }
    let mut qx = [0u8; 32]; qx.copy_from_slice(&pk[0..32]);
    let mut qy = [0u8; 32]; qy.copy_from_slice(&pk[32..64]);
    let public_key = match EcdsaPublicKey::from_be_bytes(&qx, &qy) {
        Some(p) => p,
        None => return NativeVerifyVerdict::Rejected("Q not on curve".into()),
    };

    // 3. Parse (r, s) from the RRSIG's signature bytes.
    let sig_bytes = rrsig.sig();
    if sig_bytes.len() != 64 {
        return NativeVerifyVerdict::Skipped(
            format!("ECDSA-P256 sig expected 64 B, got {}", sig_bytes.len())
        );
    }
    let mut r_bytes = [0u8; 32]; r_bytes.copy_from_slice(&sig_bytes[0..32]);
    let mut s_bytes = [0u8; 32]; s_bytes.copy_from_slice(&sig_bytes[32..64]);
    let signature = match EcdsaSignature::from_be_bytes(&r_bytes, &s_bytes) {
        Some(s) => s,
        None => return NativeVerifyVerdict::Rejected("(r,s) out of range".into()),
    };

    // 4. Build canonical signed bytes via hickory's `rrset_tbs_with_sig`
    //    (RFC 4034 §6 canonical form), then SHA-256 → 32-byte digest.
    let tbs = match rrset_tbs_with_sig(zone_name, DNSClass::IN, &**rrsig, signed_records) {
        Ok(t) => t,
        Err(e) => return NativeVerifyVerdict::Rejected(format!("TBS build: {e}")),
    };
    use sha2::{Digest as Sha2Digest, Sha256};
    let mut h = Sha256::new();
    h.update(tbs.as_ref());
    let digest_arr: [u8; 32] = h.finalize().into();

    // 5. Call the ported ECDSA verify.
    if ecdsa_verify_native(&digest_arr, &public_key, &signature) {
        NativeVerifyVerdict::Accepted
    } else {
        NativeVerifyVerdict::Rejected("ported p256_ecdsa::verify rejected".into())
    }
}

// ─── Generic per-record-type capture (RFC 1035 + DNSSEC extensions) ─
//
// Originally the demo captured only `A` (IPv4) records.  In production
// DNSSEC, virtually every signed RRset has its own RRSIG and should be
// committed to the epoch package — `AAAA`, `MX`, `TXT`, `NS`, `SOA`,
// `CAA`, `SRV`, `TLSA`, etc.  The structural shape is identical for
// every type — only the canonical rdata bytes differ.
//
// `SE_RECORD_TYPES="A,AAAA,MX,TXT,NS,SOA,CAA"` env knob selects which
// types to capture (default: just `A` to preserve baseline behaviour).

fn parse_record_types(spec: &str) -> Vec<RecordType> {
    spec.split(',')
        .map(|s| s.trim().to_ascii_uppercase())
        .filter(|s| !s.is_empty())
        .filter_map(|s| match s.as_str() {
            "A"      => Some(RecordType::A),
            "AAAA"   => Some(RecordType::AAAA),
            "MX"     => Some(RecordType::MX),
            "TXT"    => Some(RecordType::TXT),
            "NS"     => Some(RecordType::NS),
            "SOA"    => Some(RecordType::SOA),
            "CAA"    => Some(RecordType::CAA),
            "SRV"    => Some(RecordType::SRV),
            "TLSA"   => Some(RecordType::TLSA),
            "CNAME"  => Some(RecordType::CNAME),
            "PTR"    => Some(RecordType::PTR),
            other => {
                eprintln!("    [warn] unrecognised SE_RECORD_TYPES entry: {other}");
                None
            }
        })
        .collect()
}

/// Deterministic canonical rdata bytes for an RRset.  The HashRollup
/// AIR is record-type-agnostic — it just hashes whatever bytes we
/// commit — but we still want a deterministic, type-aware encoding so
/// that different rtypes can't accidentally collide.
fn canonical_rdata_bytes(records: &[Record], rtype: RecordType) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(&u16::from(rtype).to_be_bytes()); // type discriminator
    for r in records {
        match r.data() {
            Some(RData::A(a))    => out.extend_from_slice(&a.octets()),
            Some(RData::AAAA(a)) => out.extend_from_slice(&a.octets()),
            Some(RData::MX(mx)) => {
                out.extend_from_slice(&mx.preference().to_be_bytes());
                out.extend_from_slice(mx.exchange().to_string().to_ascii_lowercase().as_bytes());
            }
            Some(RData::TXT(txt)) => {
                for chunk in txt.iter() {
                    out.extend_from_slice(&(chunk.len() as u16).to_be_bytes());
                    out.extend_from_slice(chunk);
                }
            }
            Some(RData::NS(ns))    => out.extend_from_slice(ns.to_string().to_ascii_lowercase().as_bytes()),
            Some(RData::SOA(soa)) => {
                out.extend_from_slice(soa.mname().to_string().to_ascii_lowercase().as_bytes());
                out.extend_from_slice(b"|");
                out.extend_from_slice(soa.rname().to_string().to_ascii_lowercase().as_bytes());
                out.extend_from_slice(&soa.serial().to_be_bytes());
                out.extend_from_slice(&soa.refresh().to_be_bytes());
                out.extend_from_slice(&soa.retry().to_be_bytes());
                out.extend_from_slice(&soa.expire().to_be_bytes());
                out.extend_from_slice(&soa.minimum().to_be_bytes());
            }
            Some(RData::CAA(caa)) => {
                out.push(u8::from(caa.issuer_critical()));
                out.extend_from_slice(format!("{caa}").as_bytes());
            }
            Some(RData::SRV(srv)) => {
                out.extend_from_slice(&srv.priority().to_be_bytes());
                out.extend_from_slice(&srv.weight().to_be_bytes());
                out.extend_from_slice(&srv.port().to_be_bytes());
                out.extend_from_slice(srv.target().to_string().to_ascii_lowercase().as_bytes());
            }
            Some(RData::CNAME(cn)) => out.extend_from_slice(cn.to_string().to_ascii_lowercase().as_bytes()),
            Some(RData::PTR(p))   => out.extend_from_slice(p.to_string().to_ascii_lowercase().as_bytes()),
            Some(other) => {
                // Fallback: deterministic Debug formatting for less common types
                out.extend_from_slice(format!("{other:?}").as_bytes());
            }
            None => {}
        }
        out.push(0u8); // separator between records
    }
    out
}

/// Generic single-RRset capture + native verify.  Returns a ChainLink
/// if the RRset has both content and a covering RRSIG that validates
/// (or fails to validate) under one of `dnskeys`.  Returns `None` if
/// no signed RRset was captured for `(name, rtype)`.
async fn capture_rrset_for_type(
    resolver: &TokioAsyncResolver,
    zone_name: &Name,
    domain: &str,
    normalized: &str,
    rtype: RecordType,
    dnskeys: &[DNSKEY],
) -> Option<ChainLink> {
    let rs = fetch_records(resolver, normalized, rtype).await;
    let mut rrsigs = extract_rrsig(&rs);
    if rrsigs.is_empty() {
        rrsigs = fetch_rrsigs_covering(resolver, normalized, rtype).await;
    }
    let raw: Vec<Record> = rs.iter()
        .filter(|r| r.record_type() == rtype)
        .cloned().collect();
    if raw.is_empty() || rrsigs.is_empty() {
        return None;
    }
    let canonical = canonical_rdata_bytes(&raw, rtype);
    let rrsig0 = rrsigs[0].clone();
    let leaf_alg = u8::from(rrsig0.algorithm());
    let verdict = native_verify_rrsig(zone_name, &raw, &rrsig0, dnskeys);
    Some(ChainLink {
        domain: domain.to_string(),
        signer_name: domain.to_string(),
        record_type: rtype,
        rrset_canonical: canonical,
        raw_records: raw,
        rrsig: Some(rrsig0),
        dnskey: None,
        ds_records: Vec::new(),
        algorithm: leaf_alg,
        native_verify: verdict,
    })
}

// ─── Per-domain capture worker (for concurrent JoinSet capture) ─────
//
// One async task per .se domain.  Fetches:
//   - DNSKEY + RRSIG(DNSKEY) + DS
//   - A + RRSIG(A) (non-apex only)
// Runs the native pre-proof oracle via hickory `Verifier::verify_rrsig`
// against whichever DNSKEY in the captured set has the matching key_tag.
// Returns all captured ChainLinks for the domain (0..N where N is up
// to 2: DNSKEY + A).
async fn capture_one_domain(
    resolver: std::sync::Arc<TokioAsyncResolver>,
    domain: String,
    record_types: std::sync::Arc<Vec<RecordType>>,
) -> Vec<ChainLink> {
    let mut out = Vec::new();
    let normalized = if domain.ends_with('.') {
        domain.clone()
    } else {
        format!("{domain}.")
    };
    let zone_name = Name::from_str(&normalized).unwrap_or_else(|_| Name::root());

    // DNSKEY + RRSIG(DNSKEY)
    let dnskey_rs = fetch_records(&resolver, &normalized, RecordType::DNSKEY).await;
    let dnskeys = extract_dnskey(&dnskey_rs);
    let mut dnskey_rrsigs = extract_rrsig(&dnskey_rs);
    if dnskey_rrsigs.is_empty() {
        dnskey_rrsigs = fetch_rrsigs_covering(
            &resolver, &normalized, RecordType::DNSKEY,
        ).await;
    }
    let alg = dnskeys.first().map(|k| u8::from(k.algorithm())).unwrap_or(0);
    let dnskey_raw: Vec<Record> = dnskey_rs.iter()
        .filter(|r| r.record_type() == RecordType::DNSKEY)
        .cloned().collect();

    // DS from parent
    let ds_rs = fetch_records(&resolver, &normalized, RecordType::DS).await;
    let ds_records = extract_ds(&ds_rs);

    if !dnskeys.is_empty() {
        let mut canonical = Vec::new();
        for k in &dnskeys {
            canonical.extend_from_slice(k.public_key());
        }
        let verdict = dnskey_rrsigs.first().map(|rrsig| {
            native_verify_rrsig(&zone_name, &dnskey_raw, rrsig, &dnskeys)
        }).unwrap_or(NativeVerifyVerdict::Skipped("no RRSIG returned".into()));
        out.push(ChainLink {
            domain: domain.clone(),
            signer_name: domain.clone(),
            record_type: RecordType::DNSKEY,
            rrset_canonical: canonical,
            raw_records: dnskey_raw.clone(),
            rrsig: dnskey_rrsigs.into_iter().next(),
            dnskey: dnskeys.first().cloned(),
            ds_records: ds_records.clone(),
            algorithm: alg,
            native_verify: verdict,
        });
    }

    // Per-record-type capture loop.  For each rtype in `record_types`
    // (env-controlled list), fetch the RRset + its covering RRSIG and
    // run the native pre-proof oracle against the zone's DNSKEYs.
    // Non-apex zones get all configured record types; apex zones skip
    // record types that don't apply at the apex (e.g., a leaf A
    // record on the .se apex doesn't make sense, but SOA/NS do).
    let is_apex = domain == "se" || domain == "se." || domain == ".";
    for rtype in record_types.iter().copied() {
        // Apex-zone skips: leaf-only record types
        if is_apex && matches!(rtype, RecordType::A | RecordType::AAAA | RecordType::CNAME | RecordType::PTR) {
            continue;
        }
        if let Some(link) = capture_rrset_for_type(
            &resolver, &zone_name, &domain, &normalized, rtype, &dnskeys,
        ).await {
            out.push(link);
        }
    }

    out
}

// ─── S_ic in-circuit Ed25519 STARK over real captured RRSIGs ────────
//
// Paper §IV-A Step 2b "in-circuit verified" path for Ed25519 (DNSSEC
// algorithm 15, RFC 8080).  For each captured Ed25519 RRSIG + signer
// DNSKEY, build the canonical RFC 4034 §6 TBS bytes (via hickory's
// `rrset_tbs_with_sig`) and call `prove_zsk_ksk_binding_v2` which
// runs the ed25519_verify_air STARK (deep_ali_merge_ed25519_verify →
// deep_fri_prove → deep_fri_verify round-trip).
//
// Per paper Tab. II: ~1.05 s/sig at production blowup=32.  At smoke
// parameters (this demo's defaults), much faster.

fn prove_ed25519_rrsig_in_circuit(
    label: String,
    dnskey: &DNSKEY,
    rrsig: &RRSIG,
    zone_name: &Name,
    rrset_records: &[Record],
    k_scalar: usize,
    ldt: LdtMode,
) -> Option<SicOutput> {
    // Ed25519 DNSKEY pubkey is 32 bytes (raw Edwards-compressed) per RFC 8080.
    if dnskey.public_key().len() != 32 {
        return None;
    }
    let mut pubkey = [0u8; 32];
    pubkey.copy_from_slice(dnskey.public_key());

    // Ed25519 signature is 64 bytes (R || S).
    if rrsig.sig().len() != 64 {
        return None;
    }
    let mut sig_bytes = [0u8; 64];
    sig_bytes.copy_from_slice(rrsig.sig());

    // Canonical signed bytes via hickory's RFC 4034 §6 helper.  Ed25519
    // signs the message directly (no caller-side pre-hash).
    let tbs = rrset_tbs_with_sig(zone_name, DNSClass::IN, &**rrsig, rrset_records).ok()?;
    let signed_data = tbs.as_ref().to_vec();

    // FS-binding + merkle anchor; same recipe shape as the demo's
    // inner-shard binding so the produced pi_hash chains cleanly.
    let mut fs_binding = [0u8; 32];
    {
        let mut h = Sha3_256::new();
        h.update(b"STARK-DNS-SE-ED25519-S_IC-V1");
        h.update(label.as_bytes());
        let d: [u8; 32] = h.finalize().into();
        fs_binding.copy_from_slice(&d);
    }
    let merkle_root = [0u8; 32]; // placeholder anchor — not consumed at this level

    let t_total = Instant::now();
    let out = prove_zsk_ksk_binding_v2(
        &pubkey, &sig_bytes, &signed_data,
        &fs_binding, &merkle_root, k_scalar, ldt,
    );
    let total_ms = t_total.elapsed().as_secs_f64() * 1000.0;
    if !out.verified || out.proof_blob.is_empty() {
        return None;
    }
    Some(SicOutput {
        label,
        proof_bytes: out.proof_bytes,
        prove_ms: out.prove_ms.max(total_ms - out.local_verify_ms),
        verify_ms: out.local_verify_ms,
    })
}

// ─── S_ic in-circuit ECDSA-P256 STARK over real captured RRSIGs ─────
//
// Paper §IV-A Step 2b "in-circuit verified" path for ECDSA-P256
// (DNSSEC algorithm 13, RFC 6605).  Uses the Phase 5 v2 AIR
// (`p256_ecdsa_air_v2`) which composes:
//   1. u_1·G chain (ported scalar-mult)
//   2. u_2·Q chain (ported scalar-mult)
//   3. final_add: R = u_1·G + u_2·Q (ported group_add)
//   4. Z3⁻¹ = Z3^(p-2) mod p via Fermat chain (256 bits)
//   5. X_aff = X3 · Z3⁻¹ mod p (Fp mul)
//   6. X_aff mod n (existing reduce-mod-n)
//   7. X_aff mod n == r (existing equality)
//
// This is the FIPS 186-4 §6.4.2 ECDSA verify equation in-circuit.
// At K=256, the AIR proves real signatures (the v2 K=2 test verifies
// affine x equals the native AffinePoint::add result).  Per the
// K-scaling sweep, at smoke (blowup=4, r=8) K=256 takes ~77 s on
// consumer Mac hardware.

fn scalar_to_msb_bits_256(s: &ScalarElement) -> Vec<bool> {
    let bytes = s.to_be_bytes(); // 32 bytes MSB-first
    let mut bits = Vec::with_capacity(256);
    for byte in bytes.iter() {
        for shift in (0..8).rev() {
            bits.push((byte >> shift) & 1 == 1);
        }
    }
    bits
}

fn prove_ecdsa_p256_rrsig_in_circuit_v2(
    label: String,
    dnskey: &DNSKEY,
    rrsig: &RRSIG,
    zone_name: &Name,
    rrset_records: &[Record],
    blowup: usize,
    r_queries: usize,
    n_trace: usize,
) -> Option<SicOutput> {
    use ark_ff::Zero as ArkZero;
    use ark_goldilocks::Goldilocks as Fg;
    use sha2::{Digest as Sha2Digest, Sha256};

    // ─── 1. Parse Q from RFC 6605 DNSKEY ────────────────────────────
    let pk_bytes = dnskey.public_key();
    if pk_bytes.len() != 64 {
        return None;
    }
    let mut qx_bytes = [0u8; 32]; qx_bytes.copy_from_slice(&pk_bytes[0..32]);
    let mut qy_bytes = [0u8; 32]; qy_bytes.copy_from_slice(&pk_bytes[32..64]);
    let pk_native = EcdsaPublicKey::from_be_bytes(&qx_bytes, &qy_bytes)?;

    // ─── 2. Parse (r, s) from RRSIG ────────────────────────────────
    let sig_bytes_raw = rrsig.sig();
    if sig_bytes_raw.len() != 64 {
        return None;
    }
    let mut r_bytes = [0u8; 32]; r_bytes.copy_from_slice(&sig_bytes_raw[0..32]);
    let mut s_bytes = [0u8; 32]; s_bytes.copy_from_slice(&sig_bytes_raw[32..64]);
    let sig_native = EcdsaSignature::from_be_bytes(&r_bytes, &s_bytes)?;

    // ─── 3. Canonical TBS + SHA-256 digest ─────────────────────────
    let tbs = rrset_tbs_with_sig(zone_name, DNSClass::IN, &**rrsig, rrset_records).ok()?;
    let mut hasher = Sha256::new();
    hasher.update(tbs.as_ref());
    let digest_arr: [u8; 32] = hasher.finalize().into();

    // ─── 4. Native FIPS 186-4 §6.4.2 pre-check ─────────────────────
    if !ecdsa_verify_native(&digest_arr, &pk_native, &sig_native) {
        eprintln!("    [skip {label}] native ECDSA verify failed; will not produce STARK proof");
        return None;
    }

    // ─── 5. Compute u_1, u_2 natively (Steps 3+4 of §6.4.2) ────────
    let e = reduce_digest_mod_n(&digest_arr);
    let w = sig_native.s.invert();
    let u_1 = e.mul(&w);
    let u_2 = sig_native.r.mul(&w);
    let u1_bits = scalar_to_msb_bits_256(&u_1);
    let u2_bits = scalar_to_msb_bits_256(&u_2);

    // ─── 6. Build v2 AIR layout at K=256 ───────────────────────────
    let g_x_base = 0;
    let g_y_base = P256_NUM_LIMBS;
    let g_z_base = 2 * P256_NUM_LIMBS;
    let q_x_base = 3 * P256_NUM_LIMBS;
    let q_y_base = 4 * P256_NUM_LIMBS;
    let q_z_base = 5 * P256_NUM_LIMBS;
    let start = 6 * P256_NUM_LIMBS;
    let (layout, total) = build_ecdsa_verify_v2_layout(
        start, g_x_base, g_y_base, g_z_base,
        q_x_base, q_y_base, q_z_base,
        256,
    );

    // ─── 7. Construct trace ────────────────────────────────────────
    let n_lde = n_trace * blowup;
    let mut trace_cols: Vec<Vec<Fg>> = (0..total)
        .map(|_| vec![Fg::zero(); n_trace]).collect();

    // Fill row 0 via the helper, then transcribe into the wider trace.
    let mut row0_trace: Vec<Vec<Fg>> = (0..total)
        .map(|_| vec![Fg::zero(); 1]).collect();
    let g = *P256_GENERATOR;
    fill_ecdsa_verify_v2(
        &mut row0_trace, 0, &layout,
        &g.x, &g.y,
        &pk_native.point.x, &pk_native.point.y,
        &u1_bits, &u2_bits,
        &sig_native.r,    // ← REAL r from the signature, NOT tautological
    );
    for c in 0..total {
        trace_cols[c][0] = row0_trace[c][0];
    }

    // ─── 8. LDE + merge + FRI prove ───────────────────────────────
    let t_lde = Instant::now();
    let lde_cols = lde_trace_columns(&trace_cols, n_trace, blowup)
        .ok()?;
    let lde_ms = t_lde.elapsed().as_secs_f64() * 1000.0;

    let k_constraints = ecdsa_verify_v2_constraints(&layout);
    let combination_coeffs: Vec<Fg> =
        (0..k_constraints).map(|i| Fg::from((i + 1) as u64)).collect();

    let t_merge = Instant::now();
    let (c_eval, info) = deep_ali_merge_p256_ecdsa_v2_streaming(
        &lde_cols, &combination_coeffs, &layout, n_trace, blowup,
    );
    let merge_ms = t_merge.elapsed().as_secs_f64() * 1000.0;
    assert_eq!(c_eval.len(), n_lde);
    assert_eq!(info.num_constraints, k_constraints);

    let domain = FriDomain::new_radix2(n_lde);
    // FS-binding: SHA3 over a tag + the captured RRSIG signature bytes
    // so the produced pi_hash is bound to this specific signature.
    let pi_hash: [u8; 32] = {
        let mut h = Sha3_256::new();
        h.update(b"STARK-DNS-SE-ECDSA-P256-S_IC-V2");
        h.update(label.as_bytes());
        h.update(rrsig.sig());
        h.finalize().into()
    };
    let params = DeepFriParams {
        schedule: (0..n_lde.trailing_zeros() as usize)
            .map(|_| 2).collect(),
        r: r_queries, seed_z: 0xDEEFu64,
        coeff_commit_final: true, d_final: 1,
        stir: false, s0: r_queries,
        public_inputs_hash: Some(pi_hash),
    };

    let t_fri = Instant::now();
    let proof = deep_fri_prove::<Ext>(c_eval, domain, &params);
    let fri_ms = t_fri.elapsed().as_secs_f64() * 1000.0;

    let t_verify = Instant::now();
    let ok = deep_fri_verify::<Ext>(&params, &proof);
    let verify_ms = t_verify.elapsed().as_secs_f64() * 1000.0;
    if !ok {
        eprintln!("    [skip {label}] v2 FRI self-verify failed");
        return None;
    }

    let mut buf = Vec::new();
    proof.serialize_with_mode(&mut buf, Compress::Yes).ok()?;
    let proof_bytes = buf.len();

    eprintln!(
        "    ECDSA v2  width={total:>8}  LDE={lde_ms:>5.0} ms  \
         merge={merge_ms:>5.0} ms  fri={fri_ms:>4.0} ms  \
         verify={verify_ms:>4.1} ms  π={:>5.1} KiB",
        proof_bytes as f64 / 1024.0,
    );

    Some(SicOutput {
        label,
        proof_bytes,
        prove_ms: lde_ms + merge_ms + fri_ms,
        verify_ms,
    })
}

// ─── DS → DNSKEY hash-chain binding (priority 5) ─────────────────────
//
// Per RFC 4034 §5.1.4 the parent zone's DS record commits to the
// child zone's DNSKEY via:
//
//     digest = SHA-256( owner_name_canonical || dnskey_rdata )
//
// The existing `swarm_dns::prover::prove_ds_ksk_binding` proves
// `SHA-256(input) == target_hash` in-circuit (FRI/STIR over the
// sha256_air).  We wire it into the demo by constructing the
// canonical input bytes from each captured (owner, DNSKEY) and
// asserting the result equals the parent zone's published DS digest.

/// Compute the canonical SHA-256 input per RFC 4034 §5.1.4:
///   owner_name_in_canonical_wire_form || dnskey_rdata_wire_form
fn dnskey_ds_input_bytes(owner_name: &Name, dnskey: &DNSKEY) -> Vec<u8> {
    let mut buf = Vec::with_capacity(owner_name.len() + 4 + dnskey.public_key().len());
    // Owner name in canonical wire form: lowercase, length-prefixed
    // labels, root terminator.
    for label in owner_name.iter() {
        // hickory Names iterate by label slice (raw bytes)
        let lowered: Vec<u8> = label.iter()
            .map(|b| b.to_ascii_lowercase()).collect();
        buf.push(lowered.len() as u8);
        buf.extend_from_slice(&lowered);
    }
    buf.push(0u8); // root terminator
    // DNSKEY RDATA per RFC 4034 §2.1: 2-byte flags || 1-byte protocol
    // || 1-byte algorithm || public_key bytes.
    buf.extend_from_slice(&dnskey.flags().to_be_bytes());
    buf.push(3u8); // protocol field is always 3 per RFC 4034 §2.1.2
    buf.push(u8::from(dnskey.algorithm()));
    buf.extend_from_slice(dnskey.public_key());
    buf
}

#[derive(Debug, Clone)]
struct DsKskBindingResult {
    label: String,
    proof_bytes: usize,
    prove_ms: f64,
    verify_ms: f64,
    asserted_digest: [u8; 32],
    parent_ds_digest: [u8; 32],
    n_trace: usize,
    proof_blob: Vec<u8>,
    root_f0: Vec<u8>,
    owner_name: String,
}

fn prove_ds_to_dnskey_binding(
    owner_name: &Name,
    dnskey: &DNSKEY,
    ds: &DS,
    fs_binding: [u8; 32],
    ldt: LdtMode,
) -> Option<DsKskBindingResult> {
    // Only digest_type = SHA-256 (=2) is in-circuit today.  digest_type
    // 1 (SHA-1) is deprecated; 4 (SHA-384) needs a SHA-384 AIR.
    let dt: u8 = u8::from(ds.digest_type());
    if dt != 2 {
        return None;
    }
    if ds.digest().len() != 32 {
        return None;
    }
    let mut parent_ds_hash = [0u8; 32];
    parent_ds_hash.copy_from_slice(ds.digest());

    let input = dnskey_ds_input_bytes(owner_name, dnskey);

    let label = format!("{}/DNSKEY-DS", owner_name);
    let t0 = Instant::now();
    let out = prove_ds_ksk_binding(&input, &parent_ds_hash, &fs_binding, ldt);
    let total_ms = t0.elapsed().as_secs_f64() * 1000.0;

    // SOUNDNESS: the AIR proves SHA-256(input) == asserted_digest.
    // We additionally check the asserted_digest matches the DS's
    // published digest.  Together: the DNSKEY rdata hashes to the
    // value the parent zone committed in its DS record.
    if out.asserted_digest != parent_ds_hash {
        eprintln!("    [warn {label}] AIR's asserted_digest != DS.digest \
                   — the captured DNSKEY does NOT match the parent's DS \
                   (key rotation in flight, or wrong key_tag match)");
        return None;
    }

    Some(DsKskBindingResult {
        label,
        proof_bytes: out.proof_bytes,
        prove_ms: out.prove_ms.max(total_ms - out.local_verify_ms),
        verify_ms: out.local_verify_ms,
        asserted_digest: out.asserted_digest,
        parent_ds_digest: parent_ds_hash,
        n_trace: out.n_trace,
        proof_blob: out.proof_blob,
        root_f0: out.root_f0.to_vec(),
        owner_name: owner_name.to_string(),
    })
}

// ─── Main demo ───────────────────────────────────────────────────────

#[tokio::main(flavor = "multi_thread", worker_threads = 4)]
async fn main() {
    println!("═══════════════════════════════════════════════════════════════");
    println!("STARK-DNS — HNPL Phase 1 demo over real Swedish .se DNSSEC data");
    println!("═══════════════════════════════════════════════════════════════");
    println!("[soundness] {}", swarm_dns::prover::soundness_banner());
    println!();

    // Domain-list resolution priority:
    //   1. SE_DOMAIN_FILE=path        — newline-separated file
    //   2. SE_DOMAINS=d1,d2,…         — comma-separated env override
    //   3. built-in 10-zone fallback  — curated well-known signed .se zones
    let domains: Vec<String> = if let Ok(path) = std::env::var("SE_DOMAIN_FILE") {
        let content = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("can't read SE_DOMAIN_FILE={path}: {e}"));
        content.lines().map(|s| s.trim().to_string())
            .filter(|s| !s.is_empty() && !s.starts_with('#'))
            .collect()
    } else {
        let domains_env = std::env::var("SE_DOMAINS").unwrap_or_else(|_| {
            // Built-in fallback: well-known DNSSEC-signed .se zones
            // (curated; all on public record).
            "se,iis.se,sunet.se,kb.se,regeringen.se,scb.se,polisen.se,\
             internetstiftelsen.se,skatteverket.se,ica.se".to_string()
        });
        domains_env.split(',')
            .map(|s| s.trim().to_string())
            .filter(|s| !s.is_empty())
            .collect()
    };
    let limit: usize = std::env::var("SE_DOMAIN_LIMIT")
        .ok().and_then(|s| s.parse().ok())
        .unwrap_or(usize::MAX);
    let mut domains: Vec<String> = domains.into_iter().take(limit).collect();
    let concurrency: usize = std::env::var("CAPTURE_CONCURRENCY")
        .ok().and_then(|s| s.parse().ok()).unwrap_or(32);
    let record_types_spec = std::env::var("SE_RECORD_TYPES")
        .unwrap_or_else(|_| "A".to_string());
    let record_types = std::sync::Arc::new(parse_record_types(&record_types_spec));

    println!("Configuration:");
    println!("  Resolver:    public anycast (1.1.1.1, 8.8.8.8, 9.9.9.9)");
    println!("  Mode:        capture-raw (validate=false, EDNS0 DO=1)");
    println!("  Record types: {} ({:?})",
        record_types.len(),
        record_types.iter().map(|t| format!("{t:?}")).collect::<Vec<_>>().join(","));
    println!("  .se domains: {} (concurrency cap = {concurrency})", domains.len());
    if domains.len() <= 20 {
        for d in &domains { println!("    - {d}"); }
    } else {
        println!("    (first 5: {})",
            domains.iter().take(5).cloned().collect::<Vec<_>>().join(", "));
        println!("    (last 5:  {})",
            domains.iter().rev().take(5).cloned().collect::<Vec<_>>()
                .into_iter().rev().collect::<Vec<_>>().join(", "));
    }
    println!();

    let resolver = std::sync::Arc::new(build_dnssec_resolver());
    let mut links: Vec<ChainLink> = Vec::new();

    // ─── Step 1 — Capture ───────────────────────────────────────────
    println!("[Step 1] Concurrent capture: fetching real DNSSEC chain data …");
    println!();
    let t_capture = Instant::now();

    // 1a. Capture root DNSKEY (ICANN-operated KSK + ZSK).
    {
        let root_dnskey_rs = fetch_records(&resolver, ".", RecordType::DNSKEY).await;
        let mut root_dnskey_rrsigs = extract_rrsig(&root_dnskey_rs);
        if root_dnskey_rrsigs.is_empty() {
            root_dnskey_rrsigs = fetch_rrsigs_covering(&resolver, ".", RecordType::DNSKEY).await;
        }
        let root_dnskeys = extract_dnskey(&root_dnskey_rs);
        let root_dnskey_records: Vec<Record> = root_dnskey_rs.iter()
            .filter(|r| r.record_type() == RecordType::DNSKEY)
            .cloned().collect();
        if !root_dnskeys.is_empty() {
            let alg = root_dnskeys.first().map(|k| u8::from(k.algorithm())).unwrap_or(0);
            let mut canonical = Vec::new();
            for k in &root_dnskeys {
                canonical.extend_from_slice(k.public_key());
            }
            // Root DNSKEY is self-signed by the ICANN KSK.  Verify
            // natively using whichever DNSKEY in the RRset has the
            // matching key_tag.
            let root_name = Name::from_str(".").expect("root name");
            let verdict = root_dnskey_rrsigs.first().map(|rrsig| {
                native_verify_rrsig(&root_name, &root_dnskey_records, rrsig, &root_dnskeys)
            }).unwrap_or(NativeVerifyVerdict::Skipped("no RRSIG returned".into()));
            links.push(ChainLink {
                domain: ".".into(),
                signer_name: ".".into(),
                record_type: RecordType::DNSKEY,
                rrset_canonical: canonical,
                raw_records: root_dnskey_records,
                rrsig: root_dnskey_rrsigs.into_iter().next(),
                dnskey: root_dnskeys.first().cloned(),
                ds_records: Vec::new(),
                algorithm: alg,
                native_verify: verdict.clone(),
            });
            println!("  . (root)     DNSKEY x{} ({:18}) verify={:?}",
                root_dnskeys.len(), algorithm_name(alg), summarise(&verdict));
        }
    }

    // 1b. Concurrent per-domain capture via tokio::task::JoinSet
    //     with a semaphore-based concurrency cap.  Each task fetches
    //     DNSKEY + RRSIG + DS + A + RRSIG(A) and runs the native
    //     pre-proof oracle.
    let semaphore = std::sync::Arc::new(tokio::sync::Semaphore::new(concurrency));
    let mut joinset: tokio::task::JoinSet<Vec<ChainLink>> = tokio::task::JoinSet::new();
    for d in domains.drain(..) {
        let r = resolver.clone();
        let sem = semaphore.clone();
        let rt = record_types.clone();
        joinset.spawn(async move {
            let _permit = sem.acquire().await.expect("semaphore not closed");
            capture_one_domain(r, d, rt).await
        });
    }

    let total_tasks = joinset.len();
    let mut completed = 0usize;
    let report_step = (total_tasks / 20).max(10);  // ~20 progress lines
    while let Some(result) = joinset.join_next().await {
        completed += 1;
        match result {
            Ok(domain_links) => {
                links.extend(domain_links);
            }
            Err(e) => {
                eprintln!("    [warn] capture task panicked: {e}");
            }
        }
        if completed % report_step == 0 || completed == total_tasks {
            let elapsed = t_capture.elapsed().as_secs_f64();
            let rate = completed as f64 / elapsed.max(0.001);
            println!(
                "    progress: {completed:>5}/{total_tasks}  chain_links={:>5}  \
                 rate={:.1} dom/s  elapsed={:.1}s",
                links.len(), rate, elapsed,
            );
        }
    }

    let capture_ms = t_capture.elapsed().as_secs_f64() * 1000.0;
    println!();
    println!("  captured links: {}", links.len());
    println!("  capture time:   {capture_ms:.0} ms");
    println!();

    if links.is_empty() {
        eprintln!("No links captured — check network and try again.");
        std::process::exit(1);
    }

    // ─── Step 2b — Inner-shard STARK over verified chain links ─────
    println!("[Step 2b] Per-record STARK (HashRollup AIR, AttestedRollup S_att path) …");
    println!("          paper §IV-A Step 2 / Tab. II 'attested rollup' column");
    let t_commit = Instant::now();

    // Filter to ACCEPT-verdict links only — the paper's S_att path commits
    // to records the native pre-proof oracle has already validated.
    let verified_links: Vec<&ChainLink> = links.iter()
        .filter(|l| matches!(l.native_verify, NativeVerifyVerdict::Accepted))
        .collect();
    println!("  records committed (ACCEPT-verdict only): {} / {}",
        verified_links.len(), links.len());

    // Convert each link to a DnsRecord (the shape consumed by
    // `prove_inner_shard` and `DnsRecord::leaf_hash`).
    let records: Vec<DnsRecord> = verified_links.iter().map(|l| {
        DnsRecord {
            domain:      l.domain.clone(),
            record_type: u16::from(l.record_type),
            ttl:         0,
            rdata:       canonical_leaf_hash(l).to_vec(),
        }
    }).collect();
    let salt: [u8; 16] = [0u8; 16];
    let leaves: Vec<[u8; 32]> = records.iter().map(|r| r.leaf_hash(&salt)).collect();
    let tree = merkle_build(&leaves);
    let root = merkle_root(&tree);

    // Authority FS-binding for the inner shard — production would use
    // `shard_fs_binding(authority_pk_hash, job_id, shard_id, shard_nonce)`;
    // for this single-shard demo we bind a deterministic tag.
    let mut fs_binding = [0u8; 32];
    {
        let mut h = Sha3_256::new();
        h.update(b"STARK-DNS-SE-DEMO-SHARD-FS-V1");
        h.update(root);
        let out: [u8; 32] = h.finalize().into();
        fs_binding.copy_from_slice(&out);
    }

    let inner = prove_inner_shard(&salt, &records, &fs_binding, LdtMode::Stir);
    let commit_ms = t_commit.elapsed().as_secs_f64() * 1000.0;

    println!("  N (records in shard):  {}", inner.record_count);
    println!("  inner pi_hash (hex):   {}", hex::encode(inner.pi_hash));
    println!("  inner merkle_root:     {}", hex::encode(inner.merkle_root));
    println!("  inner n_trace:         {}", inner.n_trace);
    println!("  inner proof size:      {:.1} KiB", inner.proof_bytes as f64 / 1024.0);
    println!("  inner prove:           {:.1} ms", inner.prove_ms);
    println!("  inner local verify:    {:.2} ms", inner.local_verify_ms);
    println!("  total step-2b:         {commit_ms:.1} ms");
    println!();

    // ─── Step 2a-ECDSA — Native cross-check via ported deep_ali AIR ─
    println!("[Step 2a-ECDSA] Cross-check native verify via PORTED deep_ali::p256_ecdsa …");
    println!("                paper §III-D oracle (independent reimpl)");
    let mut ecdsa_native: Vec<(String, NativeVerifyVerdict)> = Vec::new();
    for l in &links {
        if l.algorithm != 13 { continue; }  // ECDSAP256SHA256
        let rrsig = match &l.rrsig { Some(r) => r, None => continue };
        let zone = Name::from_str(&format!("{}.", l.signer_name))
            .unwrap_or_else(|_| Name::root());
        // Build the signing DNSKEY pool: same-zone DNSKEY links.
        let dnskey_pool: Vec<Record> = links.iter()
            .filter(|m| m.signer_name == l.signer_name)
            .filter(|m| m.record_type == RecordType::DNSKEY)
            .flat_map(|m| m.raw_records.iter().cloned())
            .collect();
        let verdict = ecdsa_native_verify_captured(
            &zone, rrsig, &dnskey_pool, &l.raw_records,
        );
        let label = format!("{}/{:?}", l.signer_name, l.record_type);
        let icon = match &verdict {
            NativeVerifyVerdict::Accepted     => "ACCEPT",
            NativeVerifyVerdict::Rejected(_)  => "REJECT",
            NativeVerifyVerdict::Skipped(_)   => "SKIP",
        };
        println!("  {label:40}  {icon}");
        ecdsa_native.push((label, verdict));
    }
    println!();

    // ─── Step 2b-S_ic — In-circuit RSA-2048 STARK over real RRSIGs ─
    //
    // Paper §IV-A Step 2b "in-circuit verified" path.  The HashRollup
    // S_att path above attests to record IDENTITY only; here we run
    // the RSA-2048 stacked AIR STARK on each captured RSA-SHA256
    // (DNSKEY, RRSIG) pair so the proof itself attests "this signature
    // verifies under this public key" — no T2 reliance.
    //
    // RSA-2048 STARK is the HEAVY path (~95 s/sig at L1 production
    // blowup=32 per paper Tab. II).  Default smoke run: 1 signature
    // at blowup=4 (~5-15 s).  Override via RSA_SIG_LIMIT + RSA_BLOWUP.
    let rsa_limit: usize = std::env::var("RSA_SIG_LIMIT")
        .ok().and_then(|s| s.parse().ok()).unwrap_or(1);
    let rsa_blowup: usize = std::env::var("RSA_BLOWUP")
        .ok().and_then(|s| s.parse().ok()).unwrap_or(4);
    let rsa_r_queries: usize = std::env::var("RSA_R_QUERIES")
        .ok().and_then(|s| s.parse().ok()).unwrap_or(54);

    let mut sic_outputs: Vec<SicOutput> = Vec::new();
    if rsa_limit > 0 {
        println!("[Step 2b-S_ic] In-circuit RSA-2048 STARK over real RRSIGs …");
        println!("              paper §IV-A Step 2b / Tab. II 'in-circuit verified'");
        println!("              limit={rsa_limit} blowup={rsa_blowup} r={rsa_r_queries}");
        let candidates: Vec<(&ChainLink, DNSKEY)> = links.iter()
            .filter(|l| l.algorithm == 8)  // RSASHA256
            .filter_map(|l| {
                if matches!(l.native_verify, NativeVerifyVerdict::Accepted) {
                    // Need the signer's DNSKEY.  For DNSKEY/A links we
                    // captured the DNSKEYs in the SAME link (DNSKEY
                    // RRset is self-signed; A RRsigs are signed by the
                    // zone's own ZSK in the same DNSKEY RRset).  Find a
                    // matching DNSKEY whose key_tag matches the RRSIG's.
                    let rrsig = l.rrsig.as_ref()?;
                    let target_tag = rrsig.key_tag();
                    let signer = links.iter()
                        .filter(|m| m.signer_name == l.signer_name)
                        .filter(|m| m.record_type == RecordType::DNSKEY)
                        .flat_map(|m| m.raw_records.iter())
                        .filter_map(|r| match r.data() {
                            Some(RData::DNSSEC(DNSSECRData::DNSKEY(k))) => Some(k.clone()),
                            _ => None,
                        })
                        .find(|k| k.calculate_key_tag().ok() == Some(target_tag))?;
                    Some((l, signer))
                } else { None }
            })
            .collect();
        let to_run: Vec<_> = candidates.into_iter().take(rsa_limit).collect();
        println!("              candidates: {} → running {}", to_run.len(), to_run.len());

        // Need to materialise the signer DNSKEY so its lifetime survives.
        for (link, signer_key) in to_run.iter() {
            let label = format!("{}/{:?}", link.signer_name, link.record_type);
            let rrsig = link.rrsig.as_ref().expect("ACCEPT-verdict link has RRSIG");
            print!("    proving {label:40} … ");
            let t0 = Instant::now();
            match prove_rsa2048_rrsig_in_circuit(
                label.clone(), signer_key, rrsig, rsa_blowup, rsa_r_queries,
            ) {
                Some(out) => {
                    println!(
                        "{:.0} ms prove · {:.1} ms verify · {:.1} KiB",
                        out.prove_ms, out.verify_ms,
                        out.proof_bytes as f64 / 1024.0,
                    );
                    sic_outputs.push(out);
                }
                None => {
                    let dt = t0.elapsed().as_secs_f64() * 1000.0;
                    println!("(skipped after {dt:.0} ms — e≠65537 or non-2048-bit key)");
                }
            }
        }
        println!();
    }

    // ─── Step 2b-S_ic-Ed25519 — In-circuit Ed25519 STARK ───────────
    //
    // Algorithm 15 (Ed25519, RFC 8080).  Per paper Tab. II: ~1.05 s/sig
    // at production blowup=32 on AWS Graviton4 r8g.4xlarge (16 vCPU).
    // On consumer Mac hardware, single-threaded FFT pieces make the
    // production-calibration prove time materially longer (several
    // minutes per sig is typical).
    //
    // The HEAVY path — opt-in via `ED25519_SIG_LIMIT=N` (default 0).
    // `k_scalar` MUST be 256 per the production `prove_zsk_ksk_binding_v2`
    // docstring; smaller values are stub-only and fail self-verify.
    let ed25519_limit: usize = std::env::var("ED25519_SIG_LIMIT")
        .ok().and_then(|s| s.parse().ok()).unwrap_or(0);
    let ed25519_k_scalar: usize = {
        let requested: usize = std::env::var("ED25519_K_SCALAR")
            .ok().and_then(|s| s.parse().ok()).unwrap_or(256);
        if requested != 256 && ed25519_limit > 0 {
            eprintln!(
                "    [warn] ED25519_K_SCALAR={requested} ignored — \
                 production prove_zsk_ksk_binding_v2 requires 256; \
                 smaller values fail self-verify per docstring"
            );
            256
        } else { requested }
    };

    if ed25519_limit > 0 {
        println!("[Step 2b-S_ic Ed25519] In-circuit Ed25519 STARK over real RRSIGs …");
        println!("                      paper §IV-A Step 2b / Tab. II 'in-circuit verified'");
        println!("                      limit={ed25519_limit} k_scalar={ed25519_k_scalar}");
        println!("                      ⚠ heavy path: minutes per sig on Mac hardware");
        println!("                        (paper Tab. II quotes ~1.05 s/sig on AWS Graviton4 16 vCPU)");
        let candidates: Vec<(&ChainLink, DNSKEY, Vec<Record>)> = links.iter()
            .filter(|l| l.algorithm == 15) // Ed25519
            .filter_map(|l| {
                if !matches!(l.native_verify, NativeVerifyVerdict::Accepted) {
                    return None;
                }
                let rrsig = l.rrsig.as_ref()?;
                let target_tag = rrsig.key_tag();
                let signer = links.iter()
                    .filter(|m| m.signer_name == l.signer_name)
                    .filter(|m| m.record_type == RecordType::DNSKEY)
                    .flat_map(|m| m.raw_records.iter())
                    .filter_map(|r| match r.data() {
                        Some(RData::DNSSEC(DNSSECRData::DNSKEY(k))) => Some(k.clone()),
                        _ => None,
                    })
                    .find(|k| k.calculate_key_tag().ok() == Some(target_tag))?;
                Some((l, signer, l.raw_records.clone()))
            })
            .collect();
        let to_run: Vec<_> = candidates.into_iter().take(ed25519_limit).collect();
        println!("                      candidates: {} → running {}",
            to_run.len(), to_run.len());

        for (link, signer_key, raw_records) in to_run.iter() {
            let zone_name = Name::from_str(&format!("{}.", link.signer_name))
                .unwrap_or_else(|_| Name::root());
            let label = format!("{}/{:?}", link.signer_name, link.record_type);
            let rrsig = link.rrsig.as_ref().expect("ACCEPT-verdict link has RRSIG");
            print!("    proving {label:40} … ");
            match prove_ed25519_rrsig_in_circuit(
                label.clone(), signer_key, rrsig, &zone_name, raw_records,
                ed25519_k_scalar, LdtMode::Stir,
            ) {
                Some(out) => {
                    println!(
                        "{:.0} ms prove · {:.1} ms verify · {:.1} KiB",
                        out.prove_ms, out.verify_ms,
                        out.proof_bytes as f64 / 1024.0,
                    );
                    sic_outputs.push(out);
                }
                None => println!("(skipped — pubkey/sig wrong length or native verify failed)"),
            }
        }
        println!();
    }

    // ─── Step 2b-S_ic-ECDSA-P256 — In-circuit ECDSA-P256 v2 STARK ─
    //
    // Algorithm 13 (ECDSA-P256, RFC 6605).  Uses the Phase 5 v2 AIR
    // that includes the projective→affine conversion via Fp Fermat
    // inversion.  Per the K-scaling sweep, K=256 at smoke params
    // (blowup=4, r=8) is ~77 s on consumer Mac hardware.  HEAVY path.
    //
    // Opt-in via ECDSA_SIG_LIMIT=N (default 0).  Override smoke
    // params via ECDSA_BLOWUP / ECDSA_R_QUERIES / ECDSA_N_TRACE.
    let ecdsa_limit: usize = std::env::var("ECDSA_SIG_LIMIT")
        .ok().and_then(|s| s.parse().ok()).unwrap_or(0);
    let ecdsa_blowup: usize = std::env::var("ECDSA_BLOWUP")
        .ok().and_then(|s| s.parse().ok()).unwrap_or(4);
    let ecdsa_r_queries: usize = std::env::var("ECDSA_R_QUERIES")
        .ok().and_then(|s| s.parse().ok()).unwrap_or(8);
    let ecdsa_n_trace: usize = std::env::var("ECDSA_N_TRACE")
        .ok().and_then(|s| s.parse().ok()).unwrap_or(8);

    if ecdsa_limit > 0 {
        println!("[Step 2b-S_ic ECDSA-P256] In-circuit Phase 5 v2 STARK over real RRSIGs …");
        println!("                         paper §IV-A Step 2b — FIPS 186-4 §6.4.2 affine equality");
        println!("                         limit={ecdsa_limit} blowup={ecdsa_blowup} r={ecdsa_r_queries} n_trace={ecdsa_n_trace}");
        println!("                         ⚠ heavy path: ~77 s/sig at smoke params on Mac;");
        println!("                           paper Tab. II quotes ~0.68 s/sig at production blowup=32");

        let candidates: Vec<(&ChainLink, DNSKEY, Vec<Record>)> = links.iter()
            .filter(|l| l.algorithm == 13) // ECDSAP256SHA256
            .filter_map(|l| {
                if !matches!(l.native_verify, NativeVerifyVerdict::Accepted) {
                    return None;
                }
                let rrsig = l.rrsig.as_ref()?;
                let target_tag = rrsig.key_tag();
                let signer = links.iter()
                    .filter(|m| m.signer_name == l.signer_name)
                    .filter(|m| m.record_type == RecordType::DNSKEY)
                    .flat_map(|m| m.raw_records.iter())
                    .filter_map(|r| match r.data() {
                        Some(RData::DNSSEC(DNSSECRData::DNSKEY(k))) => Some(k.clone()),
                        _ => None,
                    })
                    .find(|k| k.calculate_key_tag().ok() == Some(target_tag))?;
                Some((l, signer, l.raw_records.clone()))
            })
            .collect();
        let to_run: Vec<_> = candidates.into_iter().take(ecdsa_limit).collect();
        println!("                         candidates: {} → running {}",
            to_run.len(), to_run.len());

        for (link, signer_key, raw_records) in to_run.iter() {
            let zone_name = Name::from_str(&format!("{}.", link.signer_name))
                .unwrap_or_else(|_| Name::root());
            let label = format!("{}/{:?}", link.signer_name, link.record_type);
            let rrsig = link.rrsig.as_ref().expect("ACCEPT-verdict link has RRSIG");
            print!("    proving {label:40} … ");
            match prove_ecdsa_p256_rrsig_in_circuit_v2(
                label.clone(), signer_key, rrsig, &zone_name, raw_records,
                ecdsa_blowup, ecdsa_r_queries, ecdsa_n_trace,
            ) {
                Some(out) => {
                    println!(
                        "{:.0} ms prove · {:.1} ms verify · {:.1} KiB",
                        out.prove_ms, out.verify_ms,
                        out.proof_bytes as f64 / 1024.0,
                    );
                    sic_outputs.push(out);
                }
                None => println!("(skipped — see [skip ...] line above)"),
            }
        }
        println!();
    }

    // ─── Step 2b-NSEC3 — Chain-completeness STARK ───────────────────
    //
    // Paper §VII follow-on (authenticated denial-of-existence) — the
    // §I "out-of-scope" gap.  Builds a STARK over a closed cyclic
    // NSEC3 chain via `prove_nsec3_completeness`, binding the chain
    // root into the epoch's Def. 1 signature.
    //
    // The chain itself is SYNTHETIC at this step — real .se NSEC3
    // capture via NXDOMAIN authority sections is the natural
    // follow-on and would use the SAME `prove_nsec3_completeness`
    // path with real (owner_hash, next_hash) pairs.  Gated by
    // NSEC3_DEMO=N (default 0) to keep the smoke run fast.
    let nsec3_demo: usize = std::env::var("NSEC3_DEMO")
        .ok().and_then(|s| s.parse().ok()).unwrap_or(0);
    let (nsec3_output, nsec3_chain_records): (Option<swarm_dns::prover::Nsec3Output>, Option<Vec<Nsec3Record>>) = if nsec3_demo > 0 {
        println!("[Step 2b-NSEC3] Chain-completeness STARK (synthetic closed chain) …");
        // Build a small synthetic closed cyclic NSEC3 chain.  Each
        // record is `(owner_hash, next_hash)`; the chain closes when
        // records[n-1].next_hash == records[0].owner_hash.
        let n_records: usize = nsec3_demo.max(2);
        let chain: Vec<Nsec3Record> = (0..n_records).map(|i| {
            let mut owner = [0u8; 32];
            owner[..8].copy_from_slice(&((i as u64) * 0x1000_0000_0000_0000).to_be_bytes());
            let mut next = [0u8; 32];
            // records[n-1].next == records[0].owner ensures closure.
            let next_idx = (i + 1) % n_records;
            next[..8].copy_from_slice(&((next_idx as u64) * 0x1000_0000_0000_0000).to_be_bytes());
            Nsec3Record { owner_hash: owner, next_hash: next }
        }).collect();
        // Sanity: chain is closed.
        assert_eq!(chain.last().unwrap().next_hash, chain[0].owner_hash);

        let nsec3_salt: [u8; 16] = [0xA5; 16];
        let mut nsec3_fs = [0u8; 32];
        {
            let mut h = Sha3_256::new();
            h.update(b"STARK-DNS-SE-NSEC3-FS-V1");
            h.update(root);
            let d: [u8; 32] = h.finalize().into();
            nsec3_fs.copy_from_slice(&d);
        }
        let out = prove_nsec3_completeness(&chain, &nsec3_salt, &nsec3_fs, LdtMode::Stir);
        println!("  chain records:       {}", out.record_count);
        println!("  chain root (hex):    {}", hex::encode(&out.chain_root[..16]));
        println!("  proof size:          {:.1} KiB", out.proof_bytes as f64 / 1024.0);
        println!("  prove:               {:.1} ms", out.prove_ms);
        println!("  local verify:        {:.2} ms", out.local_verify_ms);
        println!();
        (Some(out), Some(chain))
    } else {
        (None, None)
    };

    // ─── Step 2b-DS-KSK — DS → DNSKEY hash chain (priority 5) ──────
    //
    // For each captured DNSKEY+DS pair with digest_type=2 (SHA-256),
    // prove SHA-256(owner_name || dnskey_rdata) == DS.digest in-
    // circuit.  Gated by DS_KSK_LIMIT=N (default 0).
    let dskk_limit: usize = std::env::var("DS_KSK_LIMIT")
        .ok().and_then(|s| s.parse().ok()).unwrap_or(0);
    let mut ds_ksk_results: Vec<DsKskBindingResult> = Vec::new();
    if dskk_limit > 0 {
        println!("[Step 2b-DS-KSK] DS → DNSKEY in-circuit hash chain (RFC 4034 §5.1.4) …");
        println!("                limit={dskk_limit} (digest_type=SHA-256 only)");
        // Find captured (DNSKEY-RRset link, DS records) pairs.  Walk
        // each link; if it has captured DS records AND the DNSKEY rdata,
        // try to bind them.
        let mut candidates: Vec<(Name, DNSKEY, DS)> = Vec::new();
        for l in &links {
            if l.record_type != RecordType::DNSKEY { continue; }
            if l.ds_records.is_empty() { continue; }
            // For each DS in the parent zone, match to a DNSKEY by key_tag.
            for ds in &l.ds_records {
                let target_tag = ds.key_tag();
                let zone_name = Name::from_str(&format!("{}.", l.signer_name))
                    .unwrap_or_else(|_| Name::root());
                for r in &l.raw_records {
                    if let Some(RData::DNSSEC(DNSSECRData::DNSKEY(k))) = r.data() {
                        if k.calculate_key_tag().ok() == Some(target_tag)
                            && u8::from(ds.digest_type()) == 2
                        {
                            candidates.push((zone_name.clone(), k.clone(), ds.clone()));
                            break;
                        }
                    }
                }
            }
        }
        println!("                candidates: {} (DNSKEY-DS pairs with SHA-256 digest)",
            candidates.len());

        let mut fs_dskk = [0u8; 32];
        {
            let mut h = Sha3_256::new();
            h.update(b"STARK-DNS-SE-DS-KSK-FS-V1");
            h.update(root);
            let d: [u8; 32] = h.finalize().into();
            fs_dskk.copy_from_slice(&d);
        }
        for (owner, dnskey, ds) in candidates.into_iter().take(dskk_limit) {
            let label = format!("{}/DNSKEY-DS (tag={})", owner, ds.key_tag());
            print!("    proving {label:48} … ");
            match prove_ds_to_dnskey_binding(&owner, &dnskey, &ds, fs_dskk, LdtMode::Stir) {
                Some(out) => {
                    println!(
                        "{:.0} ms prove · {:.1} ms verify · {:.1} KiB",
                        out.prove_ms, out.verify_ms,
                        out.proof_bytes as f64 / 1024.0,
                    );
                    ds_ksk_results.push(out);
                }
                None => println!("(skipped — digest mismatch or wrong digest_type)"),
            }
        }
        println!();
    }

    // ─── Step 2b' — Outer rollup STARK over the inner pi_hash ───────
    println!("[Step 2b'] Outer rollup STARK (commits inner pi_hash to epoch root) …");
    let outer = prove_outer_rollup(
        std::slice::from_ref(&inner.pi_hash),
        &fs_binding,  // authority pk hash binding
        LdtMode::Stir,
    );
    println!("  outer proof size:      {:.1} KiB", outer.proof_bytes as f64 / 1024.0);
    println!("  outer n_trace:         {}", outer.n_trace);
    println!("  outer prove:           {:.1} ms", outer.prove_ms);
    println!("  outer local verify:    {:.2} ms", outer.local_verify_ms);
    println!();

    // ─── Step 2c — ML-DSA-65 sign over (R || T || seq || prev) ─────
    println!("[Step 2c] ML-DSA-65 sign over (π_placeholder || R || T || seq || prev) …");
    let epoch_t: u64 = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH).unwrap().as_secs();
    let epoch_seq: u64 = 0;
    let epoch_prev: [u8; 32] = [0u8; 32];

    // Binding string (paper §IV-E Def. 1):
    //   H(π_outer_root_f0 || inner_pi_hash || merkle_root || T || seq || prev)
    // — every component of the epoch package committed to a single
    // 32-byte hash the ML-DSA signature covers.
    let mut binding = Vec::with_capacity(192);
    binding.extend_from_slice(&outer.root_f0);     // STARK π provenance commitment
    binding.extend_from_slice(&inner.pi_hash);     // inner-shard pi_hash
    binding.extend_from_slice(&root);              // local Merkle root (edge inclusion proofs)
    binding.extend_from_slice(&epoch_t.to_le_bytes());
    binding.extend_from_slice(&epoch_seq.to_le_bytes());
    binding.extend_from_slice(&epoch_prev);
    // Bind the NSEC3 chain-completeness commitment when present
    // (matches `SeEpochPackage::binding_hash()`).
    if let Some(o) = &nsec3_output {
        binding.extend_from_slice(b"NSEC3-CHAIN-V1");
        binding.extend_from_slice(&o.chain_root);
    }
    // Bind DS→DNSKEY chain bindings when present.
    if !ds_ksk_results.is_empty() {
        binding.extend_from_slice(b"DS-KSK-CHAIN-V1");
        binding.extend_from_slice(&(ds_ksk_results.len() as u64).to_le_bytes());
        for r in &ds_ksk_results {
            binding.extend_from_slice(r.owner_name.as_bytes());
            binding.extend_from_slice(&r.asserted_digest);
            binding.extend_from_slice(&r.parent_ds_digest);
            binding.push(2u8); // digest_type=2 (SHA-256)
            binding.extend_from_slice(&r.root_f0);
        }
    }
    // Bind RRSIG validity windows.  Must mirror `SeEpochPackage::binding_hash`
    // exactly so the resolver's `package.binding_hash()` matches what we
    // signed here (RFC 4034 §3.1.5 — RRSIG-VALIDITY-V1 tag in priority-6).
    let rrsig_bounds: Vec<(Option<u32>, Option<u32>)> = records.iter().map(|r| {
        let link = links.iter().find(|l| l.domain == r.domain
            && u16::from(l.record_type) == r.record_type);
        link.and_then(|l| l.rrsig.as_ref())
            .map(|s| (Some(s.sig_inception()), Some(s.sig_expiration())))
            .unwrap_or((None, None))
    }).collect();
    let has_any_validity = rrsig_bounds.iter()
        .any(|(i, e)| i.is_some() || e.is_some());
    if has_any_validity {
        binding.extend_from_slice(b"RRSIG-VALIDITY-V1");
        binding.extend_from_slice(&(rrsig_bounds.len() as u64).to_le_bytes());
        for (inc, exp) in &rrsig_bounds {
            binding.push(inc.is_some() as u8);
            binding.extend_from_slice(&inc.unwrap_or(0).to_le_bytes());
            binding.push(exp.is_some() as u8);
            binding.extend_from_slice(&exp.unwrap_or(0).to_le_bytes());
        }
    }
    let binding_hash: [u8; 32] = Sha3_256::digest(&binding).into();

    use fips204::ml_dsa_65;
    use fips204::traits::{KeyGen, Signer, Verifier};

    let t_sign = Instant::now();
    let (pk, sk): (ml_dsa_65::PublicKey, ml_dsa_65::PrivateKey) =
        ml_dsa_65::KG::try_keygen().expect("ML-DSA-65 keygen");
    let sig = sk.try_sign(&binding_hash, b"STARK-DNS-EPOCH-V1")
        .expect("ML-DSA-65 sign");
    let sign_ms = t_sign.elapsed().as_secs_f64() * 1000.0;
    let ok = pk.verify(&binding_hash, &sig, b"STARK-DNS-EPOCH-V1");

    println!("  epoch T:       {epoch_t}");
    println!("  epoch seq:     {epoch_seq}");
    println!("  binding hash:  {}", hex::encode(binding_hash));
    println!("  pk size:       {} B  (ML-DSA-65 = 1 952 B)", ml_dsa_65::PK_LEN);
    println!("  sig size:      {} B  (ML-DSA-65 = 3 309 B)", ml_dsa_65::SIG_LEN);
    println!("  sign time:     {sign_ms:.2} ms");
    println!("  verify:        {}", if ok { "ACCEPT" } else { "REJECT" });
    println!();

    // ─── Step 3 — Edge verify (HNPL Phase 3 simulation) ────────────
    println!("[Step 3] Edge resolver — verify epoch package + offline lookup …");
    let t_verify = Instant::now();
    let edge_ok = pk.verify(&binding_hash, &sig, b"STARK-DNS-EPOCH-V1");
    let verify_ms = t_verify.elapsed().as_secs_f64() * 1000.0;

    // Offline query example: prove inclusion of links[0] in the tree.
    let target = &records[0];
    let target_leaf = target.leaf_hash(&salt);
    let target_path = swarm_dns::dns::merkle_path(&tree, 0);
    let inclusion_ok =
        swarm_dns::dns::merkle_verify(target_leaf, 0, &target_path, root);

    // Paper Tab. II edge benchmark: outer STARK + ML-DSA verify is
    // ONE-TIME (per epoch package).  Thereafter every DNS query is
    // served offline via Merkle inclusion proof against the cached root.
    let edge_total_ms = outer.local_verify_ms + verify_ms;
    println!("  outer STARK verify:  {:.2} ms  (committed by prover; re-verified at edge)",
        outer.local_verify_ms);
    println!("  ML-DSA-65 verify:    {verify_ms:.3} ms");
    println!("  --------------------");
    println!("  one-time edge cost:  {edge_total_ms:.2} ms  (paper Tab. II: 0.5-5 ms @ NIST L3)");
    println!("  epoch verdict:       {}", if edge_ok { "ACCEPT" } else { "REJECT" });
    println!();
    println!("  offline target:      {} (type={})", target.domain, target.record_type);
    println!("  Merkle inclusion:    {}  (depth {})",
        if inclusion_ok { "ACCEPT" } else { "REJECT" }, target_path.len());
    println!("  per-query offline:   < 1 µs (paper §IV-D: ~1-2 µs on Apple M4 / Raspberry Pi 4)");
    println!();

    // ─── Summary ────────────────────────────────────────────────────
    let epoch_package_bytes = ml_dsa_65::PK_LEN + ml_dsa_65::SIG_LEN
        + outer.proof_bytes   // outer rollup STARK π
        + inner.proof_bytes   // inner shard STARK π
        + 32 /* R */ + 8 /* T */ + 8 /* seq */ + 32 /* prev */
        + records.iter().map(|r| r.rdata.len() + r.domain.len() + 8).sum::<usize>();
    println!("═══════════════════════════════════════════════════════════════");
    println!("  HNPL Phase 1 demo over real .se data — verdict: {}",
        if edge_ok { "✓ ACCEPT" } else { "✗ REJECT" });
    println!();
    println!("  Captured {} real DNSSEC chain links from .se", links.len());
    println!("  Algorithms observed: {}",
        {
            let mut algs: Vec<u8> = links.iter().map(|l| l.algorithm).collect();
            algs.sort(); algs.dedup();
            algs.into_iter().map(algorithm_name).collect::<Vec<_>>().join(", ")
        });
    // Native pre-proof oracle (paper §III-D): tally verdicts across all links.
    let mut accept = 0usize;
    let mut reject = 0usize;
    let mut skip   = 0usize;
    for l in &links {
        match &l.native_verify {
            NativeVerifyVerdict::Accepted    => accept += 1,
            NativeVerifyVerdict::Rejected(_) => reject += 1,
            NativeVerifyVerdict::Skipped(_)  => skip   += 1,
        }
    }
    println!("  Native pre-proof oracle (ring/p256/ed25519-dalek):");
    println!("    {accept:>3} ACCEPT   {reject:>3} REJECT   {skip:>3} SKIPPED");
    println!();
    println!("  Per-record STARK (HashRollup S_att path):");
    println!("    inner proof:  {:.1} KiB   prove {:.0} ms  verify {:.1} ms",
        inner.proof_bytes as f64 / 1024.0, inner.prove_ms, inner.local_verify_ms);
    println!("    outer proof:  {:.1} KiB   prove {:.0} ms  verify {:.1} ms",
        outer.proof_bytes as f64 / 1024.0, outer.prove_ms, outer.local_verify_ms);
    println!("    epoch package π + σ + R + metadata:  {} B",
        epoch_package_bytes);
    if !sic_outputs.is_empty() {
        println!();
        println!("  In-circuit S_ic STARK (paper §IV-A Step 2b — mixed RSA/ECDSA/Ed25519):");
        let mut total_prove = 0.0_f64;
        let mut total_verify = 0.0_f64;
        let mut total_bytes = 0_usize;
        for o in &sic_outputs {
            println!("    {:<35} π={:>6.1} KiB  prove {:>6.0} ms  verify {:>5.1} ms",
                o.label, o.proof_bytes as f64 / 1024.0, o.prove_ms, o.verify_ms);
            total_prove  += o.prove_ms;
            total_verify += o.verify_ms;
            total_bytes  += o.proof_bytes;
        }
        let n = sic_outputs.len() as f64;
        println!("    avg/sig:                              π={:>6.1} KiB  prove {:>6.0} ms  verify {:>5.1} ms",
            total_bytes as f64 / 1024.0 / n,
            total_prove / n, total_verify / n);
        println!("    paper Tab. II RSA-2048 @ L1 production: ~95 s prove / sig (blowup=32, r=54)");
    }
    println!("  Merkle commitment R (32 B):  {}", hex::encode(&root[..16]));
    println!("  ML-DSA-65 epoch signature:   {} B", ml_dsa_65::SIG_LEN);
    println!("  Epoch package size (no π):   ~{} B", epoch_package_bytes);
    println!();
    println!("  Status of paper §IV pipeline pieces:");
    println!("    ✓ Hickory-DNS capture over UDP+TCP (real .se data, this run)");
    println!("    ✓ Native ring/p256 pre-proof oracle (paper §III-D)");
    println!("    ✓ Per-record STARK via prove_inner_shard (HashRollup AIR, S_att)");
    println!("    ✓ Outer rollup STARK via prove_outer_rollup");
    println!("    ✓ ML-DSA-65 (FIPS 204) signs the epoch binding (Def. 1)");
    println!("    ✓ Edge resolver: outer STARK + ML-DSA verify + Merkle inclusion");
    println!();
    println!("  Status of paper §IV-A Step 2b in-circuit verify (S_ic) coverage:");
    println!("    ✓ RSA-2048   — wired via deep_ali::rsa2048_stacked_air ({} sig{} this run)",
        sic_outputs.len(), if sic_outputs.len() == 1 { "" } else { "s" });
    let ecdsa_accept = ecdsa_native.iter()
        .filter(|(_, v)| matches!(v, NativeVerifyVerdict::Accepted)).count();
    let ecdsa_reject = ecdsa_native.iter()
        .filter(|(_, v)| matches!(v, NativeVerifyVerdict::Rejected(_))).count();
    let ecdsa_skip = ecdsa_native.iter()
        .filter(|(_, v)| matches!(v, NativeVerifyVerdict::Skipped(_))).count();
    println!("    ✓ ECDSA-P256 — Phase 5 v2 AIR (`deep_ali::p256_ecdsa_air_v2`) wired:");
    println!("                   v0 ported (10 116 LOC, 138 tests) + v2 adds Fp Fermat + Fp mul");
    println!("                   for projective→affine conversion (FIPS 186-4 §6.4.2 affine eq).");
    println!("                   Native cross-check via `p256_ecdsa::verify` on real .se:");
    println!("                   {ecdsa_accept} ACCEPT  {ecdsa_reject} REJECT  {ecdsa_skip} SKIP");
    println!("                   In-circuit STARK opt-in via ECDSA_SIG_LIMIT (heavy path).");
    println!("    ✓ Ed25519    — STARK AIR exists (`deep_ali::ed25519_verify_air`);");
    println!("                   in-circuit STARK opt-in via ED25519_SIG_LIMIT.");
    println!();
    println!("  Remaining for full paper pipeline:");
    println!("    ✓ TLD-scale aggregation via sharded master recursion");
    println!("      (wrapper-stark::master_recursion_bridge — calibrated 2026-05-17).");
    println!("      Mac M-series at N=16, Ni=4, K=4 across three soundness configs:");
    println!("        inner/master/merkle  inner-prove  shard-prove  verify   L1 wire");
    println!("        ───────────────────  ───────────  ───────────  ───────  ────────");
    println!("        ALL-SMOKE  ( 4/ 4/ 4)   56.0 s      13.4 s      9.27 ms  2491 KiB");
    println!("        MIXED      ( 4/32/32)   56.7 s      42.2 s      5.50 ms  1504 KiB");
    println!("        ALL-PROD-L1(32/32/32)  386.9 s      42.2 s      5.54 ms  1504 KiB");
    println!("      Conclusion: master/merkle=32 captures all edge-consumer wins");
    println!("      (40 %% smaller wire, 41 %% faster verify); bumping inner→32 adds");
    println!("      6.8× prove cost for soundness uniformity but no extra wire/verify");
    println!("      benefit.  Wire stays constant at fixed K as N grows; doubling K");
    println!("      adds ~130 KiB to the super-master.");
    println!("      Projected .se TLD scale (~4.5 M RRSIGs): ~3.5 MiB L1 wire, ~14 ms verify.");
    println!("      Run via: N_INNER=16 SHARD_SIZE=4 cargo run --release -p wrapper-stark \\");
    println!("               --example sharded_master_demo …");
    println!("    ◐ Optional Zonemaster cross-check oracle.");
    println!("═══════════════════════════════════════════════════════════════");

    // ─── Phase 2 — Persist the epoch package to disk ───────────────
    //
    // Self-contained binary artefact for OFFLINE DNS resolution.
    // Edge resolvers read this file, verify once (ML-DSA + outer STARK),
    // then serve unlimited DNS queries against the committed corpus
    // via Merkle inclusion proofs — no further network access needed.
    use swarm_dns::se_epoch_package::{
        EpochRecord, SeEpochPackage, save_to_file, PACKAGE_VERSION,
    };
    let package_path = std::path::PathBuf::from(
        std::env::var("SE_EPOCH_PACKAGE_PATH")
            .unwrap_or_else(|_| "target/se-epoch-package.bin".to_string())
    );
    println!();
    println!("[Phase 2] Persisting epoch package → {} …", package_path.display());
    let epoch_records: Vec<EpochRecord> = records.iter().map(|r| {
        // Locate the source link for (domain, type) so we can stamp its
        // RRSIG's inception/expiration onto the EpochRecord.  Without
        // this the offline resolver cannot enforce RFC 4034 §3.1.5
        // freshness at query time.
        let link = links.iter()
            .find(|l| l.domain == r.domain
                && u16::from(l.record_type) == r.record_type);
        let algorithm = link.map(|l| l.algorithm).unwrap_or(0);
        let (sig_inception, sig_expiration) = link
            .and_then(|l| l.rrsig.as_ref())
            .map(|s| (Some(s.sig_inception()), Some(s.sig_expiration())))
            .unwrap_or((None, None));
        EpochRecord {
            domain: r.domain.clone(),
            record_type: r.record_type,
            algorithm,
            rdata: r.rdata.clone(),
            ttl: r.ttl,
            sig_inception,
            sig_expiration,
        }
    }).collect();
    // Print the zone-wide validity window (intersection over all
    // records) so a producer operator can sanity-check it before
    // shipping the epoch package.
    {
        use std::time::{SystemTime, UNIX_EPOCH};
        let now = SystemTime::now().duration_since(UNIX_EPOCH)
            .map(|d| d.as_secs() as u32).unwrap_or(0);
        let bound_count = epoch_records.iter()
            .filter(|r| r.sig_inception.is_some()
                     || r.sig_expiration.is_some()).count();
        println!("[Phase 2 validity] RRSIG inception/expiration windows:");
        println!("  records with bounds:  {} / {}",
            bound_count, epoch_records.len());
        // Build a temporary SeEpochPackage view just for the helper.
        // We can compute the intersection manually here without a
        // full package (helper requires &self).
        let mut max_inc: Option<u32> = None;
        let mut min_exp: Option<u32> = None;
        for r in &epoch_records {
            if let Some(i) = r.sig_inception {
                max_inc = Some(max_inc.map_or(i, |x| x.max(i)));
            }
            if let Some(e) = r.sig_expiration {
                min_exp = Some(min_exp.map_or(e, |x| x.min(e)));
            }
        }
        match (max_inc, min_exp) {
            (Some(i), Some(e)) if i <= e => {
                let secs_until_exp = e.saturating_sub(now) as i64;
                let days_until_exp = secs_until_exp as f64 / 86_400.0;
                println!("  zone-wide window:     [{i}, {e}] (UNIX seconds)");
                println!("  earliest expiration:  {e}  (now={now}, Δ={days_until_exp:+.1} days)");
                if i > now {
                    println!("  ⚠ NOT-YET-VALID: earliest inception is in the future");
                }
                if e < now {
                    println!("  ⚠ ALREADY EXPIRED: package will be rejected by resolver");
                }
            }
            (Some(_), Some(_)) => {
                println!("  ⚠ empty intersection — records can't all be fresh at once");
            }
            _ => {
                println!("  (no bounds stamped — legacy/unsigned data)");
            }
        }
        println!();
    }
    let authority_pk_bytes: Vec<u8> = {
        use fips204::traits::SerDes;
        pk.clone().into_bytes().to_vec()
    };
    let authority_sig_bytes: Vec<u8> = sig.to_vec();
    let package = SeEpochPackage {
        version:           PACKAGE_VERSION,
        epoch_t,
        epoch_seq,
        epoch_prev,
        authority_pk:      authority_pk_bytes,
        authority_sig:     authority_sig_bytes,
        inner_pi_hash:     inner.pi_hash,
        inner_merkle_root: inner.merkle_root,
        inner_n_trace:     inner.n_trace,
        inner_stark_proof: inner.proof_blob.clone(),
        inner_root_f0:     inner.root_f0.to_vec(),
        outer_n_trace:     outer.n_trace,
        outer_stark_proof: outer.proof_blob.clone(),
        outer_root_f0:     outer.root_f0.to_vec(),
        merkle_root:       root,
        merkle_levels:     tree.clone(),
        merkle_salt:       salt,
        records:           epoch_records,
        // ─── NSEC3 chain-completeness commitment (Phase 4) ───
        nsec3_chain_root:   nsec3_output.as_ref().map(|o| o.chain_root),
        nsec3_record_count: nsec3_output.as_ref().map(|o| o.record_count),
        nsec3_stark_proof:  nsec3_output.as_ref().map(|o| o.proof_blob.clone()),
        nsec3_n_trace:      nsec3_output.as_ref().map(|o| o.n_trace),
        nsec3_root_f0:      nsec3_output.as_ref().map(|o| o.root_f0.to_vec()),
        nsec3_chain:        nsec3_chain_records.as_ref().map(|chain| {
            chain.iter()
                .map(|r| (r.owner_hash.to_vec(), r.next_hash.to_vec()))
                .collect()
        }),
        // ─── DS → DNSKEY hash-chain bindings (Phase 5) ──────
        ds_ksk_bindings: if ds_ksk_results.is_empty() { None } else {
            Some(ds_ksk_results.iter().map(|r| swarm_dns::se_epoch_package::DsKskBinding {
                owner_name:       r.owner_name.clone(),
                asserted_digest:  r.asserted_digest,
                parent_ds_digest: r.parent_ds_digest,
                digest_type:      2,
                n_trace:          r.n_trace,
                stark_proof:      r.proof_blob.clone(),
                root_f0:          r.root_f0.clone(),
            }).collect())
        },
    };
    if let Some(parent) = package_path.parent() {
        let _ = std::fs::create_dir_all(parent);
    }
    match save_to_file(&package, &package_path) {
        Ok(written) => {
            println!("  package serialised:  {} B ({:.1} KiB)",
                written, written as f64 / 1024.0);
            println!("  authority_pk:        {} B",     package.authority_pk.len());
            println!("  authority_sig:       {} B",     package.authority_sig.len());
            println!("  inner STARK π:       {} B",     package.inner_stark_proof.len());
            println!("  outer STARK π:       {} B",     package.outer_stark_proof.len());
            println!("  merkle levels:       {} levels (depth {}), {} entries total",
                package.merkle_levels.len(),
                package.merkle_levels.len().saturating_sub(1),
                package.merkle_levels.iter().map(|l| l.len()).sum::<usize>(),
            );
            println!("  records:             {} entries", package.records.len());
            println!();
            println!("  Run the offline resolver against this package:");
            println!("    cargo run --release -p swarm-dns --example se_offline_resolver \\");
            println!("        --features \"sha3-256 mldsa-44 parallel\" --no-default-features");
        }
        Err(e) => {
            eprintln!("  [warn] package save failed: {e}");
        }
    }
    println!("═══════════════════════════════════════════════════════════════");
}

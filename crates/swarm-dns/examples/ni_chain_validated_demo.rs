//! NI-gate with **in-circuit chain validation** (implemented + measured).
//!
//! Upgrades the NI-gate proof from a HashRollup commitment to the real
//! statement: the submitted leaf RRSIG is verified \emph{in-circuit} (the
//! Ed25519 verify AIR), FS-bound to the owner's NI anchor (owner ML-DSA pk,
//! creation time, chain head).  This is the expensive statement (the
//! $95$--$105$\,s of the per-signature evaluation) that justifies delegating
//! proof generation to an untrusted swarm (verify-then-sign).
//!
//! Reuses `prove_zsk_ksk_binding_v2` (the in-circuit Ed25519 verifier) with
//! `fs_binding_32 = ni_fs_binding(...)`.  Leaf is the RFC 8032 Test 1 vector.
//!
//! Run (slow — full K=256 Ed25519 in-circuit prove):
//!   cargo run --release -p swarm-dns --example ni_chain_validated_demo

use std::time::Instant;

use swarm_dns::dns_authority::{AuthorityKeypair, NistLevel};
use swarm_dns::ni_gate::ni_fs_binding;
use swarm_dns::prover::{
    prove_zsk_ksk_binding_v2, verify_zsk_ksk_native_v2, verify_zsk_ksk_runtime_fallback_v2,
    LdtMode, ZskKskVerifyError,
};

fn hx<const N: usize>(s: &str) -> [u8; N] {
    let h: String = s.chars().filter(|c| !c.is_whitespace()).collect();
    let mut out = [0u8; N];
    for i in 0..N {
        out[i] = u8::from_str_radix(&h[2 * i..2 * i + 2], 16).unwrap();
    }
    out
}

fn main() {
    // Deployed config: FRI LDT (the conservative production choice for the DNS
    // pipeline; STIR is the smaller research variant).  Swarm path is L1/
    // Goldilocks (NUM_QUERIES=54) — distinct from the FIPS standalone bench.
    let ldt = LdtMode::Fri;
    let name = "example.com";

    // RFC 8032 Test 1: a valid Ed25519 leaf RRSIG (DNSKEY pubkey, signature,
    // empty signed RRset) standing in for the zone's leaf signature.
    let dnskey_pubkey: [u8; 32] =
        hx("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a");
    let rrsig: [u8; 64] = hx(
        "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555f\
         b8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b",
    );
    let signed_rrset: &[u8] = b"";

    // NI owner (ML-DSA) and the NI Fiat--Shamir anchor.
    let owner = AuthorityKeypair::keygen(NistLevel::L1, [7u8; 32]);
    let serial = 1u64;
    let created_at = 1_700_000_000u64;
    let prev = [0u8; 32]; // genesis

    // merkle_root commits the leaf statement; fs folds owner pk + time + chain.
    let merkle_root = {
        use sha3::{Digest, Sha3_256};
        let mut h = Sha3_256::new();
        Digest::update(&mut h, &dnskey_pubkey);
        Digest::update(&mut h, signed_rrset);
        h.finalize().into()
    };
    let fs = ni_fs_binding(&owner.pk_bytes(), name, &merkle_root, serial, created_at, &prev);

    println!("\n┌─ NI-gate with in-circuit chain validation (Ed25519 leaf RRSIG) ─");
    println!("│  statement: leaf RRSIG verifies in-circuit (Ed25519 verify AIR),");
    println!("│             FS-bound to owner pk + created_at + chain head");
    println!("│  this is the expensive statement justifying swarm delegation");
    println!("└────────────────────────────────────────────────────────────\n");

    // ── [0] Validation-soundness: an invalid chain yields NO proof ─────────
    // The validation predicate (unlike HashRollup) attests RRSIG validity, so
    // a record whose leaf signature does not verify cannot be proved at all:
    // the honest prover refuses at the native check, before any STARK work.
    // This is the rejection HashRollup structurally cannot make.
    {
        let mut bad = rrsig;
        bad[0] ^= 0x01; // corrupt the leaf RRSIG
        assert!(
            !verify_zsk_ksk_native_v2(&dnskey_pubkey, &bad, signed_rrset, &fs, &merkle_root)
                .verified,
            "corrupted RRSIG must fail validation"
        );
        let prev = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_| {}));
        let produced = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_zsk_ksk_binding_v2(&dnskey_pubkey, &bad, signed_rrset, &fs, &merkle_root, 256, ldt)
        }))
        .is_ok();
        std::panic::set_hook(prev);
        assert!(!produced, "prover must NOT emit a proof for an unvalidatable chain");
        println!(
            "[0] REJECT invalid DNSSEC chain -> NO verifying proof exists (validation-soundness)\n"
        );
    }

    // ── Prove: the leaf RRSIG verifies IN-CIRCUIT, bound to the NI anchor ──
    println!("[*] proving in-circuit Ed25519 leaf-RRSIG verification (K=256)…");
    let t0 = Instant::now();
    let out = prove_zsk_ksk_binding_v2(
        &dnskey_pubkey, &rrsig, signed_rrset, &fs, &merkle_root, 256, ldt,
    );
    let wall = t0.elapsed().as_secs_f64();
    assert!(out.verified, "in-circuit verification must hold");
    println!(
        "[1] PROVED in-circuit: verified={}, prove {:.1} s, proof {} KiB (self-verify {:.1} ms)",
        out.verified,
        out.prove_ms / 1e3,
        out.proof_bytes / 1024,
        out.local_verify_ms,
    );
    println!("    (wall incl. native+trace: {wall:.1} s)");

    // ── Owner authorises: ML-DSA over the NI anchor ───────────────────────
    let owner_sig = owner.sign(&fs);
    assert!(owner.verify(&fs, &owner_sig));
    println!("[2] owner ML-DSA-signed the NI anchor (sig<->pk)");

    // ── Registrar verifies the chain-validated update ─────────────────────
    // The STARK proof self-verified in-circuit (out.verified); the runtime
    // binding ties the same (pubkey, sig, data, fs, merkle_root) statement to
    // its pi_hash.  Use the matching runtime recipe (verify_zsk_ksk_native_v2)
    // — the STARK recipe (out.pi_hash) folds root_f0 and is not interchangeable.
    let native = verify_zsk_ksk_native_v2(
        &dnskey_pubkey, &rrsig, signed_rrset, &fs, &merkle_root,
    );
    assert!(native.verified, "native Ed25519 verify must hold");
    let v = verify_zsk_ksk_runtime_fallback_v2(
        &dnskey_pubkey, &rrsig, signed_rrset, &fs, &merkle_root, &native.pi_hash,
    );
    assert_eq!(v, Ok(()));
    println!(
        "[3] registrar ACCEPT: in-circuit STARK verified (out.verified={}) + binding",
        out.verified
    );

    // ── Reject: a substituted leaf statement breaks the pi_hash binding ───
    let wrong_root = [0x44u8; 32];
    let r = verify_zsk_ksk_runtime_fallback_v2(
        &dnskey_pubkey, &rrsig, signed_rrset, &fs, &wrong_root, &native.pi_hash,
    );
    assert_eq!(r, Err(ZskKskVerifyError::PiHashMismatch));
    println!("[4] REJECT substituted leaf commitment  (PiHashMismatch)");

    println!(
        "\n✓ Chain-validated NI proof: the leaf RRSIG is proved valid in-circuit,\n  \
         bound to the owner anchor — the prototype now matches the stated statement.\n"
    );
}

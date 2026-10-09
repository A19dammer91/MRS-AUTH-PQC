<!-- README.md: MRS-AUTH-PQC -->
<div align="center">

[![CI](https://github.com/A19dammer91/MRS-AUTH-PQC/actions/workflows/ci.yml/badge.svg)](https://github.com/A19dammer91/MRS-AUTH-PQC/actions/workflows/ci.yml)
[![Tests](https://img.shields.io/github/actions/workflow/status/A19dammer91/MRS-AUTH-PQC/rust.yml?label=tests&style=flat-square&logo=githubactions&logoColor=white)](https://github.com/A19dammer91/MRS-AUTH-PQC/actions/workflows/rust.yml)
[![Benchmarks](https://img.shields.io/github/actions/workflow/status/A19dammer91/MRS-AUTH-PQC/benchmark.yml?label=benchmarks&style=flat-square&logo=githubactions&logoColor=white)](https://github.com/A19dammer91/MRS-AUTH-PQC/actions/workflows/benchmark.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue?style=flat-square)](LICENSE)
[![Rust](https://img.shields.io/badge/rust-1.70%2B-orange?style=flat-square&logo=rust)](https://www.rust-lang.org)
[![NIST](https://img.shields.io/badge/NIST-FIPS%20203%20%7C%20ML--KEM--1024-informational?style=flat-square)](https://csrc.nist.gov/projects/post-quantum-cryptography)
[![KDF](https://img.shields.io/badge/KDF-framework--native-6f42c1?style=flat-square)](src/crypto/clock.rs)
[![Interactive Demo](https://img.shields.io/badge/demo-security%20game-ff69b4?style=flat-square&logo=googlechrome&logoColor=white)](demo/mrs-auth-security-game.html)

# MRS-AUTH-PQC

### Post-Quantum Authentication with a Framework-Native Clock KDF

> **MRS-AUTH-PQC** is an experimental post-quantum authentication framework. It uses **NIST-standardized ML-KEM-1024** (FIPS 203, IND-CCA2) for confidentiality, and derives its session key from the **structure of the (19,9) Diophantine representation system** that the framework itself is built on.
>
> The key is **not hashed from a seed**. It is **derived from the structure itself**.

**Test suite status:** `cargo test` — **108 passed, 0 failed** (52.22s).

</div>

---

## ⚡ The Innovation

Most cryptographic systems derive their keys the same way: take some entropy, run it through a standard KDF, and out comes a key. HKDF-SHA256 (RFC 5869) is the common choice. It knows nothing about the application. Any bytes would do.

MRS-AUTH-PQC changes this. The session key is derived from the **(19,9) Diophantine structure** the framework is built on. Every step of the derivation is defined by the framework, is visible in the public API, and can be audited independently:

```

Kyber shared secret (256 bits of entropy)
↓
combine_seed(SS ‖ 0x00 ‖ session_id)
↓
N = first 128 bits of SHA-256(seed)          ← structured integer
↓
clock decomposition: N → (D, H, M, S, Ms)    ← bijective, branchless
↓
R(N) = ⌊(⌊N/19⌋ − dr(N)) / 9⌋ + 1            ← closed form, no search
↓
k = SHA-256(seed ‖ "k") mod R(N)             ← representation selector
↓
(A_k, B_k) = (A⁰ + 9k, B⁰ − 19k)             ← direct, no loop
↓
key = SHA-256(structured transcript)         ← single hash pass

```

### Comparison with generic HKDF

| Property | Generic HKDF | MRS-AUTH-PQC Clock KDF |
|---|---|---|
| Domain | Application-agnostic | Framework-native |
| Branches in hot path | 0 | 0 |
| Hash passes | 2 (extract + expand) | 1 |
| Structure visible in API | No | Yes (`ClockKey`) |
| Seed-to-position map | Non-injective | Bijective |
| Audit surface | 32-byte output | N, dr, R(N), k, (A_k, B_k), clock tuple |
| External KDF dependency | RFC 5869 | None |
| Entropy source | Unchanged | Unchanged (Kyber SS) |
| Maximum entropy | 256 bits | 256 bits |

The clock KDF does **not add entropy**. It shapes the entropy that already exists. Its contribution is structure: the key becomes a deterministic, auditable product of the framework rather than the output of an opaque standard primitive.

### The framework in three sentences

1. **A key is not a hash of a seed.** It is a deterministic walk through a mathematically rich structure.
2. **The clock provides the uniqueness.** T ↔ (D, H, M, S, Ms) is a bijection, branchless and audit-free.
3. **The Diophantine ladder provides the richness.** Each N has R(N) representations; the seed selects one, and the full ladder is exposed for verification.

The legacy HKDF-based hybrid KDF is preserved for reference in [`legacy/`](legacy/) and is no longer compiled into the crate. See [`legacy/README.md`](legacy/README.md) for the design rationale and a side-by-side comparison.

---

## Overview

MRS-AUTH-PQC addresses two orthogonal problems in the same framework:

**1. Confidentiality against a quantum adversary.** Handled by ML-KEM-1024 (FIPS 203), the NIST-standardized key-encapsulation mechanism formerly known as Kyber.

**2. Coercion resistance against a physical adversary.** Handled by the combinatorial multiplicity of the (19,9) Diophantine representation system, which provides a witness space in which a coerced user can produce a mathematically valid, structurally indistinguishable alternative credential.

A single protocol, a single key derivation, a single structural foundation.

The witness space is rooted in the equation:

$$\mathbf{N = 19A + 9B}$$

The authentic witness is deterministically derived from a master secret and bound to the user's identity via a cryptographic tag. Every other valid chain in the witness space acts as a valid, structurally equivalent alternative. By recursively nesting this decomposition across **three functional layers**, the framework ensures that a coerced user can safely hand over an alternative witness.

---

## Mathematical Core

The framework compresses the entire Diophantine witness-space parameter calculation into closed-form equations. The full derivations are in the papers; the essentials are:

**Anchor.** `A₀ = dr(N)` — the smallest positive A-value congruent to N modulo 9. Range 1..9, never 0 (Positive Anchor Convention).

**Maximum base.** `B₀ = (N − 19·A₀) / 9`.

**Number of representations.** `R(N) = ⌊B₀ / 19⌋ + 1`.

**The ladder.**
```

A_k = A₀ + 9k
B_k = B₀ − 19k
k = 0, 1, …, R(N) − 1

```

**Frobenius boundary (Positive Anchor).** 162 is the largest N with no representation. From 163 onward, every integer has at least one representation.

**First triangle-valid N.** The sampler's `valid` flag requires a triangle-valid candidate (`dr(B) = dr(2·dr(N))`), which is stricter than mere representability. The first N ≥ 163 satisfying this is **171**.

**Clock decomposition.**
```

T = 86,400,000·D + 3,600,000·H + 60,000·M + 1000·S + Ms

```
A bijection: every T maps to exactly one (D, H, M, S, Ms), and every tuple maps back to exactly one T.

> **Note on the anchor.** Under the Positive Anchor Convention, `A₀ = dr(N)` (range 1..9). An alternative "standard" convention would use `A₀ = N mod 9` (range 0..8), which admits A = 0 and gives Frobenius boundary 143. MRS-AUTH-PQC deliberately chooses the Positive Anchor variant: it makes every representation carry a non-trivial core A ≥ 1, which the deniability construction relies on. The digital root `dr(N) = 1 + ((N−1) mod 9)` is the definition used throughout the codebase, and the Frobenius boundary in this system is 162.

---

## Why (19, 9)

The pair (19, 9) is the smallest pair satisfying `p ≡ 1 (mod q)` for which the row/level structure of the Diophantine system becomes visible. With `m = (p − 1)/q = 2`, every representability row occurs exactly twice in succession, producing the repeated-row structure the witness-space construction depends on.

At `m = 1` (e.g. `10 ≡ 1 mod 9`), level and row coincide, and the structure collapses.

For the full derivation and the clock analogy that motivates the choice, see the papers listed under [Citation](#citation).

---

## Security Properties

| Property | Mechanism | Guarantee |
|---|---|---|
| Confidentiality | ML-KEM-1024 (FIPS 203) | IND-CCA2, NIST Level 5 |
| Key derivation | Framework-native Clock KDF | Branchless, bijective, auditable |
| Coercion-resistance | MRS(19,9) witness ambiguity | Computationally indistinguishable witnesses |
| Forward secrecy | Per-session ephemeral keys | Past sessions safe under long-term key compromise |
| Integrity | AES-256-GCM AEAD | 128-bit authentication tag |
| Timing resistance | `subtle` + constant-time arithmetic | Branch-free comparison and selection |
| Memory safety | `zeroize` + RAII drops | Secrets cleared from RAM on scope exit |

---

## Threat Model

Coercion-resistant cryptography protects against a specific, well-defined threat. MRS-AUTH-PQC is precise about that scope.

MRS-AUTH-PQC is a mathematical descendant of Rubberhose (Assange et al.). Rubberhose achieved plausible deniability by filling a disk with indistinguishable encrypted chaff. MRS-AUTH-PQC moves that haystack from disk space into abstract mathematics: a single small three-layer chain travels with the message, and alternative witnesses are generated on the fly by the Crown Equations sampler.

Under the assumptions in [`DENIABILITY.md`](DENIABILITY.md) and [`WITNESS-INDISTINGUISHABILITY.md`](WITNESS-INDISTINGUISHABILITY.md), an adversary who obtains a witness cannot mathematically prove whether it is authentic or an alternative.

**The guarantee operates at the level of mathematical proof, not psychology.** An attacker who refuses any witness short of a proof that no alternative exists cannot be stopped, because that proof does not exist by design. This is the same limit shared by every deniable scheme, Rubberhose included.

**Verification power is concentrated by design.** `MasterSecret::verify_authenticity` requires the master secret to distinguish `Authentic` from `BindingMismatch`. The public `WitnessSpace::verify_membership` path only ever sees `ValidButUnbound`. Whoever holds the master secret can tell the difference — inherent to centralized verification, not a defect.

The intended deployment holds `master_secret` server-side, ideally in a sealed enclave. Under coercion, the client computes an alternative path using only the public N.

MRS-AUTH-PQC has not undergone independent third-party audit and carries no formal certification. The ML-KEM-1024 component follows NIST FIPS 203; the framework's own coercion-resistance layer is a research construction with EasyCrypt proofs of its abstract model.

---

## Architecture

| Layer | Module | Role |
|---|---|---|
| Foundation | `core::diophantine` | `DiophantinePair`, digital root, triangle condition |
| Foundation | `forest` | `ForestNode`, `ForestBranch`, `rn`, `a0`, `b0`, Frobenius bound |
| Sampler | `sampler::cdf_sampler` | Constant-time 3-layer chain builder |
| Sampler | `sampler::supergrid` | 90/366/2520 temporal transform |
| Crypto | `crypto::clock` | Framework-native Clock KDF + AES-256-GCM |
| Crypto | `crypto::shamir` | Shamir Secret Sharing over GF(2⁸) |
| Security | `security::witness` | Authentic + alternative witness generation |
| Security | `security::witness_supergrid` | Temporal witness authentication |
| Security | `security::timecode` | HMAC-SHA256 temporal barrier |
| Security | `security::merkle` | Merkle commitment and inclusion proofs |
| Orchestration | `framework` | `MrsAuthFramework` top-level API |

The clock KDF imports `rn`, `a0`, `b0` from `forest` so the (19,9) arithmetic has a single source of truth. The `forest` module is pure mathematics with no crypto dependencies.

---

## Project Structure

```

MRS-AUTH-PQC/
├── .github/workflows/
├── Cargo.toml
├── LICENSE
├── README.md
├── DENIABILITY.md
├── WITNESS-INDISTINGUISHABILITY.md
├── Archive/
│   └── MRS_Kyber.ec
├── benches/
│   └── sampler_bench.rs
├── demo/
│   └── mrs-auth-security-game.html
├── docs/
│   ├── research-notes/
│   └── user-manual.md
├── legacy/
│   ├── README.md               
│   └── MRS_AUTH_KEM_Hybrid.ec
├── proofs/
│   ├── MRS_FloorSum.ec
│   ├── MRS_Core.ec
│   ├── MRS_Encoding.ec
│   ├── MRS_Chain.ec
│   ├── MRS_Sampler.ec
│   ├── MRS_Deny.ec
│   ├── MRS_AUTH.ec
│   └── MRS_Honey.ec
└── src/
├── lib.rs
├── framework.rs
├── core/
│   └── diophantine.rs
├── forest/
│   ├── mod.rs
│   ├── primitives.rs
│   ├── node.rs
│   └── branch.rs
├── sampler/
│   ├── mod.rs
│   ├── cdf_sampler.rs
│   └── supergrid.rs
├── crypto/
│   ├── mod.rs
│   ├── clock.rs
│   └── shamir.rs
└── security/
├── mod.rs
├── witness.rs
├── witness_supergrid.rs
├── timecode.rs
└── merkle.rs

```

---

## Installation

**Requirements:** Rust 1.70 or newer.

**From Git:**

```toml
[dependencies]
mrs_auth_pqc = { git = "https://github.com/A19dammer91/MRS-AUTH-PQC", tag = "v2.0.0" }
```

With BigInt support (optional):

```toml
[dependencies]
mrs_auth_pqc = { git = "https://github.com/A19dammer91/MRS-AUTH-PQC", features = ["bigint"] }
```

Local development:

```bash
git clone https://github.com/A19dammer91/MRS-AUTH-PQC.git
cd MRS-AUTH-PQC
cargo build --release
```

---

Quick Start

```rust
use mrs_auth_pqc::MrsAuthFramework;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. Generate an ML-KEM-1024 keypair
    let keypair = MrsAuthFramework::keygen()?;

    // 2. Session parameters
    let session_id = b"session-2026-10-09";
    let nonce = [7u8; 12];
    let associated_data = b"metadata";
    let plaintext = b"Top secret message!";

    // 3. Encrypt (session key derived from the Clock KDF)
    let envelope = MrsAuthFramework::full_encrypt(
        &keypair.public_key,
        session_id,
        &nonce,
        associated_data,
        plaintext,
    )?;

    // 4. Decrypt
    let decrypted = MrsAuthFramework::full_decrypt(
        &keypair.secret_key,
        &envelope,
        session_id,
        &nonce,
        associated_data,
    )?;

    assert_eq!(decrypted, plaintext);
    println!("Round trip successful.");
    Ok(())
}
```

Inspecting the Clock Key

The full structured derivation is exposed for audit:

```rust
use mrs_auth_pqc::crypto::derive_key_from_clock;

let seed = b"any seed bytes, or a Kyber shared secret";
let ck = derive_key_from_clock(seed);

println!("N         = {}", ck.n);
println!("clock     = {:?}", ck.clock);    // (D, H, M, S, Ms)
println!("R(N)      = {}", ck.rn);
println!("k         = {}", ck.k);
println!("(A_k, B_k) = {:?}", ck.ab);
println!("key       = {:02x?}", ck.key);
```

For the full API — MasterSecret, WitnessSpace, ForestNode, Shamir, supergrid — see the module documentation via cargo doc --open.

---

Test Suite & Continuous Integration

Every push runs the full matrix:

· Clock KDF: determinism, avalanche, bijectivity of the decomposition, representation validity.
· Forest: rn matches brute-force count, Frobenius boundary, edge cases (n ∈ {9, 18, 144, 153, 162}).
· Sampler: structural validity of generated chains across all layers; a0 = dr(N); fixed draw count across retries; first triangle-valid N is 171.
· Witness: authenticity binding, session isolation, coercion-resistance statistical tests.
· Shamir: split/recover roundtrips, commitment mismatch, subset recovery.
· At-rest protection: seal/unseal roundtrip, wrong-key rejection.
· Framework: end-to-end encryption/decryption.

```bash
cargo test
cargo test --all-features
cargo fmt -- --check
cargo clippy --all-targets -- -D warnings
cargo bench --bench sampler_bench
```

Current status: cargo test --lib — 108 passed, 0 failed, 52.22s.

---

Formal Verification

All core security properties are machine-verified in EasyCrypt. The proof scripts live in proofs/.

Scope note. These proofs verify properties of the abstract mathematical model. They are not a line-by-line verification of the Rust implementation. Implementation correctness is established through unit and regression tests.

Verification order. The .ec files are verified in dependency order. Each file only require imports files that come before it in this list.

# File Content
00 MRS_FloorSum.ec Floor-sum properties underlying the CDF prefix weights
01 MRS_Core.ec Diophantine algebra, Popoviciu cardinality, Frobenius bound
02 MRS_Encoding.ec Chain-to-bytes encoding for the honey layer
03 MRS_Chain.ec Construction and structural verification of MRS chains
04 MRS_Sampler.ec Weighted CDF sampler correctness and constant-time retry loop
05 MRS_Deny.ec Sampler-level chain-selection indistinguishability
06 MRS_AUTH.ec Temporal barrier, HMAC as PRF (EUF-CMA), forward secrecy
07 MRS_Honey.ec Honey encryption layer IND-CPA, over a generic KDF_Oracle

Benchmarks

```bash
cargo bench --bench sampler_bench
```

The clock KDF cost is dominated by a single SHA-256 pass plus one mod R(N). It runs in well under a microsecond on typical hardware, and its cost is independent of the magnitude of the input seed.

The sampler runs at near-constant time across six orders of magnitude in N (~10⁶ to ~10¹⁸), the expected result of O(1) closed-form sampling.

---

Interactive Demo

An interactive browser visualization of the security proof is available in demo/mrs-auth-security-game.html. It covers the Forest Game, adaptive attacker strategies, per-field histograms, a rolling-accuracy timeline, and a Shamir Secret Sharing walkthrough.

No build step, no server, no external dependency. Open the file directly in any modern browser.

See docs/user-manual.md for a full walkthrough.

---

Papers

· RDSI — Representation, Domain Modelling and Software Implementation. 10.5281/zenodo.23077746
· The 19-9 System: N = 19A + 9B. 10.5281/zenodo.19474707

Background material for the 90/366/2520 transformation lives in docs/research-notes/.

---

Citation

Academic use does not require citation. If you'd like to cite this work anyway:

```bibtex
@misc{elissaoui2026forest,
  title = {The Forest Analogy: Full Specification of the MRS-AUTH Cryptographic Framework},
  author = {Bilal el Issaoui},
  year = {2026},
  doi = {10.5281/zenodo.21852606},
  howpublished = {Zenodo}
}
```

---

Disclaimer

Research Prototype.
MRS-AUTH-PQC is an active research-phase cryptographic framework, built on machine-checked EasyCrypt proofs of its abstract model and a comprehensive test suite for its Rust implementation. It has not undergone independent third-party security audit, formal code review, or red-team penetration testing, and it carries no certification of any kind. Independent review is welcome, and treat production deployment accordingly until that review has happened.

Version 2.0.0 marks the transition from an HKDF-based hybrid KDF to a framework-native clock KDF. It does not indicate a security audit or production readiness.

---

License

Apache-2.0. See LICENSE for details.

# Legacy

Code in this directory is **no longer active** and is **not compiled**.
It is preserved for historical reference and for the paper's comparison section.

See `src/` for the active versions.

## Overview

| File | Replaced by | Reason |
|---|---|---|
| `hybrid_hkdf.rs` | `src/crypto/clock.rs` | HKDF is generic; the clock KDF is framework-native |

## Why the HKDF-based hybrid was replaced

MRS-AUTH v1 derived its session key by mixing the Kyber shared secret with a
serialized `MrsChain` under HKDF-SHA256 (RFC 5869, extract-then-expand). That
worked, but it had three structural problems:

1. **HKDF is generic.** It knows nothing about the (19, 9) Diophantine
   structure, the digital root cycle, or the clock hierarchy. Any bytes would
   do.
2. **The MRS chain was fed in as opaque input.** The framework's own structure
   was flattened to a byte string before being hashed. The richness of the
   ladder was invisible to the KDF.
3. **Two hash passes.** Extract and expand mean two HMAC-SHA256 rounds, plus
   a second invocation for the expand counter.

The clock KDF fixes all three.

## Advantages of the clock-derived key

### 1. Framework-native

The key is derived from the (19, 9) Diophantine structure itself, not from a
generic hash construction. Every step — N, dr(N), R(N), the branch index k,
the pair (A_k, B_k), the clock decomposition (D, H, M, S, Ms) — is defined by
the framework and can be audited independently.

### 2. Branchless

No `if`, no ternary, no loop in the hot path. The clock decomposition is a
fixed sequence of `div` and `mod`. The representation index is computed from
a closed form:

    A⁰ = dr(N)
    B⁰ = (N − 19·A⁰) / 9
    R(N) = ⌊(⌊N/19⌋ − dr(N)) / 9⌋ + 1
    (A_k, B_k) = (A⁰ + 9k, B⁰ − 19k)

All arithmetic. No control flow.

### 3. Deterministic and reproducible

The same seed always produces the same `ClockKey`. Every intermediate value is
exposed in the `ClockKey` struct, so a verifier can recompute the derivation
step by step and confirm the result.

### 4. Richer audit surface

The `ClockKey` struct exposes:

- `n` — the seed-derived integer
- `clock` — the (D, H, M, S, Ms) decomposition
- `rn` — the number of representations of `n`
- `k` — the selected branch
- `ab` — the (A_k, B_k) pair

An auditor sees the entire structure, not just a 32-byte output.

### 5. Bijective seed-to-position mapping

The clock decomposition is a bijection: every `T` maps to exactly one
`(D, H, M, S, Ms)`, and every tuple maps back to exactly one `T`. There is no
collision space to worry about, unlike hash truncation or modulo bias in
generic constructions.

### 6. Single hash pass

One SHA-256 over the structured input, not two. Cheaper, and the mixing step
is explicit rather than hidden behind an extract-then-expand convention.

### 7. No external KDF dependency

HKDF is a standard, and standards are good — but using it means the framework's
security argument is "as secure as HKDF." The clock KDF makes the security
argument self-contained: it depends only on SHA-256, on the correctness of the
clock decomposition, and on the Diophantine ladder.

### 8. Entropy source is unchanged

The 256 bits of entropy still come from the Kyber shared secret. The clock KDF
does not add entropy — it shapes it. The key is bounded by the same 256-bit
input, but its structure is now framework-native instead of generic.

## What the legacy hybrid did well

To be fair, HKDF-SHA256 remains a well-studied construction. It is:

- Standardized (RFC 5869)
- Widely reviewed
- Constant-time in its HMAC core

The clock KDF inherits those properties transitively through SHA-256, and adds
structure that HKDF cannot provide.

## Comparison

| Property | HKDF hybrid (legacy) | Clock KDF (current) |
|---|---|---|
| Domain | Generic | Framework-native |
| Branches in hot path | 0 | 0 |
| Hash passes | 2 | 1 |
| Structure visible | No | Yes (`ClockKey`) |
| Seed-to-position map | Non-injective | Bijective |
| External KDF dependency | Yes (HKDF) | No |
| Entropy source | Kyber SS | Kyber SS |
| Maximum entropy | 256 bits | 256 bits |

## References

- `src/crypto/clock.rs` — the current clock-based KDF
- `src/forest/` — the (19, 9) Diophantine structure
- Paper: *RDSI — Representation, Domain Modelling and Software Implementation*
- Paper: *The Clock [3600, 60, 1] and the (25, 12)-System: A Structural Comparison*

<!-- README.md: MRS-AUTH-PQC -->
<div align="center">

[![CI](https://github.com/A19dammer91/MRS-AUTH-PQC/actions/workflows/ci.yml/badge.svg)](https://github.com/A19dammer91/MRS-AUTH-PQC/actions/workflows/ci.yml)
[![EasyCrypt Proofs](https://github.com/A19dammer91/MRS-AUTH-PQC/actions/workflows/easycrypt.yml/badge.svg)](https://github.com/A19dammer91/MRS-AUTH-PQC/actions/workflows/easycrypt.yml)
[![Tests](https://img.shields.io/github/actions/workflow/status/A19dammer91/MRS-AUTH-PQC/rust.yml?label=tests&style=flat-square&logo=githubactions&logoColor=white)](https://github.com/A19dammer91/MRS-AUTH-PQC/actions/workflows/rust.yml)
[![Benchmarks](https://img.shields.io/github/actions/workflow/status/A19dammer91/MRS-AUTH-PQC/benchmark.yml?label=benchmarks&style=flat-square&logo=githubactions&logoColor=white)](https://github.com/A19dammer91/MRS-AUTH-PQC/actions/workflows/benchmark.yml)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue?style=flat-square)](LICENSE)
[![Rust](https://img.shields.io/badge/rust-1.70%2B-orange?style=flat-square&logo=rust)](https://www.rust-lang.org)
[![NIST](https://img.shields.io/badge/NIST-FIPS%20203%20%7C%20ML--KEM--1024-informational?style=flat-square)](https://csrc.nist.gov/projects/post-quantum-cryptography)
[![KDF](https://img.shields.io/badge/KDF-framework--native-6f42c1?style=flat-square)](src/crypto/clock.rs)
[![Interactive Demo](https://img.shields.io/badge/demo-security%20game-ff69b4?style=flat-square&logo=googlechrome&logoColor=white)](demo/mrs-auth-security-game.html)

# MRS-AUTH-PQC

### A Post-Quantum Cryptographic Framework

*Post-quantum authentication with a framework-native Clock KDF.*

> **MRS-AUTH-PQC** is a post-quantum cryptographic framework. It uses **NIST-standardized ML-KEM-1024** (FIPS 203, IND-CCA2) for confidentiality, and derives its session key from the **structure of the (19, 9) Diophantine representation system** that the framework itself is built on.
>
> The key is **not hashed from a seed**. It is **derived from the structure itself**.

**Status:** `cargo test` — **108 passed, 0 failed** (52.22s) · EasyCrypt — **all 13 proof files compile** (§12)

</div>

---

## What is MRS-AUTH-PQC?

MRS-AUTH-PQC addresses two orthogonal problems in the same framework.

**1. Confidentiality against a quantum adversary.** Handled by ML-KEM-1024 (FIPS 203), the NIST-standardized key-encapsulation mechanism formerly known as Kyber.

**2. Coercion resistance against a physical adversary.** Handled by the combinatorial multiplicity of the (19, 9) Diophantine representation system, which provides a witness space in which a coerced user can produce a mathematically valid, structurally indistinguishable alternative credential.

A single protocol, a single key derivation, a single structural foundation.

Behind both problems is a fact about numbers. Take any integer `N`. For a well-chosen pair `(p, q)`, you can write `N` as

```
N = p · A + q · B
```

in many different ways. When `p` and `q` are chosen so that `p ≡ 1 (mod q)`, those ways are not scattered. They line up. They form **two cycles that interlock** at a fixed ratio:

```
m = (p − 1) / q
```

Version 1 was published as *MRS-Hybride-PQC*. **Version 2.0.0 is no longer hybrid.** The same congruence `p ≡ 1 (mod q)` that organises the numbers (`19 ≡ 1 mod 9`) also organises the clock that the key is derived from (`25 ≡ 1 mod 12`).

This README is written for two kinds of readers at once. If you are mathematically curious, §4 shows you the double cycle with nothing but a table of numbers. If you are an engineer, §§8–19 show you the protocol, the proof, and the code. Both audiences can read both, but neither is required to.

---

## Key Contributions

1. **The double cycle.** Not a tuning knob, not a coincidence: a structural fact that governs which numbers can be written, and in how many ways. §4.
2. **The Positive Anchor Convention.** `A₀ = dr(N)` instead of `N mod 9`. It guarantees `A ≥ 1`, moves the Frobenius boundary from 143 to 162, and gives every representation a non-trivial core. §5.
3. **The fractal ladder ⧊.** The rungs of a representation that share one digital signature, with the signature proved for every rung. §6.1.
4. **A key derived from structure, not from a seed.** The session key is produced by walking the same cycle the framework is built on. No external KDF. §8.
5. **A general theorem with one optimal instance.** The framework works for any admissible `(p, q)`. It uses `(19, 9)` because that is the smallest pair that gives the double cycle on the base-9 anchor the decimal system already uses. §9.
6. **Extensions into 3 and 4 dimensions.** The same structure extends from `19A + 9B = N` to `19A + 9B + 3C = N` and to `19A + 9B + 3C + 3D = N`, without losing its shape. §10.
7. **Deniability proved by a machine.** The property that a coerced user can hand over a valid alternative is verified by EasyCrypt, line by line, with the final assumption eliminated. §11.
8. **Formal verification with a constructive distribution layer.** Every probability distribution used by the framework is built explicitly, not assumed. §12.
9. **A complete, working implementation.** A Rust crate with tests, benchmarks, and an interactive demo. §§17–21.

---

## ⚡ The Clock KDF — at a glance

Most cryptographic systems derive their keys the same way: take some entropy, run it through a standard KDF, and out comes a key. HKDF-SHA256 (RFC 5869) is the common choice. It knows nothing about the application. Any bytes would do.

MRS-AUTH-PQC changes this. The session key is derived from the **(19, 9) Diophantine structure** the framework is built on. Every step of the derivation is defined by the framework, is visible in the public API, and can be audited independently:

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
(A_k, B_k) = (A₀ + 9k, B₀ − 19k)             ← direct, no loop
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

The Clock KDF does **not add entropy**. It shapes the entropy that already exists. Its contribution is structure: the key becomes a deterministic, auditable product of the framework rather than the output of an opaque standard primitive.

### The framework in three sentences

1. **A key is not a hash of a seed.** It is a deterministic walk through a mathematically rich structure.
2. **The clock provides the uniqueness.** `T ↔ (D, H, M, S, Ms)` is a bijection, branchless and audit-friendly.
3. **The Diophantine ladder provides the richness.** Each `N` has `R(N)` representations; the seed selects one, and the full ladder is exposed for verification.

---

## 4. The Double Cycle

This is the heart of the framework. Read this section even if you skip the rest.

### 4.1 A first look — `N = 958`

Take the pair `(p, q) = (19, 9)`. Every integer can be written as `19A + 9B`. For most integers there are several ways. For `N = 958`, there are exactly six:

| k | A = 4 + 9k | B = 98 − 19k | 19·A + 9·B | dr(A) | dr(B) |
|--:|:----------:|:------------:|:----------:|:-----:|:-----:|
| 0 |      4     |       98     |    958     |   4   |   8   |
| 1 |     13     |       79     |    958     |   4   |   7   |
| 2 |     22     |       60     |    958     |   4   |   6   |
| 3 |     31     |       41     |    958     |   4   |   5   |
| 4 |     40     |       22     |    958     |   4   |   4   |
| 5 |     49     |        3     |    958     |   4   |   3   |

Look at the columns.

- The first column moves by **9** each step. Its digital root never changes.
- The second column moves by **−19** each step. Its digital root drops by exactly **1** each step, because `19 ≡ 1 (mod 9)`. This is `p ≡ 1 (mod q)` at work.
- After `q = 9` steps the digital root of `B` has run through a full cycle. Over those 9 steps `A` rises by `q² = 81` and `B` falls by `p·q = 171`, and `171 = m·q² + q = 2·81 + 9`.

Every representation sits on the same two cycles. If you know one, you know them all. And every representation of `958` sits exactly on the intersection of those two cycles. That is what "double cycle" means.

### 4.2 Where `m = 2` comes from

The number `m` is the ratio between the two steps:

```
m = (p − 1) / q = (19 − 1) / 9 = 18 / 9 = 2.
```

It is not chosen. It is forced by the pair. Once you pick `(19, 9)`, you get `m = 2`.

Why does `m` matter? Because it decides **how the pattern repeats**. When you lay out all integers from 0 upward and mark which ones can be written as `19A + 9B`, you see levels. Each level is a block of rows. `m` tells you how many rows long each block is. For `m = 2`, every level lasts two rows. For `m = 1`, every level lasts one row. For `m = 3`, three rows.

The double cycle `m = 2` is the smallest value where the pattern has real texture. At `m = 1`, the structure flattens into a plain staircase.

### 4.3 The same number, a different cycle

Change only `p`. Let `(p, q) = (10, 9)`. Now `m = 1`. The same `N = 958` has **eleven** representations instead of six:

| k | A = 4 + 9k | B = 102 − 10k |
|--:|:----------:|:-------------:|
| 0 |      4     |      102      |
| 1 |     13     |       92      |
| 2 |     22     |       82      |
| 3 |     31     |       72      |
| 4 |     40     |       62      |
| 5 |     49     |       52      |
| 6 |     58     |       42      |
| 7 |     67     |       32      |
| 8 |     76     |       22      |
| 9 |     85     |       12      |
|10 |     94     |        2      |

More representations. But the pattern is flat: one row per level, no repetition, no texture. The richness of the double cycle is gone.

This is the point. **`m = 2` is not just a larger number than `m = 1`. It is a richer shape.**

### 4.4 Why `(19, 9)`

The pair `(19, 9)` is the smallest pair satisfying `p ≡ 1 (mod q)` for which the row/level structure becomes visible. With `m = 2`, every representability row occurs exactly twice in succession, producing the repeated-row structure the witness-space construction depends on.

At `m = 1` (e.g. `10 ≡ 1 mod 9`), level and row coincide, and the structure collapses.

What makes `(19, 9)` special is that it fits the way humans count. Humans count in base 10. Our digits run from 1 to 9, not from 0 to 9. The digital root lives in `{1, …, 9}`. That is our anchor. The pair `(2·9 + 1, 9) = (19, 9)` is the smallest pair `(2q + 1, q)` that sits on the base-9 anchor. Any larger pair would work, but would add nothing.

### 4.5 The same structure, seen two ways

The Clock KDF is not a new invention bolted onto the framework. It is the same structural fact, seen from two angles. Both satisfy `p ≡ 1 (mod q)` and have the same ratio `m = 2`:

| System | Condition | Ratio | Shape |
|--------|-----------|:-----:|-------|
| Numbers | `19 ≡ 1 (mod 9)` | 2 | two 9-cycles |
| Clock | `25 ≡ 1 (mod 12)` | 2 | two 12-cycles |

The Clock KDF walks the numbers. The clock decomposition walks the clock. They are not analogies of each other. They are the same pattern, with different moduli.

---

## 5. The Positive Anchor

Every representation starts at the same anchor. We take it from the digital root of `N`:

```
A₀ = dr(N)
```

where

```
dr(N) = 1 + ((N − 1) mod 9)   ∈  {1, 2, …, 9}.
```

The digital root is the number you get by adding the digits of `N` repeatedly until only one is left. For example:

- `N = 2026`: `2 + 0 + 2 + 6 = 10`, and `1 + 0 = 1`. So `A₀ = 1`.
- `N = 123`: `1 + 2 + 3 = 6`. So `A₀ = 6`.
- `N = 999`: `9 + 9 + 9 = 27`, and `2 + 7 = 9`. So `A₀ = 9`.

Notice the third example. In normal modular arithmetic, `999 mod 9 = 0`. But here we use `9` instead of `0`. In this framework, `0` and `9` are the same value seen from two sides: `0` means "no anchor", `9` means "the anchor is the whole cycle". Because they are the same value, the anchor is **always at least 1**. It never collapses to zero. Two ways to compute it give the same answer: divide by 9 and read the repeating digit, or add the digits until one digit is left. As a congruence: `A₀ ≡ N (mod 9)`.

That matters, because a zero anchor would be a leak: any representation with `A = 0` would reveal itself as different from the rest. Under the Positive Anchor Convention, every representation carries a real, positive `A`, and no representation stands out.

The usual alternative, `A₀ = N mod 9` (range 0..8), admits `A = 0` and gives Frobenius boundary 143. MRS-AUTH-PQC deliberately chooses the Positive Anchor variant, and the digital root `dr(N) = 1 + ((N − 1) mod 9)` is the definition used throughout the codebase.

| Convention | Largest `N` without a representation |
|---|:---:|
| `A ≥ 0` (classical Sylvester: `19·9 − 19 − 9`) | 143 |
| `A ≥ 1` (Positive Anchor) | **162** |

Why `162 = 143 + 19`: writing `A = A′ + 1` turns `N = 19A + 9B` into `N − 19 = 19A′ + 9B`. So `N` is representable with `A ≥ 1` exactly when `N − 19` is representable with `A′ ≥ 0`. The whole pattern shifts by 19.

**162 is the largest integer that cannot be written as `19A + 9B` with `A ≥ 1`.** From 163 onward, every integer can be written at least one way. This is proved in `MRS_Core.ec` (the Frobenius boundary lemma) and confirmed by exhaustive search. The first integer that is also **triangle-valid** (`dr(B) = dr(2·dr(N))`) is **171**.

**In short.** The Positive Anchor Convention uses `dr(N)` rather than `N mod 9`. It guarantees `A ≥ 1`, moves the Frobenius boundary from 143 to 162, and keeps the double cycle visible without truncation.

---

## 6. The Formulas

Everything in the framework comes from a small set of formulas. We write them out plainly.

Throughout, `N` is a positive integer and `(p, q)` is an admissible pair: `gcd(p, q) = 1` and `p ≡ 1 (mod q)`. The digital root is taken modulo `q`: `dr(N) = 1 + ((N − 1) mod q)`. For `q = 9` it is the ordinary digital root.

**The anchor.**
```
dr(N) = 1 + ((N − 1) mod q)
A₀    = dr(N)                 (A₀ ≡ N (mod q))
```

**The base.**
```
B₀   = (N − p·A₀) / q
```

**The number of representations.**
```
R(N) = ⌊ (⌊N/p⌋ − dr(N)) / q ⌋ + 1        (floor-over-floor form)
R(N) = ⌊ B₀ / p ⌋ + 1                     (base form)
```

Both forms are exact and equivalent. For `(19, 9)` and `N = 958`, both give `R(958) = 6`. This matches the count from §4.1. The formula agrees with a brute-force count for every `N` from 163 to 59,999 for `(19, 9)`, and for several other admissible pairs.

**The ladder.** Every representation of `N` is on a single ladder, indexed by `k`:
```
k_max = R(N) − 1
A_k   = A₀ + q·k
B_k   = B₀ − p·k
```

For `(19, 9)` and `N = 958`, `k_max = 5`, and the six pairs in §4.1 are exactly the six values `k = 0, 1, …, 5`.

**The role of `m`.** `m` does not appear in these formulas directly. It governs the deeper pattern: how many rows each level of the sub-Frobenius grid occupies. Level `j` spans the rows

```
d ∈ [(j−1)·m,  j·m − 1]   for j = 1, 2, …, q − 1.
```

That is the structural role of `m`. It is not the count of representations. It is the shape of the pattern.

### 6.1 The Fractal Ladder ⧊

Once the anchor `A₀` is determined, the framework generates the family of representations `(A_k, B_k)` with a fixed step: one rung up changes `A` by +9 and `B` by −19. Along these rungs `dr(A)` never changes, and `dr(B)` drops by exactly 1 per rung (§4.1). Exactly one rung in every nine has the digital root that the triangle condition asks for. Those rungs form the **fractal ladder ⧊**.

As a sequence:

```
F(N) = ( k₀, k₀ + 9, k₀ + 18, …, k_max )
```

where `k₀` is the first valid index and `k_max` is the last. Every element of the sequence is congruent to `k₀` modulo 9, and every element lies within the bounds of the framework.

As a set:

```
F(N) = { k : k₀ ≤ k ≤ k_max  and  k ≡ k₀ (mod 9) }
```

The two notations describe the same object. The sequence shows how the ladder is built: start at `k₀`, add 9 each step, stop at `k_max`. The set shows what the ladder contains: every valid `k` in the range that shares the residue class of `k₀`.

**Why "ladder".** The values rise in fixed steps, like rungs on a ladder. You can only stop at the rungs, never between them. And the rungs are exactly the values where a valid representation of the right signature exists.

**Why "fractal".** The ladder repeats its pattern at every step of 9. Each step is one unit of 9, and each unit produces the same alignment between `A`, `B`, and the digital root. This self-similar structure is what makes the ladder fractal.

**What the ladder produces.** For each `k` in `F(N)`, the pair `(A_k, B_k)` is a valid representation of `N`:

```
A_k = A₀ + 9k
B_k = (N − 19·A_k) / 9
```

**A fixed point.** Stepping from one rung of `F(N)` to the next moves `k` by 9, so `A` changes by 81 and `B` by −171, because `9 · 19 = 171`. The digital root is invariant under this step: subtracting 171 from a number does not change its digital root (`dr_shift_171` in `MRS_AUTH.ec`). That is why the entire ladder carries one digital signature. Every rung, from `k₀` to `k_max`, satisfies

```
19·A + 9·B = N,     dr(A) = dr(N),     dr(B) = dr(2·dr(N)).
```

This is proved as `ladder_signature` in `MRS_AUTH.ec`, together with `ladder_A_step` and `ladder_B_step` (the signature repeats one rung higher) and `ladder_next` (the ladder is closed under the step of 9).

**Two coordinate systems.** `MRS_Core.ec` indexes the representations from `k = 0` with anchor `A₀`. The temporal barrier in `MRS_AUTH.ec` uses the anchor `A = N` and `B′ = −2N`, so its index `k` is negative. It is the same ladder in shifted coordinates.

**Where the ladder is non-empty.** The temporal-barrier ladder is empty for every `N ≤ 3077`, where the sampler returns `None`. For `3078 ≤ N ≤ 4580` it depends on `N`. From `N ≥ 4581` it is non-empty (exhaustive check up to 200,000). `ladder_nonempty` proves it formally for all `N ≥ 4760`. The full family of representations is non-empty for every `N ≥ 163`.

---

## 7. The Palindrome Block Theorem

Below the Frobenius bound, not every integer can be written as `19A + 9B`. Which ones can, and which ones cannot, is not arbitrary. It follows an exact pattern.

Write `N = d·q + r`, where `0 ≤ r < q`. The theorem is short:

> **`N` is representable if and only if `d ≥ m · r`.**

That is it. No search, no enumeration. A single inequality decides. (This is the classical `A ≥ 0` setting, where the bound is `(p − 1)(q − 1) = 144`. Under the Positive Anchor the whole pattern shifts by 19 and the boundary becomes 162, as in §5.)

The pattern this creates is called the **Palindrome Block Theorem** because the blocks look like this. There are `q − 1 = 8` levels below 144. Each level lasts `m = 2` rows. On every row of level `j`, the first `j` numbers are representable and the remaining `q − j` are gaps. So level 1 has one representable and eight gaps. Level 2 has two representables and seven gaps. And so on, up to level 8, which has eight representables and one gap.

The name "palindrome" is descriptive: as you move up through the levels, the pattern grows and then the lower rows vanish in a symmetric way. But the important thing is not the name. It is that the pattern is exact, and it is decided by one inequality.

### 7.1 Comparison of admissible pairs

| `(p, q)` | `m` | Levels `q−1` | Frobenius bound `F = (p−1)(q−1)` | Representable below `F` |
|:--------:|:---:|:------------:|:--------------------------------:|:-----------------------:|
| `(7, 2)`  |  3  |      1       |       6       |            3            |
| `(10, 9)` |  1  |      8       |      72       |           36            |
| `(11, 5)` |  2  |      4       |      40       |           20            |
| `(13, 4)` |  3  |      3       |      36       |           18            |
| `(19, 9)` |  2  |      8       |     144       |           72            |

The table makes the two knobs visible: **`q` sets the number of levels**, and **`m` sets how often each level repeats**.

### 7.2 A new proof of a classical result

The level structure also gives a purely combinatorial proof of the Sylvester genus formula:

```
g = (p − 1)(q − 1) / 2.
```

Level `j` contains `m` rows, each with `j` representables. Summing over all levels gives exactly half the Frobenius bound. Since the sub-Frobenius range has length `(p − 1)(q − 1)`, the number of gaps is also half.

This is a **level-by-level proof**, independent of the usual symmetry argument `N ↔ F − 1 − N`. The theorem holds for every admissible pair `(p, q)`.

---

## 8. The Clock KDF

The Clock KDF is described at a glance in the ⚡ section above. This section fills in the details.

### 8.1 The clock is not a metaphor

The clock decomposition `N → (D, H, M, S, Ms)` is not decoration. It is a **bijection**. Every integer `N` maps to exactly one clock tuple, and every tuple maps back to exactly one integer. The formula is:

```
N = 86,400,000·D + 3,600,000·H + 60,000·M + 1000·S + Ms
```

That is just the number of milliseconds in a day, broken into days, hours, minutes, seconds, and milliseconds. It is a natural encoding, and it is reversible.

The Clock KDF uses it to give the key derivation a **unique input**. Every different seed produces a different clock tuple, and every clock tuple produces a different representation family. The key is the product of that journey.

### 8.2 Why this matters

Hashing a seed produces a key. The key is uniformly random. But it is also **opaque**. You cannot look at the key and see where it came from. You cannot audit the derivation step by step. You cannot check that the framework did what it said it did.

The Clock KDF produces a key that is **structured**. You can print out `N`, the clock tuple, `R(N)`, `k`, and the pair `(A_k, B_k)`, and every one of those is a concrete fact about the derivation. A reviewer can read them and see the whole path from entropy to key.

### 8.3 The legacy KDF

The version-1 framework used an HKDF-based hybrid KDF. It is preserved for reference in [`legacy/`](legacy/) and no longer compiled into the crate. See [`legacy/README.md`](legacy/README.md) for the design rationale and a side-by-side comparison.

---

## 9. The General Theorem

The framework is not specific to `(19, 9)`. It works for any admissible pair. This is written down explicitly in `proofs/MRS_Framework.ec`, where the digital root, the positive anchor, the representation predicate, and the representation count are all defined for **arbitrary** `p` and `q`.

The `(19, 9)` case is the primary instance, not the definition.

So the framework could be built on `(37, 18)`, or on `(199, 99)`, or on any other admissible pair. It chooses `(19, 9)` because it is the one that speaks the same language humans already use: base-9 anchor, `m = 2`, smallest possible.

### 9.1 Scalability for large `N`

The number of representations grows like `R(N) ≈ N / (p·q)`. Exact counts (`A ≥ 1`, `B ≥ 0`), for three pairs that all have `m = 2`:

| `N` | `(19, 9)` | `(37, 18)` | `(199, 99)` |
|---:|---:|---:|---:|
| 10⁴ | 59 | 15 | 1 |
| 10⁵ | 585 | 150 | 5 |
| 10⁶ | 5,848 | 1,501 | 51 |

A larger pair means fewer rungs per `N`, hence less work per number, and a smaller witness space (§11). `(19, 9)` keeps the witness space large for moderate `N`, while the closed formulas keep the cost at O(1) for any `N`.

---

## 10. Extensions into 3 and 4 Dimensions

The 2-dimensional case is `19A + 9B = N`. But there is nothing special about two variables. The same structure extends naturally.

The chain is:

```
(19, 9)         →  19A + 9B = N              (2 dimensions)
(19, 9, 3)      →  19A + 9B + 3C = N         (3 dimensions)
(19, 9, 3, 3)   →  19A + 9B + 3C + 3D = N    (4 dimensions)
```

The numbers come from the pattern of divisors: `1 | 3 | 3 | 9`. Each new dimension divides the previous one by an integer factor. The base is always `19 ≡ 1 (mod 9)`.

The 3-dimensional count `R3(p, q, r; N)` has the same shape as the 2-dimensional count. It has its own anchor, its own ladder, its own floor formula. And it is proved in EasyCrypt, not just stated.

For the primary 3-dimensional case `(19, 9, 3)`, the numbers work out as (counts with `A ≥ 1`):

| `N` | `R3(19, 9, 3; N)` |
|----:|:----------------:|
| 19  | 1                |
| 143 | 18               |
| 958 | 924              |
| 6666 | 43017           |

Every one of those is a **separately proved lemma** in the EasyCrypt development. Not a calculated value, not a claimed value: a machine-verified fact.

The 4-dimensional case follows the same pattern, with the same structure, one dimension up.

Why does this matter? Because the witness space grows with the dimension. In 2D, each integer has `R(N)` representations. In 3D, each integer has many more. Every extra dimension multiplies the alternatives a coerced user can offer, and every one of those alternatives is still structurally indistinguishable from the real one.

The framework does not need the extra dimensions to work. It works in 2D. But the 3D and 4D extensions show that the structure is not a one-off. It is a family. And the family has room to grow.

---

## 11. Deniability

This is the part of the framework that matters most. Read it carefully.

### 11.1 The problem

Imagine a person who carries a cryptographic secret. An adversary captures them and demands the key. The person has two options: refuse, and face the consequences, or hand over the key. If the key is a single object, there is no third option.

MRS-AUTH-PQC provides a third option.

The framework does not produce a single witness. It produces a **family** of witnesses. One of them is the real one, derived from the master secret. The rest are alternatives, indistinguishable from the real one. When coerced, the user can hand over an alternative. Structurally, it is identical to the real thing. Mathematically, it cannot be shown to be fake.

This is called **deniability**. The user can deny that the witness they handed over was the real one, and no one can prove otherwise.

The size of the witness space is `R(N) ≈ N / 171` (§9.1), so for realistic `N` it is large. The Positive Anchor Convention guarantees `A ≥ 1` for every witness, so none of them degenerates into a recognisable special case.

### 11.2 The formal statement

Formalise it as a game. An adversary receives a witness and must decide which of two candidates it is. If they cannot do better than a coin flip, they learn nothing.

The theorem, proved in EasyCrypt, says exactly that. Against **any** adversary, no matter how clever, the probability of distinguishing the witness from an alternative is:

```
Pr[ the adversary guesses correctly ] = 1/2
```

Not "approximately 1/2". Not "1/2 plus a negligible term". Exactly 1/2. No computational assumption. No hardness lemma. Just symmetry.

### 11.3 The proof, in plain terms

The proof has four steps. Each is a small, natural observation.

**Step one.** The adversary always receives the same thing in both cases. This is by construction: when the challenge bit flips, the chains are swapped. The adversary's view is unchanged.

**Step two.** The challenge bit can be sampled at the end instead of the beginning. Because the chain-building has no global state, the order of sampling does not change anything the adversary can observe.

**Step three.** If you flip the challenge bit, the outcome flips. Correct guesses become incorrect, and incorrect become correct. So the probability of success equals the probability of failure.

**Step four.** If the probability of success equals the probability of failure, and the probabilities sum to 1, then both equal 1/2.

That is the whole proof. Four steps. No tricks.

### 11.4 Why this is stronger than it sounds

The property is not assumed. It is not stated as an axiom and left there. It was **an axiom** in an earlier version of the development, and it was **eliminated**. There is now a proof in `MRS_DenyProof.ec` that derives the result from first principles.

The proof is checked by a machine. Not by a reviewer, not by an audit, not by an opinion. By EasyCrypt. A program that either accepts a proof or rejects it. There is no middle ground.

---

## 12. Formal Verification

All core security properties of MRS-AUTH-PQC are formalised in EasyCrypt. The proof scripts live in `proofs/`. They are checked by EasyCrypt (`r2024.09`), and the check runs on every push through the `easycrypt.yml` workflow. SMT goals are discharged through Why3 by Z3, CVC5 and Alt-Ergo.

EasyCrypt is not a tool that helps a human reviewer. It is a **checker**. A proof either compiles or it does not. There is no judgement, no interpretation, no possibility of overlooking a step. Anyone with the same compiler and the same files gets the same answer. That is a stronger form of verification than a written audit, within the scope of what it covers.

### 12.1 Counts per file

`proofs/` holds **13 proof files**, and all 13 compile. Every lemma carries a complete proof.

| File | Lemmas | Axioms |


### 12.2 What each file does

The `.ec` files are verified in dependency order. Each file only imports files that precede it. Here is what each one does.

**`MRS_Framework.ec`** — The general foundation. Defines the digital root for any modulus, the positive anchor, the representation predicate, and the representation count — all for arbitrary admissible `(p, q)`, not just `(19, 9)`. This is where the general `p/q` theorem lives. The file establishes, among other things, that the digital root is congruent to `N` modulo `q` for every positive `q`, that it lies in the range `{1, …, q}`, and that it satisfies the expected behaviour when a multiple of `q` is added. Everything that follows is an instance of what is proved here.

**`MRS_Distr.ec`** — The distribution theory. Every probability distribution used by the framework is defined **constructively**, as an explicit mass function. There are three: a point mass, a convex combination, and a uniform distribution over a range. Each has its basic properties proved directly: the point mass is concentrated on one value, the convex combination is non-negative when the weights are, and the uniform distribution assigns equal mass to every point in range and zero outside. The file also provides a bridge to EasyCrypt's built-in distribution type, so the framework can use the standard sampling operator. Nothing here is assumed — everything is built.

**`MRS_DigitSum.ec`** — The digit-sum trace. Describes what happens when you repeatedly add the digits of a number: the sequence `N, N−9, N−18, …, dr(N)`. The file proves that every step preserves the value modulo 9, that the sequence always decreases by exactly 9, and that it ends at the digital root. It also gives the exact number of steps: `(N − dr(N)) / 9`. This is what makes the digital root a computational object, not just a definition.

**`MRS_FloorSum.ec`** — The prefix-weight specification. Describes mathematically what the Rust function `floor_sum_ct` computes. Three properties are stated and used by the sampler: the weight is zero before a filter threshold, it is monotone in the upper index, and it is positive once the threshold is reached. These three properties are what the binary search in the sampler relies on. The Rust implementation of the same function is exercised by unit tests, so the specification and the code meet at the interface.

**`MRS_Core.ec`** — The instantiation to `(19, 9)`. Fixes the specific values `A₀`, `B₀`, `k_max`. Establishes the Frobenius boundary at 162: the file proves directly that 162 has no representation and that 163 does, and it proves that every integer above 162 has one. It also introduces the representation-sampling module and gives the correctness statement for the basic sampler as a composition of already-proven lemmas — that the pair `(A₀ + 9k, B₀ − 19k)` is a valid representation with matching digital roots, for every `k` in the valid range.

**`MRS_Extensions.ec`** — The 3D and 4D extensions. Extends the framework from the 2-variable case `19A + 9B = N` to the 3-variable case `19A + 9B + 3C = N` and the 4-variable case `19A + 9B + 3C + 3D = N`. The 3-variable count `R3(p, q, r; N)` has the same shape as the 2-variable count: an anchor, a ladder, a floor formula. It is proved here, not assumed. The file also includes several machine-verified numerical examples, so that the formula can be checked against concrete values. The 4-variable count `R4` is stated with the same interface.

**`MRS_Encoding.ec`** — The chain-to-bytes encoder. Provides a single definition of the encoder and its length convention, so that all downstream files use the same encoding. Two properties are stated as interface contracts: that the encoder is injective (distinct chains give distinct byte strings), and that the encoded length matches a declared convention. These are what the honey layer needs to know to reason about position-`j` arguments.

**`MRS_Chain.ec`** — The chain builder. The module `MRSChain` constructs a chain `[N, a₁, b₁, a₂, b₂, a₃, b₃]` by calling the sampler once per layer. Whether a layer uses the triangle-valid sampler or the basic sampler depends on whether the layer index is in a filter list. The file proves that two runs with the same arguments produce the same output — a syntactic equivalence that lets other files reason about the builder without unfolding it.

**`MRS_Sampler.ec`** — The weighted CDF sampler. This file is where the sampler's behaviour is characterised. It defines the layer parameters, the reconstruction of `(A, B)` from the sampled index `t`, the prefix-weight wrapper, the binary search `select_t`, the single-attempt layer, the three-layer attempt, and the retry loop. Each of these has an interface contract that describes what it does. The retry loop is proved to use a **fixed number of draws**, independent of the outcome — that is the constant-time property the Rust implementation realises. The file also characterises the behaviour of the winning attempt as the first successful one in the list, and proves that the sampler produces a correct chain for the root input.

**`MRS_Deny.ec`** — The deniability experiment. Defines the adversary interface `MRSAdversary`, the game `DenyGame`, and the key theorem `deny_success_probability`. At this stage in the development, the theorem is stated as an axiom for modularity: the file sets up the game, and the proof is done elsewhere. The file also proves that the challenge bit is uniform (`mu 0 = mu 1 = 1/2`) and that two runs of the chain builder with the same arguments have the same distribution.

**`MRS_DenyProof.ec`** — The proof of the deniability theorem. This file **eliminates the axiom** stated in `MRS_Deny.ec`. It proceeds in four steps, each an `equiv` or a `byequiv` between two games: first, that the adversary always sees `ch0` regardless of the challenge bit; second, that the challenge bit can be sampled last; third, that flipping the bit flips the outcome; and fourth, that the success probability is exactly `1/2`. The file also proves the losslessness of the sampler modules it depends on. The main lemma `deny_success_probability_proved` has the same statement as the axiom in `MRS_Deny.ec` — it is the same theorem, now with a proof.

**`MRS_AUTH.ec`** — The temporal barrier, the fractal ladder, and zeroize. Five parts.

1. *Digital-root lemmas.* `dr(x + y) = dr(dr(x) + dr(y))` (the digital root behaves like a homomorphism for addition), and invariance of the digital root under subtracting `171 = 9 · 19`.
2. *Time model and fractal list.* A concrete time model (each of four stages costs one step) and the fractal list `{ k : first_k ≤ k ≤ k_max, k ≡ first_k (mod 9) }` with its sampler `duniform_fractal`: membership, bounds, congruence, non-emptiness, losslessness.
3. *The temporal barrier.* The module `TemporalBarrier` returns a representation of `N`, or `None` once the deadline has passed. It proves that nothing but `None` is returned past the deadline, that every returned pair satisfies `19·xa + 9·xb = N` and comes from the fractal list, that when `xb > 0` its digital root is the triangle-valid one, and that two runs under a strict deadline are indistinguishable (both return `None`).
4. *The fractal ladder ⧊.* Every rung carries the same digital signature (`ladder_signature`), the signature repeats one rung higher (`ladder_A_step`, `ladder_B_step`), the ladder is closed under the step of 9 (`ladder_next`), and it is non-empty for `N ≥ 4760` (`ladder_nonempty`).
5. *Zeroize.* A memory-state type with `Valid`, `Cleared` and `Uninitialized` states. Zeroize is idempotent and leaves the attacker with no observation. The Rust-side model `RustTemporalBarrier` is related to it through `refinement_pure` and `refinement_step1`, and `refinement_backward_security` states that an attacker either observes nothing or observes a valid representation with the correct digital-root property. This is the formal content of the `zeroize` mechanism on the Rust side.

**`MRS_Honey.ec`** — The honey layer. Proves that the `M = 5` ciphertext blobs, one of which encrypts the true chain, are indistinguishable from uniform random strings of the same lengths, with advantage at most `M·ε`, where `ε` is the AEAD's advantage against a single challenge query. The proof is a hybrid argument: `Hyb(j)` encrypts the positions below `j` with uniform noise and the others for real, so `Hyb(0)` is the real scheme and `Hyb(M)` is the random one. Each step `Hyb(j) → Hyb(j+1)` is a reduction that makes exactly one challenge query at position `j`, and two procedure equivalences (`red_real_equiv`, `red_rand_equiv`) show that the reduction reproduces the two hybrids exactly. The only assumption is the AEAD security `aead_secure`, declared inside the proof section; it becomes a hypothesis of the main theorem `honey_pseudorandom`.

### 12.3 Scope

The proofs verify the **abstract mathematical model**. The Rust implementation is verified separately by the test suite (see §19). Together they cover the model and the code; each is stated for exactly what it checks.

**What the model proves.**

- The number system: digital-root lemmas, the Positive Anchor Convention, the Frobenius boundary 162, the full family of representations.
- The temporal barrier in partial correctness: every output is a representation, comes from the ladder and carries the triangle signature.
- The fractal ladder: the signature of every rung, step invariance, closure, and non-emptiness for `N ≥ 4760`.
- The zeroize model: cleared state is unobservable.
- Deniability: exact success probability `1/2` (§11).
- The honey layer: pseudorandomness of the `M` blobs under the AEAD assumption, bound `M·ε`.

**What lies outside the model, and where it is covered instead.**

- Timing of the real code is a measurement topic. The model's time is a concrete step count in which `total_steps` is constant; constant-time behaviour of the implementation is covered by the sampler's fixed draw count (§12.2) and by benchmarks (§20).
- The Clock KDF is a design with a Rust implementation and tests (§19).
- Termination, and probability statements about the sampler's distribution over the ladder, are not part of the barrier lemmas, which are statements about what can be returned.
- The honey statement concerns ciphertexts: it contains no decryption, wrong-key behaviour or key derivation, ciphertext lengths remain visible, and the chain generator is abstract.

EasyCrypt does not support every proof technique. Two limitations appear in this development, and both are handled openly:

- **Sampling distribution limitations.** EasyCrypt r2024.09 does not expose enough of the internal structure of some sampling distributions to let the tactic engine discharge certain obligations automatically. Where this happens, the property is stated as an interface contract, with a note explaining what would be needed to prove it. The interface is verified against the Rust implementation by the test suite.
- **Recursive definitions.** EasyCrypt's `op` command does not support recursion. Where a recursively defined object would be natural — like the digit-sum trace — the object is characterised by a small set of mathematical properties instead. These properties fully determine the object, and the rest of the development uses them freely.

These are tool limitations, not gaps in the mathematics. They are documented at the point of use, in the files themselves. The directories `Archive/` and `legacy/` hold earlier files that are not part of the verified set.

### 12.4 How to check it yourself

```bash
git clone https://github.com/A19dammer91/MRS-AUTH-PQC
cd MRS-AUTH-PQC/proofs
for f in MRS_Framework.ec MRS_Distr.ec MRS_DigitSum.ec MRS_FloorSum.ec \
         MRS_Core.ec MRS_Extensions.ec MRS_Encoding.ec MRS_Chain.ec \
         MRS_Sampler.ec MRS_Deny.ec MRS_DenyProof.ec MRS_AUTH.ec \
         MRS_Honey.ec; do
  easycrypt compile -I . "$f" || exit 1
done
```

The `easycrypt.yml` workflow does exactly this on every push. If the badge is green, the proofs compile. If it is not, they do not. There is nothing in between.

---

## 13. Threat Model

Coercion-resistant cryptography protects against a specific, well-defined threat. MRS-AUTH-PQC is precise about its scope.

**The threat.** The adversary has physical access to the user. They can demand the key. They cannot be stopped by any cryptographic primitive. What they can be denied is **proof** that they received the real key.

**The defence.** The user hands over a witness. The witness is mathematically valid. It fits the same structure as the real one. Nothing in the witness reveals that it is an alternative. An adversary who refuses to accept any witness short of a proof that no alternative exists cannot be satisfied, because that proof does not exist by design. This is the same limit shared by every deniable scheme.

**Lineage.** MRS-AUTH-PQC is a mathematical descendant of **Rubberhose** (Assange et al.). Rubberhose achieved plausible deniability by filling a disk with indistinguishable encrypted chaff. MRS-AUTH-PQC moves that haystack from disk space into abstract mathematics. A single small chain travels with the message, and the alternative witnesses are generated on the fly by the Crown Equations sampler.

**Verification power is concentrated by design.** `MasterSecret::verify_authenticity` requires the master secret to distinguish `Authentic` from `BindingMismatch`. The public `WitnessSpace::verify_membership` path only ever sees `ValidButUnbound`. Whoever holds the master secret can tell the difference. This is not a defect. It is inherent to centralised verification.

The intended deployment holds the master secret server-side, ideally in a sealed enclave. Under coercion, the client computes an alternative path using only the public value `N`.

**What this framework does not claim.** MRS-AUTH-PQC has not undergone independent third-party audit. It carries no formal certification. The ML-KEM-1024 component follows NIST FIPS 203; the framework's own coercion-resistance layer is a research construction with EasyCrypt proofs of its abstract model. Independent review is welcome.

---

## 14. Security Properties

| Property | Mechanism | Guarantee |
|---|---|---|
| Confidentiality | ML-KEM-1024 (FIPS 203) | IND-CCA2, NIST Level 5 |
| Key derivation | Framework-native Clock KDF | Branchless, bijective, auditable |
| Coercion resistance | (19, 9) witness ambiguity | Machine-checked 1/2 success probability against any adversary |
| Forward secrecy | Per-session ephemeral keys | Past sessions safe under long-term key compromise |
| Integrity | AES-256-GCM AEAD | 128-bit authentication tag |
| Timing resistance | `subtle` + constant-time arithmetic | Branch-free comparison and selection |
| Memory safety | `zeroize` + RAII drops | Secrets cleared from RAM on scope exit |
| Deniability | Double-cycle witness space | Machine-checked by EasyCrypt |

The rows backed by EasyCrypt are coercion resistance, deniability, the temporal barrier and zeroize model, and the honey layer (§12). The remaining rows come from standardised primitives and from the implementation, and are covered by the test suite and the benchmarks.

---

## 15. Architecture

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

The Clock KDF imports `rn`, `a0`, `b0` from `forest`, so the (19, 9) arithmetic has a single source of truth in the Rust code. The `forest` module is pure mathematics with no cryptographic dependencies.

---

## 16. Repository Structure

```
MRS-AUTH-PQC/
├── .github/workflows/
├── Cargo.toml
├── LICENSE
├── README.md
├── COMPARISON.md
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
│   ├── MRS_DigitSum.ec
│   ├── MRS_Distr.ec
│   ├── MRS_Framework.ec
│   ├── MRS_Core.ec
│   ├── MRS_Extensions.ec
│   ├── MRS_Encoding.ec
│   ├── MRS_Chain.ec
│   ├── MRS_Sampler.ec
│   ├── MRS_Deny.ec
│   ├── MRS_DenyProof.ec
│   ├── MRS_AUTH.ec
│   └── MRS_Honey.ec
├── scripts/
│   └── count_proofs.sh
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

The `proofs/` directory is the source of truth for the security claims. The `src/` directory provides the Rust reference implementation. The `docs/`, `demo/`, `benches/`, `legacy/`, `scripts/` and `Archive/` directories are supporting material.

---

## 17. Installation

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

## 18. Quick Start

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

### 18.1 Inspecting the Clock Key

The full structured derivation is exposed for audit:

```rust
use mrs_auth_pqc::crypto::derive_key_from_clock;

let seed = b"any seed bytes, or a Kyber shared secret";
let ck = derive_key_from_clock(seed);

println!("N          = {}", ck.n);
println!("clock      = {:?}", ck.clock);    // (D, H, M, S, Ms)
println!("R(N)       = {}", ck.rn);
println!("k          = {}", ck.k);
println!("(A_k, B_k) = {:?}", ck.ab);
println!("key        = {:02x?}", ck.key);
```

Every intermediate value of the key derivation is visible. Nothing is hidden. Anyone can inspect the path from seed to key.

For the full API — `MasterSecret`, `WitnessSpace`, `ForestNode`, Shamir, supergrid — see the module documentation via `cargo doc --open`.

---

## 19. Test Suite & Continuous Integration

Every push runs the full matrix.

- **Clock KDF:** determinism, avalanche, bijectivity of the decomposition, representation validity.
- **Forest:** `rn` matches the brute-force count, Frobenius boundary, edge cases at `n = 9, 18, 144, 153, 162`.
- **Sampler:** structural validity of generated chains across all layers; `a0 = dr(N)`; fixed draw count across retries; first triangle-valid `N` is 171.
- **Witness:** authenticity binding, session isolation, coercion-resistance statistical tests.
- **Shamir:** split and recover round-trips, commitment mismatch, subset recovery.
- **At-rest protection:** seal and unseal round-trip, wrong-key rejection.
- **Framework:** end-to-end encryption and decryption.

```bash
cargo test
cargo test --all-features
cargo fmt -- --check
cargo clippy --all-targets -- -D warnings
cargo bench --bench sampler_bench
```

Two checkers, two objects, both running continuously. The Rust suite covers the implementation (108 tests); the EasyCrypt workflow covers the model. Neither substitutes for the other, and neither is a substitute for an independent audit.

---

## 20. Benchmarks

```bash
cargo bench --bench sampler_bench
```

The Clock KDF cost is dominated by a single SHA-256 pass plus one `mod R(N)`. It runs in well under a microsecond on typical hardware, and its cost is independent of the size of the input seed.

The sampler runs at near-constant time across six orders of magnitude in `N`, from roughly 10⁶ to 10¹⁸. That is the expected result of an O(1) closed-form sampling procedure.

---

## 21. Interactive Demo

An interactive browser visualisation of the security proof is available in `demo/mrs-auth-security-game.html`. It covers the Forest Game, adaptive attacker strategies, per-field histograms, a rolling-accuracy timeline, and a Shamir Secret Sharing walkthrough.

No build step. No server. No external dependency. Open the file directly in any modern browser.

See `docs/user-manual.md` for a full walkthrough.

---

## 22. Glossary

| Term | Meaning |
|------|---------|
| **Admissible pair** | A pair `(p, q)` with `gcd(p, q) = 1` and `p ≡ 1 (mod q)`. |
| **`m`** | The double-cycle ratio, `m = (p − 1)/q`. |
| **Digital root `dr(N)`** | The single digit you get by adding the digits of `N` repeatedly. In this framework, it lives in `{1, …, 9}`. |
| **Positive anchor `A₀`** | `A₀ = dr(N)`, written with a subscript. Always at least 1. |
| **Positive Anchor Convention** | `A₀ = dr(N)` (range 1..9) instead of `N mod 9` (range 0..8). Guarantees `A ≥ 1` and puts the Frobenius boundary at 162. |
| **Base `B₀`** | `B₀ = (N − p·A₀)/q`. |
| **Representation** | A pair `(A, B)` such that `p·A + q·B = N`. |
| **Representation ladder** | The sequence `(A₀ + q·k, B₀ − p·k)` for `k = 0, 1, …, k_max`. |
| **Rung** | One element of a ladder; one representation. |
| **Fractal ladder ⧊** | The sequence `k₀, k₀ + 9, k₀ + 18, …, k_max` of valid indices for a representation. Every element is congruent to `k₀` modulo 9, and every rung carries the same digital signature. |
| **Digital signature (of a rung)** | `19A + 9B = N`, `dr(A) = dr(N)`, `dr(B) = dr(2·dr N)`. Identical on every rung of the fractal ladder. |
| **Representation count `R(N)`** | The number of representations. Closed form in §6. |
| **Double cycle** | The interlocking of the `A`-progression (step `q`) and the `B`-progression (step `−p`). |
| **Level** | A block of `m` consecutive rows in the sub-Frobenius grid. |
| **Palindrome Block Theorem** | The closed criterion `d ≥ m·r` for representability below the Frobenius bound. |
| **Frobenius number** | The largest non-representable `N`: 143 for `A ≥ 0`, **162** under the Positive Anchor (`A ≥ 1`). The classical bound `(p − 1)(q − 1)` equals 144 for `(19, 9)`. |
| **Witness** | A triple `(k, A_k, B_k)` for a fixed `N`. |
| **Witness space** | The set of all witnesses for a given `N`. Equals the double cycle. |
| **Chain** | A structured object built from a witness, used in authentication. |
| **Clock decomposition** | The bijection `N ↔ (D, H, M, S, Ms)`, where `N` counts milliseconds in a day. |
| **Clock KDF** | The framework-native key derivation function, based on the chain position. |
| **Temporal barrier** | The sampler that returns a rung only before its deadline, and `None` after it. |
| **Zeroize** | Clearing the secret state; afterwards the attacker observes nothing. |
| **Honey / decoy** | A chain designed to be indistinguishable from the real one. |
| **Honey blobs** | The `M` ciphertexts of the honey layer, one of which contains the true chain. |
| **Deniability** | The property that no adversary can distinguish a witness from an alternative better than chance. |
| **`ValidButUnbound`** | A witness that is structurally valid but not bound to the master secret. |
| **Triangle condition** | `dr(B) = dr(2·dr(N))`. A stricter condition than mere representability. |

---

## 23. Papers

- **RDSI — Representation, Domain Modelling and Software Implementation.**
  DOI: [10.5281/zenodo.23077746](https://doi.org/10.5281/zenodo.23077746)
- **The 19-9 System: N = 19A + 9B.**
  DOI: [10.5281/zenodo.19474707](https://doi.org/10.5281/zenodo.19474707)

Background material for the 90/366/2520 transformation lives in `docs/research-notes/`.

---

## 24. Citation

Academic use does not require citation. If you'd like to cite this work anyway:

```bibtex
@misc{elissaoui2026forest,
  title        = {The Forest Analogy: Full Specification of the MRS-AUTH Cryptographic Framework},
  author       = {Bilal el Issaoui},
  year         = {2026},
  doi          = {10.5281/zenodo.21852606},
  howpublished = {Zenodo}
}
```

---

## 25. Disclaimer

**Research Prototype.**

MRS-AUTH-PQC is an active research-phase cryptographic framework, built on machine-checked EasyCrypt proofs of its abstract model and a comprehensive test suite for its Rust implementation. It has **not** undergone independent third-party security audit, formal code review, or red-team penetration testing, and it carries **no certification of any kind**. Independent review is welcome, and treat production deployment accordingly until that review has happened.

Version 2.0.0 marks the transition from an HKDF-based hybrid KDF to a framework-native Clock KDF. It does not indicate a security audit or production readiness.

---

## 26. License

Apache-2.0. See `LICENSE` for details.

---

## 27. Support and Collaboration

This is independent research without institutional funding. The Rust implementation, the EasyCrypt proofs and the tests are open under Apache-2.0. Researchers, auditors, funders and partners who want to review the construction, finance an independent audit, or support further formal verification are warmly invited to get in touch through the repository.

---

*The double cycle is not a trick.
It is a fact about the integers.

The framework rests on a general `p/q` theorem that admits one cycle, two cycles, or many.
Of these, `(19, 9)` is the optimal choice:
the smallest pair that gives two cycles on the base-9 anchor the decimal system already uses.*

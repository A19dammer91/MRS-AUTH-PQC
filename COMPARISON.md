```markdown
# COMPARISON.md

**MRS-AUTH-PQC v2.0.0**

This document compares three things:

1. The **v1 architecture** (HKDF-based hybrid KDF) and the **current v2 architecture** (framework-native clock KDF).
2. Two anchor formulas derived from the framework `p ≡ 1 (mod q)`: `A₀ = dr(N)` and `A₀ = N mod 9`.
3. The **MRS-AUTH-PQC security model** and the assumptions of **classical cryptography** before this framework.

Written for readers who want to understand the design choices without wading through the papers first.

---

## 1. v1 vs v2: How the session key is derived

### v1 — the hybrid HKDF approach

In v1, the session key was produced by feeding two inputs into HKDF-SHA256:

- The Kyber shared secret (256 bits of entropy).
- The serialized MRS chain (three pairs of integers, flattened to bytes).

HKDF is a standard, well-reviewed construction. It does exactly what it was designed to do: it mixes entropy and produces a uniform-looking key.

But it had three problems for this framework.

**Problem 1 — the framework had nothing to do with the key.**

HKDF does not know what a Diophantine chain is. It does not know what a digital root is. It does not know what the number 19 or the number 9 mean. Feed it anything, it produces a key. The framework's structure was flattened into a byte string and then thrown away.

**Problem 2 — the key could not be audited.**

The output of HKDF is 32 bytes. There is no intermediate value to inspect. To prove that the key was derived correctly, you have to trust HKDF. There is no structure to see because the design is to look like noise.

**Problem 3 — two hash passes for no reason.**

HKDF-Extract computes `HMAC(salt, IKM)`, then HKDF-Expand computes another HMAC to produce the output. Two passes. For a 32-byte output that fits in a single block, one pass would suffice.

### v2 — the framework-native clock KDF

In v2, the session key is produced directly from the structure the framework is built on. No HKDF. The pipeline is:

1. Combine the Kyber shared secret with the session identifier into a seed.
2. Take the first 128 bits of `SHA-256(seed)` and call it `N`.
3. Decompose `N` into a clock tuple `(D, H, M, S, Ms)`.
4. Compute `R(N)`, the number of Diophantine representations of `N`.
5. Use the seed to select one representation index `k`.
6. Compute the pair `(A_k, B_k)` directly.
7. Hash the full transcript into a 32-byte key.

Every step is defined by the framework. Every intermediate value is visible in the `ClockKey` struct. Anybody can recompute the derivation step by step and confirm the result.

### What changed, in one table

| Aspect | v1 (HKDF) | v2 (Clock KDF) |
|---|---|---|
| Domain | Generic | Framework-native |
| Hash passes | 2 (extract + expand) | 1 |
| Branches in hot path | 0 | 0 |
| Structure visible in the API | No | Yes — `ClockKey` exposes N, dr, R(N), k, (A_k, B_k), and the clock tuple |
| Seed-to-position mapping | Non-injective | Bijective |
| External KDF dependency | RFC 5869 | None |
| Entropy source | Kyber SS | Kyber SS (unchanged) |
| Maximum entropy | 256 bits | 256 bits |

### The honest part

The clock KDF does **not add entropy**. No KDF does. If the seed has 256 bits of entropy, the key has at most 256 bits of entropy. That is a hard limit of information theory and it applies to every KDF, including HKDF.

What the clock KDF adds is **structure**. The key is no longer an opaque output of a generic function. It is a deterministic product of the framework, visible in full, auditable in full, and derivable by anyone who has the seed and the code.

HKDF gives you "the output looks random to an attacker who does not know the input." The clock KDF gives you that, plus "the derivation is exactly what the framework claims it is, and you can verify that without trusting any third-party standard."

---

## 2. The framework: `p ≡ 1 (mod q)`

The foundation of this framework is a single congruence:

$$p \equiv 1 \pmod{q}$$

For the (19, 9) system, `p = 19` and `q = 9`: `19 ≡ 1 (mod 9)`.

This is not a computational convenience. It is the structural rule that makes the anchor computable without search. When `p ≡ 1 (mod q)`, the representation `N = pA + qB` collapses modulo `q`:

$$N = pA + qB \equiv 1 \cdot A + 0 \cdot B \equiv A \pmod{q}$$

So `A ≡ N (mod q)`. The anchor is a residue class modulo `q`, and any concrete value for `A₀` must be a representative of that class.

Two representatives are natural. They give rise to the two anchor formulas in the next section.

---

## 3. The two anchor formulas

Both formulas compute the starting A-value of the ladder `A_k = A₀ + 9k`. Both are representatives of the same residue class `N mod 9`. They differ only in the range of values they take.

### Formula 1 — digital root

$$A_0 = \text{dr}(N) = 1 + ((N - 1) \bmod 9)$$

Range: **1 to 9**. Never zero.

### Formula 2 — residue

$$A_0 = N \bmod 9$$

Range: **0 to 8**. Includes zero.

### Both formulas in three examples

**Example 1 — N = 2026**

Method 1 (digit sum):
```

2 + 0 + 2 + 6 = 10
1 + 0 = 1
A₀ = 1

```

Method 2 (divide by 9):
```

2026 ÷ 9 = 225,111...
Repeating digit is 1
A₀ = 1

```

Both formulas give **1**.

**Example 2 — N = 123**

Method 1 (digit sum):
```

1 + 2 + 3 = 6
A₀ = 6

```

Method 2 (divide by 9):
```

123 ÷ 9 = 13,666...
Repeating digit is 6
A₀ = 6

```

Both formulas give **6**.

**Example 3 — N = 999**

Method 1 (digit sum):
```

9 + 9 + 9 = 27
2 + 7 = 9
A₀ = 9

```

Method 2 (divide by 9):
```

999 ÷ 9 = 111
No fraction
A₀ = 0

```

Method 1 gives **9**. Method 2 gives **0**. By the modular convention (0 ≡ 9 mod 9), they represent the same residue class. Numerically, they differ.

This is the only case where the two formulas diverge: when N is a multiple of 9.

---

## 4. Advantages and disadvantages of each formula

### Formula 1 — `A₀ = dr(N)`

**Advantages**

1. **Every representation carries a non-trivial core.**
   A is never 0. Every valid `(A, B)` pair has `A ≥ 1`. A representation with `A = 0` is degenerate: the entire first coefficient of the Diophantine equation is empty. Formula 1 removes this possibility by construction.

2. **The anchor matches the digital root cycle.**
   The digital root cycle is `1 → 2 → 3 → 4 → 5 → 6 → 7 → 8 → 9 → 1 → ...`. Nine positions, no zero. `dr(N)` is exactly the position of N in this cycle. Formula 1 preserves this correspondence.

3. **Anchor value and cycle position are the same number.**
   The value of A₀ equals the position of N in the digital root cycle. If N has digital root 9, then A₀ = 9. The two numbers are identical. No translation is needed between the anchor and the cycle.

**Disadvantages**

1. **Frobenius boundary at 162.**
   Because A cannot be 0, the values N = 144 through 162 lose their only representable form. They become non-representable under this anchor.

2. **First triangle-valid N at 171.**
   The sampler requires a triangle-valid candidate (`dr(B) = dr(2·dr(N))`). Under Formula 1, the first N satisfying both representability and the triangle condition is 171.

### Formula 2 — `A₀ = N mod 9`

**Advantages**

1. **Frobenius boundary at 143.**
   Because A = 0 is allowed, values N = 144 through 162 remain representable through the (0, N/9) form. The representable region is larger.

2. **Produces the Sylvester bound.**
   The Frobenius number of (19, 9) under the non-negative-argument convention is `19·9 − 19 − 9 = 143`. Formula 2 is the formula that yields this specific boundary value.

**Disadvantages**

1. **Admits degenerate representations.**
   A representation with A = 0 is valid but structurally empty. The entire first coefficient is zero. In a system that emphasizes structural representations, this is a defect.

2. **Breaks the digital root cycle correspondence.**
   The formula uses the residue of N modulo 9, not the digital root of N. For N = 144, the digital root is 9 but the residue is 0. The anchor no longer equals the cycle position.

3. **The name "digital root" is not accurate for this formula.**
   The formula computes a residue, not a digital root. `dr(144) = 9`, but Formula 2 returns 0. The two quantities have the same residue class but different numerical values.

---

## 5. Which formula is the better fit

Formula 1 is the better fit for this framework. The reasons are structural, not aesthetic.

**Reason 1 — non-degeneracy.**

The framework's coercion-resistance layer relies on alternative witnesses being structurally equivalent to the authentic one. If A could be 0, an alternative witness could be the trivial representation with no A-component. That would make the alternative witness structurally weaker than the authentic one, which undermines the indistinguishability property. Formula 1 removes this possibility. Every representation has a substantive A-component, and every alternative witness is structurally on par with the authentic one.

**Reason 2 — the framework's mathematics is about the digital root.**

The framework's mathematical foundation describes the digital root as a cycle of nine values, 1 through 9. The anchor formula must produce a value that matches this cycle. Formula 1 does. Formula 2 introduces a tenth value (0) that is congruent to 9 but numerically distinct — a value not present in the cycle.

**Reason 3 — the anchor and the cycle position should be the same number.**

When the anchor formula produces a number that equals the digital root of N, the anchor is directly readable as the cycle position. When the anchor formula produces a residue, the anchor is a different number from the digital root for multiples of 9. The first is clearer, more consistent, and matches what the framework claims to be doing.

**Reason 4 — the representability loss is a consequence, not a defect.**

The values N = 144 through 162 become non-representable under Formula 1. This is a consequence of removing the degenerate (A = 0) form, not a loss of functionality. Those values were only representable through the degenerate case. From N = 163 onward, every integer is representable. From N = 171 onward, every integer is triangle-valid. The system is well-defined and it produces no ambiguity.

**Conclusion.**

Formula 1 (`A₀ = dr(N)`) is the foundation of the framework. It produces non-degenerate representations, it matches the digital root cycle exactly, and it keeps the anchor and the cycle position as the same number. The representability boundary at 162 is the consequence of removing the degenerate case, and that trade is worth making because the framework's coercion-resistance layer depends on every representation being structurally substantive.

Formula 2 (`A₀ = N mod 9`) is a coherent alternative. It produces a larger representable region and yields the Sylvester bound of 143. It admits degenerate representations, and its anchor value differs numerically from the digital root for multiples of 9. For a framework whose mathematics is built on the digital root, Formula 1 is the correct choice.

---

## 6. MRS-AUTH-PQC vs classical cryptography

This section compares the security model of the current repository with the assumptions that classical cryptography has made for decades.

### What classical cryptography does

Classical cryptography — RSA, AES, ECDH, HKDF, the whole traditional stack — is built around one assumption:

> **One secret, one answer.**

When you authenticate, you present your key. Either the key matches, and you are in, or it does not, and you are out. There is no middle ground.

The key itself is generated from randomness. It has no structure. It is 256 random bits, and the only thing an attacker can do is guess. Good luck.

This model works. It has worked for fifty years. It is the foundation of every secure system on the internet.

### What it does not protect against

There is one attacker the classical model does not address: **the person standing in front of you with a weapon.**

If you are coerced — at gunpoint, under legal threat, in any situation where refusal itself is dangerous — the classical model gives you two options:

1. Reveal the key. The attacker gets access to everything.
2. Refuse. The attacker knows you have a key, because the system only issues keys to people who have something worth protecting. Refusal confirms the secret exists.

There is no third option. The mathematics does not allow one. You have exactly one secret, and either you give it up or you do not.

This is the threat that MRS-AUTH-PQC addresses.

### What MRS-AUTH-PQC adds

MRS-AUTH-PQC does not replace classical cryptography. It uses ML-KEM-1024 for confidentiality and AES-256-GCM for integrity — the same building blocks every modern system uses. Those parts are as strong here as anywhere else.

What it adds is a second layer on top: a **witness space** with many valid alternatives, only one of which is cryptographically bound to your identity.

When you register with the system, the server gives you an authentic witness: a three-layer Diophantine chain that satisfies the structural equations and carries an HMAC tag linking it to your identity.

When you are coerced, you do not reveal that witness. You generate an **alternative witness**: another three-layer chain, drawn from the same witness space, that satisfies the same structural equations but carries no binding tag. To anyone who does not hold the master secret, it is indistinguishable from the authentic one. To you, it is a different object with a different internal path.

You hand the alternative witness over. The attacker sees a mathematically valid chain. The equations check out. The structure is correct. There is no way for the attacker to prove that this is not the authentic witness, because the mathematical proof that would establish this does not exist — by design.

### The two-layer structure

| Layer | Purpose | Mechanism |
|---|---|---|
| Confidentiality | Protect the message against a quantum adversary | ML-KEM-1024 (FIPS 203) |
| Integrity | Detect tampering | AES-256-GCM (128-bit tag) |
| Key derivation | Produce the session key | Framework-native Clock KDF |
| Coercion resistance | Provide plausible deniability under duress | MRS(19,9) witness space with indistinguishable alternatives |

The first three layers are standard. The fourth is what makes this framework unusual.

### Where the key comes from

There is one more difference worth naming.

In classical cryptography, the session key is derived from a random seed. The seed is random bytes; the key is what you get after running those bytes through a KDF. The relationship between the seed and the key is opaque. Nobody can tell you what the key "means" because it does not mean anything. It is a number.

In MRS-AUTH-PQC, the session key is derived from the **structure of the framework**. The seed is still random — it comes from the Kyber shared secret. But the key is the output of a sequence of steps defined by the framework: decompose the seed into a clock, find the number of Diophantine representations of N, select one, hash the transcript.

If you are curious about why the key is what it is, you can look. The `ClockKey` struct exposes every intermediate value: N, the clock tuple, R(N), k, the pair (A_k, B_k), and the final 32-byte output. You can recompute the derivation by hand and confirm that the answer is what the framework says it is.

This is not a claim about security. It is a claim about transparency. The key is not a magic number. It is the result of a computation you can follow.

### The full comparison

| Property | Classical cryptography | MRS-AUTH-PQC |
|---|---|---|
| Confidentiality | Standard (RSA, ECDH, Kyber) | ML-KEM-1024 (FIPS 203) |
| Integrity | Standard (AEAD, HMAC) | AES-256-GCM |
| Key derivation | Random seed + generic KDF | Random seed + framework-native Clock KDF |
| Key derivation visible in the API | No | Yes |
| Number of valid credentials per user | One | Many (one per N, all structurally equivalent) |
| Behaviour under coercion | Reveal or refuse | Reveal a valid alternative |
| Deniability | Not addressed | Provided by witness-space ambiguity |
| Entropy source | Random bytes | Random bytes (Kyber SS) |
| Maximum entropy | The seed's entropy | The seed's entropy (identical) |
| Foundation | Generic group theory, hashing | MRS(19,9) with `p ≡ 1 (mod q)` |

### The honest limits

MRS-AUTH-PQC does not provide mathematical invulnerability against a determined attacker. No system does.

What it provides is a specific and well-defined guarantee: **an attacker who obtains a witness cannot mathematically prove whether it is the authentic one or an alternative.** That is a proof-level guarantee, not a psychology-level one.

An attacker who refuses to accept any witness short of a proof that no alternative exists cannot be stopped. That proof does not exist by design, so the attacker can demand it forever and never receive it. But the attacker can also simply choose not to accept the witness and to continue applying coercion. The mathematics does not stop that.

This is the same limitation shared by every deniable scheme in existence. Rubberhose, the original deniable filesystem, has it. Any system that claims to solve coercion without this limitation is misrepresenting what it does.

What MRS-AUTH-PQC does is give the honest user a real option they would not otherwise have: the ability to hand over a mathematically valid credential that is not the authentic one, without ever needing to hold the master secret, and without needing to trust the attacker to accept it.

---

## Summary

**On the KDF.** v1 used HKDF. v2 uses a framework-native clock KDF. The change removes an external dependency, reduces the hash passes from two to one, and turns the key derivation into an auditable computation with every intermediate value exposed in the public API.

**On the framework.** The foundation is `p ≡ 1 (mod q)`. For (19, 9), this is `19 ≡ 1 (mod 9)`. The anchor formula follows directly from this congruence: since `N ≡ A (mod 9)`, the smallest valid anchor is read off the congruence without search.

**On the two anchor formulas.** Formula 1 (`A₀ = dr(N)`, range 1..9) and Formula 2 (`A₀ = N mod 9`, range 0..8) agree on every N except multiples of 9, where the first gives 9 and the second gives 0. Formula 1 is the better fit for this framework because it produces non-degenerate representations, matches the digital root cycle exactly, and keeps the anchor and the cycle position as the same number.

**On the security model.** Classical cryptography protects against eavesdroppers and forgers. MRS-AUTH-PQC protects against those too, using the same primitives. It also protects against coercion, using a witness-space construction that gives a coerced user a real alternative to hand over. The two layers coexist. Neither replaces the other.

**On entropy.** Neither HKDF nor the clock KDF adds entropy. The key is bounded by the entropy of the seed in both cases. What the clock KDF adds is structure, not strength.

**On honesty.** The framework does not claim more than it delivers. It provides a mathematical guarantee under a well-defined threat model. It does not provide protection against every possible attacker, and it does not pretend to.

---

*Bilal el Issaoui, Amsterdam, 2026.*
```

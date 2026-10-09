# COMPARISON.md

**MRS-AUTH-PQC**

This document compares three things:

1. The **v1 architecture** (HKDF-based hybrid KDF) and the **current v2 architecture** (framework-native clock KDF).
2. The **Positive Anchor** `A₀ = dr(N)` (current) and the **Standard Anchor** `A₀ = N mod 9` (the alternative we considered).
3. The **MRS-AUTH-PQC security model** and the assumptions of **classical cryptography** before this framework.

Written for readers who want to understand the design choices without wading through the papers first.

---

## 1. v1 vs v2: How the session key is derived

### v1 — the hybrid HKDF approach

In v1, the session key was produced by feeding two inputs into HKDF-SHA256:

- The Kyber shared secret (256 bits of entropy).
- The serialized MRS chain (three pairs of integers, flattened to bytes).

HKDF is a standard, well-reviewed construction. It does exactly what it was designed to do: it mixes entropy and produces a uniform-looking key. For any application, that would be fine.

But it had three problems we no longer accept.

**Problem 1 — the framework had nothing to do with the key.**

HKDF does not know what a Diophantine chain is. It does not know what a digital root is. It does not know what the number 19 or the number 9 mean. Feed it anything, it produces a key. The framework's structure was flattened into a byte string and then thrown away.

**Problem 2 — the key could not be audited.**

The output of HKDF is 32 bytes. There is no intermediate value to inspect. If you want to prove that the key was derived correctly, you have to trust HKDF. You cannot see the structure of the derivation because there is no structure to see — it is designed to look like noise.

**Problem 3 — two hash passes for no reason.**

HKDF-Extract computes `HMAC(salt, IKM)`, then HKDF-Expand computes another HMAC to produce the output. Two passes. For a 32-byte output that fits in a single block, one pass would suffice.

### v2 — the framework-native clock KDF

In v2, the session key is produced directly from the structure of the framework. No HKDF. The pipeline is:

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

This is a different kind of guarantee than HKDF provides. HKDF gives you "the output looks random to an attacker who does not know the input." The clock KDF gives you that, plus "the derivation is exactly what the framework claims it is, and you can verify that without trusting any third-party standard."

---

## 2. The anchor: `A₀ = dr(N)` vs `A₀ = N mod 9`

This is the design decision that separates the current version from the alternative we evaluated and set aside.

### The two options

Both anchors describe where the Diophantine ladder starts.

**Standard Anchor.** `A₀ = N mod 9`. Range 0..8. Includes zero.

**Positive Anchor (current).** `A₀ = dr(N) = 1 + ((N − 1) mod 9)`. Range 1..9. Never zero.

The two values are congruent modulo 9. They differ only at multiples of 9: one gives 0, the other gives 9. In modular arithmetic, 0 and 9 are the same class. In the representation formula `19A + 9B = N`, they are not.

### Why this matters

Take N = 144. Under the Standard Anchor, A₀ = 0, so 144 = 19·0 + 9·16 is a valid representation. Under the Positive Anchor, A₀ = 9, so 19·9 = 171 > 144 and no representation exists.

Take N = 162. Standard Anchor admits (0, 18). Positive Anchor rejects it. The next representable N under Positive Anchor is 163, and the first with a triangle-valid candidate is 171.

The Frobenius boundary moves from 143 to 162. The set of representable integers changes. The witness space changes. Everything downstream changes.

### Which is correct?

Neither is objectively more correct than the other. They are two systems. The question is which one matches what the framework is trying to do.

I chose the Positive Anchor for four reasons.

**Reason 1 — every representation carries a non-trivial core.**

Under the Standard Anchor, a representation can have A = 0. That means the entire "first coefficient" of the Diophantine equation is zero. The representation is still valid, but it feels degenerate. It is the equivalent of writing 144 as 0·19 + 16·9 — mathematically fine, structurally empty.

Under the Positive Anchor, A is always at least 1. Every representation has a substantive A-component. This is what the coercion-resistance layer needs: an alternative witness must be a *structurally equivalent* alternative, not a degenerate one.

**Reason 2 — the digital root cycle is 1 to 9, not 0 to 8.**

The framework's papers present the digital root as a cycle of nine values: 1, 2, 3, 4, 5, 6, 7, 8, 9, then back to 1. There is no zero in the cycle. Nine distinct positions, each a distinct residue.

The Standard Anchor introduces a tenth position — 0 — that is congruent to 9 but numerically distinct. This breaks the neat correspondence between the anchor value and the cycle position. The Positive Anchor preserves it: `dr(N)` is exactly the position of N in the digital root cycle.

**Reason 3 — the standard anchor hides the digital root behind a residue.**

When `A₀ = N mod 9`, the name "anchor" refers to the residue of N modulo 9. But that is not the digital root of N. The digital root of 144 is 9. Its residue modulo 9 is 0. These are different quantities.

The framework's claim is that it uses the digital root. That claim is only true under the Positive Anchor.

**Reason 4 — the boundary is not a defect.**

Under the Positive Anchor, N = 144 through 162 are no longer representable. That sounds like a loss. It is not. Those values were only representable via the degenerate (A = 0) case. Removing the degenerate case removes the values that depended on it.

From 163 onward, every integer is representable. From 171 onward, every integer is triangle-valid. The system is well-defined and it does exactly what the framework says it does.

### The two anchors side by side

| Property | Standard Anchor (`N mod 9`) | Positive Anchor (`dr(N)`) |
|---|---|---|
| Range of A₀ | 0..8 | 1..9 |
| Zero as anchor | Allowed | Never |
| Frobenius boundary | 143 | 162 |
| First triangle-valid N | Not applicable (A=0 allowed) | 171 |
| Cycle correspondence | Off by one (residue vs digital root) | Exact (A₀ = digital root of N) |
| Degenerate representations | Possible (A = 0) | Impossible |
| Match with framework's claim | Requires rephrasing | Direct |

We chose the Positive Anchor. Everything in the current codebase — the sampler, the forest module, the clock KDF, the EasyCrypt proofs — reflects this choice.

---

## 3. MRS-AUTH-PQC vs classical cryptography

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

This is the threat that the MRS-AUTH-PQC framework addresses.

### What MRS-AUTH-PQC adds

MRS-AUTH-PQC does not try to replace classical cryptography. It uses ML-KEM-1024 for confidentiality and AES-256-GCM for integrity — the same building blocks every modern system uses. Those parts are as strong here as anywhere else.

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
| Key derivation | Random seed + KDF | Random seed + framework-native Clock KDF |
| Key derivation visible in the API | No | Yes |
| Number of valid credentials per user | One | Many (one per N, all structurally equivalent) |
| Behaviour under coercion | Reveal or refuse | Reveal a valid alternative |
| Deniability | Not addressed | Provided by witness-space ambiguity |
| Entropy source | Random bytes | Random bytes (Kyber SS) |
| Maximum entropy | The seed's entropy | The seed's entropy (identical) |

### The honest limits

MRS-AUTH-PQC does not provide mathematical invulnerability against a determined attacker. No system does.

What it provides is a specific and well-defined guarantee: **an attacker who obtains a witness cannot mathematically prove whether it is the authentic one or an alternative.** That is a proof-level guarantee, not a psychology-level one.

An attacker who refuses to accept any witness short of a proof that no alternative exists cannot be stopped. That proof does not exist by design, so the attacker can demand it forever and never receive it. But the attacker can also simply choose not to accept the witness and to continue applying coercion. The mathematics does not stop that.

This is the same limitation shared by every deniable scheme in existence. Rubberhose, the original deniable filesystem, has it. Any system that claims to solve coercion without this limitation is misrepresenting what it does.

What MRS-AUTH-PQC does is give the honest user a real option they would not otherwise have: the ability to hand over a mathematically valid credential that is not the authentic one, without ever needing to hold the master secret, and without needing to trust the attacker to accept it.

---

## Summary

**On the KDF.** v1 used HKDF. v2 uses a framework-native clock KDF. The change removes an external dependency, reduces the hash passes from two to one, and turns the key derivation into an auditable computation with every intermediate value exposed in the public API.

**On the anchor.** We use `A₀ = dr(N)`, the digital root of N. This is the Positive Anchor Convention. Its range is 1..9. It makes every representation carry a non-trivial core, it matches the framework's own claim about the digital root cycle, and it moves the Frobenius boundary from 143 to 162. This is a deliberate design choice.

**On the security model.** Classical cryptography protects against eavesdroppers and forgers. MRS-AUTH-PQC protects against those too, using the same primitives. It also protects against coercion, using a witness-space construction that gives a coerced user a real alternative to hand over. The two layers coexist. Neither replaces the other.

**On entropy.** Neither HKDF nor the clock KDF adds entropy. The key is bounded by the entropy of the seed in both cases. What the clock KDF adds is structure, not strength.

**On honesty.** The framework does not claim more than it delivers. It provides a mathematical guarantee under a well-defined threat model. It does not provide protection against every possible attacker, and it does not pretend to.

---

*Bilal el Issaoui, Amsterdam, 2026.*

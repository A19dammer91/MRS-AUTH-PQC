# COMMERCIAL.md, Licensing and Partnership

**For investors, acquirers, and commercial licensees.**

MRS-AUTH-PQC is a post-quantum authentication framework with a formal
verification layer and a genuinely new structural property: coercion
resistance derived from number theory. It is currently independent research,
with no institutional funding, and it is looking for the right partner to
move from verified prototype to audited product.

This document explains what the asset is, what it is not, and what kinds of
commercial arrangements are possible.

---

## 1. What the asset is

**A cryptographic construction with a machine-checked security proof.**

Three properties, in one framework:

1. **Post-quantum confidentiality.** ML-KEM-1024 (FIPS 203, IND-CCA2, NIST
   Level 5) for key encapsulation.
2. **Coercion resistance.** A witness space derived from the (19, 9)
   Diophantine representation system, in which a coerced user can produce a
   mathematically valid alternative to the real secret. The adversary's
   success probability is proved to be exactly 1/2, against any adversary,
   with no computational assumption.
3. **A framework-native key derivation function.** The session key is
   derived from the same structure, not from an external KDF. Every
   intermediate value is deterministic and auditable.

The property in (2) is the differentiator. It is not a stylistic choice, and
it is not a tuning parameter. It follows from the arithmetic of
`p ≡ 1 (mod q)` and it is proved, not assumed.

**References:**

- *RDSI, Representation, Domain Modelling and Software Implementation.*
  DOI: https://doi.org/10.5281/zenodo.23077746
- *The 19-9 System: N = 19A + 9B.*
  DOI: https://doi.org/10.5281/zenodo.19474707

---

## 2. The technical moat

Four things make this hard to replicate quickly.

**Formal verification is deep, not decorative.**
14 EasyCrypt files, 231 lemmas, 21 axioms, 0 admits. The deniability theorem
was an axiom in an earlier version and was **eliminated by a proof**. The
fractal ladder, the Frobenius boundary, the temporal barrier, the zeroize
model, and the honey layer are all machine-checked. Reproducing this from
scratch is a multi-year effort.

**The construction is not a variant of an existing scheme.**
It is derived from a general `p/q` theorem that works for any admissible
pair. The framework chooses `(19, 9)` for mathematical reasons, not because
it is convenient. The same structure extends into 3 and 4 dimensions. This
is a family, not a one-off.

**The lineage is specific and clear.**
The coercion-resistance idea descends from **Rubberhose** (Assange et al.),
which used indistinguishable encrypted chaff on disk. MRS-AUTH-PQC moves the
haystack from storage into abstract mathematics. That inheritance is
documented and honest.

**The Rust implementation is complete.**
108 tests passing, benchmarks, an interactive browser demo, CI on every
push, no unsafe code. This is not a proof-of-concept repository.

---

## 3. What the asset is not

Three honest statements. They matter.

**Not audited.**
No independent third-party security review has been performed. No red-team
exercise. No formal code review beyond what the automated CI checks. The
EasyCrypt proofs cover the abstract model, not the implementation. This is
the single largest gap between where the project is and where a production
deployment needs it to be.

**Not certified.**
No FIPS validation. No Common Criteria. No NIST certification beyond the
use of the standardised ML-KEM-1024 primitive inside it.

**Not a finished product.**
There is no hardened SDK, no documented integration for enterprise identity
providers, no support organisation. The engine works. The wrapper around it
does not exist yet.

Any investor or acquirer should price the asset with these three facts on
the table.

---

## 4. Maturity snapshot

| Dimension | Status |
|---|---|
| Mathematical theory | Complete, documented, published |
| Formal verification (abstract model) | Complete, 231 lemmas, 0 admits |
| Rust implementation | Functional, 108 tests passing |
| CI/CD | Active on every push |
| Benchmarks | Present, near-constant time across 12 orders of magnitude |
| Documentation | README, papers, demo, user manual |
| Independent audit | **Not performed** |
| Certification | **None** |
| Production hardening | **Not done** |
| Team | Single researcher |
| Funding | None (independent) |

---

## 5. Market context

Two forces are converging, and this framework sits at the intersection.

**Post-quantum migration is a decade-long transition with a hard deadline.**
Every organisation that handles long-lived secrets has to move off RSA and
ECC before 2030. That transition is currently being served by ML-KEM,
ML-DSA, and their variants. MRS-AUTH-PQC uses the standard primitive; it
does not compete with the NIST algorithms. It adds a property they do not
have.

**Coercion resistance has no commercial provider.**
There is no widely deployed cryptographic product whose primary selling
point is that a coerced user cannot prove they handed over the real key.
The market for this is small but specific: individuals and organisations
whose threat model includes physical coercion. Journalists, activists,
high-value individuals, some government and defence contexts, and
increasingly enterprises with executives who travel to high-risk
jurisdictions.

MRS-AUTH-PQC is the first construction with a machine-checked proof of that
property in a post-quantum setting. That is a narrow moat, but it is a real
one, and it is defensible because it is not just code, it is mathematics.

---

## 6. Licensing and partnership options

Three tiers, each with a different shape. All are open to negotiation.

### 6.1 Commercial licence (per organisation)

For organisations that want to use MRS-AUTH-PQC in a proprietary product or
a closed network service, without the source-disclosure obligations of the
AGPL-3.0.

Typical scope:

- Right to use, modify, and embed the Rust implementation in closed products.
- Right to keep modifications private.
- Optional: support, updates, priority access to the author.
- Optional: custom EasyCrypt verification work for a specific use case.

Typical terms: annual fee, tiered by organisation size or deployment count.
Royalty arrangements are possible for products where the framework is the
primary value proposition.

### 6.2 Strategic partnership or sponsored development

For organisations that want to shape the direction of the framework, fund
specific extensions, or integrate it into a larger product line.

Typical scope:

- A development roadmap negotiated with the author.
- Priority access to new formal verification results.
- Joint publication or co-branding, where appropriate.
- Option to extend the framework to new dimensions or new pairs `(p, q)`.

Typical terms: development contract with milestone payments, or a research
grant with agreed deliverables.

### 6.3 Acquisition of exclusive rights

For organisations that want exclusive commercial control of the framework
in a specific vertical or region.

Scope negotiable. Exclusive rights are possible for:

- Specific industries (defence, healthcare, finance).
- Specific geographies.
- Specific product categories.

The open-source AGPL-3.0 version cannot be retracted; once released, it
remains available. Exclusive rights therefore apply to the **commercial
licence track**, not to the AGPL code itself.

### 6.4 What is not for sale

- The copyright itself (transfer of ownership).
- The right to relicense the AGPL version under different terms.
- The right to suppress the research or the papers.

The framework is public. What is negotiable is commercial use of it, not
ownership of the underlying work.

---

## 7. What a commercial engagement funds

Every commercial licence and every partnership directly funds three things:

1. **Independent security audit.** The single most important next step.
   A professional review of the Rust implementation, the sampling layer,
   and the integration surface.
2. **Continued formal verification.** Extending the EasyCrypt coverage to
   the AEAD layer, the key derivation, and the Rust refinement.
3. **Production hardening.** Documentation, SDK, integration guides, and
   support infrastructure.

Commercial revenue does not disappear into a black box. It converts
directly into the verification depth that a serious deployment requires.

---

## 8. Contact

Commercial enquiries, partnership proposals, and acquisition discussions
are welcome.

**Bilal el Issaoui**
Amsterdam, Netherlands

- **Email**: elissa.oui.amster@gmail.com
- **Alternate email**: elissa_oui@outlook.com
- **GitHub**: https://github.com/A19dammer91/MRS-AUTH-PQC

When reaching out, it helps to include:

- The nature of the interest (licence, partnership, acquisition).
- The intended use and deployment context.
- Any specific requirements around audit, certification, or support.

All conversations are treated as confidential unless otherwise agreed.

---

## 9. Honest summary

If you are an investor or acquirer reading this, here is the clearest
one-paragraph summary I can give:

> MRS-AUTH-PQC is a mathematically novel construction with a machine-checked
> proof of a security property that no other deployed system provides in a
> post-quantum setting. The theory is finished, the formal verification is
> deep, and the Rust implementation works. The project is not audited, not
> certified, and not production-hardened. It is a solo-researcher asset with
> a narrow but defensible moat. The right partner would be one that can fund
> the audit and hardening phase in exchange for commercial rights, not one
> looking for a finished product.

That is the whole case.

---

**Bilal el Issaoui**
Amsterdam, Netherlands, 2026

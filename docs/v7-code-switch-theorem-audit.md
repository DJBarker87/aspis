# Aspis V7 code-switch theorem applicability audit

Date: 2026-08-25  
Baseline: `a6fa6d817e3cf343c8639684e4ab2ce289c40355`  
Decision: **preferred local code switch BLOCKED; measured fallback fails the
wire gate; compact Tag-72 successor SELECTED**

> Update after Phase 3: the degree-corrected random-point PCS construction
> below remains a valid conditional research route, but its measured wire is
> 36,040 bytes (35,016 bytes even with a security-costly punctured source
> domain).  It is therefore not the production V7 profile.  The selected
> profile and exact 30,672-byte census are frozen in
> `docs/v7-compact-tag72-pivot.md`.

This audit is deliberately narrower than a security proof.  It checks whether
the published statements actually have the hypotheses needed by the proposed
V7 transcript.  It does not silently strengthen a paper theorem, and the Lean
companion does not introduce a paper theorem as an axiom.

## Frozen V7 statement

The source objects are committed before `gamma`:

- Stage A: 26 real M31 lanes, padded to 32;
- Stage B: three QM31 lanes represented as 12 M31 limbs, padded to 16;
- Stage A lane point: `(gamma,gamma^2,gamma^4,gamma^8,gamma^16)`;
- Stage B lane point: `(i,u,gamma,gamma^2)` with limb order
  `(1,i,u,iu)`;
- target: one QM31 row value, equivalently four M31 limbs, committed under the
  frozen V6 circle-code backend after `gamma`.

The already-proved algebraic target is

```text
G_gamma(r) = A(r,y_A(gamma)) + gamma^26 B(r,y_B(gamma))
           = sum_(lane=0)^28 gamma^lane C_lane(r).
```

The mandatory transcript order is

```text
R_A, R_B  <  gamma  <  R_G  <  fresh row/opening challenges.
```

## Sources audited

| Source | Relevant result | SHA-256 of audited PDF |
|---|---|---|
| [SwitchFold, ePrint 2026/1489](https://eprint.iacr.org/2026/1489.pdf) | Section 3.1, Theorem 2 | `d85c4bef6f59974e4a9b5a498dcb3b608a7b6ef436f09ad6280ecffc35d590d2` |
| [S-two, ePrint 2026/532](https://eprint.iacr.org/2026/532.pdf) | Theorems 15, 19 and 21; Protocol 4; Section 4.5 | `e3b0132ec598ca16835c1de3c85d0c8b07c41b5f063f1d88b5a9628c22252c3f` |
| [TensorSwitch, ePrint 2025/2065](https://eprint.iacr.org/2025/2065.pdf) | Theorem 8.5 | `5ab87ee5c9a25cb8f6321d0b406813fc50a697c001609027adc78b639f223a29` |
| [BaseFold list-decoding analysis, ePrint 2024/1571](https://eprint.iacr.org/2024/1571.pdf) | partial-evaluation/folding and batch evaluation analysis | `8b851b4d8ef1c7681ddea663b06e3bc1af323db1c1610d230beec5e702d0d3cb` |
| [BaseFold, ePrint 2023/1705](https://eprint.iacr.org/2023/1705.pdf) | original foldable-code PCS | `6c3589a81b0e25cdf12924b85e4a34fcdad01105d253f210570972ac45ccb094` |

The PDFs were fetched directly from IACR ePrint on 2026-08-25.  The hashes pin
the exact revisions used for this decision.

## Candidate 1: SwitchFold Theorem 2

SwitchFold Theorem 2 reduces an MLE opening for one `t`-interleaved source
code `C^t` to an MLE opening under a smaller `t`-interleaved code `C'^t`.
Its finite shape includes:

1. one source matrix `M in F^(k x t)` and source word `G M`;
2. the same interleaving width `t` on the target;
3. `k = t k'`;
4. a verifier vector sampled uniformly from `F^t` for the Freivalds
   reduction;
5. an MLE oracle for the target code and an MLE oracle for the source
   generator matrix;
6. sampled source rows checking `Xi G m = Xi C r_tilde`.

The current V7 preferred transcript does not meet those predicates:

| Predicate | SwitchFold Theorem 2 | V7 preferred link | Result |
|---|---|---|---|
| source commitments | one interleaved source | two independently committed sources | mismatch |
| interleave width | same `t` before and after switch | 32 and 16 source limbs, 4 target limbs | mismatch |
| mixing challenge | uniform vector in `F^t` | powers of one `gamma` | mismatch |
| field/target encoding | target is `C'^t` over the theorem field | frozen QM31 V6 circle encoding | not instantiated |
| generator-matrix MLE oracle | required | absent from the proposed wire format | missing |
| target semantics | `m = M r_tilde` for one source | sum of two heterogeneous restrictions | mismatch |

The structured powers are not merely a notation change: their zeroth
coordinate is always one, so the map `gamma -> (1,gamma,...)` is not
surjective onto `F^t`.  The Lean companion proves this finite obstruction and
the 32/16-to-4 width obstructions.

**Decision:** no direct instantiation.  Adapting Theorem 2 would require a new
heterogeneous two-source theorem, a changed wire format with generator-matrix
openings, and a new analysis of correlated structured challenges.  That is not
an optimization of the downloaded design and is not assumed.

## Candidate 2: BaseFold partial evaluation

BaseFold makes even/odd linear combinations correspond to partial evaluation
of one multilinear polynomial committed under one foldable code.  Its batch
evaluation machinery can share verifier challenges across claims.  Neither
audited BaseFold paper states the missing implication from two independently
committed, differently padded source tensors to an independently committed
post-`gamma` target word.

**Decision:** useful backend machinery, but not a theorem for the preferred
V7 link.

## Candidate 3: TensorSwitch Theorem 8.5

TensorSwitch Theorem 8.5 constructs a complete interactive tensor-code
commitment.  Its commitment phase has three rounds and three point oracles;
the opening phase adds logarithmically many rounds/oracles and its own tensor
code, delegation and extraction hypotheses.  It is not a local equality proof
between the already-fixed V7 roots.  Replacing the V7 commitment layer with
the full construction would also invalidate the current byte and CU model.

**Decision:** not a drop-in link; rejected for this profile.

## Selected construction: degree-corrected random-point PCS link

After `R_G`, the verifier samples a fresh row point `r in QM31^10` and obtains
real authenticated batch openings of

```text
A(r,y_A(gamma)), B(r,y_B(gamma)), G(r).
```

It accepts the link only when

```text
G(r) = A(r,y_A(gamma)) + gamma^26 B(r,y_B(gamma)).
```

This is conditionally supported by S-two's published multi-domain machinery:

- Theorem 15 covers heterogeneous table heights under its stated distance,
  multiplicity and minimum-height conditions;
- Protocol 4 opens a batch of committed circle polynomials at a shared
  out-of-domain point while testing both each polynomial and its quotient;
- Theorem 21 gives the degree-corrected batch-evaluation knowledge-soundness
  statement, under condition (80), with the Theorem 19 round errors.

The V7 instantiation must therefore prove all of the following before this
becomes a production theorem:

1. A, B and G are bound to the exact claimed low-degree row polynomials;
2. their possibly different domains use the Theorem-21 lifted,
   degree-corrected interface (or a separately proved unique-decoding
   specialization);
3. the row point and every opening-test challenge are sampled after `R_G`;
4. the discrepancy polynomial has the stated total-degree cap;
5. the nonzero discrepancy event receives the exact multivariate
   Schwartz--Zippel term and is added to the V7 security ledger;
6. the Fiat--Shamir/Merkle compilation authenticates every opened oracle.

Sending three unauthenticated values is explicitly insufficient.

### Implementation caveat

S-two Section 4.5 says its current released implementation uses a
non-degree-corrected, two-point quotient variant and a non-squaring-consistent
domain choice.  The paper does not provide the cross-domain list-regime proof
for that latter implementation choice.  V7 must implement the published
degree-corrected/lifted protocol or remain in a separately justified
unique-decoding regime.  Copying the current S-two implementation is not an
accepted theorem instantiation.

## Original Phase-2 gate result

| Gate | Result |
|---|---|
| preferred published local switch matches exactly | **FAIL** |
| mismatch represented in Lean without axioms | **PASS** |
| modular fallback has a published conditional route | **PASS, conditional** |
| SBF implementation authorized | **NO -- measure host fallback first** |

Phase 2 closed with permission to measure the fallback.  Phase 3 did so and
triggered the wire kill condition before SBF integration.  The algebra and
theorem audit remain retained evidence; production work continues only on the
separately documented compact Tag-72 successor.

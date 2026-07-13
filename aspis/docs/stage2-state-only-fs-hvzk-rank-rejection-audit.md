# State-only FS-HVZK rank-rejection audit

Status: conditional theorem and rejection criteria, not a hiding claim.

Date: 2026-07-13.

## Ruling

An honest-prover rejection gate can remove the bad-rank event from the
privacy advantage of **emitted proofs**.  In that construction the
Schwartz--Zippel bound is an availability/expected-runtime bound, not a
privacy-error term.

That conclusion is valid only if all of the hypotheses below hold.  In
particular, exact rank on sampled Fiat--Shamir schedules is not sufficient.
The construction still needs:

1. a universal affine-containment result for every valid witness difference;
2. an argument that the mask coins remain uniform after fixing the public
   Fiat--Shamir coins used by the rank matrix;
3. a private-Merkle/random-oracle simulator for roots and authentication
   paths;
4. inclusion of every later PCS/fold/OOD value in either the affine view or
   the random-oracle simulation; and
5. a proved lower bound on the gate's success probability over the actual
   challenge and distinct-query sampler.

The current `24000/(2^31-1)`, approximately `2^-16.45`, calculation would be
enough for expected termination only after a nonzero minor has been proved
for every allowed discrete query tuple (or a joint bad-query bound has been
proved).  Three sampled query schedules do not establish that premise.

## Model

Fix a public statement `x` and let `W_x` be its set of valid witnesses.  One
candidate proving attempt samples a fresh public salt/nonce `nu` and a uniform
mask vector `R` from a fixed finite M31 vector space `K`.  The prover builds
all oracle messages and obtains the Fiat--Shamir verifier coins and distinct
query positions

```text
C = (eta, z, gamma, fold coins, OOD coins, query positions, ...).
```

For fixed `C=c`, collect every public, non-hash, witness-dependent field
coordinate into `Y`.  This includes sumcheck messages, opened leaves,
terminal evaluations, later-layer openings, OOD values, final-polynomial
data, receipt fields, logs, and public account data whenever they are not
already a deterministic function of `x`.  The required form is

```text
Y = A_x,c R + b_x,c(w).                         (1)
```

Public linear relations that hold identically for every witness and mask may
be quotiented out, but the quotient map must be explicit and identical on
both sides of (1).  A relation inferred from one honest fixture is not a
valid quotient.

Let

```text
D_x,c = span { b_x,c(w1) - b_x,c(w0) : w0,w1 in W_x }.
```

Define the good-schedule predicate

```text
Good_x(c)  iff  D_x,c is a subspace of image(A_x,c).   (2)
```

Full row rank of `A_x,c` is sufficient but not necessary.  The exact test is
containment.  It may be implemented as
`rank(A)=rank([A | B_diff])` only when the columns of `B_diff` provably span
**all** of `D_x,c`.  Testing one pair of valid witnesses is only a negative
tooth; it cannot certify (2).

The rank gate must be a deterministic function of `x`, the frozen layout,
and public verifier coins/query positions.  It must not use the witness, the
realized mask values, an uncommitted prover hint, or a witness-derived choice
of minor.  A canonical full rank/containment algorithm is preferable to a
prover-selected minor.

## Conditional theorem

**Theorem (rank rejection for the affine public view).**  Consider the
repeating prover which runs independent candidate attempts and emits the
first candidate for which `Good_x(C)=1`.  Suppose:

1. Equation (1) holds for the complete non-hash public view for every valid
   witness and every schedule the verifier can derive.
2. Equation (2) holds whenever the gate accepts.
3. Conditional on `C=c`, the mask vector `R` is uniform on the same space
   `K` for every `w in W_x`; the distribution of `C` is also independent of
   `w`.  Fresh domain-separated random-oracle inputs are used on every
   attempt.
4. The root/authentication-path wrapper has a witness-independent simulator,
   with error `eps_merkle`, given the opened values and indices.
5. All other public bytes are deterministic functions of `x`, `C`, `Y`, and
   that simulated wrapper, or have separately stated simulation error
   `eps_other`.
6. `Pr[Good_x(C)=0] <= beta < 1`, uniformly over all allowed public histories.

Then, for every two valid witnesses `w0,w1`, the affine views of emitted
proofs are identically distributed.  The complete public views are at most
`eps_merkle + eps_other` apart (plus the explicitly stated Fiat--Shamir
programming/pre-query error).  There is no additive `beta` privacy term.
The expected number of attempts is at most `1/(1-beta)`.  With a cap of `T`
independent attempts, the no-proof probability is at most `beta^T`; if the
failure symbol/timing is in the public view, its distribution must also be
witness-independent.

**Proof.**  Fix an accepted schedule `c`.  For any `w0,w1`, (2) gives a
vector `delta in K` such that

```text
A_x,c delta = b_x,c(w1) - b_x,c(w0).
```

Translation by `delta` is a bijection on uniform `K`.  Therefore

```text
A_x,c R + b_x,c(w0)  ==dist==  A_x,c R + b_x,c(w1).
```

By hypothesis 3 the mixture weight of each accepted `c` is the same for both
witnesses.  Repeating until `Good` is exactly sampling that common mixture
conditioned on `Good=1`; bad schedules have zero mass in emitted proofs.
Hypotheses 4 and 5 lift equality of the algebraic view to the complete view
with the stated simulation errors.  The runtime and capped-failure claims are
the geometric-distribution bounds.  QED.

If the real and simulated candidate distributions are merely `epsilon`-close
before rejection, conditioning can amplify their distance by approximately
`1/(1-beta)` and can expose a mismatch in their success probabilities.  Thus
"the simulator retries too" is not by itself a proof: the simulator must
satisfy the same per-good-schedule distribution and success law.

## Why fixing a Fiat--Shamir schedule is delicate

The linear-algebra argument silently assumes uniform masks after the schedule
is fixed.  This is false for an arbitrary mask-dependent schedule.  For a
one-coordinate counterexample, let `R` be uniform, publish `S=R`, and publish
`Y=w+R`.  The matrix from `R` to `Y` has full rank, but `(S,Y)` reveals
`w=Y-S` exactly.

In the random-oracle model, a fresh oracle answer at an unpredictable
transcript prefix is uniform independently of that prefix.  This is the route
by which Fiat--Shamir coins can satisfy hypothesis 3, but it needs an actual
programming/freshness proof:

- `nu` must be uniformly unpredictable before the adversary's pre-proof
  oracle queries, not merely unique;
- `nu` (or equivalent entropy) must bind every later Fiat--Shamir prefix;
- transcript, Merkle, leaf-commitment, and mask-expansion domains must be
  separated;
- candidate attempts must use distinct fresh prefixes; and
- the proof must bound collisions and adversarial pre-queries at those
  prefixes.

The relevant zero-knowledge model is the explicitly programmable random
oracle (EPRO) model.  The BCS IOP-to-NIROP compiler proves that an HVZK IOP can
yield a malicious-verifier statistical-ZK noninteractive proof in EPRO, and
its simulator programs the Fiat--Shamir queries and simulates private Merkle
paths.  This does not give a standard-model zero-knowledge theorem for a
concrete Poseidon instantiation.  See Ben-Sasson--Chiesa--Spooner,
[*Interactive Oracle Proofs*](https://eprint.iacr.org/2016/116), especially
Sections 3.2 and 7.4.

## Merkle roots and authentication paths are a separate obligation

Rank containment proves a claim about field-valued affine observations.  A
Merkle root is a nonlinear random-oracle image of the entire committed word,
and an authentication path contains hashes of unqueried subtrees.  They are
not covered merely by adding their bytes as rows of an M31 matrix.

One of the following must be supplied:

1. the private-Merkle construction used by the BCS proof, with independent
   high-entropy leaf commitments and its simulator/error bound; or
2. a protocol-specific ROM proof showing that the masked committed words
   leave sufficient conditional min-entropy in every unopened leaf/subtree,
   that opened leaves have the simulated affine distribution, and that an
   adaptive distinguisher cannot pre-query the relevant leaf or internal-node
   preimages except with a stated probability.

BCS explicitly modifies Merkle leaves to be hiding commitments and notes that
ordinary authentication paths otherwise reveal sibling information.  A
single public proof nonce is not automatically a substitute for independent
leaf hiding randomness.  "The root looks random" is therefore not a proof of
hiding for the root/path joint distribution.

The adversary in the final theorem may choose its statement/witness after
making random-oracle queries, inspect the proof, and then make adaptive
queries.  Salt unpredictability and the Merkle simulation must cover both the
pre-proof and post-proof query phases.

## Later folds and the complete-view rule

The matrix must be generated only after the complete proof schedule is known
and must include every affine field observation from:

- all three state-only terminal points;
- the masked zerocheck claim and all independent round coefficients;
- every C1, mask-only C1, `h1`, and `G` layer-zero opening;
- OOD and quotient/opening claims;
- all later WHIR/FRI fold messages and final-polynomial values;
- gamma and point-batched combinations where the underlying values are also
  exposed;
- proof-account/receipt fields, logs, and atomic before/after account data.

For fixed public challenges, a later fold which is linear in the committed
words can be appended as rows of `A_x,c` and `b_x,c`.  A nonlinear later
message needs its own simulator.  Omitting a later value can invalidate
containment even when the layer-zero-plus-terminal matrix is surjective.
Duplicate encodings of the same value may be quotiented only as exact public
copies; a raw value and its random-oracle hash are handled by different parts
of the proof.

The current width-28 candidate additionally needs the proposed `h1` padding
repair and its zero-interval claim in this same matrix.  The known
`h1`-containment counterexample is not cured by rejecting schedules: if the
mask map is structurally zero on a witness-dependent coordinate, every
schedule is bad and the prover never terminates.

## Aborts, erasure, and nonce durability

The prover must buffer a complete candidate locally.  No rejected root,
opening, nonce, partial proof, log, receipt, transaction, telemetry record, or
remote-proving message may be published.  If retry count or timing is
observable, it is part of the public view; under the theorem it is safe only
because the success law is witness-independent, and the simulator must
reproduce it.

On rejection, candidate masks, private entropy, Merkle trees, proof bytes, and
derived seeds must be zeroized.  The durable nonce record must **not** be
erased: the nonce is burned.  Reservation must occur before mask derivation or
any oracle/proving work, and a crash must leave the nonce reserved.  A new
attempt uses fresh entropy and a new nonce.  Otherwise a crash, partial
publication, or remote-prover retry can reuse a one-time pad across views.

Mask nonces need a durable uniqueness scope covering every proof under the
same wallet/masking key.  Uniform randomness and uniqueness are separate
requirements.

## Soundness effect

If the gate is honest-prover-only and the verifier is unchanged, the accepted
language and acceptance predicate are unchanged.  Consequently the gate
neither weakens nor improves soundness.  It only changes the honest proof
distribution.

If the verifier recomputes the canonical public predicate and rejects bad
schedules, its acceptance set is a subset of the old one, so soundness cannot
increase.  A prover-supplied unchecked "rank passed" bit has no such effect.

Honest rejection is still Fiat--Shamir grinding.  An adversarial prover could
already grind arbitrary transcript prefixes, and the applicable BCS/FS
soundness theorem must be parameterized by the adversary's total random-oracle
query budget/state-restoration power.  BCS soundness is not a one-sample
union bound; its error explicitly depends on the adversary's oracle-query
budget.  The gate does not authorize treating conditioned challenges as fresh
uniform challenges in the soundness ledger.  The BCS transformation and its
query-budget-dependent soundness statement are in
[*Interactive Oracle Proofs*](https://eprint.iacr.org/2016/116), Theorem 7.1;
an explicit modern formulation for FRI-family Fiat--Shamir soundness appears
in Chiesa et al., [*Fiat-Shamir Security of FRI and Related SNARKs*](https://eprint.iacr.org/2023/1071).

If a bad-rank schedule also weakens an algebraic binding or proximity check,
then it is not privacy-only.  In that case the verifier must enforce the gate
or the bad event must remain in the soundness ledger.  Honest-prover rejection
cannot repair a malicious-prover soundness event.

## Exact production gate

The rank-rejection design may be promoted from research probe only after all
of the following are artifacts rather than assumptions:

1. A frozen basis for `D_x,c` covering all valid same-statement witness
   differences, or a stronger full-row-surjectivity proof modulo explicit
   public relations.
2. A generator for the complete `A_x,c`, including the `h1` repair and all
   later PCS/fold/OOD/account observations, independently checked against the
   production prover and verifier.
3. A canonical exact M31 rank/containment implementation whose layout,
   column order, quotient relations, query geometry, and factor schedule are
   fingerprinted.
4. A proof that every accepted schedule satisfies containment; sampled
   schedules remain regression evidence only.
5. A joint success-probability theorem for the actual q36/rate-1/16 and
   q29/rate-1/32 distinct-query samplers.  The degree-24,000 SZ calculation is
   usable only after its nonzero-minor premise is universalized.
6. An EPRO Fiat--Shamir simulator with fresh-prefix/pre-query bounds and an
   explicit private-Merkle or alternative ROM path simulator.
7. A bounded retry policy, durable burned-nonce store, zeroization, and a
   declaration of whether retry count/timing is observable.
8. A soundness ledger using the applicable BCS adversarial oracle-query bound,
   plus verifier enforcement if rank failure affects anything beyond privacy.

Until those gates close, the precise statement is:

> Exact post-schedule rejection is a valid way to turn a proved
> bad-schedule probability into an honest-prover termination term.  It does
> not by itself prove Fiat--Shamir zero knowledge, Merkle-path privacy, or
> later-fold containment, and the present sampled width-28 ranks do not yet
> establish the required termination bound.

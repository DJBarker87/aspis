# Stage 2 two-point MLE batching options

Date: `2026-07-11`

Status: **fresh kappa selected note-first on `2026-07-12` for the
one-transaction M31 circle candidate.** The alternatives remain as measured
decision provenance and are not production modes.

## Ruling (`2026-07-12`)

Select **Option A: fresh kappa after gamma**. It keeps one relation lane and
the 448-byte relation payload, measures 68,380 CU in the same-build tag-25
diagnostic, and is 2,601 CU cheaper there than disjoint `gamma^51`. More
importantly, its joint column/two-point polynomial has total degree at most 51,
versus 101 for Option C. The ledger therefore charges `51/|QM31|`
(118.3276 bits), explicitly replacing the prior `50/|QM31|` column-only term.
T3 remains one degree-six relation polynomial per layer; T8 is unchanged
because kappa is charged here rather than hidden in claim batching.

The selected transcript order is fixed: bind both points and all 102 values,
sample gamma, sample fresh exact-uniform kappa, then begin the OOD/relation
rounds. Independent lanes and disjoint gamma powers are rejected as production
encodings. This ruling selects the one-transaction engineering target; it does
not claim that the full payment verifier fits 1.4M CU or close the circle-code
soundness transport.

The v4 statement exposes the same 51 committed columns at two Boolean-MLE
points, `z` and `xor11(z)`. All 102 canonical values are fixed and absorbed
before the batching challenges. Changing C1 from CM31 to the genuine-circle
M31 code does not change this decision.

For fixed claimed values, let

```text
E_0(gamma) = claimed combined evaluation error at z
E_1(gamma) = claimed combined evaluation error at xor11(z).
```

Each is a polynomial in `gamma` of degree at most 50. If any one of the 102
column evaluations is false, at least one of `E_0,E_1` is nonzero. The question
is how one interleaved relation sumcheck binds both equations without allowing
their errors to cancel.

## Option A: fresh `kappa` after `gamma`

Sample an independent exact-uniform `kappa` after both points, all 102 values,
and `gamma` are transcript-bound, then check the single relation

```text
E_0(gamma) + kappa * E_1(gamma) = 0.
```

Equivalently, add two MLE tensor-weight components to one relation accumulator
with scales `1` and `kappa`, and combine their claimed values with the same
scales.

For nonzero `(E_0,E_1)`, the bivariate polynomial
`E_0(gamma)+kappa*E_1(gamma)` is nonzero and has total degree at most 51. A
direct Schwartz--Zippel ledger may therefore charge at most `51/|F|` for the
joint gamma/point-batching event, subject to the rest of the relation proof
being sound. Stating it instead as `50/|F| + 1/|F|` is the same union bound;
the `1/|F|` event may not disappear into an unrelated term.

Consequences:

- one new transcript label/squeeze and a named KAT re-pin;
- one relation polynomial per layer remains sufficient;
- one extra tensor component is required regardless of how `kappa` is
  obtained;
- ordering teeth must move `kappa` before the 102 values, reuse it across
  proofs, set it to a constant, and swap the two point scales;
- its exact SBF cost must be measured, principally one SHA-256 squeeze plus
  field operations.

## Option B: two independently checked relation lanes

Carry two relation accumulators and check both equations separately. This
retains the degree-at-most-50 gamma argument without a point-batching
challenge, but it is not “free independence”: every layer needs a second
degree-6 relation polynomial and boundary/evaluation check.

At four layers the proof prefix grows by at least `4 * 7 * 16 = 448` bytes,
before any additional framing. Verifier relation work and its T3 accounting
must be remeasured/recounted rather than assumed to double exactly. If the two
lanes share fold challenges, a proof must show that shared randomness still
binds both polynomial messages; otherwise another batching challenge has only
been moved, not removed.

Consequences:

- no new point-batching squeeze;
- larger proof and materially more relation verification;
- a new two-lane prefix/KAT and lane-swap/omit/mix teeth;
- the cleanest statement of the existing “degree 50, non-doubling” argument,
  if the two lanes are in fact checked independently.

## Option C: disjoint powers of the existing `gamma`

Keep one relation polynomial and no new squeeze by checking

```text
E_0(gamma) + gamma^51 * E_1(gamma) = 0.
```

The two degree ranges cannot cancel identically: the first occupies powers
`0..50`, while a nonzero shifted second equation occupies `51..101`. The
combined polynomial is nonzero with degree at most 101, giving a candidate
`101/|F|` gamma term.

This is a real protocol alternative, not an implementation of the currently
recorded degree-50 statement. It would require a note-first T5 amendment,
KAT/vector changes, and a check that `gamma^51` is carried into the relation
weights without widening the per-leaf 51-column RLC. T5 is currently well away
from the binding conjectural term, but no system-bit conclusion may be inferred
until the complete ledger is recomputed.

Consequences:

- no extra transcript hash and one relation polynomial per layer;
- one second tensor component, scaled by the already available next gamma
  power;
- a wider degree term and explicit “shift omitted/off-by-one” teeth;
- potentially the cheapest verifier path, to be established by measurement.

## Rejected shortcuts

- A fixed public scalar permits deterministic cross-point cancellation.
- Reusing a per-layer OOD `mu` creates schedule/dependency conflicts and does
  not supply a pre-claim independent point-batching challenge.
- Calling the two MLE points a S-two Frobenius-conjugate pair is false; they
  live in Boolean tensor coordinates and require Aspis's custom relation.
- Counting 102 serialized values as a degree-101 polynomial without stating
  Option C confuses byte count with the selected batching algebra.

## Evidence required for an owner ruling

1. A same-build host/SBF probe for A, B, and C, with observable sinks and the
   exact relation work each option retains.
2. Proof-byte deltas and transcript-hash counts, not component projections.
3. Canonical rejection plus deliberately weakened acceptance for cancellation,
   order, omitted-lane, scale, and point-swap vectors.
4. A note-first term assignment covering T3, T5, T8, and the exact KAT change.
5. Confirmation that the chosen rule composes with the circle tensor
   accumulator through every fold and the terminal four coefficients.

Those rows now exist in `results/stage2/two_point_batching_probe.json`; the
ruling above closes this selection gate. Tag 24 may advance only with fresh
kappa and the named downstream KAT.

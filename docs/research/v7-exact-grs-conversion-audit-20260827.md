# Exact V7 circle/line-to-GRS conversion audit

Date: 2026-08-27

## Result

The two opaque conversion propositions formerly stored in
`ExactDecoderInstantiation` are gone. They are replaced by
`ExactGRSConversion`, whose fields expose:

- an equivalence between the message type and its stated coordinate
  dimension;
- an exact finite evaluation-point family and its injectivity proof;
- exact coordinate multipliers and their nonvanishing proof;
- an injective message-to-polynomial map and its degree bound; and
- the pointwise equality between every released encoder coordinate and the
  corresponding generalized Reed--Solomon coordinate.

Multiplication by every coordinate multiplier is packaged as an explicit
equivalence. Exact Hamming-agreement equality and arbitrary-threshold
equivalence are derived theorems, not fields of the structure.

The terminal concrete results are:

```text
exactFinalEncoder_eq_grs
exactFinalAgreementCount_eq_grs
exactFinal9558_transport

exactInitialEncoder_eq_grs
exactInitialAgreementCount_eq_grs
exactInitial38230_transport
```

`ExactDecoderInstantiation.initialThreshold_transport` and
`ExactDecoderInstantiation.finalThreshold_transport` expose the same result
at the decoder interface. Consequently `publishedApplicability` now contains
only the remaining Guruswami--Sudan applicability proposition; it no longer
contains a circle/line-to-GRS proposition.

## Mathematics audited and reused

The proof reuses the released definitions rather than introducing another
encoder or field model:

- `V7C1ConcreteProjectionBinding.exactInitialEncoder`, the exact stored
  log-20 circle evaluator;
- `V7Tag73ExactOneFoldEncoderBinding.exactFinalEncoder`, the exact stored
  log-18 natural-line evaluator;
- `V7ExactOneFoldDomains.storedInitialCirclePoint20` and
  `storedFirstLineX18`, including their bit-reversed ordering and injectivity
  theorems;
- the exact `M31Exact -> CM31Exact -> QM31Exact` tower from
  `V5ComponentCQM31TowerExact`;
- the generator/order and west-pole avoidance results behind the exact circle
  domain;
- the natural-basis polynomial conversion and its injectivity/completeness
  theorems;
- `V5FriCircleEncoderDistance.CirclePolynomialRealization`,
  `circleNumerator`, its degree and injectivity proofs, the stereographic
  evaluation identity, and parameter injectivity; and
- the V6 distance, parameter, and published-interface files used by the
  algorithmic decoder boundary.

No existing GRS definition in mathlib or Aspis covered this exact boundary.
The new `generalizedReedSolomonEncode` is the conventional coordinate formula
`v_i * p(a_i)` and is connected directly to the released encoders.

## Final 256-to-2^18 line code

For stored index `i`, the point and multiplier are

```text
a_i = algebraMap M31Exact QM31Exact (storedFirstLineX18 i)
v_i = 1.
```

The message polynomial is the existing
`naturalCoefficientPolynomial`. Its degree is at most 255, its map from 256
natural-basis coefficients is injective, and
`exactFinalMessagePolynomial_complete` proves that every polynomial of degree
at most 255 occurs. Thus this is the full dimension-256 GRS code.

The point family is injective by the exact stored-line-domain theorem and the
injectivity of the M31-to-QM31 algebra map. The coordinate permutation is the
identity because the GRS points are indexed in the released bit-reversed
order. Since every multiplier is one, received words need no transformation.

## Initial 1024-to-2^20 circle code

Let the exact released stored point at index `i` be `(x_i,y_i)`. The GRS point
is the exact stereographic parameter

```text
t_i = algebraMap M31Exact QM31Exact (y_i / (1 + x_i)).
```

For released message `m`, let `p0_m` and `p1_m` be the existing two natural
circle polynomials. The message polynomial is the existing cleared numerator

```text
q_m = mobiusLift 512 p0_m + (2 * X) * mobiusLift 511 p1_m.
```

The coordinate multiplier is

```text
v_i = ((1 + t_i^2)^512)^(-1).
```

The proof establishes:

```text
q_m(t_i) = (1 + t_i^2)^512 * exactInitialEncoder m i
```

and hence

```text
exactInitialEncoder m i = v_i * q_m(t_i).
```

The parameters `t_i` are pairwise distinct by the existing exact circle
realization. Their denominator factor is nonzero: every `t_i` lies in the
embedded M31 base field, where `-1` is a proved nonsquare, so
`1 + t_i^2 != 0`. This also proves every `v_i` nonzero and makes its scaling
explicitly invertible.

The existing circle-numerator theorems prove that `m -> q_m` is injective and
that `degree q_m <= 1024`. The message space still has exactly 1024
coordinates, recorded by `messageCoordinates`. It is therefore a
1024-dimensional subcode of the conventional degree-at-most-1024 ambient GRS
code, exactly as the paper's Section 6.2 describes; it is not misstated as the
full 1025-dimensional polynomial space. This ambient-code embedding is the
needed list-decoding direction: every close released codeword is exactly the
corresponding close ambient GRS word, while restricting an ambient decoder's
list to the injective released message image can only shrink the list.

As for the final code, the coordinate permutation is the identity because the
point family retains the released stored bit-reversed order.

## Exact agreement transport

For both encoders and every received word and message, Lean proves literal
equality of the two agreement counts. The threshold results are equivalences,
not inequalities:

```text
closeAtLeast 9558 exactFinalEncoder received message
  <-> closeAtLeast 9558 exactFinalGRSConversion.grsEncoder received message

closeAtLeast 38230 exactInitialEncoder received message
  <-> closeAtLeast 38230 exactInitialGRSConversion.grsEncoder received message
```

No received-word scaling is needed because the nonzero column scaling is
already part of the GRS encoder and the encoded words are pointwise equal.

## Kernel and replay status

Every terminal `#print axioms` report contains only:

```text
propext
Classical.choice
Quot.sound
```

The focused replay is:

```sh
tools/replay_v7_exact_grs_conversion.sh
```

It checks Lean 4.32.0, rejects `sorry`, `admit`, project `axiom`
declarations, and `native_decide` in the changed proof sources, rejects
`sorryAx` and compiled-reduction axioms in the replay output, recompiles both
modules, and checks the terminal axiom reports.

## Boundary that remains external

This change does not formalize Guruswami--Sudan or the correlated-agreement
theorem. The executable decoder completeness/soundness, its multiplicity-three
Guruswami--Sudan applicability statement, and deterministic polynomial-time
claims remain fields of the algorithm package. The published correlated-
agreement reductions elsewhere in Aspis also remain external at their already
named boundaries.

No V7 protocol step, wire format, security parameter, Rust verifier code, or
Pool semantic definition is changed by this conversion proof.

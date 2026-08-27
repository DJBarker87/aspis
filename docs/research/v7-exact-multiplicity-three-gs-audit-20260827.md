# Exact V7 multiplicity-three Guruswami--Sudan audit

Date: 2026-08-27

## Result

Lean now proves exact multiplicity-three interpolation/list-decoding theorems
for both concrete V7 GRS instances:

```text
final:   256 messages -> 2^18 symbols, degree <= 255,
         threshold 9558, list cap 99

initial: 1024 messages -> 2^20 symbols, degree <= 1024,
         threshold 38230, list cap 100
```

The terminal concrete packages are:

```text
exactFinalMultiplicityThreeGS
exactInitialMultiplicityThreeGS
```

For each received word they expose a nonzero interpolation coefficient
vector, its six multiplicity-three Hasse constraints at every evaluation
point, the finite polynomial-root candidate set, a single-valued decoded
list, exact completeness/soundness, no duplicates, and the published output
bound. The separate terminal completeness theorems are:

```text
exactFinalRootCandidates_complete
exactFinalGSDecode_mem_iff
exactFinalGSDecode_length_le_99

exactInitialRootCandidates_complete
exactInitialGSDecode_mem_iff
exactInitialGSDecode_length_le_100
```

`ExactDecoderInstantiation.multiplicityThreeGuruswamiSudanApplicable` and
the derived opaque `publishedApplicability` proposition have been removed
from `AlgorithmicCircleDecoderV7.lean`.

## Initial degree convention

The initial released message space has 1024 field coordinates, but its exact
stereographic numerator is only proved to have maximum degree 1024. It is a
1024-dimensional subcode of the 1025-dimensional ambient polynomial space
of degree at most 1024; it must not be silently replaced by the degree-less-
than-1024 code.

`exactInitialAmbientDegreeConvention` proves all three relevant facts:

```text
degree (messagePolynomial message) <= 1024
initialRate = 1024 / 1048576
initialRate != 1023 / 1048576
```

The initial interpolation machinery therefore uses weight 1024. The final
natural-basis encoder uses the conventional degree bound 255 for its full
256-dimensional polynomial space.

## Exact interpolation parameters

The common multiplicity is 3 and the selected Y-degree is 112. The six Hasse
constraints are exactly the derivative pairs

```text
(0,0), (1,0), (0,1), (2,0), (1,1), (0,2).
```

For the final instance, weighted degree `D = 28673` gives:

```text
weighted monomials = 1626522
constraints        = 6 * 262144 = 1572864
28673 < 3 * 9558 = 28674
```

For the initial instance, weighted degree `D = 114689` gives:

```text
weighted monomials = 6480098
constraints        = 6 * 1048576 = 6291456
114689 < 3 * 38230 = 114690
```

The monomial counts are kernel-checked finite sums. A finite-dimensional
linear-map kernel argument produces a nonzero interpolation vector because
the coefficient-space dimension is strictly larger than the constraint-space
dimension.

## Multiplicity and root forcing

`interpolationSubstitute` is the ordinary univariate polynomial `Q(X,f(X))`.
Lean proves exact first- and second-derivative chain rules from the six Hasse
constraints. At every agreement coordinate these imply that the value, first
derivative, and second derivative vanish. Since two is nonzero in the exact
QM31 field, the Taylor coefficients of orders zero, one, and two vanish, and

```text
(X - a_i)^3 divides Q(X,f(X)).
```

Distinct evaluation points then contribute three roots each, counted with
multiplicity. Weighted-degree substitution proves

```text
degree Q(X,f(X)) <= D.
```

Thus at either exact threshold, a nonzero `Q(X,f(X))` would have strictly more
roots than its degree. `interpolationSubstitute_eq_zero_of_agreement` concludes
the exact polynomial identity `Q(X,f(X)) = 0`.

## Exact released-code transport

The proof reuses `exactFinalGRSConversion` and `exactInitialGRSConversion`.
Their concrete point families, point-injectivity proofs, message polynomial
maps, degree bounds, nonzero multipliers, bit-reversed coordinate ordering,
and released-encoder coordinate identities are unchanged.

For the final code every multiplier is one, so the interpolation values are
the received symbols themselves. For the initial code Lean defines

```text
normalizedReceived i = (multiplier i)^(-1) * received i
```

and uses the existing nonzero-multiplier proof to establish exact equality
between normalized polynomial-agreement cardinality and agreement with the
concrete GRS word. The existing released-word/GRS agreement transports then
connect both root-completeness theorems to the exact released V7 encoders.

## Candidate production and list caps

For each received word, `Classical.choose` fixes one nonzero interpolation
solution. The root-candidate set is the finite set of released messages whose
message polynomial satisfies `Q(X,f(X)) = 0`. The decoded list retains exactly
the candidates meeting the concrete released-word agreement threshold.

This is a deterministic, single-valued finite mathematical decoder: it uses
no randomness or caller-supplied oracle. It is intentionally a specification-
level `noncomputable` definition; this change does not claim an extracted or
polynomial-time interpolation/factorization implementation.

Completeness follows from the multiplicity-three root theorem. Soundness is
definitionally enforced by the exact agreement filter. The exact V7 pairwise
overlap theorems and the existing Johnson counting lemmas prove fewer than 100
final close messages and fewer than 101 initial close messages, yielding list
lengths at most 99 and 100 respectively.

## Kernel and replay evidence

The focused replay is:

```sh
tools/replay_v7_exact_multiplicity_three_gs.sh
```

It checks Lean 4.32.0, rejects `sorry`, `admit`, project `axiom`
declarations, and `native_decide`, builds the exact boundary and GS modules,
directly replays both changed source files, and verifies every terminal axiom
report.

The formal-source replay was run at revision
`805021f139d30db3848fb35fc6411d8cacda9238` with:

```sh
/usr/bin/time -l ./tools/replay_v7_exact_multiplicity_three_gs.sh
```

The command exited 0 in 159.30 seconds, with peak RSS 5,960,253,440 bytes and
zero swaps. Every terminal `#print axioms` report contains only:

```text
propext
Classical.choice
Quot.sound
```

There is no `sorryAx`, project axiom, compiled-reduction axiom, or substantive
`native_decide` dependency.

## Boundary that remains external

This result closes exact finite-list decoding for the two V7 GRS instances in
Lean. It does not prove a polynomial-time executable implementation of
interpolation or polynomial factorization. The existing
`initialDeterministicPolynomialTime` and `finalDeterministicPolynomialTime`
interface propositions are therefore unchanged.

The S-two width-29 correlated-agreement theorem remains external. In
particular, this proof does not address the stronger quantifier pattern in
which a different nearby candidate may be selected for each batching
challenge. Guruswami--Sudan statements for unrelated V5 code instances and
the Ganesh/WUR extraction path are also out of scope.

No V7 proof protocol, wire format, security parameter, Rust verifier, or Pool
semantic definition is changed.

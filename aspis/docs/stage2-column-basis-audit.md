# Stage 2 C1 column-basis audit

Date: `2026-07-11`

Status: **M31 C1 is a valid candidate only with a circle-polynomial PCS. It
is not a wire-only optimization of the current Aspis PCS. No product or
architecture ruling follows from this audit.**

## Why current Aspis opens CM31

`SpendTraceV4` stores 49 M31 columns, but the current prover interprets each
column vector as coefficients of an ordinary univariate polynomial
`f(T)=sum_j c_j T^j`. It scales by the CM31 coset offset and runs a CM31 NTT:

- `crates/aspis-statement/src/trace_v4.rs` defines the M31 trace;
- `crates/aspis-prover/src/lib.rs` `coset_evaluate` (lines 83-125) performs
  the CM31 NTT and the layer-zero commit path calls it (lines 833-840);
- `crates/aspis-core/src/proof.rs` fixes layer-zero fibers as four CM31
  values;
- `crates/aspis-core/src/verify.rs` parses those CM31 values and applies the
  multiplicative-FFT fold over CM31 denominators.

Those evaluations are genuinely CM31. For the one-term polynomial `f(T)=T`,
the codeword contains the non-real circle-coset point itself. Its second M31
limb is data, not padding.

Two names had obscured this distinction:

- `raw_fibers` selects proof payload packaging: the verifier receives the
  four committed values and recomputes the fold. It does not select M31 wire
  values.
- `late_lift_qm31` means layer zero stays CM31 until a QM31 challenge is
  applied. It does not mean layer zero stays M31.

The exact-wide CM31 diagnostic is therefore faithful to the current custom
PCS, but it does not prove that this PCS is the best basis for the payment
statement.

## Primary-source M31 alternative

Official Stwo source was audited at
`starkware-libs/stwo@5d10e6b4baa559766e7bbae133b918121211a9c5`:

- `crates/stwo/src/core/circle.rs` represents circle points by separate M31
  `(x,y)` coordinates;
- `core/poly/circle/domain.rs` constructs base-field circle domains;
- `prover/poly/circle/evaluation.rs` and `poly.rs` keep circle evaluations
  and FFT coefficients in the base field;
- `prover/pcs/mod.rs` commits and decommits base-field columns;
- `prover/poly/circle/secure_poly.rs` lifts to secure-field coordinate
  columns only after challenge batching;
- `prover/backend/cpu/fri.rs` performs a circle-to-line first fold followed
  by line folds.

Thus circle domains do not intrinsically require CM31 code symbols. Aspis
chose a CM31 multiplicative Reed-Solomon-style encoding over the circle group;
Stwo uses M31-valued circle polynomials evaluated at M31 `(x,y)` points.

## What an M31 Aspis variant changes

An honest M31 variant must move as one protocol change:

1. replace the CM31 coset NTT with the circle FFT and pin coefficient order;
2. use a circle-to-line first fold and line folds thereafter;
3. replace scalar geometric OOD weights with circle-basis weights and secure
   circle points;
4. parse and authenticate M31 C1 leaves while retaining QM31 C2;
5. change roots, queries, proof offsets, a wire discriminator, and the KAT;
6. re-derive the circle-FRI soundness transport and T1/T2 mapping.

The coefficient fold is host-conformant for the candidate first layer: the
first four circle basis terms align with
`a0 + alpha*a1 + alpha^2*a2 + alpha^3*a3`, and the pinned test mechanically
checks bit-reversed ordering and the normalized circle-to-line/line fold.
This is not a soundness-transport result or a production PCS integration.
T5 remains degree 50 merely from changing the C1 basis; C2 and gamma still
span 51 columns.

For slot order `(x,y), (x,-y), (-x,-y), (-x,y)`, the normalized candidate
fold is:

```text
g_pos = (v0+v1)/2 + alpha*(v0-v1)/(2y)
g_neg = (v2+v3)/2 + alpha*(v2-v3)/(-2y)
out   = (g_pos+g_neg)/2 + alpha^2*(g_pos-g_neg)/(2x)
```

On the four-term circle basis this equals the coefficient fold above. Stwo's
raw inverse-butterfly convention omits the halves and is therefore four times
this normalized value; the conformance test must pin that normalization rather
than accepting a global-factor drift.

## Host conformance result

`crates/aspis-prover/tests/m31_circle_conformance.rs` and its test-only scalar
reference module pin Stwo commit
`5d10e6b4baa559766e7bbae133b918121211a9c5`. They pass an actual 49-column,
1,024-coordinate `SpendTraceV4` through the log-12 M31 circle encoder and
check:

- official Stwo FFT vectors and direct point evaluation;
- the bit-reversed `(p, Jp, Ap, JAp)` four-slot geometry;
- the normalized first two folds against coefficient/line evaluation;
- secure-circle OOD evaluation in the `[y, x, pi(x), ...]` tensor basis; and
- late gamma recombination before/after encoding, folding, and OOD evaluation.

Those last two checks are deliberately narrow. The original OOD check is a
one-point algebraic identity. `aspis-core` now separately implements and
materialization-tests the reverse-ordered `[..., pi(x), x, y]` tensor
component, the circle-to-line tail, the non-panicking rational sampler, and
bounded singular/subfield rejection. Those arithmetic units are not yet wired
to the production relation sumcheck or proof transcript. Two sequential s=2
samples and their weakened-order acceptance/rejection fixture are pinned at
the core transcript level, but the complete C1/C2 production absorption order
remains open. Late gamma
covers the 49 C1 columns at powers 0..48 only; the two C2 helpers at powers
49/50, both statement points, 102 pre-gamma values, and challenge-order teeth
remain open. The normalized fold uses one actual-trace fiber and challenge;
boundary/random fibers and an official full-PCS differential remain production
gates.

The separate later-line conformance artifact
`results/stage2/m31_line_fri_conformance.json` closes the host arithmetic/order
question, not the PCS integration. Against official Stwo at the same pinned
commit, 48 deterministic randomized cases cover 108 radix-4 rounds and 1,077
four-value fibers. Stwo's `LinePoly` stores coefficients in bit-reversed order:
two raw line folds at `alpha` and `alpha^2` equal four times the bit-reversal of
Aspis's adjacent natural-order radix-4 fold. After `r` rounds the raw scale is
`4^r`. The bridge is explicit, so the existing natural MLE/`WeightAccumulator`
variable order does not change. Merkle authentication, transcript challenges,
proof framing, and SBF execution are still unimplemented for this candidate.

The separate `stage2-circle-soundness-transport.md` audit draws the theorem
boundary. The direct `L'_10` tensor code is a subcode of S-two's full circle
code, so its scaled-GRS isometry and Johnson-regime code facts apply
conservatively. They do not prove Aspis's grouped arity-4 correlated-agreement
steps, two-phase C1/C2 batching, custom Boolean-MLE relation, rational OOD
denominator, or BCS/ROM ledger. No T1/T2 number is transported by the host
conformance tests.

The trace-vector interpretation is explicit. Aspis is a multilinear PCS:
`c1[column][row]` is a message/MLE coordinate in the big-endian Boolean index
order used by `WeightAccumulator::from_claim`, and is fed directly to the
low-degree encoder. It is not an AIR evaluation interpolated by a circle IFFT.
The conformance test checks the MLE/`eq(z,x)` claim before encoding so an IFFT
reinterpretation cannot enter silently.

The candidate-only KAT binds the separate discriminator, MLE coordinate
contract, Stwo commit, 784-byte leaf, fold, OOD value, and the requirement for
a new circle-tensor OOD weight component plus transcript re-pin. The measured
artifact is `results/stage2/m31_circle_conformance.json`. It assigns no
production envelope version.

## Structural delta at q36

| item | current CM31 C1 | candidate M31 C1 | delta |
| --- | ---: | ---: | ---: |
| one 49-column, four-slot C1 leaf | 1,568 B | 784 B | -50% |
| 36 distinct C1 openings | 56,448 B | 28,224 B | -28,224 B |
| parsed C1 M31 limbs | 14,112 | 7,056 | -50% |
| prepared C1 base multiplications | 42,336 | 28,224 | -14,112 (-33.3%) |

C2 bytes and helper arithmetic remain unchanged. The first-fold cost does not
scale mechanically from this table: the candidate loses the current free
unit-circle conjugate inversion and needs measured circle/line denominator
handling.

## Calibration entry

The old fixed51 RLC model priced one row of 51 M31 values per query. The exact
current-PCS fiber contains four slots of 49 CM31 values: 392 M31 limbs, a
`392/51 = 7.686` limb-count mismatch before helper work. The prior seam-basis
warning identified the right uncertainty but stopped before pinning slot count
and value type. This is recorded as a shared calibration miss; neither the old
113K model nor a limb-ratio projection may decide the gate.

## Required evidence before selection

The decision packet needs four separate artifacts:

1. a diagnostic-only q36 M31 four-slot arithmetic/leaf probe under the
   standard heap, explicitly excluding PCS validity;
2. host conformance of an actual 49-column `SpendTraceV4` circle FFT, first
   fold, one-point OOD algebra, and C1 late-gamma recombination against the
   pinned Stwo source;
3. production integration of the host-conformant circle-tensor accumulator and
   line-FRI bridge with the s=2 transcript, C2 powers 49/50, authenticated
   roots/KAT and weakened corruption vectors;
4. only after production conformance, an in-place multi-seed verifier
   measurement.

The M31 diagnostic can price the lever. It cannot authorize the replacement
PCS, freeze one-transaction infeasibility, or adopt transport splitting.

## Current-PCS conjugate-pair compression

There is a genuine symmetry in the current ordinary-univariate layer zero.
For M31 coefficients and unit-circle CM31 domain points,

```text
conj(f(s_i)) = f(conj(s_i)) = f(s_(N-1-i)).
```

Writing `N = 4F` and the current fiber as
`L[f][m] = f(s_(f+mF))`, conjugation maps fibers and slots as

```text
f_bar = F - 1 - f
L[f_bar] = [conj(L[f][3]), conj(L[f][2]),
            conj(L[f][1]), conj(L[f][0])].
```

The test checks this componentwise on the real 49-column trace. A verifier
could reconstruct the partner leaf and apply the unchanged fold using the
original orientation and domain point. It does not halve the queried payload:
the four conjugates live in the partner fiber, so a scalar opening remains 32
bytes and the 49-column wide opening remains 1,568 bytes.

At lr10, the C1 tree would shrink from 1,024 to 512 leaves. That is not a valid
drop-in for the current pure-radix-4 tree, and C1 would no longer share C2's
Merkle depth. It requires canonical query indices plus an orientation bit,
mixed-radix or binary Merkle semantics, a new root/transcript KAT, and renewed
soundness accounting for the two-to-one query map. At q36 the expected unique
C1 leaves move only from 35.3915 to 34.7963, about 0.595 leaf. Verdict:
algebraically valid symmetry, but not a wire-compatible payload-halving or a
credible ten-percent incremental lever.

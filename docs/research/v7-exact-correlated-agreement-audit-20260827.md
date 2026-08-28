# Exact V7 correlated-agreement audit (2026-08-27/28)

## Result

This branch reconstructs the correlated-agreement/curve-decodability argument
for both exact released V7 codes.  The terminal Lean theorems are:

```lean
exactV7FinalDegreeThreeCurveDecodable :
  DegreeThreeCurveDecodable exactFinalEncoder 9557 foldChallengeCap

exactV7InitialWidth29CurveDecodable :
  Width29CurveDecodable exactInitialEncoder 38229 initialBatchChallengeCap
```

The corresponding `PublishedOneFoldCurveDecodability` and
`PublishedInitialWidth29CurveDecodability` predicates are discharged by
theorems, not supplied by callers in the exact V7 K1.3/K1.4 route.
`V7Tag73ExactConcreteK13K14Events` derives the final predicate internally,
while `V7Tag73CausalK14FailureProbability` derives the initial predicate after
the caller supplies only equality with the concrete released encoder.  The
lower historical/generic reduction remains parameterized and is not put in a
dependency cycle with the exact V7 construction.

## Source theorem reconstructed

The source map is recorded in
`v7-exact-correlated-agreement-theorem-map-20260827.md`.  The principal source
is S-two, IACR ePrint 2026/532, Definition 24 and Theorem 25, used in its
Theorems 28/29.  Its algebraic source is BCH+25, *On Proximity Gaps for
Reed--Solomon Codes*, IACR ePrint 2025/2055, especially Lemma 3.1 and Sections
3.2 and 4.1.  The checked BCH+25 PDF SHA-256 is
`8f6b42e6f75101698f0d7ff6f26d0d8776e27880b386c7932d3f8890c39df572`.
The repository bibliography also pins the S-two PDF as described in the
theorem map.

The reconstruction proves the substance rather than importing Theorem 25:
one multiplicity-three trivariate interpolant, fixed global and local
irreducible factors, smooth specialization, finite-characteristic Hensel
lifting, regular/pole-controlled specialization, weighted zero counting,
incidence extraction, and the existing root-union finalization.

## Exact parameters and released code image

| Instance | Domain | Released message | Polynomial bound | Strict support | Agreement | Release cap |
|---|---:|---:|---:|---:|---:|---:|
| initial width 29 | `Fin 1048576` | `Fin 1024 → QM31Exact` | degree `≤ 1024` | `38229 < card` | `≥ 38230` | `336869026605739` |
| final degree 3 | `Fin 262144` | `Fin 256 → QM31Exact` | degree `≤ 255` | `9557 < card` | `≥ 9558` | `9396508281246` |

The initial degree convention is intentionally not changed to degree
`< 1024`.  Its released image has dimension 1024 inside the 1025-dimensional
ambient degree-`≤ 1024` space.  `exactInitialLinear`, encoder addition/scalar
laws, and the released-image lift prove closure for the actual message image.
The terminal theorem returns `Fin 29 → InitialMessage QM31Exact`; it never
substitutes the full ambient polynomial space.  The final theorem similarly
returns four actual `FinalMessage QM31Exact` values.

The initial interpolation constraints normalize each released coordinate by
the inverse of the exact nonzero GRS multiplier.  After constructing the
ambient challenge curve, the proof multiplies the coordinate curves back by
those exact multipliers and invokes the released-image theorem.  The final
GRS multipliers are one.

## Challenge-dependent candidates and the fixed branch

The strategy retains its adversarial quantifiers:

```text
for every challenge gamma, strategy.candidate gamma and strategy.support gamma
```

No candidate list is fixed before the challenge and no `∀ γ, ∃ Cγ` is
exchanged with `∃ C, ∀ γ`.  Each valid candidate is first shown to be a root
of the one symbolic interpolant specialized at its own challenge.

The outer selection proof then assigns each challenge to a literal pair
`(R,H)`, where `R` is one global irreducible factor and `H` is one irreducible
factor after a single uniform smooth `X=x₀` specialization.  A weighted
pigeonhole theorem counts that exact pair.  It does not merely observe that
each specialization has some linear factor.

The selected fiber explicitly excludes:

- challenges where the entire interpolant specialization vanishes (the
  content exception in BCH+25);
- challenges where specialization causes factor collision or a multiple
  root, detected by resultants;
- challenges where the local leading coefficient vanishes (poles).

`SimpleSpecializedRoot` contains both the specialized root equation and the
nonzero specialized `Y` derivative.  Separability/resultant nonvanishing is
proved over `QM31Exact`; no characteristic-zero derivative principle is used.
The chosen local factor is proved irreducible over `QM31Exact(Z)`, and the
regularized Hensel derivative is explicitly nonzero before lifting.

## From the branch to a common released-code curve

The Hensel development constructs the unique formal branch at `X=x₀`, proves
the regularized coefficient recurrence and weight bounds, excludes poles,
and specializes it at each challenge in the fixed fiber.  Weighted zero
counting makes the branch a bounded polynomial curve.  Incidence counting
then shows that the per-coordinate received curves equal that branch on all
coordinates needed for interpolation.

Lagrange interpolation produces ambient component polynomials, after which
the released-image lift explicitly produces component messages.  Finally the
existing `V6Width29CorrelatedAgreement` and
`V5FriDegreeThreeCorrelatedAgreement` root-union lemmas use selected-set sizes
strictly greater than `28·2^20` and `3·2^18`, respectively.

The conservative arithmetic proved before the terminal applications is:

```text
initial outer budget = 87,316,067,086,790
                     < 336,869,026,605,739

final outer budget   = 2,388,155,905,379
                     < 9,396,508,281,246
```

These are the existing release caps.  The exact GS list caps 100 and 99 do
not, by themselves, replace the BCH+25 weighted factor budget.  This branch
therefore records no tighter production correlated-agreement cap and changes
no security parameter.

## Kernel axioms and replay

Both terminal theorem families contain `#print axioms`.  The expected and
observed pure-mathematics footprint is exactly the ordinary Lean foundations:

```text
propext
Classical.choice
Quot.sound
```

There is no `sorryAx`, project axiom, `admit`, `native_decide`, compiled
reduction axiom, or theorem-shaped conversion/correlated-agreement premise.

The focused replay is:

```sh
tools/replay_v7_exact_correlated_agreement.sh
```

For high-memory release evidence it is run on `nuc.local` in a dedicated
workspace and a one-worker systemd scope with explicit `MemoryHigh`,
`MemoryMax`, and `MemorySwapMax=0`.

The final synchronized replay used the 40 exact proof/integration sources whose
sorted SHA-256 manifest has SHA-256
`50d80211b272a638f15cd14feef5ee1d61f1aca572fbc95d1ded287a43ac4883`.
Those files were checked byte-for-byte equal between the local branch and the
NUC workspace before the run.  They are based on
`e1add10ea5782ecbf517f8ec3124d6fa6373818b` and were committed, without any
post-replay proof-source change, as
`620fe61e453dedb9353b8965bfe8e83ed6747d7f`.

The release command was equivalent to:

```sh
systemd-run --user --scope --collect \
  --unit=aspis-v7-correlated-final-replay-20260828-r2 \
  -p MemoryHigh=34G -p MemoryMax=40G -p MemorySwapMax=0 \
  /usr/bin/time -v env \
    PATH=/home/dombarker/.elan/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin \
    V7_EXACT_CORRELATED_REPLAY_OUT=/home/dombarker/project-offloads/aspis-v7-exact-correlated-agreement-20260828/replay-final-20260828-r2 \
    ./tools/replay_v7_exact_correlated_agreement.sh
```

It passed with exit status 0 in 45.38 seconds, maximum resident set size
14,839,184 KiB, and zero swaps.  The three measured replay stages were:

| Stage | Wall time | Peak RSS | Swaps | Exit |
|---|---:|---:|---:|---:|
| focused six-target Lake build | 2.66 s | 968,796 KiB | 0 | 0 |
| direct final terminal replay | 39.27 s | 14,839,184 KiB | 0 | 0 |
| direct initial terminal replay | 2.97 s | 6,653,424 KiB | 0 | 0 |

The replay log is
`/home/dombarker/project-offloads/aspis-v7-exact-correlated-agreement-20260828/replay-final-20260828-r2/lean432.log`,
with SHA-256
`240df1a6bd429bfb3d9c3a961536a789bfb3bee4e36225210ed85989f527340a`.
It contains all four terminal axiom reports and the final line
`PASS exact V7 correlated agreement` is emitted by the wrapper.

The cold focused proof of the largest width-29 branch-to-released-curve module
was separately run as
`aspis-v7-correlated-initial-curve-branch-20260828-r2.scope`.  It passed in
8:05.52 with `/usr/bin/time` maximum RSS 38,995,880 KiB, zero swaps, and exit
status 0 under `MemoryHigh=34G`, `MemoryMax=40G`, and `MemorySwapMax=0`.
During that run the sampled cgroup peak was lower than `/usr/bin/time`'s peak;
the audit conservatively records the larger `/usr/bin/time` measurement.

An earlier monolithic initial-terminal attempt was stopped manually at a
sampled cgroup peak of 25,771,704,320 bytes (about 24.0 GiB), with zero swap
and before OOM.  It was not rerun unchanged with a larger cap: the declaration
was isolated into the `InitialRoot`, `InitialBranch`, `InitialSelection`,
`InitialCurveBranch`, `InitialCurve`, and `Initial` modules.  The successful
cold and final replays above cover that refactored proof.

Before promotion to `main`, current `origin/main` at
`0ad65eb6708d83e78282c304d8ec3dd9350c197d` was merged without conflict as
`835c71adc0d7fda4db320b4f67638077a58e9e1b`.  The checksum-synchronized merged
source tree was then replayed again in
`aspis-v7-correlated-main-merge-replay-20260828-r1.scope`, under the same
34/40-GiB no-swap limits.  That post-merge replay passed in 8:29.32, with
`/usr/bin/time` peak RSS 38,999,324 KiB, sampled cgroup peak
36,040,204,288 bytes, zero swaps, and exit status 0.  Its log is
`/home/dombarker/project-offloads/aspis-v7-exact-correlated-agreement-20260828/replay-main-merge-20260828-r1/lean432.log`,
SHA-256
`8093ae6686422a44983c5520c13a6f237f4ee1d6c748e690abebb2e18fa6d60c`.
The log again contains all four terminal axiom reports with only `propext`,
`Classical.choice`, and `Quot.sound`.

## Boundaries that remain

This change proves mathematical curve decodability/correlated agreement.  It
does not prove that the noncomputable GS interpolation/factorization decoder
is a deterministic polynomial-time executable implementation.  The two
`ExactDecoderInstantiation.*DeterministicPolynomialTime` fields therefore
remain explicit.  SHA/random-oracle assumptions, Poseidon security,
source/toolchain/runtime refinement boundaries, and Ganesh/WUR observed-proof
extraction are unchanged and out of scope.

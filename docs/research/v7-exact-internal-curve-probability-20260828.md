# V7 exact internal curve-probability bridge — 2026-08-28

## Result

`V7Tag73ExactInternalCurveProbability.lean` specializes the causal Tag-73
K1.3/K1.5 probability bounds to the exact V7 correlated-agreement theorems.
The operational theorem signatures no longer receive either published
curve-decodability result from their caller.

The bridge provides:

- `exact_causal_oneFold_duplex_alpha_probability_le`;
- `exact_causal_restored_k15_residual_duplex_gamma_probability_le`;
- `exact_causal_restored_k15_duplex_gamma_probability_le`.

The one-fold specialization constructs the exact algebraic encoder binding
from the Tag-73 schedule, exact initial/final encoders and exact inverse tables,
then installs `exactV7FinalPublishedOneFoldCurveDecodability`.  The restored
K1.5 specializations install
`exactV7InitialPublishedWidth29CurveDecodability`.

The remaining operational inputs are protocol-specific counterfactual/source
coordinate providers and, for the ungated K1.5 statement, the already explicit
absence of a restored K1.4 certificate.  SHA-256, Poseidon and deployed-source
bindings are not silently discharged here.

## Focused replay

The target was copied to the existing exact-correlated-agreement NUC workspace
and built under a systemd cgroup:

```text
unit: aspis-v7-exact-internal-curve-02
target: AspisFormal.K1.V7Tag73ExactInternalCurveProbability
result: PASS (8,971 jobs)
wall: 11.07 s
peak RSS: 6,752,404 KiB
swap: 0
MemoryHigh: 22 GiB
MemoryMax: 28 GiB
MemorySwapMax: 0
```

The four printed declarations report exactly the following axiom union:

```text
propext
Classical.choice
Quot.sound
```

There is no `sorry`, `admit`, `sorryAx`, project-specific axiom, or supplied
published coding theorem in these declarations.

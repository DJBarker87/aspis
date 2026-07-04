# Open soundness question: whir-p3 Johnson divergence (feeds Stage 1)

Recorded per Stage 0 work item 4 (design §7.4). Status: **open**. Owner:
Stage 1 soundness audit (design §8.1).

## The question

The staged design records that a whir-p3 cross-validation of the reference
native v0 found the local folding schedule **not upstream-equivalent**: the
local schedule started folding PoW at **13 bits versus upstream's 36 bits**
under Johnson-regime accounting. The cross-validation artifacts are not in
this repository (see Deviation 1 in `docs/stage0-gate.md`); the divergence is
carried over as design-document context because it constrains what may be
claimed about ANY v0-lineage verifier, including the one bootstrapped here.

## What it implies for this tree

1. **No Johnson-bound number may be quoted publicly** for this substrate
   until the divergence is resolved or the claim is re-labelled. The
   `johnson_lr12_q80_g16` profile name is a query-count shape, not a security
   statement; its label is `heuristic` and stays that way through Stage 0.
2. The v0 bootstrapped here has **no round-wise PoW at all** — a single
   grinding check after the final-poly absorb (16 bits in both Stage 0
   profiles). This is a further simplification relative to both the reference
   v0 and upstream WHIR, and it must appear as its own line in the Stage 1
   proximity-parameter accounting (queries per round, rate, grinding, regime,
   per-round budget in bits).
3. Related v0 gaps the Stage 1 audit checklist already names, restated here
   because they interact with the Johnson question: no out-of-domain samples
   (upstream WHIR uses nonzero OOD in the list-decoding regime), no
   sumcheck/fold interleaving, queries derived once after all roots and the
   final value rather than per round.

## Exit criteria

Closed when the Stage 1 soundness note (`docs/aspis-soundness-note.md`)
either (a) derives a per-round soundness budget for the implemented schedule
in a stated regime (UD / Johnson / capacity) against the pinned upstream
`WizardOfMenlo/whir` reference and re-labels every profile accordingly, or
(b) documents that the implemented schedule cannot reach the target in the
Johnson regime and the headline claim is moved to the capacity conjecture
with the asymmetry stated wherever a CU number is quoted.

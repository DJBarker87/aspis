# V7 Tag-73 restored K1.3 provider checkpoint — 2026-08-29

## Result

The restoration-wide K1.3 provider no longer assumes that the completed
client store contains an accepting node, and it no longer accepts a q16
schedule from the parser/source boundary.

The exact completed full-run projection proves that the accepted root remains
stored at node zero. Strict checked-source/actual-run alignment proves that
root is schedule-exhausted. For every accepting stored node, the existing
operational state-map invariant constructs the exact first-cap-203 selected
q16 ledger. The remaining per-node source data is therefore limited to:

- canonical decoding of the 641 fixed QM31 values;
- the verifier-recorded gamma bytes and their exact decoding; and
- the verifier-recorded alpha-zero bytes and their exact decoding.

The strongest new constructor is
`exact_restored_operational_k13_provider_of_source` in
`AspisFormal/AspisFormal/K1/V7Tag73ExactRestoredOperationalK13Classifier.lean`.

## Focused replay

- Parent revision: `b13dd614`
- NUC workspace:
  `<build-root>`
- systemd unit: `aspis-v7-k13-provider-20260829-r5.scope`
- target:
  `AspisFormal.K1.V7Tag73ExactRestoredOperationalK13Classifier`
- limits: `MemoryHigh=10G`, `MemoryMax=14G`, `MemorySwapMax=0`
- Lean workers: one
- result: exit 0, 8,925/8,925 targets, build successful
- wall time: 6.38 seconds
- peak RSS: 6,937,364 KiB
- swaps: 0

The exact source file was synchronized to the pinned cached NUC workspace
before the run. No package-wide release replay was repeated.

## Axiom audit

Every new principal result reports a subset of exactly:

- `propext`
- `Classical.choice`
- `Quot.sound`

There is no `sorry`, `admit`, `sorryAx`, `native_decide`, or project-specific
axiom.

## Remaining K1.3 boundary

Construct the per-node canonical fixed-field and gamma/alpha-zero source data
from the literal translated verifier/replay caller. The q16 schedule and event
nonvacuity are no longer part of that boundary. The corrected K1.3 failure
event must then be bounded under the actual joint law and composed with K1.4
and K1.5.

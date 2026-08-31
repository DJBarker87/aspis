# V7 restored q16 joint-event handoff — 2026-08-31

## Result

The restored-root K1.3 query event is now connected deterministically to one
literal causal exposure trial containing both:

- the accepted 34-bit final-work digest; and
- every q16 digest block consumed by the deployed first-cap-203 search.

The strongest theorem is
`exact_restored_root_query_failure_has_joint_trial_coordinate`.  It starts
from membership in the source-closed restored-root K1.3 query event and
constructs an exact operational input, the intrinsic consistency set, and one
`ExactCompilerExposureTrial`.  The trial's 513-coordinate factor belongs to
the joint successful final-work/q16 bad event, and the bad set has cardinality
at most 9,557.

This rules out an invalid composition in which the K1.3 bad set, final-work
digest, and q16 forest are supplied by independently chosen witnesses.

## Canonical schedule repair

The existing canonical future-free construction carried a selected q16 ledger
certificate but its type did not retain that the selected counter and schedule
were exactly those of the deployed tape.  The lower construction did establish
those facts, but they were lost at its existential interface.

The interface now retains:

- `selectedQ16CounterExact`; and
- `selectedQ16ScheduleExact`.

The lower selected-ledger theorem exposes the corresponding equalities, and
`exact_root_k13_data_selected_schedule_eq_operational` transports them through
the environment/final-state index casts.  Therefore every admissible restored
root data witness selects the same schedule as the literal accepted operational
tape.

## Formal boundary still open

This milestone is pointwise.  The remaining q16 probability endpoint is to
prove that the intrinsic pre-q16 consistency set is a function only of the
residual coordinates after removing the final-work and q16 slots.  Once that
residual factorisation is available, the existing finite conditioning theorem
can be instantiated directly; no new q16 counting theorem is needed.

## Focused replay

```text
cd AspisFormal
lake env lean AspisFormal/K1/V7Tag73ExactRestoredQ16JointEventHandoff.lean
```

The focused replay exits zero.  Peak process RSS was 5,721,473,024 bytes with
zero swaps.  Both principal theorem axiom reports are exactly:

```text
propext
Classical.choice
Quot.sound
```

There is no `sorry`, `admit`, `sorryAx`, native decision shortcut, or
project-specific axiom in the new theorem surface.

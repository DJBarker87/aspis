# Tag-73 compact-semantic read-schedule result

Status: **PASS**

The kernel-checked theorem
`V7CompactSemanticReadSchedule.accepted_main_exposes_exact_271_reads`
extracts an ordered `FieldReadTrace` directly from an accepted translated
production call.  Its length is exactly

```text
1 initial claim + 10 semantic rounds * 27 fields/round = 271 QM31 fields.
```

No independently supplied field/message vector occurs in the theorem.
Every trace edge is tied to the translated production
`V6FixedFieldReader.next_qm31` result and carried reader state.

## Pinned inputs and outputs

- Lean: `4.32.0`
- source SHA-256:
  `1f7043d7420fe85b4c08c4090ad22bac68961da1092a7f980177c161b499531d`
- compiled `.olean` SHA-256:
  `58875f7327c771729d69ff3f981d56158dd7f52f35ba72005569263396c96670`
- passing log SHA-256:
  `7b7f268b37e8e32e97ec48785e5a729393d3b198064e731858edc5c90fbc7ca1`
- exact prerequisite source-bridge SHA-256:
  `1e45009650690933eca7e3b4e5535632ce1f9023510dbfd637f1145e10722732`

The focused passing invocation was
`aspis-tag73-readschedule-proof03.scope`, under `MemoryMax=16G`,
`MemorySwapMax=0`, `TasksMax=64`, `LEAN_NUM_THREADS=1`, and `lean -j1`.
It completed in 4.04 seconds with peak RSS 2,572,672 KiB and zero swaps.

The prerequisite source bridge was rebuilt once in the same Lean/dependency
universe immediately before the focused proof.  It completed in 15.98 seconds
with peak RSS 2,642,348 KiB and zero swaps.

## Axiom audit

All nine printed public read-schedule theorems depend exactly on Lean's
`propext`, `Classical.choice`, and `Quot.sound`.  The passing log contains no
`sorryAx` and no project-specific axiom.

The initial compile exposed three local proof-shape errors. Those were repaired
without changing any statement. Only the passing replay log is retained.

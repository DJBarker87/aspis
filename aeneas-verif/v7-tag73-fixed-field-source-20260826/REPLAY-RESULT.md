# Focused replay result

Status: **PRODUCTION TRANSLATION AND AXIOM-FREE EXECUTABLE LEAN ROOT GREEN**

On 2026-08-30 the complete focused Aeneas translation passed. The raw output
was staged separately for Lean 4.32, with exact executable replacements for
all generated external templates. The five-module focused compilation passed
in 34.058 seconds; the largest module used 3,433,020 KiB RSS. Every job ran
with zero swap.

`#print axioms` for
`verify_v7_compact_transcript_and_relation_prepared_with_hiding_context`
reports exactly `propext`, `Classical.choice`, and `Quot.sound`. There is no
project-specific axiom, `sorry`, `sorryAx`, native-decision certificate or
external runtime operation in that production-root closure.

The production revision, 115-file source closure, accepted call graph, and
39-MiB LLBC are frozen. Charon completed successfully; the LLBC SHA-256 is
`d05f26ee7b8bbd4f16c3bccd50348b129d1c25dd51a950730141a9e418d479e3`.
The focused pure layout model passed on the NUC in 4.63 seconds with peak RSS
6,727,628 KiB, zero swaps, no OOM, and exit status zero.

The original Aeneas run was stopped after it proved pathological. Focused
traces reduced the remaining failure to rustc's terminal-return cleanup around
`finish_onefold_relation`, not production Rust. Nine preceding compatibility
patches advanced translation through every earlier failure. The tenth patch,
`aeneas-d860ac47-terminal-return-capture.patch`, preserves Rust move semantics:
it retargets only certified terminal local-zero producers to a fresh capture,
moves the capture once into the existing pending-return option, and recognizes
only audited no-op cleanup shapes. It never synthesizes `Copy` for the
non-`Copy` production return value. Applying all ten patches produces Aeneas
Git tree `de8340302a8a14448e47e2a878ac726ed29228b2`.

The remaining source task is theorem construction, not translation: invert
literal successful production-root control flow to construct the exact
641-QM31 packed-field trace and compose it with the frozen K1.3 projection.

The first inversion layer is now kernel checked in
`V7Tag73GeneratedReaderBridge.lean`. Literal production-root success exposes
the exact initialized reader; initialization fixes the packed section at
9,936 bytes and the remaining count at 641. Every literal successful reader
step decrements that count by exactly one and proves all four returned limbs
strictly below `P`; successful finish proves count zero. Consequently any
complete exposed trace contains exactly 641 canonical QM31 values. The focused
run passed in 3.07 seconds at 2,514,604 KiB RSS with zero swap, and every
printed theorem reports exactly `propext`, `Classical.choice`, and
`Quot.sound`.

Still missing is the middle control-flow inversion that constructs the
complete trace from all nested semantic, point-claim, relation and final-vector
calls, followed by the exact packed-bit/value and K1.3 projection composition.

## 2026-08-30 K1.3 fixed-field projection closure

The middle control-flow, packed-bit and K1.3 projection steps described above
are now kernel checked.  The strongest theorem is
`generated_production_root_success_constructs_k13_fixed_projection` in
`proof/V7Tag73GeneratedPackedReaderBridge.lean`.

Starting only from literal success of the translated
`verify_v7_compact_transcript_and_relation_prepared_with_hiding_context`, it
constructs:

- the exact 9,936-byte fixed section;
- canonicality of all 2,564 packed M31 limbs;
- canonical high-padding rejection;
- one exact family of 641 `QM31Exact` values;
- `FixedFieldDecodeExact`; and
- `CurrentSourceFixedFieldProjection` for the projected deployed tape.

Focused NUC replay:

```text
unit: aspis-v7-k13-fixed-projection-20260830-r4.service
exit status: 0
wall: 1:01.21
GNU-time peak RSS: 7,829,728 KiB
swap: 0
olean SHA-256: b981aa970f58d82e7061b502f2348985f70d1185a2f865dd134a13278da8beac
```

The theorem's exact `#print axioms` result is:

```text
propext
Classical.choice
Quot.sound
```

There is no `sorry`, `admit`, `sorryAx`, `native_decide`, or project-specific
axiom.  This closes the generated semantic-root fixed-field endpoint.  It does
not claim the remaining outer caller/parser namespace alignment or the final
done-restoration-node `rawMessages` transport; those remain explicit source
composition work.

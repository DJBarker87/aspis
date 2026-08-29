# Nested-return drop-switch compatibility fix

After the zero-write shared-continuation fix, translation reaches the error
exit of `finish_onefold_relation`'s `for sample in 0..2` loop.  Rustc guards
the terminal destruction of the two `FnOnce` values with Boolean locals:

```text
if copy _516 { Drop QueryFold } else {}
if copy _517 { Drop DeriveQueries } else {}
```

The existing nested-return lowering consumes terminal `StorageDead`, `Drop`,
and plain Boolean drop-flag assignments when Aeneas's default
`drop_as_no_op` boundary is active.  It did not recognize these equivalent
conditional drops, so the return suffix was split at the switches.  The trace
shows one generated carry moving return local `_0`; later propagation then
attempts a second carry from the now-bottom `_0`.  No field of the successful
`V6VerifiedTranscript` result is bottom, and the preceding `_517` copy itself
succeeds.

`aeneas-d860ac47-loop-return-drop-switch.patch` extends only that terminal
cleanup recognizer.  It accepts a switch only when its discriminant copies a
plain local and either (a) both branches contain exclusively `Drop`,
`StorageDead`, or `Nop`, with at least one `Drop`, or (b) one branch is empty
and the other is a nonempty cleanup-only block ending in exactly `Return`.
Case (b) covers rustc's split encoding where the empty arm falls through to a
duplicate cleanup and return in the surrounding tail.  The outer suffix
recognizer still requires that fallthrough tail to end in `Return`.  The rule
is disabled by `-eval-drops`; no ordinary computational branch, bottom check,
or join rule is relaxed.

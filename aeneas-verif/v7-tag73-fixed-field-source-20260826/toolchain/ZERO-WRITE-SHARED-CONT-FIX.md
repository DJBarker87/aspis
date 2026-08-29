# Zero-write shared-continuation compatibility fix

The seven-patch translator reaches the production `finish_onefold_relation`
sample loop and fails while composing an input abstraction's one-sided
continuation with a branch-local abstraction.  The latter contains only an
immutable shared borrow and immutable shared loans.  There is no mutable value
to write back, but the existing narrow one-sided-continuation fast path
recognizes only the loans, so it incorrectly enters the complete-continuation
composer and raises on the intentionally absent input-abstraction output.

`aeneas-d860ac47-zero-write-shared-cont.patch` extends that existing fast path
only to an `ASharedBorrow` whose type contains no mutable borrows.  Such a
borrow carries no backward write and therefore has the same zero-write
continuation semantics as the already accepted shared loans.  Mutable borrows,
shared values containing mutable state, structured mutable projections, and
every complete continuation retain the strict composition path.

The triggering diagnostic is recorded in
`evidence/aeneas-merge-abs-debug/terminal-context.txt`.

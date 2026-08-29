# First-class enum-constructor function names

Charon materializes an enum constructor used as a first-class function, such
as `map_err(V6TranscriptError::Wire)`, as a function declaration. In Lean the
enum constructor already owns the canonical `V6TranscriptError.Wire` name, so
registering the materialized function under the same name prevents extraction.

`aeneas-d860ac47-first-class-variant-function-name.patch` detects only a
function name which is already registered to a `VariantId` and gives the
materialized function an `_fn` suffix. Calls are renamed through Aeneas's normal
identifier map. The enum constructor and its type retain their canonical names;
no Rust execution or generated expression changes.

With this patch and the borrow-free shared-destructure identity patch, the
34 MiB production Tag-73 LLBC completed Lean generation in 360.28 seconds at
2,707,180 KiB peak RSS with zero swap.

# Pinned translation toolchain

- Source-audit host Rust: `rustc 1.93.0 (254b59607 2026-01-19)`, host
  `aarch64-apple-darwin`, LLVM 21.1.8; Cargo
  `1.93.0 (083ac5135 2025-12-15)`.
- Charon extraction Rust: the tool's pinned `nightly-2026-06-01` toolchain at
  `<build-path>/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu`,
  reporting `rustc 1.98.0-nightly (14210df0e 2026-05-31)`, LLVM 22.1.6,
  and Cargo `1.98.0-nightly (fbb61be30 2026-05-26)` on
  `x86_64-unknown-linux-gnu`.  The NUC's default stable Rust 1.94.1 is not the
  compiler selected by Charon.
- Charon: version 0.1.223, source commit
  `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`.  The pinned Linux x86-64
  replay binary has SHA-256
  `b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c`.
- Aeneas: source commit
  `d860ac47ed548d3da6d799afc013779ce470516c` plus only the compatibility
  patches frozen in this bundle. Applying the ten patches in manifest order
  produces Git tree `de8340302a8a14448e47e2a878ac726ed29228b2`.
  Its isolated Docker build uses `memory-reservation=18G`, `memory=20G`, and
  `memory-swap=20G` (therefore zero container swap), matching the
  user-authorized parallel-lane
  high/max/no-swap envelope; Docker state, OOM status, and inner GNU-time
  resource output are retained with the build evidence.
- Lean: 4.32.0, commit
  `8c9756b28d64dab099da31a4c09229a9e6a2ef35`,
  `x86_64-unknown-linux-gnu`, for final focused replay.
- Generated modules are checked against the audited Lean-4.32 Aeneas backend
  prepared from Aeneas `b59d5188c082f704a418c7cb4e52ad69328002d1`
  using tracked patch SHA-256
  `5abaafc2d345511dda0eb96cd40154daff137f79dc4bcfa8247a45acea639c9c`
  and Lake manifest SHA-256
  `5d15524cf34ff705bebbd037e80baec63683d5d5a3a37a539a62f17405a2fc62`.
  This is the runtime/Lean-library compatibility layer only; the translator
  producing this bundle remains the patched d860ac47 tree above.

The Aeneas compatibility patch must address the original
`finish_onefold_relation` join failure without changing extracted Rust or
generated result semantics.  Its source diff, build command, binary hash, and
the pre-patch failure are retained under `toolchain/` and `logs/`.

`BASE-PATCHES.sha256` pins the bundle-local copies of the three already
audited patches from the preceding V7 accepted-source work.  The additional
`aeneas-d860ac47-loop-input-identity.patch` repairs a type-information loss in
the loop matcher: `match_ctx_with_target` previously received only symbolic
ids, even though its own comment specifies identity substitution for ids not
present in `sid_to_value_map`.  Retaining the already-existing complete
`symbolic_value` lets that branch construct the identity `tvalue`; mapped
inputs and every Rust/generated result branch are unchanged.

The fifth patch is the narrowly checked shared-Box dereference compatibility
fix documented in `SHARED-BOX-DEREF-FIX.md`. It permits only rustc's
compiler-generated copy of a borrow-free `Box<T>` when `T` is primitively
copyable; it does not make Rust boxes generally copyable.

The sixth patch is the nested-return drop-flag compatibility fix documented
in `LOOP-RETURN-DROP-FLAG-FIX.md`. In default drop-as-no-op mode it recognizes
only a Boolean literal assignment to a plain local inside a terminal return
cleanup suffix; reference and projection writes remain outside the rule.

The seventh patch is the structured-loop break-cleanup fix documented in
`LOOP-BREAK-LIFETIME-CLEANUP-FIX.md`. It moves only the immediate post-loop
lifetime cleanup to current-loop breaks, using the prepass's existing guarded
cleanup path, so live mutable iterator handbacks close before loop synthesis.

The eighth patch is the zero-write shared-continuation fix documented in
`ZERO-WRITE-SHARED-CONT-FIX.md`. It extends the existing one-sided-continuation
case only to a shared borrow whose type contains no mutable borrow.

The ninth patch is the nested-return conditional drop-switch fix documented
in `LOOP-RETURN-DROP-SWITCH-FIX.md`.

The tenth patch is the source-faithful terminal return-capture fix documented
in `TERMINAL-RETURN-CAPTURE-FIX.md`. It preserves moves through a fresh capture
local and never synthesizes `Copy` for a non-`Copy` production return value.

The focused compatibility series additionally includes the borrow-free
shared-value destructuring fix documented in
`BORROW-FREE-SHARED-DESTRUCTURE-FIX.md`. It preserves identity only after
nested loans have been removed and the remaining value contains no borrow.

The first-class variant-function naming fix is documented in
`FIRST-CLASS-VARIANT-FUNCTION-NAME-FIX.md`. It adds `_fn` only when a Charon
function declaration would otherwise collide with an already registered enum
variant constructor.

The Lean namespace-shadow fix makes a local basename collide when a registered
global Lean name begins with that basename plus `.`. Thus a Rust local called
`transcript` becomes `transcript1` when the generated module also contains the
global `transcript.*` namespace. The rule changes names only, and only for the
Lean backend. The complete focused series, including this patch, has Git tree
`8819b20bdc1713f7acd15e770caf0b955d3d677c`.

`stage-generated-lean432.sh` preserves raw Aeneas output and creates a separate
Lean-4.32 staging tree. It uses the same executable mutable-iterator model as
the frozen V5 and V7 Merkle source bridges, decides sixteen stored Rust Boolean
equalities, uncurries one two-argument `QM31::add` function item, and returns
Rust unit with the unchanged state of one no-op `FnMut`. It also replaces eight
Debug/expect-only string literals with a kernel-proved empty `Str`, preventing
Lean's UTF-8 native-decide certificates from entering the verifier theorem.
The staged tree replaces the generated `TypesExternal` and `FunsExternal`
templates with tracked executable models for every reached container,
iterator, conversion, option, arithmetic and sorting operation. Four
Debug-only unwrap/expect sites retain their exact fail-closed result branches
as explicit matches, so unused panic formatting is outside the theorem
closure.
Every rewrite has an exact expected occurrence count and fails closed if the
generated shape changes. `GENERATED-LEAN432.sha256` authenticates the staging
script and all three executable support files.

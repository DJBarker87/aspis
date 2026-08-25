# Frozen-original to staged bridge

## Decision

A fully generated function-level refinement theorem is not currently
possible. Charon emits the frozen production LLBC, but Aeneas aborts before
emitting a Lean declaration for the original `finish_onefold_relation` body:

```text
Could not find symbolic value @27 in src_to_joined_map
Source: 'crates/aspis-core/src/v6_transcript.rs', lines 782:4-836:1
Compiler source: interp/InterpJoin.ml, line 1968
```

There is therefore no original generated Lean function to put on the left
side of an equality. Claiming an exact Aeneas-to-Aeneas theorem would require
either fixing `InterpJoin` or adding a new verified interpreter/refinement
checker for the relevant LLBC subset. This bundle does neither and introduces
no source-correspondence axiom.

The strongest honest bridge is two-part:

1. a deterministic byte-level transformation certificate for every patch
   stage, rooted in the frozen production source hashes; and
2. kernel-checked result equality for the exact fixed control skeleton and
   the one reachable-path specialization.

## Byte/source certificate

`source-transform/SOURCE-TRANSFORM-CERTIFICATE.tsv` records the SHA-256 of
`v6_transcript.rs`, `sumcheck.rs`, and `field.rs` before any patch and after
each of the fifteen patches. `prepare-source-blobs.sh` now checks each row
immediately after applying the corresponding patch and rejects a missing,
reordered, stale, fuzzy, or content-different transformation.

The certificate begins at:

- transcript `8422e8fa817fae3a7db01976725fcfd3642ea837f4e87366829f63309c6f28d3`;
- sumcheck `9cb353d5640d00717f0fbe4c46b2870597602774abe6e47ce73e04b25fb48bd7`;
- field `e118899472e3049db688573570296f06696be659524bbf6a62ace537f0316312`.

It ends at:

- transcript `ed6e21c6ad34b7346eb7e3eebb1fc39af7e5a40366a8522b7b84b7a3dc6c9fdb`;
- sumcheck `1474bda4d9014c958197a44d094706c2d9653a3146c707265a711f9a2fc6a4ea`;
- field `934bd0b7e9eedf48cf33b5c0f3d0ce690052d5546878bc4f9fd82cb75d0ba008`.

The passing local certificate transcript is retained at
`logs/source-transform-certificate-pass.log`.

## Kernel-checked semantic bridge

`proof/V7Tag73FrozenStagedAcceptedPathBridge.lean` models the exact fixed
control sequence with arbitrary `Aeneas.Std.Result` transitions. It proves:

- `frozen_staged_finish_control_result_exact`;
- the corresponding success, first-failure, and divergence equivalences;
- `terminal_dispatch_reachable_result_exact`;
- `tag73_terminal_shape_true`;
- `frozen_staged_tag73_accepted_control_result_exact` and its success
  equivalence.

The main equality covers point rows 0--2, OOD samples 0--1, relation rounds
1--3, and extraction of the formerly inline tail. Since every transition is
arbitrary and result-valued, it does not assume that an intermediate call
succeeds or terminates.

The focused NUC gate passed under `MemoryMax=12G`, `MemorySwapMax=0`,
`TasksMax=64`, and `lean -j1`. The small generic transformation prerequisite
compiled in 2.29 seconds at 2,537,468 KiB maximum RSS. The bridge itself
compiled in 2.29 seconds at 2,525,356 KiB maximum RSS. Both recorded zero
swap. The bridge source, olean, and pass-log SHA-256 values are:

- `368433dd185ef4c90e197c985216180bd8df0935dc3dbb1bc68e650c58963e42`;
- `9bae1b02ac1c34ac458ed51fe4bb6eb94889cf3d3900b50556ba37fc8e61272c`;
- `f26f0291d01ef71cfeb3ada032cfdbc44bcf0ba4732e2427556a895fee65732e`.

The principal theorem's axiom print contains only Lean's `propext` and
`Quot.sound`; it contains no project axiom and no `sorryAx`.

The terminal-dot specialization is intentionally an accepted-path theorem,
not a false global equivalence. The staged `sumcheck::dot` makes its generic
fallback unreachable. The frozen and staged versions are equal on the Tag-73
state because four radix-4 folds give weight log length `2`, and the final
vector has exactly four values. The theorem leaves both off-path fallback
results arbitrary and proves they cannot affect the returned result.

The three-row `qm31_dot3` refactor is likewise scoped to the production call:
its inputs are three type-level 29-element rows sharing the type-level
29-element power table. The generic public function's behavior on
length-mismatched slices is not claimed equivalent, because that state is not
reachable from the Tag-73 call.

## Patch classification

- Fixed point/OOD/relation loop unrolling: kernel-checked result equality.
- `zip` to indexed common-prefix traversal: kernel-checked order/stop
  equality.
- Deferred-halving maximum: kernel-checked empty and nonempty equality.
- Named wire-error adapter: kernel-checked constructor equality.
- Lambda lifts and helper extraction: byte-certified movement of the same
  expressions and state, represented in the exact control theorem.
- Component `for` loops to indexed `while` loops: byte-certified same-order
  traversal; their staged bodies are transparent in generated Lean.
- Terminal fallback removal: kernel-checked only under the exact reachable
  Tag-73 shape.
- Three-row QM31 refactor: accepted-path binding to the fixed 29-element
  production arrays; no claim for malformed length-mismatched callers.

## Exact residual

What remains is not a mathematical relation assumption. It is the absence of
a generated semantics for the frozen original function itself. Closing that
last tool boundary requires either:

- an upstream `InterpJoin` fix followed by a direct Aeneas theorem equating
  the original and staged results; or
- a separately verified LLBC refinement checker which consumes both pinned
  ASTs and validates the recorded transformation relation.

Until then, the source binding is a reproducible byte certificate plus
kernel-checked transformation semantics. The accepted-path cryptographic and
arithmetic claims remain in the generated staged proof and are not weakened.

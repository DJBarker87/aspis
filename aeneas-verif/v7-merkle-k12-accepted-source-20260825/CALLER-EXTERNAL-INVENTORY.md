# Transparent caller external-interface inventory

## Emitted surface

The transparent caller translation emits two external Rust-library types and
fifteen external Rust-library functions.  The authoritative signatures are
the untouched templates under `caller/generated/V7MerkleCaller/`.
`TypesExternal.lean` and `FunsExternal.lean` instantiate every template entry
with executable Lean; neither file contains an axiom or placeholder.

| Emitted item | Existing executable source | Owned disposition |
| --- | --- | --- |
| `core.array.iter.IntoIter` | `v5-relation-full-source-20260820/generated/Relation/TypesExternal.lean` | Reused array-plus-cursor structure. |
| `core.slice.iter.Windows` | `generated/V7MerkleK12/TypesExternal.lean` | Reused slice/width/cursor structure. |
| array `IntoIterator::into_iter` | `v5-relation-full-source-20260820/generated-linked/RelationLinked/FunsExternal.lean` | Reused exactly. |
| array `IntoIter::next` | same RelationLinked file | Reused exactly. |
| `core::array::from_fn` | `v5-relation-acceptance-20260815/generated/V5RelationCompactNewGenerated.lean` has the exact emitted result signature for its fixed length; `v5-fri-coordinate-production-full-20260821/generated/V5CoordinateProductionFull/FunsExternal.lean` supplies the same call-state threading pattern | Adapted to arbitrary emitted `N` using structural recursion, one increasing `Usize` call per element, and the exact `F → Result (Array T N)` result. |
| mutable-array `IntoIterator::into_iter` | `v5-transcript-prefix-complete-20260821/generated/Zero/FunsExternal.lean` | Reused exact iterator/back-function model. |
| generic `Iterator::any` | `generated/V7MerkleK12/FunsExternal.lean` and `v5-fri-arithmetic-exact-20260820/generated/FriArithmetic/FunsExternal.lean` | Reused exact loop model. |
| `Option::ok_or` | `v7-onefold-accepted-source-20260825/parser/generated-exact/V7DeferredParser/FunsExternal.lean` | Reused exactly. |
| `Option` `Try::branch` | `v5-merkle-deployed-source-20260815/generated/V5MerkleDeployedSource/FunsExternal.lean` | Reused exactly. |
| `Option` `FromResidual::from_residual` | same V5 Merkle file | Reused exactly. |
| `Result::ok` | `v5-fri-byte-decoders-20260814/generated/V5FriDecoderGenerated/FunsExternal.lean` | Reused exactly. |
| mutable-slice iterator `any` | no executable exact-signature definition was present; the only repository hit was an axiom in `v5-fri-arithmetic-exact-20260820/generated/FriArithmetic/FunsExternal.lean` | Adapted the executable shared-iterator `anyAux` pattern from that file to Aeneas's existing `core.slice.iter.IteratorIterMut.next`, reinserting the item through its generated back function. |
| windows iterator `next` | `generated/V7MerkleK12/FunsExternal.lean` | Reused exactly. |
| `Slice::last` | same V7 Merkle file and the V7 deferred-parser file | Reused exactly. |
| `Slice::windows` | `generated/V7MerkleK12/FunsExternal.lean` | Reused exactly, including zero-width panic. |
| `Slice::sort_unstable_by_key` | no executable repository definition was found | Supplied executable monadic insertion sort over the same `FnMut` key and `Ord` interfaces. Rust leaves equal-key order unspecified; the model preserves every element and chooses one permitted equal-key order. |
| `Vec::clear` | `generated/V7MerkleK12/FunsExternal.lean` | Reused exactly. |

The apparent count of seventeen rows includes the two types; there are exactly
fifteen function declarations in Aeneas's function template.

## Combined import and generated compatibility overlay

The executable caller external modules import `V7MerkleK12.TypesExternal` and
`V7MerkleK12.FunsExternal`.  Thus the two generated roots use one definition
for the identical `Windows`, generic `Iterator::any`, window traversal,
`Slice::last`, and `Vec::clear` interfaces.  Only caller-unique interfaces are
declared again.  The deferred parser is combined by the separately frozen
`toolchain/v7-deferred-parser-combined-external.patch`, which likewise removes
only its duplicate `Slice::last` declaration.

Aeneas's raw caller `Funs.lean` remains byte-for-byte archived.  Before kernel
compilation, `toolchain/v7-merkle-caller-generated-compat.patch` applies six
interface-level repairs required by the result-aware backend/library pair:

1. select the value-only mutable iterator method for the generic trait;
2. make an emitted `Prop` comparison explicit as `Bool` with `decide`;
3. use the executable forward/backward mutable-enumerate `next` helper;
4. apply the accumulated first mutable-iterator back function;
5. use the executable forward/backward mutable-enumerate constructor; and
6. apply the accumulated enumerate back function.

The same overlay also applies the four-root bundle's already documented
failure-diagnostic normalization to the caller duplicate of
`truncate_sha256_v7`: the unused `Result.expect` message is replaced by the
empty `Str`. The raw Aeneas file is compared before this step. Success values,
hash inputs, branches, and errors are unchanged; the normalization prevents
Lean's compiled string literal from adding a native-decision axiom to the
otherwise definitional namespace-equality proof.

The overlay changes no production branch, constant, hash call, query slice, or
Merkle operation.  It is checksum-covered and is replayed only after the raw
generated file has been compared with the archived Aeneas output.

The focused combined compile passed on nuc.local in transient unit
`aspis-v7-caller-lean-compile-05` (invocation
`5997e62169f44c6da0b4d75e2e826472`): exit 0, 14.38 s wall,
2,611,984 KiB maximum RSS, and zero swaps.  Exact commands and all failed
interface-diagnostic attempts are retained under
`caller/evidence/lean-compile-01/`.

## Production relevance

The caller itself directly needs `from_fn`, `sort_unstable_by_key`, windows,
generic `any`, array iteration, `Option::ok_or`, and `Result::ok`.  The
transparent gamma call graph additionally causes Aeneas to emit mutable-array
iteration support.  `Vec::clear`, windows, `last`, and generic `any` are used by
the transparent two-tree verifier reached by the caller.

The caller's sort key closure is translated transparently and returns the
first `u32` component without mutable state.  Therefore the permitted ordering
choice among equal keys cannot conceal acceptance: the immediately following
translated windows/`any` check rejects every adjacent equal public position.
The source-facing theorem must still derive that fact from the generated
caller control flow; this inventory is not a replacement for that theorem.

## Static audit commands

The executable-definition search used focused `rg` queries over
`aeneas-verif/**/{TypesExternal,FunsExternal}.lean` and exact generated files,
for each fully qualified template name.  The final placeholder/axiom gate is:

```sh
rg -n '\b(axiom|sorry|admit|sorryAx)\b' \
  aeneas-verif/v7-merkle-k12-accepted-source-20260825/caller/generated \
  --glob '*.lean'
```

That command is expected to find `axiom` only in the two untouched
`*_Template.lean` provenance files.  Restricting the same check to
`TypesExternal.lean`, `FunsExternal.lean`, `Types.lean`, and `Funs.lean` must
return no matches.

`replay-caller-namespace-bridge.sh` additionally compiles the independently
generated Merkle, caller, and deferred-parser modules in one environment,
applies both deterministic overlays, and checks the cross-namespace theorem
file `caller/proof/V7MerkleCallerNamespaceBridge.lean`.

Its final run, unit `aspis-v7-caller-namespace-12` and invocation
`f0abe441f3674d20b8f1edd446abfaa6`, passed in 23.69 seconds with
2,612,928 KiB maximum RSS and zero swaps. Every printed namespace/wire theorem
uses exactly `[propext, Classical.choice, Quot.sound]`.

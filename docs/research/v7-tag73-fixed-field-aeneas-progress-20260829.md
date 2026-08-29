# V7 Tag-73 fixed-field Aeneas progress — 2026-08-29

## Scope

This checkpoint targets one source endpoint only:

```text
literal production Tag-73 verifier success
  -> exact 641 decoded fixed QM31 fields
  -> CurrentSourceFixedFieldProjection
  -> ExactRestoredOperationalK13SourceNodeData
```

The focused Charon root is the production function
`verify_v7_compact_transcript_and_relation_prepared_with_hiding_context` with a
generic query callback.  No production Rust or cryptographic relation was
changed.

## Frozen inputs

- Aeneas commit: `d860ac47ed548d3da6d799afc013779ce470516c`
- Charon commit: `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`
- generic LLBC SHA-256:
  `8acbe11cd3800b27e325bf3ef089a58e02f27fce84e08c55b928807d518ebd18`
- focused `WeightAccumulator::weight_at` caller LLBC SHA-256:
  `f3a0a653484cb6d372910ad43d6e7442bbeb0ae485d81d6ebee6a0b81b98e89a`

## Translator findings

The focused caller exposed Aeneas bookkeeping differences for immutable
iterators and shared loans.  Each patch is restricted to translator state which
has no mutable write-back path:

1. the function return place is not a drop flag;
2. distinct fixed-point input abstractions remain distinct;
3. target-only empty match abstractions are removed only after source match
   normalization;
4. fixed-point type comparison erases only free lifetimes in shared-only types;
5. a uniquely paired dead shared borrow may be removed from a mixed match-only
   abstraction;
6. immutable parentless abstraction groups are canonicalized before matching;
7. equivalent groups are ordered by stable borrow/loan ids rather than
   alpha-renamed abstraction ids.
8. flattening an immutable nested shared loan preserves the symbolic identity
   of a value once the remaining value contains no borrow.

All changes are comparison/translation changes.  Mutable references, static
lifetimes, bound lifetimes, normal non-equivalence matching, actual execution
contexts and generated continuations keep their original rules.

## Isolated build policy

Every candidate toolchain build runs on `nuc.local` with:

```text
MemoryHigh=18G
MemoryMax=20G
MemorySwapMax=0
TasksMax=128
```

The frozen build script verifies every base patch, every focused extra patch,
the exact patched Git tree, the pinned Charon commit and the static binary
version before accepting an output.

## Current checkpoint

The earlier symbolic-execution checkpoint tree was:

```text
4e2776773a3df1163bc7f4bb6d89cf94ec2ffb73
```

The final isolated Aeneas binary is:

```text
version: d860ac47-tag73-fixed-field-canonicalgroup-r2
SHA-256: ced86946af8774132668f1f0c66668204c740bc8e9ec6d711879b249445f412e
tree:    4e2776773a3df1163bc7f4bb6d89cf94ec2ffb73
```

Its NUC build completed in 3:33.94 with 587,968 KiB peak RSS and no swap.

The tiny caller now completes all Aeneas symbolic execution, including the
multilinear iterator, nested `LineM31Batch` bit loop, deferred-bit loop, every
`WeightComponent` variant, shared-lifetime duplication, and differing
abstraction groups.  The focused run took 8.59 seconds, peaked at 259,024 KiB,
and used no swap.

The Pure/Lean failure at that checkpoint was:

```text
Could not find var for symbolic value: 4764
symbolic/SymbolicToPureCore.ml:520
```

The value was an immutable, borrow-free `Vec<WeightComponent>` freshened while
flattening a nested shared loan. The final focused patch preserves its existing
symbolic identity only after loan removal and only when the remaining value has
no borrow. The frozen caller now completes Pure/Lean generation in 9.48 seconds
at 295,772 KiB peak RSS with zero swap. Its generated `Types`, `FunsExternal`
and `Funs` modules compile with Lean 4.31.0 against the pinned Aeneas runtime.

No production Rust or cryptographic statement changed.

The complete 34 MiB generic verifier LLBC subsequently completed Aeneas
translation and Lean source generation in 360.28 seconds at 2,707,180 KiB peak
RSS with zero swap. The exact patched source tree for that run is:

```text
958a3350ff74aa0863d07f00a6061d0397bc94f1
```

The generated `TypesExternal`, `Types` and `FunsExternal` modules compile. The
complete generated `Funs` module now reaches two separate Aeneas Lean-runtime
integration issues: the mutable-slice iterator model and a local `transcript`
value shadowing the generated `transcript` namespace. Those are backend binding
work; the production Rust graph and the formerly failing fixed-field Pure path
both generate successfully.

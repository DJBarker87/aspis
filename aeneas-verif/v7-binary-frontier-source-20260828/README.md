# V7 production binary-frontier source bridge

This bundle extracts the literal production
`aspis_core::v6_onefold::binary_frontier_nodes` implementation and proves the
arithmetic performed by one successful adjacent-window loop body.

The source revision used for extraction was
`eb3497af8a191e1fd9310bc3e0e0c7a446a3e41e` on
`research/v7-q16-scheduler-replay-20260828`.

## Extraction

The pinned Linux Charon command was:

```text
/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/bin/charon cargo \
  --preset aeneas \
  --start-from crate::v6_onefold::binary_frontier_nodes \
  --dest-file frontier-extraction/V7BinaryFrontier.llbc \
  -- --manifest-path crates/aspis-core/Cargo.toml --lib
```

The pinned Aeneas command was:

```text
/home/dombarker/project-offloads/aeneas-d860-v6-linux/bin/aeneas \
  -backend lean -split-files -emit-json \
  -namespace V7BinaryFrontierSource \
  -dest frontier-extraction/generated \
  frontier-extraction/V7BinaryFrontier.llbc
```

The generated `*_Template.lean` files are not part of this bundle and are not
imported. `TypesExternal.lean` and `FunsExternal.lean` provide transparent
definitions for the small foreign iterator/option/shift surface used by the
extraction.

## Current strongest result

`V7BinaryFrontierBodyBridge.source_frontier_body_adds_exact_log2` starts from
literal translated loop-body success and exact iterator/slice observations. It
proves that the translated Rust body returns:

```text
expanded + floor(log2(left XOR right))
```

The proof follows the translated XOR, nonzero assertion, `leading_zeros`, both
checked `u32` subtractions, the `u32 -> usize` cast and the checked `usize`
addition. There is no arithmetic callback or conclusion-shaped source premise.

## Replay

On `nuc.local`, with pinned Aeneas Lean backend and Lean 4.31:

```text
systemd-run --user --wait --collect \
  --unit=aspis-v7-frontier-body-29 \
  -p MemoryHigh=8G -p MemoryMax=12G -p MemorySwapMax=0 \
  ./compile-generated.sh <generated-lean-root> \
  /home/dombarker/project-offloads/aeneas-d860-v6/backends/lean
```

Result: exit 0, 6.099 seconds service runtime, zero swap. `#print axioms`
reported exactly:

```text
propext
Classical.choice
Quot.sound
```

## Digests

```text
166a91348ba468ddecd16574154b5425609276d51f7d3dfbfb07effce4d6a406  extraction/V7BinaryFrontier.llbc
1b9ba984d8238a7c5da264078f134c4c3f587a9c13bea7a7cfe74adad3c9a26e  generated/V7BinaryFrontier/Funs.lean
7b8b6c3520bf2a714833e4880cea6bd5e9d3edde0481a482d884d9ab1a54d352  proof/V7BinaryFrontierBodyBridge.lean
```

## Remaining source closure

The next proofs lift this body theorem through the translated windows loop,
prove the translated insertion-sort/order/range checks, and connect the full
production return value to the already kernel-checked canonical adjacent-XOR
q16 frontier formula.

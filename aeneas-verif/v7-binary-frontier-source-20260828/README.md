# V7 production binary-frontier source bridge

This bundle extracts the literal production
`aspis_core::v6_onefold::binary_frontier_nodes` implementation and proves both
the arithmetic performed by each adjacent-window body and the complete
translated windows loop.

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

`V7BinaryFrontierLoopBridge.translated_windows_loop_exact` starts from the
literal translated iterator state, an exact duplicate-free remaining list and
the checked `usize` headroom. It constructs translated loop success and proves
that the final accumulator is:

```text
expanded + sum(floor(log2(left[i] XOR left[i + 1])))
```

Its body theorem follows the translated XOR, nonzero assertion,
`leading_zeros`, both checked `u32` subtractions, the `u32 -> usize` cast and
the checked `usize` addition. The loop theorem then follows every translated
`windows(2)` transition and checked addition. There is no arithmetic callback
or conclusion-shaped source premise.

The insertion-sort closure has also reached a source-backed checkpoint:

- `V7BinaryFrontierSortModel.bubbleLeft_sorted_prefix` and
  `bubbleLeft_perm` prove the pure adjacent-swap insertion mathematics; and
- `V7BinaryFrontierSortSourceBridge.translated_inner_insertion_exact` proves
  that the literal translated predecessor-shift loop, followed by writing its
  saved key at the returned cursor, is exactly that `bubbleLeft` operation.

The source theorem includes the returned-cursor bound needed by production's
outer array write. It does not assume that the translated result is sorted.

## Replay

On `nuc.local`, with pinned Aeneas Lean backend and Lean 4.31:

```text
systemd-run --user --wait --collect \
  --unit=aspis-v7-frontier-loop-06 \
  -p MemoryHigh=22G -p MemoryMax=28G -p MemorySwapMax=0 \
  ./compile-generated.sh <generated-lean-root> \
  /home/dombarker/project-offloads/aeneas-d860-v6/backends/lean
```

Result: exit 0, 11.699 seconds service runtime, zero swap. `#print axioms`
reported exactly:

```text
propext
Classical.choice
Quot.sound
```

The focused sort-source replay used unit
`aspis-v7-frontier-sort-source-07`; it exited 0 in 14.692 seconds with zero
swap and reported the same exact axiom set.

## Digests

```text
166a91348ba468ddecd16574154b5425609276d51f7d3dfbfb07effce4d6a406  extraction/V7BinaryFrontier.llbc
1b9ba984d8238a7c5da264078f134c4c3f587a9c13bea7a7cfe74adad3c9a26e  generated/V7BinaryFrontier/Funs.lean
29b8692b94e73d1c0d59ab27dbdf5160e285636585add7dbadaba50f631a467f  proof/V7BinaryFrontierBodyBridge.lean
3911bf62d05373ce65cc2d0bcb0996dab4551445c76ca06e8e905c5e9c73e65a  proof/V7BinaryFrontierLoopBridge.lean
a47f9642deb9f233a5c6c8b00a18fdeec4e1dc272e3a1e506120fc5e8cea714b  proof/V7BinaryFrontierSortModel.lean
4195bbfe023fb0711fc3285b0237254584e796bffd5b228472ae78f8a17840c6  proof/V7BinaryFrontierSortSourceBridge.lean
```

## Remaining source closure

The next proof lifts the inner insertion theorem through production's outer
`1..Q` loop. After that, the duplicate/range validation and full return value
must be connected to the already kernel-checked canonical adjacent-XOR q16
frontier formula.

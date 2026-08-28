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

The insertion-sort and fixed-q16 closures are source-backed:

- `V7BinaryFrontierSortModel.bubbleLeft_sorted_prefix` and
  `bubbleLeft_perm` prove the pure adjacent-swap insertion mathematics; and
- `V7BinaryFrontierSortSourceBridge.translated_inner_insertion_exact` proves
  that the literal translated predecessor-shift loop, followed by writing its
  saved key at the returned cursor, is exactly that `bubbleLeft` operation;
- `translated_outer_insertion_sort_exact` and `translated_sort_from_one`
  prove that production's complete outer loop returns a sorted permutation;
- `translated_duplicate_scan_accepts` proves literal adjacent duplicate
  validation accepts every pairwise-distinct sorted schedule; and
- `translated_binary_frontier_q16_exact` starts from the complete production
  helper at `q = 16`, depth 18 and proves its exact checked return formula.

`V7BinaryFrontierK13Integration.translated_frontier_nodes_eq_semantic` then
constructs the operational Rust `u32[16]` from the Tag-73 query injection and
proves that the translated helper returns exactly
`semanticFrontierNodes schedule.positions`. This discharges the former
pointwise frontier-mathematics input when the accepted tape is instantiated
with the production helper.

The enclosing production
`aspis_core::v7_onefold::derive_first_v7_compact_queries` caller has also been
extracted from the same source revision. Its generated helper namespace is
replayed independently through the body, loop, insertion-sort and K1.3
integration bridges under `caller/proof/`. In particular,
`V7FirstCompactFrontierK13Integration.translated_frontier_compact_iff_semantic`
proves that the literal helper's cap-203 decision is equivalent to the frozen
K1.3 semantic admission predicate.

The caller extraction required only transparent generated-code repairs: avoid
the `transcript` parameter/name-space shadow, reuse the already generated
frontier types and foreign definitions, and supply the literal extra `u32`,
`Result.map_err`, and `Vec -> Array` operations. No production Rust changed.

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

The full fixed-q16 replay used unit
`aspis-v7-frontier-full-q16-final`; it exited 0 in 15.194 seconds with zero
swap. The K1.3 integration can be included by supplying a Lean-4.31
AspisFormal project containing the focused semantic frontier build:

```text
./compile-generated.sh <generated-lean-root> \
  /path/to/aeneas/backends/lean \
  /path/to/aspis-formal-project
```

The caller extraction and all four caller frontier bridges were also compiled
with the same Lean 4.31/AspisFormal path and zero swap.

## Digests

```text
166a91348ba468ddecd16574154b5425609276d51f7d3dfbfb07effce4d6a406  extraction/V7BinaryFrontier.llbc
1b9ba984d8238a7c5da264078f134c4c3f587a9c13bea7a7cfe74adad3c9a26e  generated/V7BinaryFrontier/Funs.lean
29b8692b94e73d1c0d59ab27dbdf5160e285636585add7dbadaba50f631a467f  proof/V7BinaryFrontierBodyBridge.lean
3911bf62d05373ce65cc2d0bcb0996dab4551445c76ca06e8e905c5e9c73e65a  proof/V7BinaryFrontierLoopBridge.lean
a47f9642deb9f233a5c6c8b00a18fdeec4e1dc272e3a1e506120fc5e8cea714b  proof/V7BinaryFrontierSortModel.lean
7ee9f9775b7b3e6f2d1ea8533e91b72cecbdb3948bdd5e3595c5ccc5e652fb66  proof/V7BinaryFrontierSortSourceBridge.lean
ec384cb07f8f830dd34791c46cbcbda0cd48d5f8581047a9637cf8a032bc7a38  proof/V7BinaryFrontierK13Integration.lean
9b4d98e15af61a82c3f0112a40608acc3fa346a6ba29c8a02478d226d1a24157  compile-generated.sh
acff57d54c85fdab875f42d6ce2da8390179ca424f8e087afa7a53d58383a086  caller/V7FirstCompact.llbc
d83c41b859860d34e12f5f9e34082d28b84d08e73d6055c56e3b1d4a08a5b14d  caller/generated/V7FirstCompact/Funs.lean
69f6b6130cf9f72d574b96a3e5bf1304426f6d9fd9768dd80a75fbec8575eac4  caller/generated/V7FirstCompact/FunsExternal.lean
a85832837449b806c730dabaedb802eb997892bd09b4ed77d27b246aebfe7834  caller/generated/V7FirstCompact/Types.lean
9c573383d5b50dced1cd948f6886ac640cf03c375dacd0e8dfeabde699630aed  caller/generated/V7FirstCompact/TypesExternal.lean
f69d1a816e14e3ecce85026d1b162c726a0b41ec0070d7d12626dabe8b09dea4  caller/generated/V7FirstCompact/translation.json
401c01f6295e20ba034480e95200b7acb860db9a00168c43e3a9cd13f9e637aa  caller/proof/V7FirstCompactFrontierBodyBridge.lean
b71fa9e8fc7bef1544ec981092de9370c4b45d4ed059f30989d7bef988932468  caller/proof/V7FirstCompactFrontierLoopBridge.lean
809eb566103b0a2355adaf530f78383dae45ac51d05ddf8fe4779b42b9e3a9bf  caller/proof/V7FirstCompactFrontierSortSourceBridge.lean
c72e3c80fcfd46ce032d834d00b209316608f2cb1b39840dbabdec8180e3aaa6  caller/proof/V7FirstCompactFrontierK13Integration.lean
```

## Remaining source closure

The frontier mathematics, literal helper, caller-local helper, and cap-203
semantic equivalence are closed. The remaining step is the outer returned
schedule/tape construction. The current Aeneas translation emits `done none`
on the accepted branch even though the Rust source returns the constructed
schedule, so that wrapper cannot honestly be used as a returned-value theorem.
This is now isolated as a source-tool translation repair/re-extraction task;
it is not an additional frontier formula or probability premise.

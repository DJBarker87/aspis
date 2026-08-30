# V7 Tag-73 current caller source replay

## Result

**PASS.** The accepted production entry point

`V7Tag73CurrentHelpersOpaque.v7_verifier.verify_v7_read_only_with_statement_digest`

was extracted from source revision
`bcd03b12293f2737dfa1da1436092a0a24a6ae24`, translated by the pinned
Charon/Aeneas toolchain, compiled through the complete 139-target staged Lean
graph, and audited at `proof/CurrentCallerAudit.lean`.

No production Rust file and no K1 mathematical theorem is changed by this
bundle.

## Frozen artifacts

| Artifact | SHA-256 |
|---|---|
| Complete current-caller LLBC | `b4d931347481d70935e1aa6445173f68a38e678cc3b67eba6a467ca502c1be69` |
| Raw Aeneas caller `Types.lean` | `e6258f7a420199d2e42e9e26ca90c344f1b76074ea45f032390f042767853bd9` |
| Raw Aeneas caller `Funs.lean` | `470d8c68c224b26f54db77276af71cbd89b196cdc65dd47d088105b61c8e4c9a` |
| Raw Aeneas `translation.json` | `c2b997513b8a98352bb70a46f29a081699cd1a1616fb1d2b1d9da862e8ad2cf0` |
| Accepted staged caller `Types.lean` | `02c93204cbcaa6f5389fed89b9e67074536c6375f990a4504bba297c7780138b` |
| Accepted composed caller `Funs.lean` | `f89bcd1ab299f2161b735bd41d5094a29801aaa8c8fcdfb23d83e84f80fae4cd` |
| `CurrentCallerAudit.lean` | `61aba9074593b8c8efb88bb1fa258b26ff729d8b090d59eee9980f0930f78cc1` |
| Complete audit log | `259915ac17ee4f65fce8343cf2124e8b7d28dfaa9a2f595c28920707806bed93` |
| Staged-output manifest | `c9365ad8b1e6786138193afda8969fc64f54bda592db7998c5c9fb270de5b82b` |

The complete LLBC is
`extraction/V7Tag73CurrentNormalizedStatementOwnedTwoHelpersOpaque.llbc`.
The raw Aeneas output is under `generated-current/`; the accepted Lean source
is under `proof/`.

## Focused release evidence

| Gate | Wall | Peak RSS | Swap | Exit |
|---|---:|---:|---:|---:|
| Owned-accessor optimized Rust test | 1:48.23 | 462,448 KiB | 0 | 0 |
| Complete current caller Charon extraction | 14.97 s | 512,272 KiB | 0 | 0 |
| Complete current caller Aeneas translation | 11:45.20 | 2,694,524 KiB | 0 | 0 |
| Exact staging/generator pass | 0.96 s | 28,420 KiB | 0 | 0 |
| Complete staged Lean graph, 139 focused targets | 201.12 s summed | 3,179,956 KiB worst target | 0 throughout | all 0 |
| Final `CurrentCallerAudit.lean` target | 1.11 s | 2,514,584 KiB | 0 | 0 |

The Aeneas release unit was
`aspis-v7-current-caller-aeneas-owned-r9`, invocation
`87103b4a36d34f749c96815db9ff17ba`. The optimized Rust gate was
`aspis-v7-static-owned-rust-r10`, invocation
`967040badf194fd19f8143086ded3e05`.

The corrected staged graph was compiled serially under zero-swap units with
`MemoryMax` between 6 and 8 GiB. The final audit unit was
`aspis-v7-current-audit-r19`, invocation
`a2832e65dec94b6e98d2f0ee59f2419c`. Every target has its own
`/usr/bin/time -v` record under
`evidence/nuc/current-caller-lean-owned-r19/`.

## Kernel and forbidden-construct audit

The strongest production caller reports exactly:

```text
[propext, Classical.choice, Quot.sound]
```

Every accepted result is a subset of that set. In particular, the exact gamma
and dot-product output-limb bridges are axiom-free. The accepted source scan is
clean for:

```text
sorry
admit
sorryAx
native_decide
project-defined axiom declarations
```

Generated `*_Template.lean` files are archival Aeneas interface templates and
are excluded from both the compile order and accepted-source scan.

## Exact helper split

The combined LLBC leaves only these two functions opaque because each triggers
a distinct context-sensitive join defect when inlined into the full caller:

- `aspis_core::v6_onefold::gamma_combine_v6_c1_slot_major`;
- `aspis_core::field::qm31_dot3`.

Both production functions are independently extracted and literally
translated. The combined namespace reconnects them through structural maps.
The kernel-checked endpoint theorems are:

- `gamma_combine_v6_c1_slot_major_split_exact`;
- `qm31_dot3_split_exact`.

This is an extraction decomposition, not a cryptographic assumption and not a
trusted hint.

## Resource correction

An unpartitioned generated-constant path was stopped at
22,866,784,256 bytes cgroup memory with zero swap and was not rerun with a
larger cap. The accepted generator validates and factors the five circle
tables and the 15-entry atomic copy-pattern registry before elaboration. The
corrected full graph peaks at 3,179,956 KiB on its worst individual target.

## Remaining explicit boundary

This closes the production Rust-to-Aeneas caller path at the selected source
revision. It does not prove SHA-256 itself: the caller still receives the hash
callback represented in its Rust signature. Charon, the patched Aeneas
translator, the guarded source-equivalent extraction normalizations, the
executable Rust standard-library models, the compiler, and the Lean kernel
remain the ordinary source-tool trust base. Those are provenance/tool
boundaries, not new premises in the K1 mathematics.

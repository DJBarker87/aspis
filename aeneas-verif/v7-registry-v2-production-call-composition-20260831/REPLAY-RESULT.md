# V7 Registry V2 production-call composition replay

## Result

**PASS for the independently translated production components and their exact
accepted-path composition.**

The strongest checked theorem is:

```text
V7RegistryV2ProductionCallComposition.translated_components_compose_exact_accepted_path
```

It composes current literal ASQ8 reconstruction, current literal canonical
ASR8 production, successful Registry V2 atomic caller/writeback, all
transaction-local fixed-width correspondences, and both immutable deployment
certificate roots.

This is deliberately not reported as a one-root literal translation of
`process_with_clear_return_data`. The current Aeneas `AccountInfo` borrow join
described in `README.md` remains the exact blocker to that stronger statement.

## Focused release gates

| Gate | Unit | Invocation | Wall | Peak RSS | Swap | Exit |
|---|---|---|---:|---:|---:|---:|
| Charon codec extraction | `aspis-v7-production-call-charon-codecs-02` | `08219fc8000e4a9893dae92fffa41374` | 14.68 s | 518,492 KiB | 0 | 0 |
| Aeneas codec translation | `aspis-v7-production-call-aeneas-codecs-02` | `bfda9ce1f18d43a0bbb3291d0ee30f8e` | 1.93 s | 152,064 KiB | 0 | 0 |
| Generated codec types | `aspis-v7-production-codecs-types-renamed-01` | `4c2d53af82b44c74b4d164cc341de0b1` | 1.99 s | 2,601,936 KiB | 0 | 0 |
| Generated codec externals | `aspis-v7-production-codecs-externals-renamed-01` | `032288f7f2814f90a16b02e7c8a62de1` | 1.19 s | 2,557,328 KiB | 0 | 0 |
| Generated codec functions | `aspis-v7-production-codecs-funs-renamed-02` | `0d6d840844ab49c59efbbfa411505899` | 2.26 s | 2,641,340 KiB | 0 | 0 |
| Codec source bridge | `aspis-v7-production-codecs-bridge-renamed-02` | `6e2ea604490c496c9136deda19ac8971` | 1.40 s | 2,560,204 KiB | 0 | 0 |
| Deployment dependency bridge | `aspis-v7-production-compose-deployment-olean-01` | `69945a06171048b19ccbe4a8804af565` | 2.74 s | 2,582,900 KiB | 0 | 0 |
| Final composition theorem | `aspis-v7-production-compose-capstone-06` | `511fa5fd2fcb4693bb0182bfda9e85ba` | 1.27 s | 2,565,384 KiB | 0 | 0 |

All jobs were focused, bounded, and used zero swap. No broad unchanged
regression was rerun.

## Axioms and forbidden constructs

The two codec theorems and the final composition theorem each print exactly:

```text
[propext, Classical.choice, Quot.sound]
```

The accepted proof/generated sources are clean for `sorry`, `admit`,
`sorryAx`, `native_decide`, and project-defined axioms. Generated archival
templates are excluded from the accepted compile graph.

## Frozen artifact hashes

See `evidence/SHA256SUMS` for the LLBC, generated accepted Lean, proofs, and
checked namespace staging transform.

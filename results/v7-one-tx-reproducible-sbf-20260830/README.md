# V7 one-transaction reproducible Linux SBF evidence

The provenance-complete `r6` replay passed from exact source commit
`da77d5f5a22681200cceec8e90fc69ac2cc81ad8`. It authenticated the Linux
platform-tools/SBF SDK plus both Cargo registry namespaces before and after
building, exported the source twice, used independent target/output
directories, and required byte-identical results.

| program | bytes | SHA-256 | A/B |
|---|---:|---|---|
| atomic-marker Pool | 525,888 | `82606a25f00fd683b06186cdaae519b52c793d9a2f16f9d3f7c40c2b241685c2` | identical |
| Tag-73 verifier | 1,812,264 | `c43960303f2d67606362dc09d74f3a7983dcfcbe0665984a385a0efa7ddc5e47` | identical |

The capped service exited zero after 9:49.19. Its observed cgroup peak was
2,094,817,280 bytes under MemoryHigh=9 GiB and MemoryMax=12 GiB; swap peak was
zero. `reproducible-sbf.json` is SHA-256 `1b66865f...`. The materialized
eleven-case bundle (`b4ca543d...`) passed the exact offline validator
(`206e1237...`). No Agave execution or CU measurement occurred because no
prebuilt Linux Agave 4.2+ `solana` and `solana-test-validator` pair exists in
the inspected assets.

This successful build is not, by itself, a mainnet-ready Pool release. The
SBF analyzer reports the production permissionless-checkpoint function
`plan_pair_forest_checkpoint_accounts_v1` at stack offset 4,368 bytes, 272
bytes beyond the 4,096-byte SBF limit (estimated frame 4,544 bytes). The spend
terminal is not the flagged function, but the Pool ecosystem release remains
blocked until that checkpoint frame is restructured and the Pool SBF/runtime
evidence is refreshed.

No transaction was signed, submitted or deployed.

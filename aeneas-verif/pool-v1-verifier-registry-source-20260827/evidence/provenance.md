# Verifier-registry source provenance and focused resources

Base source commit: `62da33248eadcbc446b907d7ead675a78ee49447`

## Authenticated inputs

| Artifact | SHA-256 |
|---|---|
| `programs/aspis-pool/src/registry.rs` | `ef68bfef98e6885167119ff6cb947f116177c0648f3aec4941893ac774079017` |
| `VerifierRegistryProduction.llbc` | `f84e23debef7576870c9ae14eca8dbf54bd6d697b83fe801186519060e62583f` |
| `VerifierRegistryDecoders.llbc` | `c44c14e7ff5f713907065ce7632acb60a13b6fbb59378470e962b695b0625d8c` |
| `AspisFormal/Pool/VerifierRegistryV1.lean` | `5fe551399c0051107a5d3362041e89e69d613cd280f83b7cd84280c8fd6aa8a9` |
| `AspisFormal/Pool/AuthorizationReceiptV1.lean` | `59e82b9b173c29632df22b8530024fbfe47157b2217b80198d0d2ac6d75d6c49` |

## Checked Lean sources

| Artifact | SHA-256 |
|---|---|
| decoder `Types.lean` | `cf58a940b3de9895d56c8c56cc67bdc351078323c80694dc285a7e81393ff0c1` |
| decoder `FunsExternal.lean` | `df2464b0fbc0b8f4b8a6d118d524596455ad66bf4f6b65122eca54271788c7be` |
| decoder `Funs.lean` | `e8f4d1fce255835dfa0d77d863cf6e56a006da7c28b4ecb708e28ebca61b755b` |
| readonly `Funs.lean` | `8665ed0735b0c85e38146458858759c45835edc62bf8dd9f9cc882409a7015c9` |
| `PoolV1VerifierRegistrySourceBridge.lean` | `62bbaa1ad3c57a748cb5160f6c81881c6b2b0d465a38c095f2f5be07c54264ed` |

Both LLBC files record `has_errors=false`.  The production LLBC records
Charon `0.1.223`, target `x86_64-unknown-linux-gnu`, `sysroot=default`, Aeneas
preset, and the sole start root
`aspis_pool::registry::authenticate_verifier_selection_v1`.  It contains the
complete source text of `registry.rs`, providing an independent byte-level
source pin in addition to the repository digest.

The production Charon run completed in 56.00 seconds at 510,080 KiB maximum
RSS.  The focused Lean stages observed these NUC peaks before the final
one-command replay:

| Stage | Peak RSS | Swap |
|---|---:|---:|
| generated decoder types | 2,565,820 KiB | 0 |
| generated decoder functions | 3,200,920 KiB | 0 |
| exact readonly-account function | 2,585,068 KiB | 0 |
| source bridge and terminal theorems | 6,944,288 KiB | 0 |

Every heavy check used Lean 4.32 with `LEAN_NUM_THREADS=1` in a NUC user
cgroup configured as `MemoryHigh=12G`, `MemoryMax=16G`, and
`MemorySwapMax=0`.

The final clean one-command replay of `check-focused-lean.sh` completed with
exit status 0 in 20.68 seconds, reached 6,925,512 KiB maximum RSS, and used
zero swaps.  It compiled all four generated/source stages and printed the
axioms of every terminal theorem as exactly `propext`, `Classical.choice`,
and `Quot.sound`.

## Exact remaining boundaries

Only the following Solana runtime operations remain parameters:

1. `Pubkey::find_program_address`, with the literal production registry/entry
   seeds and exact pool/profile/release/program ordering visible in Lean; and
2. `AccountInfo::try_borrow_data`, whose successful immutable byte slice is
   passed directly into the exact translated registry and entry decoders.

SHA-256, Poseidon, the Circle theorem and Tag-73 proof soundness are not used
by this registry policy theorem.  Receipt authenticity/issuer soundness also
remain in their already-named `AuthorizationReceiptV1` interfaces; the bridge
proves only their exact registry-authorization component.

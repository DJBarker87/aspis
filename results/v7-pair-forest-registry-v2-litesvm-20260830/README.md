# V7 Registry V2 combined one-transaction evidence

Date: 2026-08-30

This bundle is the first executable end-to-end measurement of the eight-lane
Pool terminal through immutable Registry V2 and the current production Tag-73
verifier. It is not a sum of component estimates:

```text
TxV1 -> Pool -> ASR2/ASE2 authentication -> Tag-73 verifier CPI
     -> exact ASR8 -> canonical nullifier-marker creation
     -> lane/history update -> optional SPL custody CPI
```

Every selected success uses a true `VersionedMessage::V1` transaction with the
production wallet budget configuration: 10,000-lamport priority fee, 1,400,000
CU limit, 8 MiB loaded-account-data limit and 256 KiB heap. The 30-KiB proof
stays in its verifier-owned account. It is not embedded in the transaction.

## Selected combined result

| Operation | History | Combined CU | TxV1 bytes | CU headroom to 1.3M | Byte headroom to 4,096 |
| --- | --- | ---: | ---: | ---: | ---: |
| private transfer | same page | 1,161,460 | 845 | 138,540 | 3,251 |
| private transfer | rollover | 1,207,174 | 878 | 92,826 | 3,218 |
| withdrawal | same page | 1,153,110 | 1,010 | 146,890 | 3,086 |
| withdrawal | rollover | 1,218,822 | 1,043 | 81,178 | 3,053 |

All four rows run the strict current proof, including all three 35/31/34-bit
work checks. The worst case remains below 1.3M CU and uses only 25.5% of the
4,096-byte target. The exact ledgers are the four
`production-*-success.json` files.

Each success checks all of the following after execution:

- the loader-v3 Registry and verifier deployments are finalized (`None`
  upgrade authority) and match the exact executable SHA-256 stored by V2;
- ASR2 is frozen and unpaused, ASE2 is active for the exact profile, release,
  statement version, policy and selected program;
- the Tag-73 CPI returned an exact canonical 792-byte ASR8 from the selected
  program;
- the live lane and root-history images equal the authenticated candidate;
- a previously absent canonical nullifier PDA was created and consumed;
- master, retained checkpoint, Registry, entry and proof accounts stayed
  byte-exact;
- withdrawal debits the vault and credits only the bound destination by the
  exact amount.

## Real Registry V2 governance

The harness does not seed synthetic ASR2/ASE2 images. Each run installs the
loader-v3 programs in LiteSVM, authenticates their Program/ProgramData linkage,
executes real V2 initialize and schedule instructions, waits for the activation
slot, activates the entry and freezes the Registry. The production-verifier
run measured:

| V2 operation | CU | TxV1 bytes |
| --- | ---: | ---: |
| initialize immutable Registry | 106,065 | 504 |
| schedule immutable Tag-73 verifier | 929,136 | 617 |
| activate | 12,794 | 373 |
| freeze | 4,914 | 340 |

The expensive schedule step hashes the complete 1,819,480-byte verifier
ProgramData payload once. It still fits below 1.4M CU. A wrong Registry
executable hash is rejected at 99,843 CU and a wrong verifier executable hash
at 920,533 CU; both preserve the Registry and entry accounts byte-for-byte.

The frozen honest fixtures are 256-byte ASR2 SHA-256
`cb0aa4373e923eace3187333a5485728240a36c2ff8ecdf7c33779e8226d604c`
and 320-byte ASE2 SHA-256
`e82965fc06929e94d9318b355d8c387d8d87cd34c459c612fe1923ae133fd81e`.
Every production ledger has its own byte-identical sidecars.

## Adversarial/rollback coverage

| Case | CU | TxV1 bytes | Result |
| --- | ---: | ---: | --- |
| mutated strict proof | 975,390 | 845 | rejected after production verifier CPI; exact rollback |
| wrong active release | 36,629 | 845 | rejected before verifier CPI; exact rollback |
| stale selected lane | 72,167 | 845 | rejected by verifier against current authenticated lane; exact rollback |
| replay after successful settlement | 23,727 | 845 | canonical marker rejects; settled state preserved |
| wrong-length ASR8 | 47,114 | 845 | rejected; exact rollback |
| canonical ASR8 bound to wrong lane account | 50,151 | 845 | rejected; exact rollback |
| failed withdrawal Token CPI after honest verifier success | 1,151,875 | 1,010 | marker/lane/history/vault/destination all roll back exactly |

The two malformed-result cases select a 20,816-byte test-only verifier through
the same immutable V2 ProgramData/hash certificate, so the Pool's return-data
boundary is exercised rather than bypassed. The failed-custody case runs the
production Tag-73 verifier successfully, then replaces Tokenkeg locally with a
fail-closed test double; the whole Solana transaction rolls back.

## Pinned source and artifacts

The production SBF source commit is
`4722228b991ebb72850b8d79dd54b0fee4899462`.

| Input | Git tree / artifact SHA-256 | Bytes |
| --- | --- | ---: |
| Pool source | `0bebca6b10c61e1d97949da10e6b4901d5117fa0` | - |
| verifier source | `0b9627c523ac47682f3c987abd68ae2027ac5eb2` | - |
| Registry source | `50edc0c660f12c68baa6298f8f01e3422ea8b70b` | - |
| `aspis_pool.so` | `0e94c98d28437f0b01dce546fdefaad21dc10772a4d46991c2a573d8129cd4f6` | 534,608 |
| `aspis_verifier.so` | `97df12937d46e25a2eeefeac16ce31925fd473c672d6b656548be9220adbcc6d` | 1,819,480 |
| `aspis_registry.so` | `0f14c7b74ec6cbe3b3f637b0f24c7e8cdc46fd09f5b2e495fd51ada16ad8f11b` | 189,824 |
| result double | `3693edf83f100ca90229a8aa0406182d71fd56b6480a1fa7366c4caff4ad5c29` | 20,816 |

The Linux SBF jobs used `solana-cargo-build-sbf 2.3.0`, platform-tools v1.48
and Rust 1.84.1. They ran sequentially in a systemd cgroup with
`MemoryHigh=8G`, `MemoryMax=12G`, `MemorySwapMax=0`. Peak RSS was 565,232 KiB
for Pool, 567,460 KiB for verifier, 200,068 KiB for Registry and 168,080 KiB
for the focused result-double retry. Every selected build exited 0 with zero
swap. Exact logs, `/usr/bin/time -v` records, hashes and sizes are under
`build-evidence/`.

## Replay

From the repository root, using the committed SBF artifacts:

```sh
bash results/v7-pair-forest-registry-v2-litesvm-20260830/replay-local.sh \
  /tmp/aspis-v7-registry-v2-replay
```

The script refuses to overwrite its output directory, rebuilds only the local
LiteSVM harness with the locked offline graph, and executes all four honest
shapes plus the seven failure/replay cases. Each JSON ledger contains full
program logs, return-data hash, exact transaction bytes, CU, governance
receipts and before/after atomicity checks.

`preliminary-budget-only/` retains the first diagnostic run, which omitted the
wallet's priority-fee and heap-budget instructions. Those rows remain useful
for attribution but are not the selected packet/CU evidence.

## Honest remaining gates

This is deterministic local LiteSVM/Agave 4.2.1 evidence, not a devnet or
mainnet receipt. It is one Linux SBF build, not yet the final independent A/B
reproducibility comparison. No cryptographic relation, transcript, proof wire,
ASQ8, ASF8 or ASR8 byte changed in this work.

Before activation, the still-required work is:

1. refresh the Rust-to-Charon/Aeneas-to-Lean bridges for Registry V2
   ProgramData parsing/code hashing and the exact Pool/verifier V2 selector;
2. compose those bridges with the existing marker, lane/history, custody and
   rollback caller theorems;
3. reproduce the selected SBFs independently and freeze the final binary
   equality/stack analysis;
4. execute the same Registry lifecycle and all four terminal shapes on the
   feature-enabled 4-KiB devnet path, then perform the final deployment audit.

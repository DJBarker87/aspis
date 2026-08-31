# V7 Registry V2 mainnet readiness — 1 September 2026

## Decision

**NO GO.** The one-transaction runtime candidate is locally green, but this is
not yet a deployable mainnet release candidate.

The decisive issue is identity, not CU. The measured Pool and Registry IDs are
fixture constants, and the verifier binary pins them. The tested verifier ID is
the historical V5 mainnet ID whose ProgramData was closed. No production
program identities or deployment-key custody records exist for this candidate.
Changing those IDs changes the verifier binary and the identity-bound
statements/proofs, so the affected formal, build, lifecycle and devnet evidence
must be regenerated.

Public devnet is also externally blocked: at finalized slot 491,160,606 the
TxV1/4KiB feature account was absent. The read-only gate failed closed and no
public deployment or lifecycle was attempted.

## What is complete

| Gate | Frozen result |
| --- | --- |
| Exact runtime source | commit `7179f7c550fe0461f4251dea5268af73876da91d`, tree `72d8ccd295994277bcb5f9df922c2a1483ac0443` |
| Reproducible Linux SBF | two isolated copies, all three binaries byte-identical, stack gate green, zero swap |
| Pool SBF | 534,608 B, SHA-256 `0e94c98d28437f0b01dce546fdefaad21dc10772a4d46991c2a573d8129cd4f6` |
| Verifier SBF | 1,819,480 B, SHA-256 `97df12937d46e25a2eeefeac16ce31925fd473c672d6b656548be9220adbcc6d` |
| Registry SBF | 189,824 B, SHA-256 `0f14c7b74ec6cbe3b3f637b0f24c7e8cdc46fd09f5b2e495fd51ada16ad8f11b` |
| Signed local lifecycle | official Agave 4.2.0; identical bytes simulated/submitted; all 11 cases finalized |
| Honest cases | all four changed the expected protected state and stayed below 1.3M CU |
| Negative cases | all seven landed as failures with exact protected-account rollback |
| Terminal transport | ASQ8 320 B, transient ASF8 1,880 B, ASR8 792 B; proof remains in its account |
| Statement/proof inventory | exact hashes for four requests, statements, results, proof accounts, candidates and proof bodies |
| Secrets scan | no tracked keypair/PEM/mnemonic/private-key assignment or production key configuration found |
| Public devnet preflight | read-only, finalized, feature inactive, no signing/submission/deployment |

The SBF build used platform-tools v1.48 and
`solana-cargo-build-sbf 2.3.0`, offline and locked, under
`MemoryHigh=10G`, `MemoryMax=12G`, `MemorySwapMax=0`. Cgroup peak was
1,144,864,768 bytes. The signed lifecycle ran under the same hard memory cap;
its peak was 1,553,203,200 bytes and it used no swap.

## Exact landed runtime envelope

These are real combined one-transaction Agave CU measurements, not sums of
components.

| Finalized case | Packet bytes | Landed CU | Result |
| --- | ---: | ---: | --- |
| transfer, same page | 833 | 1,161,348 | success |
| transfer, rollover | 866 | 1,207,062 | success |
| withdrawal, same page | 998 | 1,152,942 | success |
| withdrawal, rollover | 1,031 | 1,218,654 | success |
| strict proof mutation | 833 | 975,278 | rejected, exact rollback |
| wrong Registry/release | 833 | 36,573 | rejected, exact rollback |
| stale selected lane | 833 | 72,055 | rejected, exact rollback |
| replay/nullifier | 833 | 23,671 | rejected, exact rollback |
| malformed result | 833 | 47,002 | rejected, exact rollback |
| mutated result | 833 | 50,039 | rejected, exact rollback |
| failed withdrawal CPI | 998 | 1,151,707 | rejected, exact rollback |

Worst honest headroom is 81,346 CU to the 1.3M target and 3,065 bytes to the
4,096-byte TxV1 ceiling. The full signed suite is frozen at SHA-256
`2772c65a6ae68a7fa66790b1451e905c1df2e61afdef76e2443254fd02b464e8`.

## Exact identity blocker

| Program | Runtime-tested ID | Why it cannot be promoted |
| --- | --- | --- |
| Pool | `5PjDJaGfSPJj4tFzMRCiuuAasKg5n8dJKXKenhuwZexx` | fixture `[0x41; 32]`; verifier hard-codes it |
| Verifier | `7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue` | historical V5 ID; ProgramData `cdRqe7MGCEJ2Z6iZfWuXtuymRiAhXtyfDgT47sKZr69` was closed at slot 435,019,804 |
| Registry | `5bV6jUfhDHCQVA1WfKBUnXUsboJgoKgkzkKcxr3joew5` | fixture `[0x44; 32]`; verifier hard-codes it |
| policy binding | `[7; 32]` | explicit audit-only verifier constant |

The verifier source itself labels these values as an audit-build release
capability and says production activation remains blocked until generated
production Pool/Registry/policy constants replace them. No tracked deployment
keypair exists, and same-ID verifier redeployment is not proved.

Production selection must freeze: all three program IDs, Registry multisig,
policy binding, deployment domain, asset mint/ID, fee payer and
upgrade-authority custody. Then regenerate:

1. source/blob/tree and Rust-to-Lean/Aeneas bindings;
2. all three SBFs, dual-build equality and stack analysis;
3. canonical PDAs and account inventory;
4. identity-bound ASQ8/ASF8/ASR8, proof accounts and proofs;
5. the signed four-honest/seven-negative local lifecycle;
6. public-devnet finalized lifecycle after TxV1 activation;
7. deployed byte/ProgramData/authority receipts; and
8. wallet, indexer, relayer and RPC-quorum startup manifests.

## Authority and rollback boundary

Registry V2 intentionally accepts only immutable loader-v3 deployments:

- Registry ProgramData authority must be `None` before V2 initialize;
- verifier ProgramData authority must be `None` before V2 schedule;
- Pool must be made immutable before accepting real custody; and
- Registry state freeze zeros governance authority.

Deploying upgradeable first creates a short verification/rollback window: dump
the deployed bytes, compare SHA-256 through two RPCs, and redeploy the last
audited artifact if necessary. `set-upgrade-authority --final` ends that
window. Registry freeze then removes pause/unpause/retire as well. There is no
post-final code rollback and no post-freeze Registry rollback or fund rescue.
This needs explicit two-person human approval, not an automated default.

The exact unsigned Registry V2 instruction builders exist, but there is no
reviewed executable offline/multisig ceremony tool in this revision. Operators
must not hand-encode governance bytes; that tool is a P0 launch gate.

## Dependency and secret review

The targeted read-only scan found no tracked sensitive filenames or private
key material. Production RPC/WS credentials, alerts and persistent keys are
also absent, which is correct for the repository but means operations are not
configured.

The local RustSec database was commit
`6420e39260b3d771b049954cf5d52b57e2118da4` dated 27 August 2026. Two workspace
advisories (`curve25519-dalek 3.2.0`, `ed25519-dalek 1.0.1`) do not reach the
selected SBF normal dependency graphs. Those SBF graphs still reach unmaintained
`bincode 1.3.3` and `libsecp256k1 0.6.0`, unsound-advisory
`rand 0.7.3`, and yanked `num-bigint 0.4.7`. The wallet reaches the
curve/Ed25519 vulnerabilities through its signature-verification feature and
also reaches the three unmaintained/unsound warnings plus yanked
`chacha20 0.10.1`. A documented exploitability/upgrade decision remains P1,
promoted to P0 before shipping any affected in-process signing path.

## Open launch gates

### P0

1. select/custody deployable production IDs and replace audit constants;
2. consolidate complete current K1/source closure onto the exact release source;
3. regenerate every identity-affected artifact and repeat the signed lifecycle;
4. wait for public-devnet TxV1 activation and land the finalized public suite;
5. approve the immutable/no-rollback model and incident procedure;
6. freeze production asset/policy/canary configuration; and
7. implement and audit the offline/multisig deployment/governance ceremony tool.

### P1 before public beta

1. configure independent paid RPC/WS providers, paging and alert ownership;
2. close the dependency exploitability/upgrade review;
3. run external security/operations review and cold recovery rehearsal; and
4. prove wallet/indexer/relayer startup gates against both providers.

## Evidence and replay

- Machine manifest:
  [`release/v7-registry-v2-mainnet-rc1/manifest.json`](../../release/v7-registry-v2-mainnet-rc1/manifest.json)
- Statement/proof inventory:
  [`statement-inventory.json`](../../release/v7-registry-v2-mainnet-rc1/statement-inventory.json)
- Disabled production ceremony:
  [`runbook.md`](../../release/v7-registry-v2-mainnet-rc1/runbook.md)
- Offline verifier:
  [`verify.sh`](../../release/v7-registry-v2-mainnet-rc1/verify.sh)
- Dual SBF audit:
  [`reproducible-sbf-stack-audit.json`](../../results/v7-registry-v2-release-audit-20260831/dual-linux-sbf-r2/reproducible-sbf-stack-audit.json)
- Signed/finalized local suite:
  [`suite.json`](../../results/v7-registry-v2-release-audit-20260831/agave-finalized-r1/evidence/suite.json)
- Public-devnet gate:
  [`gate.json`](../../results/v7-registry-v2-release-audit-20260831/devnet-feature-gate-r2/gate.json)

Run `release/v7-registry-v2-mainnet-rc1/verify.sh` for the focused offline
consistency check. It deliberately reports `releaseDecision=NO_GO` and does not
build, sign, submit, deploy, contact an RPC or rerun the lifecycle.

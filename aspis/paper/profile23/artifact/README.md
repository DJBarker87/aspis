# Profile 23 artifact guide

Status: scaffold. Commands marked `TODO` do not exist yet and must not be
advertised as reproducible until implemented and tested on a clean machine.
This guide covers the frozen local release; it contains no mainnet, novelty,
audit, or production-readiness claim.

## Scope

The headline object is one local Solana/Agave transaction that consumes a
finalized, pre-uploaded proof account, verifies the complete Profile 23 proof,
and atomically writes the nullifier marker and next pool state. Proof-account
creation, chunk uploads, readback, and `FinalizeProof` are prior transactions.
They are excluded from headline CU but included in lifecycle evaluation.

The canonical manifest is:

```text
results/stage2/profile23_one_transaction_release.json
```

All displayed facts must be generated from that manifest after verifying its
cross-links. Do not transcribe numeric values into artifact scripts.

## Required environment capture

Before release, fill and machine-generate:

- source commit/tag, dirty-tree disclosure, submodules, and lockfiles;
- container or Nix derivation and immutable image digest;
- host CPU, RAM, OS/kernel, architecture, and disk;
- Rust, Cargo, Solana/Agave, LLVM and SBF tool versions;
- validator genesis, feature set, account fixtures, compute-budget and heap
  instructions;
- default feature set and exact SBF build command; and
- expected runtime, peak memory, disk, network access, and nondeterminism for
  every tier.

## Reproduction tiers

<!-- markdownlint-disable MD013 -->

| tier | purpose | must produce | expected resources | command |
| --- | --- | --- | --- | --- |
| 0 | cached bundle and stale-claim audit | hashes, complete live-evaluation-matched gate result, cross-link report, generated-paper-macro diff | TODO | `TODO: artifact verify --tier 0` |
| 1 | fast semantic/teeth tests | relation/parser/transcript/finalization/rollback/privacy report | TODO | `TODO: artifact verify --tier 1` |
| 2 | clean default SBF rebuild | byte-equality, length/hash, features and configured-address report | TODO | `TODO: artifact verify --tier 2` |
| 3 | pinned local Agave replay | raw transactions/RPC/logs, literal CU, exact pre/post account images, failures | TODO | `TODO: artifact verify --tier 3` |
| 4 | slow theorem certificates | regenerated ledgers, Good23/rank products, independent-checker outputs and negative fixtures | TODO | `TODO: artifact verify --tier 4` |
| 5 | fresh proof and mining | fresh statement/proof/account frame, q3/attempt statistics, mining/proving time and memory, accepting replay | TODO | `TODO: artifact verify --tier 5` |

<!-- markdownlint-enable MD013 -->

Tier 0 must fail if the inherited stale soundness value appears, any canonical
manifest field differs from a source artifact, a required gate is red, the
proof account is mutable, the pairwise-hiding field is missing, generated
paper files are dirty, or mainnet language is enabled without immutable
mainnet evidence.

## Raw-output layout

The implemented runner should create a new content-addressed directory rather
than overwriting evidence:

```text
artifact-output/<bundle-hash>/
  environment.json
  source-status.txt
  manifest-crosslinks.json
  hashes.txt
  generated-paper-facts.{json,tex,md}
  tests/
  build/
  validator/
    genesis/
    feature-set.json
    transactions/
    rpc/
    logs/
    accounts-before/
    accounts-after/
  certificates/
    generated/
    independently-checked/
    negative-fixtures/
  lifecycle/
  prover-miner/
  contention/
```

Preserve command lines, exit status, stdout/stderr, start/end timestamps, and
tool versions. Summarized JSON does not replace raw validator logs, RPC
responses, transaction bytes, or account images.

## Lifecycle experiment

Measure proof-account and pool creation, every upload chunk, full readback,
finalization, and the accepting spend separately. Report transaction count,
serialized size, CU, fees, rent-exempt balances, retained bytes, latency, and
failure behavior. Separately report prover wall time/peak memory, q3 schedule
outcomes, bounded attempts/Abort, canonical-work mining, and complete
time-to-spend.

## Contention and failure experiment

Run controlled workloads for same-nullifier/same-pool,
different-nullifier/same-pool, and independent-pool spends. Capture account
lock conflicts, success/rejection counts, client retries, CU, and per-slot
throughput. Include corrupt proof, stale anchor/sequence, malformed owner and
length, noncanonical fields, unauthorized upload/finalize, gaps/overlaps,
write-after-finalize, double-finalize, pool reinitialization, account-type
substitution, replay, and front-running/griefing cases. Every failed case must
show exact unchanged pre/post state or explain the expected System CPI rollback.

## Independent certificate check

The Good23 checker must reconstruct public matrices from the pinned layout and
schedule rather than consume matrices supplied by the generator. It verifies
dimensions, ranks, pivots, kernels, constant preimage cardinality, nonzero
minors, source guards, and fingerprints. Publish at least one independently
constructed malformed certificate per checked invariant and show rejection.

## Clean-release and anonymity rules

The public artifact binds a clean signed revision and content-addressed bundle.
For double-blind review, create a separate scrubbed snapshot without repository
history, author URLs, acknowledgments, grant metadata, DOI/ePrint links,
configured program address, or deployment identifiers. Keep the mapping to the
canonical bundle private until venue policy permits disclosure.

The configured local address is not deployment evidence. A later deployment
artifact must additionally record the Program/ProgramData accounts, loader
owners and linkage, deployed bytes/hash, remaining capacity, finalized slot,
upgrade-authority state, proof/account identities, transaction signature,
literal CU, and exact post-state.

# V5 Tag-67 deployment record

Status date: 2026-07-23
Decision: **Ready for mainnet deployment**

V5 Tag 67 is enabled in the default `aspis-verifier` feature set and routes
only through the atomic verify-and-apply wrapper. The plain manifest-default
SBF build is byte-identical to the production-feature binary. This record
binds the code, formal proof, runtime envelope, and deployment handoff to that
artefact.

At this 2026-07-23 preflight cutoff, V5 had not yet been deployed on mainnet.
The q18/g37 Tag-65 transaction finalized on 2026-07-16 is a separate release
preserved under
[`aspis-spend-q18-g37-mainnet-v1`](../aspis-spend-q18-g37-mainnet-v1/).

## Release artefact

| Item | Value |
| --- | --- |
| Canonical program ID | `7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue` |
| SBF | `results/spend/v5-production-tag67-freeze-stream3-20260722/aspis_verifier_v5_production_tag67.so` |
| Size | 1,258,496 bytes |
| SHA-256 | `4cf3c1d5ddd47efa68875c0070247e007083c5c9bb2d5988db0d644a609edf40` |
| Provenance | `aspis_verifier_v5_production_tag67.provenance.json` |
| Provenance SHA-256 | `a7c9f7bea70d9805d8aff093fad309c911c752f2d47f6ad489c2f2eda1d7c3ec` |
| Source identities | 77/77 matched against the build workspace |
| Toolchain identities | 91/91 matched |
| ProgramData allocation minimum | 1,258,496 bytes |
| Suggested fresh allocation | 1,300,000 bytes, leaving 41,504 bytes |

### Release identity

| Identity | Value |
| --- | --- |
| Clean build source commit | `06788d44d30ea8cbd391899dddaf6f0acc6e4a3f` |
| Clean build source tree | `9b6bdfddb3c213addc2bb705c8130cce4fb2c351` |
| Candidate tag | `aspis-v5-tag67-frozen-candidate-v1` |
| Candidate tag commit | `d98a2e69618dc95b95c1996506ed8c05904a56a1` |
| Release metadata tree | `919f461131dbdceb8fa00783a16658fa10059ac6` |
| Candidate manifest | [`release/aspis-v5-tag67-frozen-candidate-v1/manifest.json`](../aspis-v5-tag67-frozen-candidate-v1/manifest.json) |
| Frozen SBF | 1,258,496 bytes, SHA-256 `4cf3c1d5ddd47efa68875c0070247e007083c5c9bb2d5988db0d644a609edf40` |

The source commit and source tree identify the clean checkout that produced
the frozen SBF. The candidate tag resolves to the later commit whose tree
contains the release bundle, manifest, and finalized devnet record. The
manifest records the earlier build source and the exact SBF identity; it does
not try to name the commit that contains itself. The
[release facts record](../release-facts.json) supplies that outer binding from
the candidate tag to its commit.

Later documentation or release-index changes do not replace any identity in
this table. They refer back to the candidate tag and commit while the program
remains exactly 1,258,496 bytes with the stated SHA-256. If a later change
alters even one SBF byte, it requires a new manifest and candidate tag. A
byte-identical rebuild from a later source commit may add a new parity record,
but it does not rewrite this candidate's build-source or tag history.

The production-feature build and the later manifest-default build produced the
same bytes. `v5-production-tag67` is therefore both the measured binary and the
default deployment binary. A fresh clone of public `main` at
`06788d44d30ea8cbd391899dddaf6f0acc6e4a3f` then rebuilt the manifest-default
program to the same 1,258,496 bytes and SHA-256. The
[source-parity attestation](../../results/spend/v5-production-tag67-freeze-stream3-20260722/source-parity-attestation.json)
reconciles every build-snapshot/source delta and records the clean command,
tree, tool, and output identities.

## Mainnet CU policy

The measured-and-derived V5 CU ceiling is **1,356,912 CU**, leaving
**43,088 CU** below Solana's 1.4 million limit. The mainnet runner enforces
two conditions before submission:

- the canonical nullifier PDA bump is 255, so on-chain address derivation
  takes one 1,500-CU attempt; and
- simulation of the exact signed transaction bytes succeeds at or below 1,356,912 CU.

The runner then submits the same serialized transaction and verifies its
landed CU and refetched bytes. The transaction compute limit is also
1,356,912 CU, so execution above the policy ceiling fails atomically.

The original runtime 2.3.13 topology derivation used the absent-marker
create-account path:

| Selector | Measured missing-marker CU | Measured/max parent hashes | Grammar ceiling |
| ---: | ---: | ---: | ---: |
| 0 | 1,331,232 | 457 / 487 | 1,350,688 |
| 1 | 1,333,896 | 467 / 487 | 1,348,232 |
| 2 | 1,326,480 | 442 / 487 | **1,353,616** |

Each missing-marker measurement completed the real System Program
create-account CPI and repeated identically three times. The selector-0
initialized program-owned marker control consumed 1,328,897 CU, also
identically three times, without a CPI.

That topology bound covers the complete proof grammar:

- proof body: at most 77,278 bytes;
- sealed proof account: at most 77,318 bytes;
- pool: exactly 80 bytes;
- nullifier marker: exactly 72 bytes;
- instruction: exactly 169 bytes;
- five frontier sections: at most 338/338/284/230/176 nodes;
- total frontier nodes: at most 1,366;
- executed internal parent hashes: at most 487.

Every additional radix-4 parent is budgeted at 512 CU, above its measured
SHA-256 syscall, loop, and child-copy cost. The GoodA/GoodB control-flow
variation receives a separate 4,096-CU allowance. The missing-marker path
upper-bounds the initialized program-owned marker path because it performs the
same verification plus the create-account CPI. The accepted prefunded
System-owned marker path is measured separately below.

The original machine-readable topology derivation is
[`v5_universal_accepted_topology_cu_policy.json`](../../results/spend/v5-production-tag67-freeze-stream3-20260722/v5_universal_accepted_topology_cu_policy.json),
SHA-256
`0da8ebbaee5b26bf82814bbc1cd7ebdfc1d542a8207bea30fb882ffb51c904cf`.

### Current mainnet runtime and prefunded marker

Mainnet-beta reported Agave `4.1.0`, feature set `3345198602`, on
2026-07-23. The release SBF was replayed on the matching official validator
across selectors 0, 1, and 2 with real missing-marker System Program CPI.
The totals were 1,331,178, 1,333,842, and 1,326,426 CU, each exactly 54 CU
below the 2.3.13 result. The present-marker control remained exactly
1,328,897 CU; this is the initialized program-owned marker control.

The runtime also accepts a canonical System-owned, empty marker PDA that has
already received lamports. A one-lamport fixture exercises the longest
supported path: transfer to rent exemption, allocate, then assign. The exact
mainnet instruction sequence includes the compute-unit price instruction
before Tag 67. It measured 1,334,528, 1,337,192, and 1,329,776 CU across the
three selectors. The price instruction contributes 150 CU and the prefunded
marker path contributes another 3,200 CU over the corresponding absent-marker
execution.

| Selector | Prefunded baseline | Extra parents | GoodA/GoodB reserve | Bump-255 CU ceiling |
| ---: | ---: | ---: | ---: | ---: |
| 0 | 1,334,528 | 30 × 512 | 4,096 | 1,353,984 |
| 1 | 1,337,192 | 20 × 512 | 4,096 | 1,351,528 |
| 2 | 1,329,776 | 45 × 512 | 4,096 | **1,356,912** |

The SHA-256 parent-hash charge, instruction metering, heap costs, CPI byte
cost, and 1.4M transaction limit used by the release policy remain compatible.
Selector 2 remains governing after topology normalization. The runtime
identity, release hashes, all marker-mode measurements, and pinned source
references are in
[`results/spend/v5-mainnet-runtime-4.1.0-20260723/`](../../results/spend/v5-mainnet-runtime-4.1.0-20260723/).

The table derives topology and GoodA/GoodB variation from the frozen replay
family. Transcript challenge sampling also has bounded retry paths. Rather
than treating this calculation as a theorem over every accepted byte string,
the mainnet runner simulates the exact signed candidate transaction against
the V5 CU ceiling.

`Pubkey::find_program_address` charges another 1,500 CU after each failed bump.
The historical topology record predates this runner scope. A future policy or
binary that accepts a wider bump range or a higher simulation result gets a
new ceiling.

## Formal correspondence

The formal proofs pass under Lean 4.32 default limits.

- **Component A:** maintained rank/applicability theorems and source
  correspondence at the selected release schedule. The runtime independently
  recomputes GoodA and GoodB for every selected branch.
- **Component B:** deterministic sampler/evaluator/layout correspondence and
  maintained terminal theorem.
- **Component C:** actual-current sampler, encoder, arithmetic/folds, finish,
  packer, and public output. The final public theorem is
  `generated_public_run_output_matches_deployed`.
- **Tag 67:** generated instruction guards and six actual LE64 reads construct
  the work values used by Lean; the digest predicate and all six ordered
  batch/fold0/fold1/fold2/fold3/final steps are proved.
- **Combined integration theorem:**
  `FormalClosureStream1.current_source_combined_capstone` joins that concrete
  Component-A result, B, C operational/public output, and the Tag-67
  instruction-decoding and verifier theorem.

The combined theorem's only remaining Tag-67 Rust-to-Lean assumption is:

```text
∀ state nonce,
  actualTranscriptGrindingDigest state nonce =
    rustHash state ((3 : Byte) :: List.ofFn (nonceLEBytes nonce))
```

This is the pinned-Aeneas `HashFn` application boundary. No parser,
projection, digest-predicate, or six-step correspondence premise remains.
The audited integration theorems use only
`{propext, Classical.choice, Quot.sound}`.
The external cryptographic and toolchain boundary is collected once in the
[assumptions ledger](../../docs/assumptions-ledger.md).

Principal entry points:

- `aeneas-verif/current-source-abc-capstone-20260722/proof/CurrentSourceABCapstone.lean`
- `aeneas-verif/component-c-runtime-downstream/released-trace-families-current-20260722/proof/RuntimeReleasedTraceFamiliesCurrentJoin.lean`
- `aeneas-verif/tag67-work-wire-correspondence/proof/Tag67WorkVerifierClosure.lean`
- `AspisFormal/AspisFormal/V5ProductionCap17RetryControl.lean`

## Production control flow

The host caller:

- attempts indices 0 through 16;
- draws fresh OS entropy for every attempt and witness component;
- fixes the canonical host hash;
- retries only `AllGoodCandidatesBad`;
- propagates every other error immediately;
- records the successful attempt index; and
- fails closed after 17 unsuccessful attempts.

Fixture RNG, selector overrides, and deterministic fallback are excluded from
the production path.

The production dispatcher exposes Tag 67 and no Tag-66 diagnostic arm. It
requires five ordered accounts, checks ownership/signer/writable flags,
re-derives the canonical nullifier PDA, requires the executable System
Program, rejects account aliasing, verifies before the first write or CPI, and
rejects a reused nullifier.

## Validation record

- `cargo check --workspace --release --locked`: passed.
- Verifier Tag-67 tests: 22 passed.
- Dispatch tests: 3 passed.
- Focused production retry, entropy, PoW, layout, account-size, and
  duplicate-spend tests: passed.
- Component-C and combined Lean 4.32 replays: passed.
- Rust formatting, diff hygiene, JSON validation, provenance checks, and
  targeted credential scan: passed.
- Manifest-default SBF versus production SBF: byte-identical.
- Fresh-clone manifest-default build at public commit `06788d4`: byte-identical.
- Production SBF devnet deployment and atomic Tag-67 execution: finalized at
  slot `478299357`, 1,335,952 CU in both simulation and landed metadata.
- Devnet pool transition 0 → 1, canonical nullifier creation, sealed-proof
  retention, signed-transaction refetch, and same-nullifier replay rejection:
  passed.
- Exact Agave 4.1.0 all-selector replay, including the prefunded marker path:
  passed; the V5 CU ceiling is 1,356,912 CU.

## Deployment handoff

The binary is ready for a fresh deployment with at least 1,258,496 bytes
of ProgramData allocation. An upgrade must first compare that requirement with
the actual on-chain ProgramData allocation. The deployment operator supplies
the RPC URL, program identity, payer, funding, and signing authorization, then
publishes the resulting signature alongside the SBF and provenance hashes.

The same SBF was subsequently deployed through the devnet-only executor as
program
[`EZYH9FF…zQRFS`](https://explorer.solana.com/address/EZYH9FFDGj9gSacmDhvYBqPAzcSm9cfURwuz1CtzQRFS?cluster=devnet).
The atomic Tag-67 transaction
[`38mNKeM…WtEuLC`](https://explorer.solana.com/tx/38mNKeMmRf9Ttqmde8jZqCMq8F1piHhCEqGYVYrSHEggTu21C93wWAEhoDkZ2qJHeTX7j3qCmibNNmZ6awWtEuLC?cluster=devnet)
finalized at slot `478299357` with 1,335,952 CU. The
[original frozen candidate bundle](../aspis-v5-tag67-frozen-candidate-v1/)
contains the sanitized full execution record, proof and statement, and
offline verifier. Its 2.3.13 topology record remains immutable; the
[Agave 4.1.0 addendum](../../results/spend/v5-mainnet-runtime-4.1.0-20260723/)
binds the exact priced transaction shape and prefunded-marker execution. At
this preflight cutoff, no V5 mainnet transaction had been submitted.

The deployment checklist and publication record are in the
[V5 mainnet deployment handoff](../../docs/reviews/v5-mainnet-deployment-handoff.html).

After the mainnet transaction evidence is recorded, temporary rent is recovered in three
separate transactions: close the sealed proof to the dedicated payer, close
ProgramData directly to the operator's locally pinned refund wallet, then sweep
the payer's remaining balance to that wallet. The commands verify the
finalized Tag-67 transaction and the preceding account state before signing.
The refund public key is supplied from outside the repository; the repository
contains no default recipient.

## Evidence layout

`main` retains the final production SBF, provenance, three selector proofs and
measurements, marker-mode controls, statement, and topology CU evidence under
`results/spend/v5-production-tag67-freeze-stream3-20260722/`. Duplicate SBF
paths are relative symlinks to the canonical binary.

Regenerable LLBC, raw/versioned Aeneas output, build logs, intermediate
feature-only SBFs, and the temporary-suffixed devnet build are preserved at
[`research-archive-v5-production-closure-2026-07-22`](https://github.com/DJBarker87/aspis/releases/tag/research-archive-v5-production-closure-2026-07-22).

## Outcome addendum — 2026-07-25

This addendum records the result of executing the frozen candidate. It does
not rewrite the 2026-07-23 preflight above.

The exact 1,258,496-byte SBF identified by SHA-256
`4cf3c1d5ddd47efa68875c0070247e007083c5c9bb2d5988db0d644a609edf40`
was deployed as program
[`7Q2nGsP…CieRmue`](https://explorer.solana.com/address/7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue).
Deployment transaction
[`RHt7eEr…Ndp3RMf`](https://explorer.solana.com/tx/RHt7eErpgLvc7Z2QDWVSj4dmYTg9s4bU62CgWfN5Y1N2BUkAMmQ1V3P8RhtpX9px7aUfAYa8CNSo5Rx5Ndp3RMf)
finalized at slot `434999519`.

The production proof and statement have SHA-256
`330414df587974684643a6062d092db0519d746f0c7efe4ed2108775b685feaf`
and
`0cdc34bc7f835640cff76d1085df9ba966df9f39eb228f3002f927cf30958113`,
respectively. Atomic Tag 67
[`EJviPgF…3vJ2fE`](https://explorer.solana.com/tx/EJviPgF12i9iK2CveVaQSMeFQqDMFPQ1iPRUYEwNQE3zGquTUZNJXPZEENorcQtsnQj1orFmH1TPsgdbR3vJ2fE)
finalized at slot `435019536`. The canonical nullifier PDA bump was exactly
`255`; simulation and landed metadata both reported `1,334,452 CU`, below the
frozen `1,356,912 CU` policy ceiling.

The executor used a hash-chained, crash-resumable per-wire journal. Each
replacement wire received a fresh finalized-expiry gate and exact signed-wire
simulation, while any wire whose send authority had been consumed could only
be polled until finality or expiry. Standard provider-neutral Solana JSON-RPC
over HTTPS and WSS was sufficient; the completed run did not require a paid
RPC tier.

For lifecycle accounting, this V5 proof required 84 transactions: two pool
initialization transactions, one proof-account create, 79 proof uploads, one
proof seal (Tag 62), and one atomic verify-and-apply (Tag 67). Program
deployment and the three cleanup transactions are deliberately outside that
84-transaction lifecycle count. The older 71-transaction figure belongs to
the smaller q18/g37 proof lifecycle and was not a mid-run change to V5.

Temporary rent was then recovered in the prescribed order:

| Operation | Finalized transaction | Slot | Amount | Fee |
| --- | --- | ---: | ---: | ---: |
| Close sealed proof to dedicated payer | [`5FF19Ec…71hZXbW`](https://explorer.solana.com/tx/5FF19EceNFBVbrNzvhxTnbK8bWSysAHVLRjbfggamY3YSeUFzdk54c4GT9GKitBWGkntNG2Zx9xHgbzp371hZXbW) | `435019649` | `525,660,961` lamports | `10,000` lamports |
| Close ProgramData directly to pinned wallet | [`uZ6q5a2…kBdHkWn`](https://explorer.solana.com/tx/uZ6q5a2jGYcscEZgnLghPrqNwp9Hxq3REgYmt6gnb3JuorkUUEQUeJkVWy2e88j9bSLHgRvT2DytjRW2kBdHkWn) | `435019804` | `9,049,204,080` lamports | `10,000` lamports |
| Sweep dedicated payer to pinned wallet | [`4haJ6dP…zbj1JyUW`](https://explorer.solana.com/tx/4haJ6dPmSFkscFKC57QoCUUcf46vU77av9Y8UfcRyCWjfydzHjCeJCsfuthmifXJfVWreZZM8JTDUdBgzbj1JyUW) | `435020068` | `1,931,690,802` lamports | `5,000` lamports |

The protected refund pin was
`Dni6HwfsjJ3sQFTEtKVGL6RgE7zAXnKA7K8MLBBm2RZp`. Its two direct receipt
transactions credited a total of `10,980,894,882` lamports. The payer was
left at zero lamports. The sanitized evidence and offline verification
materials are collected in
[`release/aspis-v5-tag67-mainnet-v1/`](../aspis-v5-tag67-mainnet-v1/).

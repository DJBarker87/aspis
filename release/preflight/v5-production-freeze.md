# Aspis V5 production freeze preflight

Status date: 2026-07-22

Decision: **GO for production-default and mainnet deployment readiness.** The
default `aspis-verifier` feature set is now `spend-production` plus
`v5-production-tag67`, and tag 67 routes only through the atomic
verify-and-apply wrapper. A fresh manifest-default SBF build is byte-identical
to the frozen production artifact whose accepted-input CU ceiling is recorded
below.

No devnet or mainnet transaction was submitted. Deployment or upgrade remains
a separate operator action requiring the actual RPC/program identities,
ProgramData allocation check, funding, and explicit transaction authorization.

## Identity and current accepted measurement artifact

- Canonical program ID: `7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue`.
- Accepted feature-only SBF:
  `results/spend/v5-devnet-feature-build.HOos4d/aspis_verifier_v5_tag67.so`.
- SBF size: `1,074,224` bytes.
- SBF SHA-256:
  `d90ad7d50a84f590625737f8b99ca36c9624ab5709a4e5cbebd07e3f8928ab99`.
- Provenance SHA-256:
  `1607487a67996cd18f7c1dd0b6613001a4ba5b073b4e3f286acc50b11b4e4351`.
- Provenance source HEAD:
  `27e8265d28de88e7967626a2d2432ef161fb4f49`.
- Provenance build policy: `--no-default-features --features v5-cu-probe`,
  Solana `cargo-build-sbf 2.3.0`, platform-tools `v1.48`, Rust `1.84.1`.
- Runtime proof SHA-256:
  `30db5e0b0e3610848e6e134bb109b9646785e6760ca13d0bc57ea500228d4d49`.
- Runtime statement SHA-256:
  `9732df3d67fdc29dc70c7d5293cea1e426c81bafafa775fc95637a203990af2b`.

The accepted measurements bind this exact historical feature-only SBF, not a
future `v5-production-tag67` SBF. Before the Stream-3 rebuild, comparison of
that historical provenance's 77 source identities against the live tree found
five mismatches: `crates/aspis-core/src/transcript.rs`,
`programs/aspis-verifier/Cargo.toml`, `programs/aspis-verifier/src/dispatch.rs`,
`programs/aspis-verifier/src/lib.rs`, and
`programs/aspis-verifier/src/v5_good_gate_probe.rs`.

The fresh Stream-3 feature-only SBF is
`results/spend/v5-production-freeze-stream3-20260722/aspis_verifier_v5_tag67.so`:
1,081,384 bytes, SHA-256
`8dad5ff8cabac2d9ce1f28968010f39bbc14cecad4252de81b3dc89e4b92c418`.
Its provenance JSON has SHA-256
`c004d000a3a3ff17436267e272bb738f2cb6802237d98e0bfe056c5c83bb4fac`,
records HEAD `27e8265d28de88e7967626a2d2432ef161fb4f49`, and its 77 recorded source
identities were checked byte-for-byte against the workspace after the build.
The canonical program ID remains
`7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue`.

The frozen production candidate is
`results/spend/v5-production-tag67-freeze-stream3-20260722/aspis_verifier_v5_production_tag67.so`:
1,258,496 bytes, SHA-256
`4cf3c1d5ddd47efa68875c0070247e007083c5c9bb2d5988db0d644a609edf40`.
It was built exactly once with `--no-default-features --features
v5-production-tag67` in the isolated directory
`/private/tmp/aspis-v5-production-tag67-stream3-20260722/build`. Its fresh
provenance inventory has SHA-256
`a7c9f7bea70d9805d8aff093fad309c911c752f2d47f6ad489c2f2eda1d7c3ec`;
all 77 source and 91 toolchain identities matched after the build, and the
durable SBF is byte-identical to the isolated output. The production-feature
inventory is schema 2 because the existing `v5-devnet-build` wrapper is
hard-coded to `v5-cu-probe`; build output is retained in the coordinator
transcript rather than falsely borrowing the probe build's stdout/stderr
hashes.

After closing the final formal gate and enabling tag 67 in the manifest
default, an isolated plain-default build produced exactly the same 1,258,496
bytes and SHA-256
`4cf3c1d5ddd47efa68875c0070247e007083c5c9bb2d5988db0d644a609edf40`;
`cmp` confirmed byte equality with the frozen artifact. The switch, comments,
and host-only feature-unification guard therefore introduced no deployed-code
delta, so the artifact-bound simulations and universal CU ceiling apply to the
production default without another proof-mining or CU campaign.

## Authoritative measured envelope

All three accepted results exercised a missing System-owned nullifier marker,
observed the real System Program create-account CPI, and repeated identically
three times:

| Selector | Transaction CU | Headroom below 1,400,000 | Production meaning |
| --- | ---: | ---: | --- |
| 0 | 1,333,625 | 66,375 | honest least-Good branch for this fixture |
| 1 | 1,335,039 | 64,961 | test-only regenerated selected-Good branch; worst measured |
| 2 | 1,327,627 | 72,373 | test-only regenerated selected-Good branch |

These are authoritative for the three accepted fixtures and exact SBF only;
those three rows alone are not a universal accepted-input CU bound. The frozen
grammar and conservative maximum-topology bound below close that gate.

The production-feature SBF replayed every available cached selector proof
without proof regeneration. Missing-marker CU was 1,331,232, 1,333,896, and
1,326,480 for selectors 0, 1, and 2 respectively; each repeated identically
3/3 and completed the real System Program create-account CPI 3/3. The
selector-0 present program-owned zero-marker control was 1,328,897 CU in 3/3
identical repeats, with no System Program CPI. Selector 1 is the worst directly
measured production-artifact fixture at 1,333,896 CU (66,104 headroom).

The frozen parser/account policy is: proof body at most 77,278 bytes, sealed
proof account at most 77,318 bytes (40-byte header), pool exactly 80 bytes,
nullifier marker exactly 72 bytes, and instruction exactly 169 bytes. Across
the five canonical opening sections the grammar permits at most 1,366 frontier
nodes. Normalizing each production-artifact selector baseline to the 487-parent
maximum with the proven 512-CU-per-additional-parent allowance and adding the
4,096-CU accepted Good-gate control-flow allowance yields selector ceilings of
1,350,688, 1,348,232, and 1,353,616 CU. The universal frozen-grammar ceiling is
therefore **1,353,616 CU with 46,384 CU headroom**, governed by selector 2.
The bound and derivation are artifact-bound in
`v5_universal_accepted_topology_cu_policy.json` (SHA-256
`0da8ebbaee5b26bf82814bbc1cd7ebdfc1d542a8207bea30fb882ffb51c904cf`).

## Dispatch and atomicity

With the default `v5-production-tag67` feature, the minimal production
dispatcher routes tag 67 directly into
`process_v5_full_cu_transaction_with_verifier`, which parses the
exact 169-byte public wire and invokes the existing atomic
`verify_and_apply_atomic_payment_state` wrapper. The production entrypoint has
no tag-66 arm and does not call the probe entrypoint.

The wrapper enforces exactly five accounts in this order:

1. read-only, program-owned sealed proof account;
2. writable, program-owned, exactly 80-byte pool state;
3. writable canonical nullifier PDA, either an exactly 72-byte program-owned
   zero marker or an empty System-owned account to create;
4. writable System-owned payer signer; and
5. the exact executable System Program.

Proof, pool, nullifier, and payer keys must be distinct. The live pool fixes
the sequence, anchor, deployment domain, and statement digest supplied to the
verifier. Verification completes before the first CPI or state write. A
missing marker is created at the canonical PDA; an existing matching marker
fails with `ATOMIC_ERROR_NULLIFIER_ALREADY_SPENT`; malformed or foreign marker
state fails closed. Writable locking serializes the pool and marker mutation.

## Default-enable closure record

The default gate is closed and enabled. Every switch condition is green:

- Component-B deterministic sampler/evaluator/layout correspondence: **green
  under the accepted Stream-1 status**. Stream 3 does not rerun or independently
  upgrade that formal result.
- Component-C sampler/encoder, arithmetic/fold, packer, and public-output
  correspondence: **green**. The final public theorem is
  `generated_public_run_output_matches_deployed` in
  `aeneas-verif/component-c-runtime-downstream/released-trace-families-current-20260722/proof/RuntimeReleasedTraceFamiliesCurrentJoin.lean`.
  It packages the extracted public evaluator, all four actual runtime rounds,
  finish, and packer, and concludes exact output length and row equality with
  maintained `deployedEvaluate`. The clean Lean 4.32 replay is
  `released-trace-families-current-20260722/replay-lean432.sh`.
- Stream-2 tag-67 transcript/work-wire correspondence: **green with one named,
  accepted transparent tool boundary**. The exact dependency is theorem
  `AspisTag67WorkVerifierClosure.exactGrindingHashInput` in
  `aeneas-verif/tag67-work-wire-correspondence/proof/Tag67WorkVerifierClosure.lean`:

  ```text
  ∀ state nonce,
    actualTranscriptGrindingDigest state nonce =
      rustHash state (grindingHashPayload nonce)
  ```

  Here `grindingHashPayload nonce` is exactly
  `(3 : Byte) :: nonceLEBytes nonce` (`DOM_GRIND || nonce_le64`). The same
  equation is the sole correspondence premise of
  `exactRustWorkVerifierCorrespondence_of_hash_application` and the final
  `tag67AcceptedWireAndVerifierClosure`. This is the accepted pinned-Aeneas
  `HashFn`/Arrow-FFI application boundary; `HashFn` remains arbitrary and no
  SHA or random-oracle faithfulness is inferred. The production-default tag-67
  path relies on this explicitly named equation. Evidence is retained in
  `aeneas-verif/tag67-work-wire-correspondence/` and
  `aeneas-verif/v5-transcript-absorb-input/`.
- Stream 1's combined final formal capstone: **green**. The theorem
  `FormalClosureStream1.current_source_combined_capstone` in
  `aeneas-verif/current-source-abc-capstone-20260722/proof/CurrentSourceABCapstone.lean`
  concludes maintained Component A, maintained Component B, actual-current
  Component-C operational fold closure, Component-C public-output closure, and
  Tag-67 wire/verifier closure. Its only Tag-67 implementation/model premise
  is the exact `HashFn` application equation stated above. The clean combined
  Lean 4.32 replay passes under default limits; all audited capstones use only
  `{propext, Classical.choice, Quot.sound}` and the forbidden-premise scan is
  green.

The CU condition is green for the frozen grammar at 1,353,616 CU. Program size
is 1,258,496 bytes, so fresh local deployment readiness requires
`--max-len 1258496` or a larger explicit chosen allocation; `--max-len 1300000`
would retain 41,504 bytes of allocation headroom. A 1,200,000-byte allocation
is insufficient by 58,496 bytes. No authorized/read-only RPC program identity
was supplied, so this preflight does not claim any existing on-chain
ProgramData allocation is sufficient. An upgrade must separately verify the
actual ProgramData allocation; a fresh local deployment is exactly
allocation-ready.

Those conditions are now recorded and `programs/aspis-verifier/Cargo.toml`
sets `default = ["spend-production", "v5-production-tag67"]`. Mainnet
submission remains a separate explicit authorization.

## Frozen inventory

### Production source

- Workspace manifests and lockfile: `Cargo.toml`, `Cargo.lock`.
- Verifier manifest/entrypoint/dispatch:
  `programs/aspis-verifier/Cargo.toml`,
  `programs/aspis-verifier/src/lib.rs`,
  `programs/aspis-verifier/src/dispatch.rs`.
- Atomic state and proof lifecycle:
  `programs/aspis-verifier/src/atomic_payment.rs`,
  `programs/aspis-verifier/src/lifecycle.rs`.
- V5 strict verifier and transaction wrapper:
  `programs/aspis-verifier/src/v5_full_transaction.rs`,
  `programs/aspis-verifier/src/v5_cu_probe.rs`,
  `programs/aspis-verifier/src/v5_atomic_terminal.rs`,
  `programs/aspis-verifier/src/v5_fri_checks.rs`,
  `programs/aspis-verifier/src/v5_private_openings.rs`,
  `programs/aspis-verifier/src/v5_relation_stress.rs`,
  `programs/aspis-verifier/src/v5_relation_stress_fast.rs`,
  `programs/aspis-verifier/src/v5_relation_stress_root.rs`,
  `programs/aspis-verifier/src/v5_good_gate_probe.rs`, and
  `programs/aspis-verifier/src/v5_wire_skeleton.rs`.
- Host production caller and masks:
  `crates/aspis-prover/src/v5_real_host_proof.rs`,
  `crates/aspis-prover/src/v5_mask.rs`, and their manifest/module wiring.
- Shared runtime dependencies: every `aspis-core` and `aspis-statement` source
  identity emitted by the fresh SBF provenance.
- Explicit tooling:
  `xtask/src/spend_devnet.rs`, `xtask/src/spend_devnet/v5.rs`,
  `xtask/src/v5_cu_probe.rs`, `xtask/src/main.rs`, and the xtask manifest.

### Formal proof artifacts

Keep formal source separate from generated runtime evidence. It includes the
Stream-1 Component A/B/C closure selected by its final gate, plus
`AspisFormal/AspisFormal/V5ProductionCap17RetryControl.lean`,
`AspisFormal/AspisFormal/V5NonceWorkAuthentication.lean`, and the named
Component-B/Component-C correspondence modules. Stream-2 evidence includes
`aeneas-verif/tag67-work-wire-correspondence/REPORT.md`,
`aeneas-verif/tag67-work-wire-correspondence/proof/Tag67WorkVerifierClosure.lean`,
its axiom audit, and the companion
`aeneas-verif/v5-transcript-absorb-input/` report/proofs. The retained theorem
dependency is the exact `exactGrindingHashInput` equation named above. The
release also retains the final Component-C public-output bundle and the
current-source A/B/C/Tag-67 combined capstone named in the closure record.

### Reproducible generated evidence

- The final production-feature SBF and schema-2 provenance inventory under
  `results/spend/v5-production-tag67-freeze-stream3-20260722/`. The direct
  build was necessary because `v5-devnet-build` is pinned to `v5-cu-probe`;
  the inventory honestly leaves separate stdout/stderr hashes null and binds
  the exact command, SBF, 77 source identities, and 91 toolchain identities.
- The isolated manifest-default build after switch enablement is byte-identical
  to that final SBF. The release source commit plus this exact equality records
  the non-emitting default/guard changes without pretending that the earlier
  schema-2 JSON was generated after those changes.
- The runtime proof and strict statement sidecar produced by
  `v5-devnet-artifact`.
- Missing-marker local simulation JSON for selectors 0/1/2, the selector-0
  present-marker control, and the artifact-bound universal CU policy JSON.
- The final source/provenance identity comparison, artifact SHA-256, program
  ID, account-size bound, CU envelope, and targeted test logs.
- The current accepted historical inputs under
  `results/spend/v5-devnet-feature-build.HOos4d/` remain evidence for their own
  pinned SBF hash only.

### Exclude from the release bundle

- `target/`, isolated Cargo/SBF build directories, local-validator ledgers,
  temporary keypairs, RPC caches, logs, and OS temporary directories.
- `aspis-pow-metal` and other local mining/build helpers unless separately
  source-reviewed and intentionally shipped as tools.
- Tag-66 diagnostics, selector-override fixtures, obsolete CU controls, and
  exploratory `results/spend` JSON/binaries not named by the final evidence
  index.
- Devnet execution journals/signatures and any mainnet material from an older
  release. Never reuse old keypairs as frozen source or evidence.

## Exact final commands

All paths must be absolute and lexically normal. Create the isolated empty
build directory outside the workspace/toolchain protected trees. Put the new,
empty durable freeze and simulation-evidence directories under
`results/spend/<freeze-dir>/` so the final evidence is inventory-able. Do not
delete or reuse an old directory.

The frozen production-feature SBF build was:

```sh
NO_DNA=1 \
CARGO_TARGET_DIR=/private/tmp/aspis-v5-production-tag67-stream3-20260722/build/cargo-target \
/Users/dominic/.local/share/solana/install/active_release/bin/cargo-build-sbf \
  --manifest-path /Users/dominic/ZK/programs/aspis-verifier/Cargo.toml \
  --no-default-features --features v5-production-tag67 --arch v0 --offline \
  --skip-tools-install --tools-version v1.48 \
  --sbf-sdk /Users/dominic/.local/share/solana/install/active_release/bin/platform-tools-sdk/sbf \
  --sbf-out-dir /private/tmp/aspis-v5-production-tag67-stream3-20260722/build \
  -- --locked
```

After formal closure and switch application, the release coordinator ran one
isolated manifest-default parity build (no feature override):

```sh
NO_DNA=1 \
CARGO_TARGET_DIR=/private/tmp/aspis-v5-default-final.VjZMOa/cargo-target \
/Users/dominic/.local/share/solana/install/active_release/bin/cargo-build-sbf \
  --manifest-path /Users/dominic/ZK/programs/aspis-verifier/Cargo.toml \
  --arch v0 --offline --skip-tools-install --tools-version v1.48 \
  --sbf-sdk /Users/dominic/.local/share/solana/install/active_release/bin/platform-tools-sdk/sbf \
  --sbf-out-dir /private/tmp/aspis-v5-default-final.VjZMOa \
  -- --locked
```

The output was byte-identical to the frozen production artifact. This parity
build did not submit a transaction and did not replace the durable measured
artifact.

Generate a runtime-bound proof/statement (local filesystem only):

```sh
cargo run -p aspis-xtask --bin aspis-xtask --locked -- v5-devnet-artifact \
  --network devnet \
  --program-id 7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue \
  --pool <DEVNET_POOL_PUBKEY> \
  --sequence 0 \
  --proof-out <ABS_FREEZE_DIR>/v5_runtime_proof.bin \
  --statement-out <ABS_FREEZE_DIR>/v5_runtime_statement.json
```

Local transaction simulation reusing that one SBF, including real missing
marker System Program CPI and three repeats of selectors 0/1/2:

```sh
NO_DNA=1 \
V5_CU_PREBUILT_SBF=<ABS_FREEZE_DIR>/aspis_verifier_v5_tag67.so \
V5_CU_PREBUILT_SBF_SHA256=<FRESH_SBF_SHA256> \
V5_CU_RESULTS_DIR=<ABS_NEW_EMPTY_RESULTS_DIR> \
cargo test -p aspis-xtask --locked --release \
  v5_full_transaction_all_selected_good_branches_cu_measurement \
  -- --ignored --nocapture
```

Fast replay of an already frozen proof in both marker modes (no proof mining or
SBF build):

```sh
V5_CU_FROZEN_DIR=<ABS_FREEZE_DIR> \
V5_CU_FROZEN_MARKER_MODE=missing \
V5_CU_PREBUILT_SBF_SHA256=<FRESH_SBF_SHA256> \
cargo test -p aspis-xtask --bin aspis-xtask --locked --release \
  v5_frozen_artifact_marker_mode_cu_measurement -- --ignored --nocapture

V5_CU_FROZEN_DIR=<ABS_FREEZE_DIR> \
V5_CU_FROZEN_MARKER_MODE=present \
V5_CU_PREBUILT_SBF_SHA256=<FRESH_SBF_SHA256> \
cargo test -p aspis-xtask --bin aspis-xtask --locked --release \
  v5_frozen_artifact_marker_mode_cu_measurement -- --ignored --nocapture
```

Read-only devnet preflight (no transaction, no mutation):

```sh
cargo run -p aspis-xtask --bin aspis-xtask --locked -- v5-devnet-readiness \
  --rpc-url https://api.devnet.solana.com \
  --payer-keypair <ABS_PAYER_KEYPAIR> \
  --program-keypair <ABS_PROGRAM_KEYPAIR> \
  --pool-keypair <ABS_POOL_KEYPAIR> \
  --proof-account-keypair <ABS_PROOF_ACCOUNT_KEYPAIR> \
  --sbf <ABS_FREEZE_DIR>/aspis_verifier_v5_tag67.so \
  --sbf-provenance <ABS_FREEZE_DIR>/aspis_verifier_v5_tag67.provenance.json \
  --proof <ABS_FREEZE_DIR>/v5_runtime_proof.bin \
  --statement <ABS_FREEZE_DIR>/v5_runtime_statement.json \
  --program-max-len <EXACT_PROGRAM_MAX_LEN> \
  --fee-reserve-lamports <EXACT_FEE_RESERVE_LAMPORTS>
```

Do not run `v5-devnet-execute` without separate explicit authorization. No
mainnet transaction command belongs in this preflight.

## Coordinator finalization record

This section records finalization after the shared source tree stabilized.
Actual command outputs remain generated evidence rather than being replaced by
this summary.

- Frozen source identity/commit: the release commit containing this record.
  The original production-feature SBF was made from the dirty shared tree
  based on `27e8265d28de88e7967626a2d2432ef161fb4f49`; its exact inputs remain the
  77 hashes in the fresh provenance. The final manifest-default parity build
  ran against the release source tree and emitted identical bytes.
- Fresh SBF path:
  `results/spend/v5-production-tag67-freeze-stream3-20260722/aspis_verifier_v5_production_tag67.so`.
- Fresh SBF bytes and SHA-256: `1,258,496` and
  `4cf3c1d5ddd47efa68875c0070247e007083c5c9bb2d5988db0d644a609edf40`.
- Fresh provenance path and SHA-256:
  `results/spend/v5-production-tag67-freeze-stream3-20260722/aspis_verifier_v5_production_tag67.provenance.json`,
  `a7c9f7bea70d9805d8aff093fad309c911c752f2d47f6ad489c2f2eda1d7c3ec`.
- Provenance identities equal the production-feature frozen source/toolchain:
  **green, 77/77 source and 91/91 toolchain**. Separate build stdout/stderr
  hashes are null and explicitly disclosed because the direct build output
  lives in the coordinator transcript. The later default-build byte equality
  is separately and explicitly recorded; the older JSON is not relabelled as
  post-switch provenance.
- Release workspace check command/outcome: `cargo check --workspace --release
  --locked`: **green** (warnings only).
- Relevant verifier/prover test commands/outcomes: bounded retry 4/4; production
  entropy/PoW 3 focused tests; verifier tag-67 22 tests; candidate/default
  dispatch, duplicate-spend ordering, and xtask wire/layout focused tests:
  **green**. One overbroad prover filter was interrupted after entering an
  unrelated expensive integration test; its relevant five unit tests had
  already passed and the three intended tests were rerun by exact name.
- Fresh SBF build command/outcome: direct exact `cargo-build-sbf` with
  `--no-default-features --features v5-production-tag67` and isolated
  `/private/tmp/aspis-v5-production-tag67-stream3-20260722/build`: **green;
  exactly one production-feature SBF build**. The subsequent required
  manifest-default parity build was **green and byte-identical**.
- Local transaction simulations: cached selectors 0/1/2, missing marker and
  real create-account CPI, three repeats each; selector 0 also present-marker
  control, three repeats: **green**.
- Missing-marker CU selectors 0/1/2: 1,331,232 / 1,333,896 / 1,326,480.
  Present-marker selector 0: 1,328,897. Universal frozen-grammar bound:
  **1,353,616 CU / 46,384 headroom**, policy SHA-256
  `0da8ebbaee5b26bf82814bbc1cd7ebdfc1d542a8207bea30fb882ffb51c904cf`.
- Local deploy allocation: exact minimum `program_max_len = 1,258,496`; an
  existing on-chain allocation is **not claimed** because no RPC identity was
  supplied.
- Frozen maximum proof/account bytes: 77,278 / 77,318; pool 80; marker 72;
  instruction 169.
- Stream-1 final formal gate references:
  `generated_public_run_output_matches_deployed`,
  `FormalClosureStream1.PublicOutput.component_c_actual_public_output_closure`,
  and `FormalClosureStream1.current_source_combined_capstone`: **green under
  Lean 4.32 default limits, with only the accepted three axioms**.
- Stream-2 correspondence evidence references:
  `aeneas-verif/tag67-work-wire-correspondence/REPORT.md` and
  `proof/Tag67WorkVerifierClosure.lean`, specifically
  `AspisTag67WorkVerifierClosure.exactGrindingHashInput`; companion root-absorb
  evidence under `aeneas-verif/v5-transcript-absorb-input/`: **green subject
  only to the accepted HashFn/Arrow-FFI application equation stated above**.
- Final decision: **GO for production-default and mainnet deployment
  readiness**. The frozen/default SBF requires an allocation of at least
  1,258,496 bytes; 1,300,000 bytes leaves 41,504 bytes. An actual deployment or
  upgrade is not claimed and awaits operator-supplied identities, allocation
  verification, funding, and explicit transaction authorization.

## Final integration record

The previously prepared one-line switch is applied in the verifier manifest;
the standalone patch is no longer an unapplied release input. The shared-tree
implementation, formal closure, frozen evidence, and default enablement are
integrated as one curated V5 release change so their exact cross-component
dependency is preserved. No staging, commit, or push action itself authorizes
an on-chain transaction.

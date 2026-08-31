# Registry V2 production ceremony and rollback runbook

Status: **disabled**. The manifest decision is `NO_GO`; none of the write
commands below is authorized for these audit-identity binaries.

This is a command-exact operator sequence for a future candidate rebuilt
against selected production identities. Angle-bracket values and every
`UNSELECTED` manifest field are hard stops, not defaults.

## 1. Roles and custody

Use separate principals for:

- offline/air-gapped Pool, verifier and Registry program identities;
- a hardware-backed deploy/upgrade authority used only during staging;
- a low-balance fee payer;
- an independently controlled threshold Registry governance multisig;
- read-only RPC/monitoring operators; and
- the two human approvers for every irreversible authority/freeze step.

No keypair, seed phrase, spending/viewing key, RPC secret or alert token may be
written to the repository, CI output, release archive or shell history. Record
only public keys and device/key fingerprints in the signed ceremony record.

## 2. Required production selections

Freeze these values before rebuilding:

1. Pool, verifier and Registry program IDs and custody/recovery fingerprints;
2. Registry governance multisig, policy binding and minimum activation delay;
3. deployment domain, asset mint/asset ID, Pool/vault identity and canary caps;
4. primary/fallback RPC and WebSocket providers in independent regions/vendors;
5. final profile/release/statement versions and every compiled program ID;
6. immutable deployment/no-rollback approval and incident owner.

Replace the three `*_AUDIT_V1` constants in
`programs/aspis-verifier/src/v7_pair_forest_dispatch.rs`, replace the verifier
`declare_id!` if necessary, and remove fixture identities from the release
generator. Rebuild every item listed in
`manifest.json.productionIdentitySelectionsRequired.evidenceThatMustBeRegenerated`.

## 3. Read-only cluster gate

Set endpoints in a private operator environment:

```sh
export RPC_PRIMARY='<independent-mainnet-rpc>'
export WS_PRIMARY='<matching-primary-websocket>'
export RPC_FALLBACK='<independent-fallback-mainnet-rpc>'
export WS_FALLBACK='<matching-fallback-websocket>'
export TXV1_SOLANA='<official-provenance-verified-agave-4.2+-solana>'
```

Both providers must report mainnet genesis
`5eykt4UsFv8P8NJdTREpY1vzqKqZKvdpKuc147dw2N9d`, agree at finalized
commitment, and report the TxV1 feature active:

```sh
scripts/v7_txv1_4k_feature_gate.sh "$TXV1_SOLANA" "$RPC_PRIMARY"  '<fresh-primary-evidence-dir>'
scripts/v7_txv1_4k_feature_gate.sh "$TXV1_SOLANA" "$RPC_FALLBACK" '<fresh-fallback-evidence-dir>'
```

Any absent feature account, provider disagreement, unhealthy RPC, wrong
genesis hash or less-than-finalized response aborts the ceremony.

## 4. Staged deployment and byte comparison

Do not deploy this bundle's binaries. For a newly rebuilt and approved
candidate, repeat the following separately for Pool, verifier and Registry.
The initial deploy remains upgradeable only long enough to permit byte
comparison and a pre-final rollback.

```sh
export RPC="$RPC_PRIMARY"
export PROGRAM_KEYPAIR='<offline-or-hardware-program-identity>'
export PROGRAM_ID='<public-program-id>'
export DEPLOY_AUTHORITY='<hardware-deploy-authority>'
export FEE_PAYER='<low-balance-fee-payer>'
export SBF='<absolute-path-to-frozen-sbf>'
export DUMP='<new-task-owned-dump-path>'
export SBF_BYTES="$(wc -c < "$SBF" | tr -d ' ')"

solana program deploy \
  --url "$RPC" \
  --program-id "$PROGRAM_KEYPAIR" \
  --upgrade-authority "$DEPLOY_AUTHORITY" \
  --fee-payer "$FEE_PAYER" \
  --max-len "$SBF_BYTES" \
  --commitment finalized \
  --output json \
  "$SBF"

solana program show \
  --url "$RPC" --commitment finalized --output json "$PROGRAM_ID"

solana program dump \
  --url "$RPC" --commitment finalized "$PROGRAM_ID" "$DUMP"

cmp -s "$SBF" "$DUMP"
shasum -a 256 "$SBF" "$DUMP"
```

Run `program show` and `program dump` through the fallback RPC as well. The
program ID, ProgramData address, byte length, SHA-256 and authority must match
the signed candidate manifest exactly. `--skip-feature-verify` and
`--skip-preflight` are prohibited.

Before immutability, the only binary rollback is an explicit redeploy of the
last separately audited artifact:

```sh
solana program deploy \
  --url "$RPC" \
  --program-id "$PROGRAM_ID" \
  --upgrade-authority "$DEPLOY_AUTHORITY" \
  --fee-payer "$FEE_PAYER" \
  --max-len '<frozen-programdata-max-len>' \
  --commitment finalized \
  --output json \
  '<absolute-path-to-previous-audited-sbf>'
```

That rollback invalidates the candidate evidence and requires a fresh dump,
hash, lifecycle and release decision.

## 5. Irreversible immutability gate

Registry V2 initialization requires the Registry ProgramData authority to be
`None`; scheduling requires the verifier ProgramData authority to be `None`.
The Pool must also be immutable before accepting custody. After two-person
out-of-band comparison of IDs, hashes, ProgramData addresses and recovery
records, execute once per program:

```sh
solana program set-upgrade-authority \
  --url "$RPC" \
  --commitment finalized \
  --upgrade-authority "$DEPLOY_AUTHORITY" \
  --final \
  "$PROGRAM_ID"

solana program show \
  --url "$RPC" --commitment finalized --output json "$PROGRAM_ID"
```

There is no post-final program rollback command. A mismatch after `--final`
requires a new program identity and a new release.

## 6. Registry V2 governance

Do not hand-encode registry instructions. Build them through the exact
functions in
`crates/aspis-pool-wallet-v1/src/registry_transaction_builder.rs`:

- `build_initialize_registry_instruction_v2`;
- `build_schedule_registry_profile_instruction_v2`;
- `build_activate_registry_entry_instruction_v2`; and
- `build_freeze_registry_instruction_v2`.

This revision exposes those as an unsigned library but does not contain the
reviewed offline/multisig ceremony executable needed for mainnet. That missing
tool is a P0 blocker. It must display and independently re-decode every account
meta and instruction byte, emit a sign-only transaction/message digest, collect
multisig approval, simulate the identical signed bytes, submit them, and retain
finalized receipts.

The required order is:

1. initialize V2 against the immutable Registry ProgramData and exact Registry
   executable-payload SHA-256;
2. schedule the exact immutable verifier ProgramData, SBF hash, profile,
   release, statement version, policy and nonzero activation delay;
3. wait through the on-chain activation delay;
4. activate and prove Pool/verifier selection on public devnet, then mainnet
   canary only after separate authorization;
5. freeze the Registry only after every value and alert path is verified.

Registry freeze zeros governance authority. After it, pause, unpause, retire
and release rotation are impossible. There is no Registry rollback or rescue
path for an immutable funded Pool.

## 7. Canary and monitoring

Before real custody, both RPCs must agree on program bytes/authorities,
Registry generation/status, active entry, Pool/vault state and finalized slot.
Start with a separately approved low-value canary limit. Stop all submission on
any alert in `manifest.json.rpcAndMonitoring.requiredAlerts`.

Operational rollback is deliberately limited: stop wallets/relayers, preserve
all evidence, publish an incident notice and prevent new deposits. It cannot
change immutable program code, undo a nullifier, or recover funds from a faulty
immutable transition. This residual risk requires explicit human acceptance.

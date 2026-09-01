# V7 live Pool witness adapter — 2026-09-01

## Classification

**C — ADAPTER COMPLETE; TERMINAL EXECUTION BLOCKED**

The production-shaped transfer and withdrawal adapters are complete and pass
focused offline tests. They consume canonical finalized Pool/Registry account
images plus the wallet's authenticated retained checkpoint, construct the
exact Tag-73 witness, ASQ8 request, ASF8 semantic statement, expected ASR8,
and hand those values to the production prover with fresh attempt entropy.

No live terminal transaction was simulated or landed in this work. The local
host has Agave 2.3.0 rather than the required 4.2+, and the NUC was not
reachable from this session. Accordingly there are no transaction-byte, CU,
signature, finalized-slot, or pre/post-account-hash measurements. Existing
public-devnet evidence was not changed, and no synthetic result is reported as
a live lifecycle.

Base: `97e50660d61bfc07fb22bb0a6cc8a268fe073352`  
Tested implementation: `5e5dc29fbc1c3ec5ceaa739dae72af8b0407208c`  
Branch: `research/v7-live-pool-witness-adapter-20260901`

## Architecture and authenticated field sources

`LaneForestDurableStateV2::authenticated_spend_membership_v2` exports one
tracked output at one retained checkpoint. It finds the canonical finalized
append event, binds the output event to its pair witness, reconstructs the
occupied/empty pair representation, verifies the pair path against the saved
lane root, and verifies all eight saved lane roots against the checkpoint's
global root. The exported value includes the checkpoint point, address and
sequence so a current-path or different-checkpoint substitution is rejected.

`authenticate_live_pair_forest_snapshot_v2` independently authenticates:

- the ASM8 master owner, non-executable status, PDA, version, eight-lane mask,
  identity and verifier policy;
- all eight current ASL8 lane owners, PDAs, lane order, roots, indices and
  frontiers;
- the ASC8 checkpoint owner, PDA, master/deployment identity, sequence,
  global root and per-lane sequences;
- the finalized Registry selection, exact legacy/V2 family, Registry/entry
  PDAs, Tag-73 profile and release bindings, verifier program, provider-set
  digest and finalized point.

The transfer/withdrawal constructors join that live snapshot with the durable
membership export and a task-owned note opening. They recompute and compare
the note commitment, owner key and nullifier, derive the output lane using the
frozen production rule, use the current selected lane as the append
before-state, and run the canonical pair-forest trace compiler for the exact
candidate afterstate. ASQ8, ASF8 and expected ASR8 are encoded, decoded back,
and checked with the exact statement/result binding validator.

The withdrawal path additionally authenticates the legacy SPL mint, vault
PDA, vault authority, destination token account, mint agreement, balances,
amount and value conservation before proving.

The pair leaf is constructed with `PoolV1PairLeafWitnessV1::single_output` or
`two_outputs`, and the selected slot is checked with
`require_selected_spendable`. Thus occupied slots remain algebraic witnesses;
emptiness is not inferred from the absence of a hash preimage.

`tools/v7-live-pool-proof` is a separate production-prover handoff crate. It
does not enable `insecure-spend-fixture`. The proof-account public key is used
as the exact public attempt nonce via `generate_for_mask_nonce`; the two
private seeds come from OS entropy and the nonce is burned through
`DurableStateOnlyMaskNonceStore` before the genuine Tag-73 transfer or
withdrawal prover entry point runs. No ASR8 can be supplied by the caller.

## Fixture constants eliminated

The live path contains none of the earlier synthetic checkpoint sequence,
deployment domain, selected-lane population, deterministic witness roots,
deterministic nullifier, deterministic fixture entropy, fixed Pool account,
or fixed candidate afterstate. The only fixed values are protocol constants:
the Tag-73 profile/release bindings, account/wire versions, lane count, tree
depth, canonical empty roots, and legacy SPL Token program identity.

## Focused validation

Commands and resource measurements are recorded in
`results/v7-live-pool-witness-adapter-20260901/evidence.json`. Results:

- focused wallet compile: pass, peak RSS 671,367,168 bytes;
- retained-checkpoint membership export: 1 passed, peak RSS 853,573,632 bytes;
- live transfer/withdrawal adapter tests: 2 passed, peak RSS 809,664,512 bytes;
- live production-prover handoff and bundle command compile: pass, peak RSS
  160,514,048 bytes;
- exact finalized Registry selection test: 1 passed, peak RSS 100,499,456
  bytes.

The adapter tests create an independent eight-lane account set, append a
fresh single-output deposit pair, construct a checkpoint from the resulting
eight roots, authenticate the encoded account images, then build both exact
terminal plans. Negative assertions reject a different checkpoint sequence,
a mutated historical lane root, selection of the algebraically empty second
slot, and an underfunded withdrawal vault. Existing canonical codecs and
Registry selection tests cover malformed wire and Registry account inputs.

Canonical adapter outputs are 320-byte ASQ8, 1,880-byte ASF8 and 792-byte
expected ASR8. These are protocol wires, not transaction-size measurements.
The frozen 997-byte / 1,201,757-CU baseline was neither rerun nor attributed to
this adapter run.

## Replay and secret handling

The bundle command is:

```sh
NO_DNA=1 CARGO_BUILD_JOBS=2 cargo run --release --locked \
  --manifest-path tools/v7-live-pool-proof/Cargo.toml \
  --bin prove-from-live-bundle -- \
  /absolute/task-owned/live-bundle.json \
  /absolute/new-proof-output \
  /absolute/new-nonce-ledger
```

The bundle contains finalized account images and points. A separately named
task-owned secret JSON contains the input/output note openings and nullifier
key. The command never prints these values, refuses to overwrite proof output
or reuse a nonce-ledger directory, and records only public identities and
hashes. The secret file must remain mode 0600 outside the repository and be
destroyed after evidence is frozen.

Exact focused commands are also in
`results/v7-live-pool-witness-adapter-20260901/replay-commands.txt`.

## Lifecycle matrix and blocker

No requested live cluster case is marked executed. Init, deposit, checkpoint,
genuine live-note proof generation, transfer, withdrawal, stale-lane, replay,
wrong-checkpoint/release, malformed-ASQ8/ciphertext, and failed-CPI rollback
remain `not-run` in the evidence JSON.

The smallest remaining step is operational and concrete: on a reachable
Agave 4.2+ host, run the existing disposable feature-cluster wrapper; submit
init, deposit and checkpoint with the existing canonical builders; persist
the finalized scanner/durable-wallet state and finalized Pool/Registry account
bundle; invoke `prove-from-live-bundle`; upload that proof; then use the
existing TxV1 builder's byte-identical simulate/send/finalize path. This does
not require verifier mathematics, cryptographic parameters, production Pool
source, or frozen SBF/CU changes.

The result is safe to cherry-pick as host-only, default-off research plumbing.
It does not establish public devnet lifecycle completion, production
identities, or mainnet readiness. `mainnetReady` remains false.

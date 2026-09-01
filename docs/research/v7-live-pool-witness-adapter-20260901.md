# V7 live Pool witness adapter — 2026-09-01

## Classification

**B — LIVE TRANSFER COMPLETE; WITHDRAWAL BLOCKED**

The production-shaped transfer and withdrawal adapters pass focused offline
tests. On a disposable Agave 4.2.0 cluster with TxV1 active at genesis, the
live path then initialized a fresh eight-lane Pool, deposited a fresh note,
finalized checkpoint 0, reconstructed its membership from those accounts,
generated and sealed a genuine Tag-73 proof, simulated the exact signed TxV1
wire, submitted the same bytes, and finalized the same-page transfer.

The live withdrawal runner and remaining negative matrix are not complete, so
this is not a complete lifecycle claim. Public devnet was not used or changed;
all identities and funds were explicitly disposable and audit-only.

Base: `97e50660d61bfc07fb22bb0a6cc8a268fe073352`  
Tested implementation: `14389d767d375db88b97a1aae2ff323145fdbaf0`
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
The frozen one-transaction verifier consumes the repository's existing
canonical-fixed audit wire, so the adapter transcodes only the 641 packed
fixed QM31 values after proving. This adds exactly 320 bytes; roots, work
nonces, queries, private salts and Merkle frontiers remain byte-identical. The
accepted live proof was 30,720 bytes and its ASJA payload was 31,408 bytes.

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
expected ASR8. The genuine signed terminal TxV1 was 1,378 serialized bytes and
used 1,199,794 CU in both exact-wire simulation and finalized execution. The
frozen 997-byte / 1,201,757-CU reference remains a separate prior measurement;
it is not relabelled as this live run.

## Finalized disposable-cluster evidence

Agave reported `solana-cli 4.2.0`, runtime feature set `565236538`, and TxV1
feature `txv1aq4pp281K9um3tnPgkfX8UqtFT6wcVW3hNezGLL` active at slot 0. The
fresh ledger genesis hash was
`GcgcXEk2fnmGb3zBbALLy41dyyeNexXLwQ68eagpt8fc`.

| Operation | Bytes | Simulated CU | Landed CU | Finalized slot |
| --- | ---: | ---: | ---: | ---: |
| Pool initialize | 784 | 131,942 | 131,942 | 151 |
| Deposit | 651 | 1,112,379 | 1,112,379 | 183 |
| Checkpoint | 581 | 703,262 | 703,262 | 215 |
| Terminal transfer | 1,378 | 1,199,794 | 1,199,794 | 563 |

The terminal signature is
`36xzE8aH8EwQ5vn8Y7H6gCnRqfNKJTWH6DxesKz2gH5swp66tLuq6xsSwUQgevgNGmYTZiuCKJAxMVPvZTrkZtgr`;
its signed-wire SHA-256 is
`6a6e30d8449b8f3ee65840adae3ad250a65e32288c9f32cc27e8dd376ec4d338`.
It contained SPL Noop ciphertext carrier followed by exactly one terminal
ASQ8. The selected verifier returned exact ASR8 and consumed 1,132,448 CU.

Before/after hashes prove that selected lane 5 and its live history page
changed, the nullifier marker was absent then created, and master, checkpoint,
vault, proof account and all seven non-selected lanes were unchanged. Exact
per-account hashes and all RPC responses are in
`results/v7-live-pool-witness-adapter-20260901/local-feature-active-live-transfer/`.
The proof account remained sealed and was not closed; close/refund is still a
missing matrix case.

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

Finalized live cases are Pool initialize, deposit, checkpoint, genuine
live-note proof generation/upload, and same-page private transfer. The
transfer proves the adapter no longer depends on the deterministic Pool root:
the input note and append before-state came from independently created live
accounts, while deposit and output routing were sampled until both selected
the same live-created lane page.

Transfer rollover, withdrawal, different-lane concurrency, stale/replay,
wrong-checkpoint/release, malformed-ASQ8/result/ciphertext, failed withdrawal
CPI rollback, and proof close/refund remain unexecuted and are explicitly
`not-run` in machine-readable evidence.

The smallest remaining integration is host-side: generalize the live child
and terminal builder from transfer-only to the already implemented withdrawal
plan and its five custody accounts, then add reusable mutation/replay and
proof-close runners. No cryptographic integration or production program
change is currently indicated.

The result is safe to cherry-pick as host-only, default-off research plumbing.
It establishes one genuine finalized local transfer, not public-devnet
lifecycle completion, production identities, or mainnet readiness.
`mainnetReady` remains false.

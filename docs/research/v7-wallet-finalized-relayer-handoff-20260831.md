# V7 wallet finalized relayer handoff — 2026-08-31

## Revision and scope

- Branch: `research/v7-wallet-runtime-handoff-20260831`
- Frozen base: `69ec6de5fb2cb8f4600dc071dc4ca3e1c7e97bb7`
- Final implementation revision: the commit containing this report; the exact
  SHA is reported in the external handoff.
- Production changes are confined to the local wallet crate. No Pool,
  Registry, verifier, cryptographic relation, transcript, on-chain wire, Lean,
  Aeneas, deployment, signature, RPC submission, or public network was changed
  or exercised.

The base audit found that the opaque V2 activation permit already has a real
consumer in `ActivatedWalletRuntimeV2`, and the populated migration suite
already contains a finalized-spend fixture. This milestone therefore does not
duplicate either branch. It closes the remaining local physical handoff from a
durable finalized-success relayer journal record into the authoritative ASL2
wallet transaction.

## Result

`ActivatedWalletRuntimeV2::apply_finalized_journal_event_v2` now accepts an
otherwise uncorrelated Pool event intent only together with:

- a live, locked `DurableRelayerExecutionJournalV1` handle;
- the exact nonzero ASRJ request identity;
- an exact signed transaction retained by that request;
- a successful finalized outcome, rather than pending, terminal failure, or
  finalized execution failure;
- the same finalized chain point as the Pool event;
- the same transaction signature as the Pool event's primary event identity;
- the exact provider-set digest pinned by the runtime activation permit.

Only after those bindings succeed does the existing runtime route the intent
through the authoritative ASL2 prepare/recover path. The exact relayer
observation is retained inside the same checksummed ASL2 record as the Pool
event, note additions, finalized-spend markers, lane/checkpoint update, and
cursor advance. A second request cannot relabel an already committed event.

The crate-private binding method gives the permit-gated runtime one canonical
live-journal handoff without adding another public intent mutation surface. The
existing public ASRJ-to-observation constructor remains the typed
finalized-success capability for deliberately composed lower-level callers and
codecs. Rust API visibility alone therefore does not forbid a downstream
caller from choosing the lower-level API; a production process selecting the
authoritative runtime must route relayed events through this facade.

## Crash and authority model

ASRJ and ASL2 do not share a filesystem transaction, and this milestone does
not claim that they do. Safety instead uses monotonic direction:

1. ASRJ successful finality is terminal and immutable.
2. Its live handle retains the ASRJ file lock throughout ASL2 application.
3. ASL2 prepares the complete successor before replacing the authoritative
   image and uses the existing external monotonic prepared-next protocol.
4. Startup rolls the exact prepared successor forward after a lost response.
5. Reapplying the same immutable ASRJ capability is idempotent; a different
   request identity for the same event conflicts.

The populated handoff test injects `AfterCommit`, causing the first runtime
call to lose its response after the monotonic service accepted the exact ASL2
successor. Restart recovers finalized head 109 and an exact journal retry is a
no-op success. The ASRJ bytes remain unchanged.

The migrated V1 ASRJ directory is deliberately fenced by ASMG/ASRT after the
one-way ownership transfer. Continuing V2 relayer execution therefore uses a
fresh authority directory (`v2-relayer/`) rather than silently re-enabling a
retired legacy writer.

## Focused adversarial coverage

The retained finalized-capability unit test proves that absent, simulated-only,
signed-but-pending, terminal-failure, and finalized-failure records cannot
produce a finalized wallet observation; a successful finalized record survives
journal restart and conflicting outcome replacement fails.

The populated runtime integration now additionally proves:

- an unknown request fails before ASL2 mutation;
- a journal point/signature that does not identify the Pool event fails before
  ASL2 mutation;
- a provider digest different from the activated runtime policy fails before
  ASL2 mutation;
- all three failures leave the ASL2 bytes exactly unchanged;
- a lost response after monotonic commit recovers the exact successor on
  restart;
- exact finalized-journal replay is idempotent;
- an alternate valid request for the same Pool event is rejected as an event
  conflict;
- the source journal remains byte-exact throughout.

## Focused verification and resources

All commands ran locally and offline. `/usr/bin/time -l` reported zero swaps.

| Command | Result | Wall | Peak RSS |
|---|---:|---:|---:|
| cold focused feature-library compile | exit 0; filter matched zero and is not counted as a test | 28.29 s | 907,526,144 B |
| `cargo test --no-default-features --features wallet-v2-reference-tests --lib finalized_journal_capability -- --nocapture` | 1 passed | 0.25 s | 95,649,792 B |
| `cargo test --no-default-features --features wallet-v2-reference-tests --test v7_populated_wallet_migration populated_handoff_is_one_way_recoverable_and_activation_stays_explicit -- --exact --nocapture` | 1 passed | 6.62 s | 760,299,520 B |
| `cargo clippy --no-default-features --features wallet-v2-reference-tests --lib --test v7_populated_wallet_migration --no-deps` | exit 0; 16 pre-existing library warnings | 12.47 s | 534,167,552 B |

Only focused consumers were run; no unchanged full regression was repeated.
Warnings shown by Cargo are pre-existing in untouched Pool/wallet code.

## Remaining production boundaries

This is a merge-worthy, default-off local runtime milestone, not complete
production wallet activation. The following remain external or unimplemented:

1. **Deployed event source.** No deployed Pool program currently emits the
   compact wallet event ABI used by the older `lane_forest_rpc_v2` bridge. Its
   authenticated ASD8 snapshot is a separate store and cannot be substituted
   for ASL2. A production scanner must construct the exact Pool V2 intent from
   finalized transaction/account evidence and bind the transaction signature
   used here.
2. **Provider/ledger qualification.** Provider quorum, ledger correctness,
   finality/reorg policy, startup receipt, and the truth of execution-result and
   poststate digests remain external. This runtime enforces exact activated
   identities; it does not prove provider honesty.
3. **Relayer service.** Simulation, signing request, submission, polling, and
   finality evidence acquisition remain the responsibility of the external
   relayer process. The ASRJ state machine fail-closes their durable local
   transitions but does not operate the service.
4. **Prover service.** Witness/prover request transport, proof generation,
   proof-account upload, retry, and cancellation remain external to this
   handoff.
5. **Key custody.** Note/nullifier key generation, hardware-backed custody,
   backup, recovery, rotation, secure deletion, and compromise response remain
   external.
6. **Monotonic provider.** Production mode still requires the separately
   specified rollback-independent monotonic provider and an honest in-crate
   qualification adapter. Test/reference backends cannot mint production
   qualification.

Until those boundaries are closed, V2 remains default-off. This change does
not weaken that activation gate.

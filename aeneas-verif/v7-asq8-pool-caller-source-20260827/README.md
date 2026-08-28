# V7 ASQ8 Pool caller accepted-source bridge

This bundle pins the production-inactive one-terminal Pool caller at base
`bbb1bd67f56a99d26e5b84de26afdafb55e04957` and closes the source boundary in
three focused pieces:

1. `ASQ8Dispatch` is the Charon/Aeneas translation of
   `invoke_pair_forest_terminal_with_runtime_v1`, including the outer ASR8
   decoder.  Its strongest theorem proves that translated success cleared stale
   return data, invoked the authenticated verifier program with exactly four
   readonly/non-signer metas in proof/master/checkpoint/selected-lane order,
   sent the exact request bytes, and consumed the immediate 792-byte ASR8 return.
2. `ASQ8NextLane` is the translation of `next_pair_forest_lane_v1`.  Its source
   theorem proves a successful canonical-frontier run preserves master/lane
   identity and installs exactly the ASR8 index/root/frontier.
3. `ASQ8CallerWriteOrderBridge` is an executable operational model of the exact
   outer control flow after verifier return.  It proves every modeled late
   failure leaves Pool-owned lane/history/marker images unchanged; accepted
   transfer writes exactly those three images; accepted withdrawal reaches the
   same writes only after exact account selection, CPI success, and exact token
   deltas.  It also proves the ASR8 equalities pin the retained checkpoint,
   current selected-lane snapshot, and deterministic output lane.

The raw outer function is present as `extraction/ASQ8CallerRaw.llbc`.  Charon
extracts it without errors.  Pinned Aeneas 0.1.223 rejects the generic root at
its higher-ranked `FnOnce` lifetime relation before translation.  That is why
the outer write-order layer is an explicit operational model rather than a
claim that Aeneas translated Solana account persistence.

## Source change

One behavior-preserving extraction refactor changes the internal verifier
runtime method from `&[AccountInfo]` to the exact `&[AccountInfo; 5]` already
constructed at the callsite.  The Solana implementation invokes with
`account_infos.as_slice()`.  This avoids Aeneas's unsupported array-to-slice
conversion over `AccountInfo` interior references.  No instruction, account,
dispatch, or persistence behavior changes.

## Trust and composition boundaries

The source theorem does not model Solana PDA derivation, loader IDs, CPI
execution, account borrowing, rollback, or persistence.  They remain explicit
runtime boundaries.  The broad ASR8 decoder graph also keeps canonical digest,
deterministic lane, and 688-byte afterstate codec calls as named composition
interfaces; those source functions are independently covered by the existing
`v7-forest-terminal-source-20260827` bundle.  The registry authorization step is
the existing exact theorem
`corrected_production_success_implies_exact_authorization` in
`pool-v1-verifier-registry-source-20260827`; this bundle begins with the selected
verifier output of that theorem and proves its exact CPI use.

There are no `sorry`, `admit`, `sorryAx`, `native_decide`, or conclusion-shaped
axioms in the compiled proof sources.  The strongest translated dispatch theorem
reports only Lean's standard axioms plus the named codec/loader interfaces above.
The pure write-order results use only standard Lean axioms, and the two exact
accepted-write theorems are axiom-free.

## Focused checks

- Rust: `cargo test -p aspis-pool --features pair-forest-account-evidence pair_forest_dispatch::tests -- --nocapture`
- Frozen LLBC and all generated/proof Lean modules: `./replay.sh`
- Forbidden proof construct scan is part of `replay.sh`.

No SBF build, CU measurement, network call, deployment, or mainnet action is in
scope for this bundle.

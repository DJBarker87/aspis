# V7 Registry V2 one-terminal caller Rust-to-Lean bridge

This focused bundle closes the fixed-width operational source projection for
the Registry V2 one-transaction eight-lane Pool caller measured at
`7179f7c550fe0461f4251dea5268af73876da91d`. It changes no production Rust,
wire format, proof system or deployment state.

The production source audited here is byte-identical to the Registry V2 path
at `4722228b991ebb72850b8d79dd54b0fee4899462`. `source-audit.sh` pins the
literal Pool, selected verifier, Registry governance and statement-codec files
and their control-flow order. Charon/Aeneas separately translates a
fixed-width projection of that fail-closed caller. The two parts deliberately
do not turn Solana runtime behavior, SHA-256 or PDA derivation into invented
pure-Rust theorems.

## Closed path

The projected caller preserves the production order and bindings:

1. exact 320-byte canonical ASQ8, Pool master, retained checkpoint and
   selected live lane;
2. immutable Registry V2 policy, distinct canonical ASR2/ASE2 accounts,
   loader-v3 ProgramData identities, nonzero certified executable hashes,
   zero upgrade authority and exact active profile/release/version;
3. exact selected verifier and six pairwise-distinct read-only CPI accounts in
   the order proof, master, checkpoint, lane, registry, entry;
4. selected-program success and exact 792-byte canonical ASR8 decoding;
5. exact ASR8 transition, master, selected lane, output lane, nullifier,
   checked next index and canonical next frontier;
6. ASR8 byte identity preserved from verifier return data through the caller's
   acceptance certificate and returned Pool state;
7. same-page or rollover history, selected-lane root/index/frontier,
   nullifier marker, transfer custody or checked withdrawal deltas;
8. byte-exact rollback in the translated transaction wrapper for every
   rejected path.

The harness tests all four transfer/withdrawal × same-page/rollover success
shapes, runtime rollback, wrong release, malformed/mutated ASR8, 18 independent
Registry V2 certificate mutations, and ASQ8/ASR8 canonicality plus exact return
byte identity.

## Strongest results

`translated_accepted_atomic_transaction_has_exact_writeback` starts from an
actual successful translated atomic-wrapper execution and produces the caller
execution together with `ExactAcceptedWriteback`. This includes
`ExactReleaseAuthentication`, `ExactResultBinding`, `ExactMarkerBinding`,
`ExactFinalizedCore`, all three successful mutable borrows, exact transfer or
withdrawal custody, and preservation of unrelated state.

`translated_rejected_atomic_transaction_is_exact_prestate` proves that a
translated rejected transaction returns the exact pre-state, no acceptance
certificate and a concrete error.

The focused intermediate results are:

- `translated_authentication_success_is_exact`;
- `translated_result_success_is_exact`;
- `translated_marker_success_is_exact`;
- `translated_prepare_success_is_exact`;
- `translated_finalize_success_is_exact`;
- `translated_withdrawal_apply_success_is_exact`;
- `translated_apply_prepared_success_is_exact`;
- `translated_accepted_caller_has_exact_writeback`.

Every printed theorem depends on a subset of `propext`, `Classical.choice` and
`Quot.sound`. Compiled source contains no `sorry`, `admit`, `sorryAx`,
`native_decide`, project axiom or conclusion-shaped restoration premise. The
uncompiled generated external template's standard `Option` equality interface
is replaced by a transparent definition in `FunsExternal.lean`.

## ASR8 correction and verifier composition

The actual `PoolV1PairForestTerminalResultV1` does **not** serialize the old
lane index, root or frontier. Those values are authenticated inputs to the
selected verifier's ASF8 reconstruction, not caller-controlled ASR8 fields.
This bridge therefore proves only the fields ASR8 really carries and the exact
verified afterstate it returns. It does not preserve the older projection's
fictional `source_root` or `source_frontier` fields.

Consequently, live selected-lane snapshot/root/frontier binding composes at the
selected-verifier acceptance theorem. The Pool caller source proof then shows
that the verifier-returned afterstate is the one written atomically. Existing
focused source bundles separately cover the fresh nullifier-marker lifecycle,
lane invariant, history and withdrawal-vault mechanics.

## Explicit remaining boundaries

- correspondence between this fixed-width operational projection and the
  hash-pinned `AccountInfo` production caller;
- Registry V2 codec/PDA and loader-v3 Program→ProgramData parsing, executable
  payload SHA-256 and the one-time immutable-deployment certificate;
- selected Tag-73 verifier cryptographic acceptance, including ASF8 historical
  checkpoint and current selected-lane snapshot reconstruction;
- Solana ownership, PDA derivation, borrow, CPI, return-data and instruction
  rollback semantics;
- SPL Token behavior for the five-account withdrawal CPI;
- Charon, Aeneas, the Rust compiler and Lean kernel.

These are named primitive/runtime/tool/refinement boundaries. They are not
hidden theorem premises. In particular, this bundle is not a literal
translation of Solana `AccountInfo`, loader-v3 or SHA-256 internals.

## Replay

```sh
./source-audit.sh
./replay-rust.sh
CHARON_BIN=/path/to/charon AENEAS_BIN=/path/to/aeneas ./replay-extraction.sh
AENEAS_LEAN_BACKEND=/path/to/aeneas/backends/lean \
  LEAN_BIN=/path/to/lean-4.31.0 ./replay-lean.sh
```

The replay uses one Cargo job and one Lean thread. Exact revisions, hashes,
resource limits and measured peaks are recorded in `REPLAY-RESULT.txt` and
`evidence/`.

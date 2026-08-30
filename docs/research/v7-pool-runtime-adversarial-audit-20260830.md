# V7 Pool runtime adversarial audit — 2026-08-30

## Frozen scope

This focused audit starts from
`bcd03b12293f2737dfa1da1436092a0a24a6ae24`. It covers the Rust-side
versioned verifier registry, Pool registry authentication, legacy-SPL vault
custody, eight-lane append/history/checkpoint state, one-terminal
private-transfer and withdrawal settlement, nullifier persistence, and
operator controls.

It does not change the Tag-73 proof relation, transcript, ASQ8/ASF8/ASR8
codecs, transaction layouts, wallet, verifier CU path, Lean, or Aeneas. It
does not constitute a deployment or validator-runtime test.

## Result

One genuine fail-closed inconsistency was found and fixed. The eight-lane
withdrawal terminal checked the fixed legacy SPL Token program address,
executable flag, signer flag, and writable flag through
`plan_legacy_withdrawal_transfer_from_identity_v1`, but unlike Pool
initialization, deposit, and the legacy withdrawal caller it did not also
authenticate that the account owner was a supported Solana program loader.

The corrected call chain is:

1. `programs/aspis-pool/src/pair_forest.rs`:
   `process_pair_forest_terminal_with_verifier_v1` selects the five exact
   withdrawal token accounts.
2. It calls
   `programs/aspis-pool/src/processor.rs::require_token_program_account` on
   the supplied legacy SPL Token program account before verifier execution.
3. That helper requires the canonical program key, executable/read-only/
   nonsigner privileges, and ownership by `bpf_loader`,
   `bpf_loader_upgradeable`, or `loader_v4`.
4. The existing vault planner then authenticates mint, vault, destination,
   vault-authority PDA, balances, and exact `TransferChecked` parameters.

The adversarial test now supplies the canonical SPL Token key and executable
bit with `native_loader` ownership. It receives exactly
`InvalidTokenProgram`, never reaches the verifier, performs zero custody CPI,
and leaves every account byte unchanged. The positive BPF-loader case still
exercises both CPI failure rollback and successful exact vault/destination
balance deltas followed by lane/history/nullifier writes.

## Surfaces audited without another source change

| Surface | Existing fail-closed properties checked in source/tests | Result |
|---|---|---|
| Registry governance | canonical registry/entry PDAs; exact account counts; alias rejection; signer-only read-only authority; generation compare-and-increment; nonzero activation delay; pause/unpause no-op rejection; active exact-compatible replacement before retirement; irreversible freeze | no additional Rust gap found |
| Pool registry consumer | registry program/authority/policy binding; canonical read-only registry and entry accounts; active-slot and retirement checks; paused registry rejection; exact profile/release/verifier selection | no additional Rust gap found |
| Vault initialization/deposit | canonical mint and token-program identity; supported loader; canonical Pool vault and authority PDAs; legacy token-account canonical fields; exact pre/post amount delta; CPI failure before state commit | no additional Rust gap found |
| Eight-lane state | canonical master/lane/checkpoint/page PDAs; fixed eight-lane ordering; alias rejection; occupied/empty pair deposit; selected-lane-only append; page rollover; append-only retained roots; checkpoint no-progress rejection | no additional Rust gap found |
| Terminal private transfer | exact master/checkpoint/live-lane/request binding; registry/verifier/proof binding; verified afterstate; lane/history/nullifier borrows acquired before writes; replay rejection | no additional Rust gap found in the host path |
| Terminal withdrawal | all private-transfer bindings plus destination, mint, vault, authority, token program, exact custody delta, and rollback ordering | supported-loader gap fixed |

## Hard activation blocker: no canonical nullifier-marker provisioning path

The current one-terminal source requires a marker state that a normal client
cannot create through any dispatched eight-lane Pool instruction.

The exact path is:

1. `programs/aspis-pool/src/nullifier.rs::pool_v1_nullifier_marker_address`
   derives the canonical PDA from the Pool and canonical nullifier bytes.
2. `plan_nullifier_marker_consumption_v1` recognizes either a data-empty
   System-owned PDA (`CreateOrAllocateSystemOwned`) or an exact-size,
   Pool-owned, all-zero PDA (`PopulateProgramOwnedZeroed`).
3. `programs/aspis-pool/src/pair_forest.rs::process_pair_forest_terminal_with_verifier_v1`
   explicitly rejects every preparation except `PopulateProgramOwnedZeroed`.
4. `plan_pair_forest_spend_layout_v1` supplies no payer or System Program
   accounts, so this terminal cannot allocate/assign the System-owned form.
5. `programs/aspis-pool/src/processor.rs::process_instruction` dispatches
   eight-lane initialize (`AS8I`), checkpoint (`AS8C`), deposit (`AS8D`),
   and terminal (`ASQ8`, plus audit-only `ASF8`), but no marker-reservation
   instruction.
6. `terminal_base_accounts` in the host test fixture directly constructs the
   canonical marker as a Pool-owned zero account. That is useful unit-test
   state, but it is not evidence that an external client can create the PDA;
   allocating and assigning this Pool PDA requires the Pool program's
   `invoke_signed` seeds.

Therefore the eight-lane terminal is **not operationally activatable yet** on
a fresh chain state, despite the terminal's marker-consumption logic being
fail-closed. This is not a cryptographic defect, but it is a hard lifecycle
blocker and must not be hidden by preloaded host fixtures.

### Smallest safe design options

1. **Create the marker inside the terminal.** Add exact payer and System
   Program accounts, accept the System-owned empty form, and use the already
   reviewed `create_or_allocate_pda` pattern with Pool PDA seeds and a rent
   check. Replan after creation and before copying the marker. This preserves
   one atomic terminal instruction and avoids early nullifier disclosure, but
   changes account layouts/TxV1 size, CU, source bridges, and rollback tests.
2. **Add a permissionless marker-reservation instruction.** It would accept
   payer/System Program, derive the marker from canonical Pool/nullifier
   inputs, create an exact rent-exempt Pool-owned zero PDA, and write no
   consumed marker. This keeps ASQ8 unchanged but introduces a prior lifecycle
   transaction, discloses the nullifier before settlement, and needs explicit
   anti-griefing, abandoned-rent recovery, authority, and replay analysis.
3. **Fold reservation into an existing proof-account setup/finalization
   phase through an explicit Pool call.** This may avoid a new wallet-visible
   phase, but it has the same early-disclosure and abandoned-account questions
   and introduces a cross-program/source interface. It must not be treated as
   an implicit capability of the current proof upload path.

No option was implemented in this branch because each changes lifecycle,
accounts, wire/CU, or another program boundary. The production design must
select one explicitly and then add real validator rollback and rent-exemption
evidence.

## Focused verification

Baseline, before the change:

- `NO_DNA=1 cargo test -p aspis-registry --lib`: 10 passed.
- `NO_DNA=1 cargo test -p aspis-pool --lib --features v7-pair-forest-one-tx-candidate`:
  101 passed.

Changed-path preflight:

```text
NO_DNA=1 cargo test -p aspis-pool --lib \
  --features v7-pair-forest-one-tx-candidate \
  pair_forest::tests::one_terminal_withdrawal_authenticates_loader_and_checks_custody_delta_before_writes \
  -- --exact
```

Result: 1 passed, 100 filtered out. A final changed-package focused suite is
also green:

```text
NO_DNA=1 cargo test -q -p aspis-pool --lib \
  --features v7-pair-forest-one-tx-candidate
```

Result: 101 passed in 9.44 seconds. `rustfmt --check` on the changed Rust file
and `git diff --check` pass. Workspace-wide `cargo fmt --all -- --check` is not
green at the frozen base because it reports pre-existing formatting deltas in
unmodified cryptographic and dispatcher files; this audit did not rewrite
them. No unchanged project-wide regression is justified by this audit.

## Release conclusion

The loader-owner inconsistency is closed without changing cryptography, wire
formats, or wallet behavior. The reviewed registry, vault, lane/history, and
atomic write ordering expose no second concrete Rust defect in this focused
pass. Mainnet activation remains blocked until canonical nullifier-marker
creation is implemented and demonstrated through the real runtime lifecycle.

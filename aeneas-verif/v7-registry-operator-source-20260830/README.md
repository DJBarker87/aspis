# V7 registry/operator and selected-verifier source closure

This bundle freezes the exact V1 guarantee that exists today. It does not
claim that a release/profile binding is a deployed-program code hash.

## What is closed

The production source hashes in `evidence/source-sha256.txt` cover:

- canonical 128-byte registry and 192-byte entry decoding;
- registry/entry PDA, owner, signer and writable-shape authentication;
- initialize, delayed schedule, pause/unpause, activate, compatible retire and
  irreversible registry freeze;
- authority and generation checks, checked generation increments, two-account
  preborrow before commit, and Solana transaction rollback on CPI/error;
- exact Pool policy, active interval, verifier program, profile, release and
  statement-version selection;
- a read-only, nonsigner executable verifier account owned by legacy BPF,
  upgradeable BPF or loader-v4;
- proof ownership, verifier-CPI success, exact returned program, exact 792-byte
  ASR8 framing, canonical decode and semantic result binding.

The focused Rust tests add spoofed payer/System-account rejection,
cross-policy and malformed-entry atomic rejection, all three supported-loader
positive cases, wrong loader/program/privilege negatives, and stale/missing/
wrong/malformed verifier-return rejection without input mutation.

`harness/src/lib.rs` is a fixed-width operational projection of those source
checks. Charon starts at
`registry_operator_and_selected_verifier_source_roots`; Aeneas translates both
the mutating operator family and the separate read-only selected-verifier
family. The principal Lean results are:

- `translated_operator_rejection_is_exact_rollback`;
- `translated_operator_success_is_exact_apply`;
- `translated_operator_preserves_unrelated_pool_state`;
- `translated_frozen_registry_rejects_authority_gate`;
- `translated_generation_mismatch_rejects_authority_gate`;
- `translated_compatible_replacement_success_binds_exact_relation`;
- `translated_selected_verifier_success_has_exact_guarantee`;
- `translated_combined_root_keeps_operator_and_selection_separate`.

## Explicit hard boundary

V1 never receives or parses upgradeable-loader ProgramData. It does not check
the verifier's upgrade authority and does not hash executable bytes. Registry
`IMMUTABLE` prevents future registry mutations; it does **not** make an
upgradeable verifier immutable. The Lean theorem
`current_v1_selection_is_independent_of_programdata_code_hash_and_authority`
makes the omission explicit rather than hiding it behind an assumption.

Accordingly, V1 registry closure is not sufficient for mainnet activation.
The minimal on-chain V2 design and compatibility/CU consequences are recorded
in `docs/research/v7-registry-operator-closure-20260830.md`.

## Replay

```sh
./aeneas-verif/v7-registry-operator-source-20260830/replay-rust.sh

CHARON_BIN=/absolute/path/to/charon \
AENEAS_BIN=/absolute/path/to/aeneas \
./aeneas-verif/v7-registry-operator-source-20260830/replay-extraction.sh

AENEAS_LEAN_BACKEND=/absolute/path/to/aeneas/backends/lean \
LEAN_BIN=/absolute/path/to/lean \
./aeneas-verif/v7-registry-operator-source-20260830/replay-lean.sh
```

Only the ordinary Solana runtime/PDA/System-CPI/transaction-rollback semantics
and the Charon/Aeneas/compiler toolchain remain source-tool boundaries. There
is no project-specific Lean axiom, `sorry`, `admit` or `native_decide` in the
compiled bundle.

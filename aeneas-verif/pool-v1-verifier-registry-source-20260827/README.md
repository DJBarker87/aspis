# Pool V1 verifier-registry source bridge

This focused bundle proves the read-only Pool V1 verifier-registry selection
path from production Rust success to the existing pure
`AspisPool.VerifierRegistryV1.Authorized` predicate.

## Production root and translator result

The production root is
`aspis_pool::registry::authenticate_verifier_selection_v1` in
`programs/aspis-pool/src/registry.rs`.  Pinned Charon extracted that exact root
successfully.  Aeneas translated its pure subcalls, including the literal
`require_readonly_registry_account` body, but could not translate the outer
two-element `AccountInfo` slice pattern because the generic slice indexer
instantiated over Solana's interior-mutable account type.  The two PDA helpers
also stop at Solana's `Pubkey::find_program_address`.

`correctedAuthenticate` is the minimal correction: it replaces only the
unsupported two-account destructure, then executes the exact translated policy
validator, readonly-account helper and registry/entry decoders.  Its two named
Solana runtime boundaries are:

- `find_program_address`, receiving the literal production seed strings in
  their exact order; and
- `try_borrow_data`, returning the immutable byte slice consumed by the exact
  decoders.

No production Rust was changed.  There is no source-equality axiom and no
authorization-shaped premise.

## Source-check inventory

| Rust lines | Lean inventory |
|---|---|
| 127-132 | exact two-account list in `SuccessfulTrace` |
| 134 | generated `validate_verifier_policy_v1` |
| 137-144 | generated readonly helper and literal registry PDA seeds |
| 146-149 | `try_borrow_data` boundary and generated registry decoder |
| 150-163 | exact immutable/pool/authority/policy/pause checks |
| 165-179 | generated readonly helper and literal entry PDA seeds |
| 180-183 | `try_borrow_data` boundary and generated entry decoder |
| 184-202 | exact selection/status/activation/retirement checks |
| 204-213 | exact authenticated output projection |

## Checked result

`corrected_production_success_implies_exact_authorization` proves that any
successful corrected production execution yields:

- exactly two readonly, non-executable, non-writable, non-signer accounts owned
  by the policy's registry program;
- exact registry and entry PDA inputs and keys;
- a valid policy and exact decoded registry/entry;
- pool, authority, policy, verifier-program, profile, release and statement
  version bindings;
- immutable-policy equality and an unpaused registry;
- active status, activation-slot passage and exact retirement handling; and
- the exact returned policy, pool, selection, registry generation and
  authentication slot.

The terminal theorem composes these facts into the existing formal
`Authorized` model.  Focused `#print axioms` reports only Lean/Mathlib's
`propext`, `Classical.choice` and `Quot.sound`.

`corrected_production_success_implies_receipt_registry_authorization` also
maps the exact generated selection into
`AuthorizationReceiptV1.Binding.selection`.  It discharges the registry side
of `AcceptedReceipt` without claiming the separate receipt-account
authenticity or verifier `IssuerSound` obligations.

## Focused replay

Run `check-focused-lean.sh` with Lean 4.32, a compatible Aeneas Lean backend,
an `AspisFormal` Lean path and a fresh output directory.  RAM-heavy replay is
intended for the NUC with `LEAN_NUM_THREADS=1`, `MemoryHigh=12G`,
`MemoryMax=16G` and `MemorySwapMax=0`.

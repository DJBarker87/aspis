# V7 K1.3 restored challenge invariant — 2026-08-29

## Result

The exact Tag-73 future-free controller now carries a kernel-checked invariant
for the verifier-decoded gamma and alpha-zero challenge records.  The invariant
is preserved by challenge/candidate processing, verifier replies, raw-message
submission, the operational trace, stored snapshots, and restoration.

For every completed node in the literal returned restoration accumulator, Lean
therefore derives exact gamma and alpha-zero bytes, decoded QM31 values, record
membership, and canonical decoder success.  Together with the existing exact
selected-q16 ledger theorem, these values are no longer inputs to the K1.3
source provider.

The only remaining per-node K1.3 source input is the production verifier's
canonical decoding of its 641 fixed QM31 proof fields.

## Strongest theorems

- `done_state_has_exact_gamma_alpha_zero`
- `projected_restoration_child_k13_challenge_invariant`
- `exact_fixed_package_root_k13_challenge_invariant`
- `exact_restored_operational_k13_data_of_source_node`
- `exact_restored_operational_k13_provider_of_source`

## Focused replay

- Target: `AspisFormal.K1.V7Tag73ExactRestoredOperationalK13Classifier`
- NUC unit: `aspis-v7-k13-classifier-r3.scope`
- Jobs: 8,926
- Wall: 6.47 seconds
- Peak RSS: 6,932,976 KiB
- Swap: 0
- Exit: 0
- Axiom union: `propext`, `Classical.choice`, `Quot.sound`

No `sorry`, `admit`, `sorryAx`, `native_decide`, or project-specific axiom is
present in the changed proof sources.

## Next boundary

Build the Rust-to-Lean/Aeneas bridge from literal production
`V6FixedFieldReader` success (`next_qm31` plus `finish`) to
`CurrentSourceFixedFieldProjection`.  This must preserve the current proof wire
and must not use the default-off 320-byte experimental canonical audit.

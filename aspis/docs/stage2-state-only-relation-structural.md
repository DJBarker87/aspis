# Profile-20 relation structural optimization

Status: exact rewrite promoted to the state-only and atomic-v3 relation
verifiers. No proof, commitment, Fiat--Shamir, OOD, sumcheck, or query change.

## Object and equivalence

The relation accumulator contains the public 64-by-16 binary covector that is
one on inactive copy rows. The frozen state-only covector has eight distinct
16-bit row masks. The legacy `Grouped64x16` implementation materialized each
mask as sixteen QM31 zero/one values and applied an ordinary arity-four dual
fold twice.

For consecutive fold challenges `a0,a1`, the low 16-entry dual basis is

`[1,a1^3,a1^2,a1] tensor [1,a0^3,a0^2,a0] / 16`.

The promoted component retains each `u16` mask through the first fold. At the
second fold it computes the nine nontrivial cross-products shared by all row
masks, adds the selected basis entries for each mask, and expands to the same
64-value dense covector used by the legacy path. All later relation code is
unchanged.

The initial covector, the intermediate covector after the first fold, the
64-value covector after the second fold, both later folds, and the terminal dot
are equal. Therefore the running claim, every boundary comparison, and the
terminal comparison are unchanged for every challenge sequence.

## Guards

- The legacy evaluator remains available as
  `verify_state_only_relation_with_inactive_masks_legacy_reference`.
- The base component is compared with the legacy evaluator at every fold and
  terminal dot over 64 random QM31 challenge sequences.
- The different atomic-v3 inactive-mask object has its own 64-sequence guard.
- The full profile-20 production proof passes both evaluators. Perturbing each
  prepared point claim produces the same rejection in both paths.
- Full production verification rejects profile-20 statement-value, OOD-value,
  and sumcheck-message corruptions after promotion.
- Append-only tag 44 retains literal legacy and optimized paths plus an SBF
  prepared-claim corruption tooth.

## Measurements

Tag 44, five identical simulations per arm:

- legacy: 381,657 CU;
- deferred binary: 339,615 CU;
- isolated exact saving: 42,042 CU.

The saving localizes to 3,008 CU in point/covector setup and 39,782 CU in the
first relation round, offset by a 747-CU increase in the second round. Later
rounds and the final dot are identical.

After promotion, the literal profile-20 relation marker is 183,150 CU and its
overlap ledger books 183,153 CU, down from the prior 225,230-CU bucket. The
complete state-only diagnostic is 1,123,507 literal CU and 1,123,441 CU in the
overlap-subtracted ledger.

Atomic tag 43 uses the distinct atomic-v3 inactive masks through the same
generic specialization. Its literal relation marker is 183,148 CU. The
complete read-only atomic candidate is 1,270,356 literal CU; the
overlap-substituted ledger is 1,270,348 CU, leaving 129,652 CU under 1.4M.

The tag-44 delta replaces the relation bucket exactly once. It is not added as
a separate saving to either integrated ledger.

## Artifacts

- `results/stage2/state_only_relation_structural_probe.json`
- `results/stage2/state_only_width28_global_inactive.json`
- `results/stage2/atomic_state_only_profile20_cost.json`

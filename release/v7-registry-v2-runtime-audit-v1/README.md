# Registry V2 runtime audit inputs

This directory pins the measured Registry V2 one-transaction evidence at
`7179f7c550fe0461f4251dea5268af73876da91d` and exposes a fail-fast verifier:

```bash
release/v7-registry-v2-runtime-audit-v1/verify-inputs.sh
```

The verifier checks source/tree identities, every file in the original bundle
inventory, all three SBF artifacts, four success cases, seven rejection/replay
cases, packet sizes, CU, Registry V2 governance and rollback claims.

The original manifest remains an immutable description of the earlier
LiteSVM/single-build input evidence. The subsequent independent Linux A/B
build is frozen under
`results/v7-registry-v2-release-audit-20260831/dual-linux-sbf-r2`, and the
unsigned official-Agave 4.2 simulation suite is frozen under
`results/v7-registry-v2-release-audit-20260831/agave-runs/r6`.

Use `scripts/v7_registry_v2_dual_sbf_audit.sh` for the independent Linux A/B
build and stack gate, `scripts/v7_txv1_bundle_verify.sh` for the deterministic
eleven-case input bundle, `scripts/v7_txv1_agave_suite_materialize.sh` for the
completed case-evidence audit, and `scripts/v7_txv1_4k_feature_gate.sh` for the
read-only Agave/devnet TxV1 activation check.

The Agave suite is real local `simulateTransaction` CU, not devnet CU and not
a landed/finalized receipt. It reads no key, signs/submits no transaction and
uses no public cluster.

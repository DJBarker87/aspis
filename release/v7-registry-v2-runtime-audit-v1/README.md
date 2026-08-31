# Registry V2 runtime audit inputs

This directory pins the measured Registry V2 one-transaction evidence at
`7179f7c550fe0461f4251dea5268af73876da91d` and exposes a fail-fast verifier:

```bash
release/v7-registry-v2-runtime-audit-v1/verify-inputs.sh
```

The verifier checks source/tree identities, every file in the original bundle
inventory, all three SBF artifacts, four success cases, seven rejection/replay
cases, packet sizes, CU, Registry V2 governance and rollback claims.

It does not turn the existing single Linux build into reproducible-build
evidence and does not relabel LiteSVM measurements as Agave or devnet results.
Use `scripts/v7_registry_v2_dual_sbf_audit.sh` for the independent Linux A/B
build and stack gate. Use `scripts/v7_txv1_4k_feature_gate.sh` for the read-only
Agave/devnet TxV1 activation check.

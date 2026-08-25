# Aspis Registry V1 LiteSVM runtime evidence

This isolated bundle exercises the governed `aspis-registry` SBF artifact in
LiteSVM without RPC, validator, deployment, or network transactions. It pins
the already focused-built artifact by exact size and SHA-256 before execution.

The single lifecycle run covers registry-PDA initialization, exact activation
delay, early-activation rollback, activation, pause/unpause, a distinct active
compatible replacement, retirement continuity, immutable freeze, wrong and
missing authority signatures, a wrong entry PDA, stale generation, and whole-
transaction rollback after successful System Program CPI account creation.

Rejected transactions record before/after account existence, owner, lamports,
data length and data SHA-256. The fee payer is handled separately because a
runtime-executed rejection charges its transaction fee; rollback requires its
delta to equal the fee and no rent debit. Every transaction carries an exact
1,400,000-CU limit, and success/failure simulation metadata must equal execution
metadata.

Pinned runtime inputs:

- LiteSVM `0.16.0` / Agave runtime `4.2.1`.
- `artifacts/aspis_registry.so`: 102,648 bytes, SHA-256
  `1066ffc4bf8a12a0ea56b64474b70e172162fc7852b66293c0c8c5f1380f0ff6`.
- The program address and all keypairs are deterministic local-test identities,
  not deployment identities.

The focused replay command is:

```sh
bash results/registry-v1-runtime-litesvm-20260825/replay-focused.sh
```

Runtime measurements and exact snapshots are written to `evidence.json`; the
one-line run result is written to `run.log`.

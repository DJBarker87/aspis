# Results

The current machine-readable release is
[`stage2/profile23_one_transaction_release.json`](stage2/profile23_one_transaction_release.json).
It records 35/35 passing gates and binds the exact q18 proof, statement, and
SBF identities used by the finalized devnet execution.

The self-contained publication copies are in
[`release/profile23-q18-g37/`](../release/profile23-q18-g37/), where
`verify.sh` checks the release certificate, evidence, proof, program, and
paper together.

The remaining `stage2/` records are source artifacts, measurements, and four
regression proof fixtures consumed by the current release machinery. The
complete Stage 0/1 record, rejected profiles, and superseded measurements are
available under the `research-archive-2026-07-14` tag.

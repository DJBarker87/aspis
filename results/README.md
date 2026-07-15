# Results

The current machine-readable release is
[`stage2/profile23_one_transaction_release.json`](stage2/profile23_one_transaction_release.json).
It records 36/36 passing gates and binds the exact 64,447-byte q18 proof,
statement, and 921,848-byte SBF identities used by the finalized devnet and
mainnet executions. The local worst-case tag65 measurement is 1,340,803 CU.

The sanitized, source-committed devnet execution record is
[`devnet-finalized.raw.public.json`](../release/profile23-q18-g37-mainnet-v1/evidence/devnet-finalized.raw.public.json).
It records tag65 signature
`4HRnTBPqSh9HW4Nw52rJgnd36fzR6CiKgiaL29WkeH4Gk4xLJVhGEt9CAStyUTpuajo9sw4iDLXQHWwFFQALWmto`
at slot `476282685`, consuming 1,340,749 CU.

The self-contained mainnet publication is in
[`release/profile23-q18-g37-mainnet-v1/`](../release/profile23-q18-g37-mainnet-v1/), where
`verify.sh` checks the release certificate, evidence, proof, program, and
paper together.

The remaining `stage2/` records are source artifacts, measurements, and four
regression proof fixtures consumed by the current release machinery. The
complete Stage 0/1 record, rejected profiles, and superseded measurements are
available under the `research-archive-2026-07-14` tag.

# Profile23 q18/g37 mainnet release v1

This immutable bundle contains the exact Profile23 q18/g37 proof, public
statement, SBF verifier, 36/36 release certificates, finalized devnet and
mainnet evidence, independent mainnet RPC reconciliation, cleanup and refund
receipts, a byte-level archival reconstruction of the deployed SBF and landed
instruction, the publication paper, and the prepublication security review at
`review/prepublication-security-review.html`.

`certificates/release-execution-time.json` is the exact certificate bound by
the finalized executor evidence. `certificates/release.json` is the current
publication certificate. It differs only by its timestamp and explanatory
metadata note; acceptance and mutation repository-path sanitation byte
lengths and hashes; corrected soundness metadata; removal of duplicated
release snapshots from the proof-independent complete-Good and HVZK sources;
and the q18 program-manifest comment and hash. The proof, statement, SBF,
security values, gates, and CU values are identical in both certificates.
`manifest.json` records this provenance.

`certificates/mainnet-readiness.json` is the current read-only publication
preflight. It describes stronger signing, recovery, fee, and cleanup controls
as required future policy; it is not an execution attestation and does not
claim that per-wire crash recovery ran. The exact pre-execution copy is kept
separately as `certificates/mainnet-readiness-execution-time.json`.

The finalized mainnet verification transaction is
`4Er5afhxfcFmpeTuFqEeNQEbCBri3pkc6ymx7ST5wfNpSBYwQDHA9DtCuDBpD5WuEDXs7ozL3sK5msc6QWE4q9Fo`.
It finalized at slot `432933949` and consumed `1,343,749` CU. View it using
the cluster-pinned [Solana Explorer](https://explorer.solana.com/tx/4Er5afhxfcFmpeTuFqEeNQEbCBri3pkc6ymx7ST5wfNpSBYwQDHA9DtCuDBpD5WuEDXs7ozL3sK5msc6QWE4q9Fo?cluster=mainnet-beta)
or [Solscan](https://solscan.io/tx/4Er5afhxfcFmpeTuFqEeNQEbCBri3pkc6ymx7ST5wfNpSBYwQDHA9DtCuDBpD5WuEDXs7ozL3sK5msc6QWE4q9Fo?cluster=mainnet).

After execution, `6,985,137,600` lamports were returned to the funding source.
The exact nonrefundable cost was `14,883,400` lamports (`0.0148834` SOL), and
the disposable payer ended at zero.

Run the offline verifier from this directory:

```bash
./verify.sh
```

It requires Bash, `jq`, and either `sha256sum` or `shasum`. It checks every
published byte plus the critical identities, hashes, signatures, slots,
compute use, state transition, cleanup, independent-provider agreement, and
cost equations.

The offline verifier authenticates the frozen reconstruction result. To
repeat its live archival RPC replay from this directory, run:

```bash
python3 tools/reconstruct_profile23_mainnet_sbf.py \
  --sbf-path program/aspis_verifier.so \
  --proof-path proof/profile23-q18-g37.bin \
  --statement-path proof/statement.json \
  --output /tmp/profile23-mainnet-reconstruction.json \
  --compare-substantive \
  evidence/mainnet-sbf-and-instruction-reconstruction.json
```

The live replay is network-bound by archival Solana JSON-RPC access. It
compares two providers' finalized 1,069-transaction buffer histories and raw
transaction bodies, binds every loader write to the exact buffer and
authority, reconstructs the 921,848-byte SBF, and checks the deployment,
tag-65 instruction, proof log, and refund equation.

The `*.raw.public.json` files are derived public copies of the immutable
executor records. Operator-specific filesystem locations were replaced with
bundle paths, and serialized cleanup transaction bytes were omitted. Each copy
records the SHA-256 of its immutable source; `manifest.json` records all source
commitments and transformations.

No signing key, funding operations record, recovery log, serialized signed
transaction bytes, or operator-specific absolute path is included in the text
artifacts. The exact deployed SBF is retained byte-for-byte and may contain
non-secret compiler and toolchain source-path strings.

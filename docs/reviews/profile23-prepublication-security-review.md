# Prepublication security review

*Markdown rendering of the frozen HTML review artifact
([profile23-prepublication-security-review.html](profile23-prepublication-security-review.html),
SHA-256 `86bfa54b18eeff10930cd42485d7652d158395c58b0c2dd899dfbce7a395b09b`).
The HTML file is the artifact of record; the release bundle pins a
byte-identical copy at `review/prepublication-security-review.html` in its
SHA-256 manifest.*

Internal hostile review · 14 July 2026 · Profile 23 q18/g37 mainnet-v1

This review targets the exact release claim, production tag-65 instruction,
transcript/parser boundary, release evaluator, and the public mainnet
evidence. It is an internal engineering review, not an independent external
audit.

> **Disposition:** no exploitable acceptance bypass, signer/owner/PDA
> confusion, account-aliasing route, arithmetic overflow, proof-parser panic,
> PoW downgrade, or trailing-byte ambiguity was found in the released path.
> The artifact is suitable for publication as a research result after the
> corrections recorded below. It is not cleared as a persistent value-bearing
> service.

## Scores

| Dimension | Grade | Basis |
|---|---|---|
| Security | B | All reviewed P0 checks pass and no exploit was found; no external audit or coverage-guided program fuzzing. |
| Correctness | B | Host, local-validator, devnet, and finalized mainnet paths agree; theorem assumptions remain executable evidence rather than machine-checked proofs. |
| Error handling | B | Production paths fail closed and use checked arithmetic; build output retains warning and deprecated-interface debt. |
| Testing | B | Large unit, mutation, release-gate, local-validator, devnet, replay, and mainnet evidence surface; no independent fuzz campaign. |
| Code organization | B | Release modules are separated, but the historical research tree remains large. |
| Documentation | A | Publication paper, release bundle, manifests, reproducible checks, evidence reconciliation, cost ledger, and failure archive are present. |

## Hostile checks

| Boundary | Result | Evidence reviewed |
|---|---|---|
| Authorization | Pass | Proof/refund and payer signer checks; proof/pool program ownership; canonical executable System Program. |
| Account identity | Pass | All unsafe account aliases rejected; canonical nullifier PDA derived from domain, nullifier, and runtime program ID. |
| State transition | Pass | Typed pool/nullifier bytes, sequence overflow check, already-spent rejection, post-CPI recheck, and nonfallible final writes. |
| Rent/refund | Pass | Refund destinations sign, system ownership is checked, balance addition is checked, and the proof receives a tombstone before draining. |
| Proof parser | Pass | Exact q18 header, g37/fold/final work, selector range, complete suffix consumption, and no accepted trailing data. |
| Production dispatch | Pass | Tag 65 calls the production verifier with diagnostic bypass disabled; feature unions that expose diagnostic paths fail closed. |
| Network evidence | Pass | Official mainnet RPC and an independent endpoint agree; the signature is absent on devnet and testnet; proof digest and state changes match. |

## Findings and corrections

### R-01 · Operational correctness · High · resolved

**Finding.** The read-only readiness artifact described per-signed-wire
persistence, restart reconciliation, live fee enforcement, resource lifecycle
tracking, and cleanup-only transitions as though the current top-level
executor implemented them. The executor only bracketed the generic run with
hash-chained top-level checkpoints. A crash after the first mutation could
not be safely resumed through that wrapper.

**Fix applied.** Readiness now exposes `read_only_preflight_green`, states
`readiness_is_execution_attestation=false`, and moves the stronger contract
under `required_future_*` fields. Documentation calls the current journal a
top-level run checkpoint journal. Successful future runs mark that journal
complete. The historical finalized chain evidence was not changed.

### R-02 · Deployment-domain portability · Medium · documented constraint

**Finding.** The statement binds the pool public key, state, and public spend
fields, but not cluster genesis, runtime program address, or SBF identity.
The release certificate binds the frozen SBF separately. The same proof is
valid on every compatible deployment that deliberately clones the
statement-bound values. This is not a replay against one live pool, whose
sequence and nullifier state prevent reuse, but it can become an economic
double spend across linked cloned deployments.

**Fix for this release.** The paper states the portability explicitly and
records that it enabled exact-proof devnet rehearsal followed by mainnet
execution. The demo pool had no redeemable asset. **Required fix before
economically linked deployment:** use independent pool identities or add a
deployment-domain field to pool state and `AtomicPaymentStatementV3`, absorb
it into the transcript, then regenerate the proof and release certificate.

### R-03 · Claim semantics · Medium · resolved

**Finding.** At `T=2^128`, the booked BCS raw-success inequality exceeds one
and is vacuous. Presenting 100.161 bits without naming the normalization
would invite an incorrect standard raw-success interpretation.

**Fix applied.** The theorem, abstract, README, and evaluation identify the
claim as conditional classical-ROM success probability per random-oracle
query. The soundness section now says explicitly that the raw bound is not
booked as the security floor.

### R-04 · Stale q16 comments · Low · resolved

**Finding.** Two production comments still described the q18 path as q16.

**Fix applied.** The comments now say q18. The parser and release gates
already enforced q18, so this did not affect executable behavior.

### R-05 · Independent assurance · Medium · open before value-bearing use

**Finding.** The finite-parameter reduction, state-restoration premise, and
affine-image reconstruction are not formalized in a proof assistant or
independently audited. The program has extensive deterministic and
adversarial tests, but no published Trident or equivalent coverage-guided
fuzz campaign.

**Fix.** Before protecting economic value, commission an independent
cryptographic and Solana-program audit, fuzz every tag-65 account permutation
and malformed proof boundary, and machine-check the state-transition
invariants and finite-field rank/reduction obligations.

### R-06 · Build warning debt · Low · open

**Finding.** The workspace emits deprecated Solana-interface, unexpected-cfg,
dead-code, and private-interface warnings. None reviewed was an executable
release-path defect, but the volume can hide future regressions.

**Fix.** Migrate to the current loader/system interface crates, register the
SBF cfg with Cargo check-cfg, delete or feature-gate retired code, and make
CI deny new warnings once the existing baseline is removed.

### R-07 · Host signing dependencies · Medium · open before another value-bearing run

**Finding.** A 14 July 2026 `cargo audit` scan reports
[RUSTSEC-2024-0344](https://rustsec.org/advisories/RUSTSEC-2024-0344) in
`curve25519-dalek 3.2.0` and
[RUSTSEC-2022-0093](https://rustsec.org/advisories/RUSTSEC-2022-0093) in
`ed25519-dalek 1.0.1`. Both enter through `aspis-xtask -> solana-sdk 2.3.1`;
`cargo tree -i` does not place them in the production verifier's SBF
dependency path, which instead uses patched `curve25519-dalek 4.1.3` and no
`ed25519-dalek 1.x`. The Solana keypair loader recomputes the public key from
the secret and rejects the mismatched keypair needed for RUSTSEC-2022-0093.
The timing issue in RUSTSEC-2024-0344 is present in host signing, but
exploitation requires useful observations over repeated signatures; this
runner is local and finite, not a public signing oracle. The completed payer
is empty and ProgramData is closed. The advisories therefore do not change
signature correctness, the finalized execution, the proof logic, or the
soundness claim, but they remain host-tooling risk before another
value-bearing run. The audit also reports ten allowed unsound, unmaintained,
or yanked transitive-dependency warnings; those are dependency-hygiene work,
not a green supply-chain result.

**Fix.** Before another value-bearing signing run, migrate the host executor
to a Solana SDK/split signer stack that resolves both advisories (including
`ed25519-dalek >= 2` and `curve25519-dalek >= 4.1.3`), rerun the signer and
executor tests, and repeat the dependency audit. Do not suppress these
advisories merely to make the audit command green. A lockfile-only update is
insufficient because the current Solana keypair crate pins the vulnerable
major versions.

## Release evidence

- Release: q18, batch g37, 36/36 gates, 100.161449-bit conditional
  work-normalized floor.
- Proof: 64,447 bytes, SHA-256
  `d4f529964d1cf9ccd9c5568b694796ba54191c6be38d341c66efa08c830cdc3d`.
- Mainnet verification:
  `4Er5afhxfcFmpeTuFqEeNQEbCBri3pkc6ymx7ST5wfNpSBYwQDHA9DtCuDBpD5WuEDXs7ozL3sK5msc6QWE4q9Fo`,
  slot 432933949, 1,343,749 CU.
- Demo-payer cost after refunds: 14,883,400 lamports; 6,985,137,600 of the
  7 SOL funding transfer returned to its source. The source-paid inbound
  funding fee is outside that figure.
- Versioned bundle verifies content hashes and excludes keypairs, signed
  cleanup wire bytes, recovery logs, and local secret-bearing manifests.

## Final decision

The exact, narrowly scoped research claim is publication-ready once the
versioned bundle's final hashes pass. No unresolved finding invalidates the
finalized mainnet execution or the conditional work-normalized theorem as
written. R-02, R-05, and R-07 block treating this artifact as authorization
for a value-bearing production service without another protocol/review
cycle.

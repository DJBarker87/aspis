# V7 eight-lane strict combined TxV1 harness

This directory executes one real top-level eight-lane Pool private transfer
through the selected Tag-73 verifier CPI and the final Pool settlement. It is a
single transaction, not a component sum:

```text
TxV1 -> Pool ASQ8 -> registry/entry authentication -> selected verifier
     -> exact ASR8 -> lane/history/nullifier settlement
```

The selected fixture is the 30,720-byte strict-work canonical-fixed proof with
frontier 201. All
three production 35/31/34-bit work checks execute; there is no threshold bypass.
The Pool begins with 13 populated pairs in lane 3. A successful run checks the
exact 792-byte ASR8, exact next lane/history/marker images, and byte-exact
preservation of master, checkpoint, registry, entry, and proof accounts. A
failed run checks byte-exact rollback of every protected account and empty
return data.

## Exact current measurements

All compact-request rows use the same deterministic 13-pair populated lane,
strict fixture and 799-byte `VersionedMessage::V1` packet. The final row was
executed with the real 1,400,000-CU runtime limit, not an oversized diagnostic
budget.

| Variant | Proof bytes | TxV1 bytes | Verifier CPI CU | Combined CU | Delta from V0 |
|---|---:|---:|---:|---:|---:|
| V0 compact packed | 30,400 | 799 | 1,970,586 | 2,069,373 | baseline |
| canonical fixed, exact-once | 30,720 | 799 | 1,813,655 | 1,912,443 | -156,930 |
| + immutable six-account lane invariant | 30,720 | 799 | 1,353,473 | 1,452,893 | -616,480 |
| + packed digest selector | 30,720 | 799 | 1,310,134 | 1,409,554 | -659,819 |
| + exact ASR8 reuse/direct binding | 30,720 | 799 | 1,310,134 | 1,400,108 | -669,265 |
| + binary Copy weights (selected) | 30,720 | 799 | 1,296,770 | **1,386,744** | **-682,629** |

The selected path has **13,256 CU** of headroom under 1.4M and **3,297
bytes** of headroom under the 4,096-byte TxV1 target. The exact accepted result
is `evidence/strict-vc-exact-once-6acct-invariant-packed-direct-result-copy-weight-txv1-runtime1400000.json`.

The two 469k blocks were duplicated 20-parent Poseidon reconstructions:

- before CPI, recomputing the Pool-owned persisted lane root from its frontier;
- after CPI, recomputing the proof-authenticated next root from the exact ASR8
  frontier.

The invariant path does not trust caller bytes. It retains owner, writable,
signer, PDA, length, magic/version/format, master/lane, canonical digest,
index/capacity, inactive-frontier, genesis, retained-history, and exact ASR8
checks. It omits only active root/frontier recomputation under the Pool's
inductive write invariant. The verifier independently authenticates the two
Pool registry accounts, rooted in audit-build immutable Pool/registry/policy
constants. No new top-level meta or transaction byte is required. Production
activation is restricted to freshly initialized lane PDAs written only by the
proved initialize/deposit/terminal paths; there is no unchecked migration
claim.

The selected verifier also uses three default-off, algebraically equivalent
optimisations: canonical fixed fields with exactly-once query canonicality,
four digest lanes packed before their common selector, and binary generated
Copy weights specialized to skip/add. The Pool reuses the exact canonical ASR8
bytes returned by the authenticated verifier and performs the equivalent
field-wise result binding instead of rebuilding an ASF8 object.

## Instrumented phase ledger

The earlier V0 profile build adds checkpoint overhead and consumes more than
the uninstrumented path. Successive Pool checkpoints identified the duplicated
root reconstruction and result-object work:
Successive Pool checkpoints report:

| Interval | CU |
|---|---:|
| entry to request decoded | 1,220 |
| master decoded | 4,263 |
| checkpoint decoded | 3,749 |
| invariant lane decoded | 4,194 |
| request/account binding | 2,184 |
| layout and retained-history binding | 50,517 |
| marker planning | 3,655 |
| transfer withdrawal-plan no-op | 214 |
| verifier CPI body | 1,970,586 |
| result semantic binding | 7,514 |
| invariant next-lane encoding | 2,809 |
| ASR8 encoding | 2,482 |

CPI setup/return and log syscalls account for the remaining difference. The
uninstrumented 2,069,373-CU row is the release-relevant total.

## Harness use

```text
aspis-v7-pair-forest-combined-rejection \
  <aspis_pool.so> <aspis_verifier.so> <evidence.json> \
  <proof-body-or-payload.bin> <success|failure> [runtime-compute-limit] \
  [asq8|asf8]
```

The input can be either the proof body alone or the complete payload excluding
the 40-byte `ASPU` account header. For a body, the harness supplies the exact
688-byte authenticated candidate-afterstate prefix. Thus a later honest proof
fixture can be swapped in without changing harness source.

The `transcode_vc` helper converts the selected packed proof's 641 fixed QM31
values to the experimental +320-byte canonical representation while copying
the authenticated tail byte-for-byte:

```text
transcode_vc <packed-proof.bin> <canonical-proof.bin> <frontier-nodes>
```

## Selected build and replay

The selected source chain ends at `6045276e`, including Pool commits
`e86d48cc` and `d14ea1b1`. Build the two programs with these exact default-off
feature sets:

```text
cargo build-sbf --manifest-path programs/aspis-pool/Cargo.toml \
  --features pair-forest-source-result-invariant-audit,pair-forest-verifier-lane-invariant-audit,pair-forest-direct-result-audit \
  --sbf-out-dir <artifact-dir>

cargo build-sbf --manifest-path programs/aspis-verifier/Cargo.toml \
  --features v7-pair-forest-fixed-canonical-exact-once-audit,v7-pair-forest-lane-invariant-audit,v7-pair-forest-packed-digest-audit,v7-pair-forest-binary-copy-weights-audit \
  --sbf-out-dir <artifact-dir>
```

Replay the exact deployable-limit measurement:

```text
cargo run --release \
  --manifest-path results/v7-pair-forest-combined-rejection-litesvm-20260828/harness/Cargo.toml -- \
  <artifact-dir>/aspis_pool.so \
  <artifact-dir>/aspis_verifier.so \
  <new-evidence.json> \
  results/v7-pair-forest-combined-rejection-litesvm-20260828/evidence/v7-pair-forest-transfer-strict-work-canonical-fixed.bin \
  success 1400000 asq8
```

Selected frozen hashes:

| Artifact | SHA-256 |
|---|---|
| Pool SBF | `62509dd10f735bdd207370813352b62d02cb0e02b80eae5640bee7c2282826b5` |
| Verifier SBF | `b3e4bac791651c37c9bf148827f90a7bb17b8a622ee1e6fb2291614efbde4843` |
| Strict canonical proof | `ce2aa9bcb2fa4eed70f0f1f09befd656e5146e2208bd590c07c348d7dff2cfe3` |

## Boundaries

- Runtime: deterministic local LiteSVM 0.16.0; no RPC, devnet, mainnet,
  deployment, signing service, or external state mutation.
- Transaction: true TxV1, 799 serialized bytes, 3,297 bytes of headroom to
  4,096.
- CU above 1.4M is diagnostic evidence only, never a deployability claim.
- This harness changes no cryptography and contains no threshold bypass.
- The six-account invariant and arithmetic variants are audit-only features.
  The build pins deterministic audit IDs; generated deployment IDs and the
  corresponding source/formal bridges are required before activation.
- This isolated branch predates the main worktree's lifecycle stack cleanup.
  Its Pool build log still flags init/deposit frames, although the exercised
  terminal path is frame-safe. The final release binary must be rebuilt from
  the integrated stack-clean source and reproduce this measurement.

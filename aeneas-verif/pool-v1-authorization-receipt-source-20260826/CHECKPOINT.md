# Pool V1 authorization-receipt encoder source checkpoint

This checkpoint links the exact extracted production function
`encode_pool_v1_authorization_receipt_v1` to
`AuthorizationReceiptAccountWireV1.encodeWireReceipt`.  Its proof includes
the exact transitive source equality for `encode_verifier_dispatch_result_v1`.

## Pinned inputs

- Rust repository revision: `6f1abc0bb514e36d308c37bda56c353edaeeb637`.
- `authorization_receipt.rs` at that revision: SHA-256
  `512e7a02f3f8718d520e8c9ff4445f0e691039841cc72ade9f02c21d861225f3`.
- `verifier_dispatch.rs` at that revision: SHA-256
  `fbfa90d9d8de5a36b476786132c52f7c64ee7b75a5ec3a89ea0c18d76e77c8bb`.
- Charon revision: `cb50ff16f4e4f5951e7c94503f8f18544355dd64`.
- Aeneas revision: `d860ac475a9fca81de8b77d861d879fc90a8ef06`.
- Extracted root: public `encode_pool_v1_authorization_receipt_v1`, which
  transitively contains `encode_verifier_dispatch_result_v1`.
- Extracted production spans: binding-field encoder
  `verifier_dispatch.rs:240:0-271:1`, binding validation
  `verifier_dispatch.rs:117:0-147:1`, and dispatch-result encoder
  `verifier_dispatch.rs:436:0-448:1`, plus authorization-receipt encoder
  `authorization_receipt.rs:72:0-91:1`.

The formal target pins the ASVS byte layout, including magic `ASVS`, offsets
`0,4,5,6,7,8,12,13,16,48,80,112,144,176,184,216,248,280,312,344,376,380,384`,
little-endian integer encoding, transition discriminants, the canonical M31
digest limbs, and all 32-byte binding fields. Receipt SHA domains and PDA seed
order remain in the already-checked wire model.  The outer source proof now
also pins the ASVA magic/version/hash/status bytes, verified-slot LE64 field,
dispatch splice at `[16,400)`, digest splice at `[400,432)`, and the SHA-256
callback's exact two-slice input order `[receiptDigestDomain,
authorizationReceiptPrefix]`.  `GeneratedSha256Matches` is the explicit SHA
implementation boundary: the proof assumes only that a successful extracted
callback output agrees with `Sha256` on the concatenation of those supplied
slices.  It does not assume or claim a SHA implementation theorem.

## Checked declarations

The terminal theorem is `encode_receipt_source_exact`. Its local chain includes
`encode_dispatch_result_source_exact`, exact U32/U64 byte conversion,
header/scalar writes, all fourteen binding-field writes, totality of the
generated eight-limb digest loop, successful binding validation consequences,
the exact ASVA header and dispatch/digest slices, exact SHA preimage equality,
and final 432-byte output-array normalization.

There are no `sorry`, `admit`, project axioms, or conclusion-shaped premises.
The generated external file contains only transparent definitions for slice
iteration, the M31 modulus constant, and M31 little-endian bytes.

Focused NUC gate `aspis-receipt-outer-checkpoint-v2` passed with one Lean
thread, `MemoryMax=14G`, `MemorySwapMax=0`, 36.65 seconds wall time,
7,284,492 KiB peak RSS reported by `/usr/bin/time`, and zero job swap.
Every printed theorem depends only on Lean/Mathlib foundations:
`propext`, `Classical.choice`, and `Quot.sound` (the first small byte theorem
does not need `Classical.choice`; `take392_append_exact` needs only `propext`).

## Artifact hashes

- `extraction/AuthorizationReceiptEncoder.llbc`:
  `7824e20e95bef1697670984cd67c8c5a5ca56c70720ebd4b329c7bb28dd4ba32`.
- `generated/AuthorizationReceiptEncoder/Types.lean`:
  `463bcb248c64df9a330d106a58545ec1d7e7892b523ef5f3645a23497e4de93f`.
- `generated/AuthorizationReceiptEncoder/Funs.lean`:
  `74a6ae06ac283cbe98f0f019ab2c5eac0df5790b866f7e894b9c1f200e9ed5ff`.
- `generated/AuthorizationReceiptEncoder/FunsExternal.lean`:
  `c4a93b8ba69fd8f34f62ed4749b1ffcc4b4b9d62fce9e9a4161310ef6578471a`.
- `proof/AuthorizationReceiptEncoderSourceBridge.lean`:
  `93ab3fc30cb26c71578e50cafa0e43a8f1571b1e387f265dd323daa7fccd6af0`.

The smallest remaining source-equality boundary is the request/account/PDA
wrapper around this receipt encoder.  Those encoders require subsequent
separately extracted roots; none is claimed by this checkpoint.

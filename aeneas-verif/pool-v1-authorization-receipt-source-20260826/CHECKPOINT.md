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

## Binding-digest source checkpoint

The next bounded root is the exact public production function
`pool_v1_authorization_receipt_binding_digest_v1` at
`authorization_receipt_account.rs:200:0-212:1`, including the binding-digest
domain constant at `authorization_receipt_account.rs:67:0-68:54` and the
transitive dispatch encoder described above.  The account source at the pinned
Rust revision has SHA-256
`132b264453c4d3c286b4d39f92b132c8e662495f809ff2ad57559d37098245cf`.

The terminal theorem is `binding_digest_source_exact`.  From a successful
generated execution it proves that the returned 32-byte array is exactly
`bytes32List (sha256 (wireBindingDigestPreimage binding))`.  Its local bridge
pins the callback's exact two-slice input order to
`[bindingDigestDomain, encodeWireDispatchResult binding]`.  The only external
boundary is `GeneratedSha256Matches`: a successful generated callback result
must equal the abstract `Sha256` value on the concatenation of the slices
actually supplied by Rust.  No Solana/PDA, Poseidon, or circle assumption is
used by this root.

The focused theorem inventory is:

- `binding_digest_domain_generated_exact`;
- `binding_digest_preimage_source_exact`;
- `binding_digest_source_exact`;
- the transitive dispatch chain ending in
  `encode_dispatch_result_source_exact`, including exact scalar encoding,
  binding-field writes, validation, and canonical M31 digest-loop totality.

Charon gate `aspis-receipt-binding-charon-v3` passed from the pinned committed
source tree with `--start-from
crate::pool_v1::authorization_receipt_account::pool_v1_authorization_receipt_binding_digest_v1`,
one Cargo job, `MemoryMax=14G`, `MemorySwapMax=0`, 8.80 seconds wall time,
489,880 KiB peak RSS, and zero swap.  Aeneas gate
`aspis-receipt-binding-aeneas-v1` passed in 1.02 seconds with 241,960 KiB peak
RSS and zero swap.  The normalized generated `Types`, transparent external
definitions, and `Funs` each passed Lean 4.32 gates
`aspis-receipt-binding-{types,external,funs}-v4` with zero swap.  Their peak
RSS values were 2,510,564 KiB, 2,499,740 KiB, and 2,531,140 KiB respectively.

Focused proof gate `aspis-receipt-binding-proof-v4` passed with one Lean
thread, `MemoryMax=14G`, `MemorySwapMax=0`, 32.90 seconds wall time,
7,213,532 KiB peak RSS reported by `/usr/bin/time`, and zero swap.  All sixteen
printed declarations depend only on `propext`, `Classical.choice`, and
`Quot.sound`; `byteOfGenerated_toNat` needs only `propext` and `Quot.sound`.
There are no `sorry`, `admit`, project axioms, conclusion-shaped premises, or
`#exit`.

The raw Aeneas output hashes for `Types.lean` and `Funs.lean` are respectively
`68aae987513fd1fe63fa798aac25b87c0b712410f7df7f0dcb91aa92835b8722`
and `e6c825336506ab36207ddf5603347db0703a1442636496a27ce6fd151c0190cc`.
The tracked Lean 4.32 normalization changes only their generated `import
Aeneas` line to the same scoped `Aeneas.Std`, discriminant, and Rust-attribute
imports used by the preceding receipt checkpoint; reverse-normalizing those
lines reproduces the two raw hashes exactly.

### Binding-digest artifact hashes

- `extraction/AuthorizationReceiptBindingDigest.llbc`:
  `9f29d671662844090d98681f76924bf77daf4d187acc0a6f5660bc71c8963b11`.
- `generated/AuthorizationReceiptBindingDigest/Types.lean`:
  `dba3111f2733e4627b72e04cf9d1e83cfd0af1479785058d7eecc1685a90d660`.
- `generated/AuthorizationReceiptBindingDigest/Funs.lean`:
  `f33b18241deb879bc82647b5ba0ae9c01560db66cdb021cfec2a213a810397f4`.
- `generated/AuthorizationReceiptBindingDigest/FunsExternal.lean`:
  `dbb4e90df9e16aa8ea7c3b00a6037d5de9334a743286dcb40f17fd3ad76cb860`.
- `proof/AuthorizationReceiptBindingDigestSourceBridge.lean`:
  `b31e78d2a4448c41f09fbe06a12a1a5aaec2468da0213959d119525320dcd155`.

The smallest remaining production source-equality boundary is
`pool_v1_authorization_receipt_pda_inputs_for_binding_v1` at
`authorization_receipt_account.rs:225:0-236:1`, together with
`PoolV1AuthorizationReceiptPdaInputsV1.dynamic_seeds` at lines 103:0-113:1.
It is now a small constructor theorem over this checked binding digest and
will pin the dynamic seed order `[proof_account, statement_digest,
binding_digest]` with the bump kept separately.  The separately hashed request
digest root at lines 214:0-223:1 remains the next prerequisite for pending and
finalized account-image construction.

## PDA-input constructor and dynamic-seed source checkpoint

This checkpoint combines exactly two independently named Charon start roots in
one extraction so both declarations share the same generated
`PoolV1AuthorizationReceiptPdaInputsV1` type:

- public `pool_v1_authorization_receipt_pda_inputs_for_binding_v1` at
  `authorization_receipt_account.rs:225:0-236:1`;
- public `PoolV1AuthorizationReceiptPdaInputsV1::dynamic_seeds`, whose impl
  spans lines 103:0-113:1 and whose function body spans lines 106:4-112:5.

The terminal constructor theorem is
`pda_inputs_for_binding_source_exact`.  A successful extracted call maps to
the formal `PdaInputs` record with the exact proof-account and statement-digest
copies, the supplied bump, and the SHA-256 binding digest proved by the
preceding source chain.  The formal conversion adds only the already-frozen
static seed string `aspis-verify-receipt-v1`; Rust deliberately returns that
static prefix out of band.

`dynamic_seeds_source_exact` proves that the extracted fixed
`[[u8; 32]; 3]` method returns exactly
`[proof_account, statement_digest, binding_digest]`.  The combined theorem
`pda_dynamic_seeds_source_exact` composes the two production roots and proves
that their returned list is exactly `wirePdaDynamicSeeds sha256 binding` in
that order.  The proof does not model or assume Solana address derivation or
curve rejection.  Its only external boundary is the same explicit successful
SHA callback equality used by the binding-digest checkpoint; no Poseidon or
circle boundary is present.

Charon gate `aspis-receipt-pda-charon-v1` passed from the pinned committed
source using these two exact start roots, one Cargo job, `MemoryMax=14G`,
`MemorySwapMax=0`, 8.56 seconds wall time, 494,032 KiB peak RSS, and zero swap.
Aeneas gate `aspis-receipt-pda-aeneas-v1` passed in 1.07 seconds with
234,632 KiB peak RSS and zero swap.  Lean 4.32 gates
`aspis-receipt-pda-types-v1`, `aspis-receipt-pda-external-v2`, and
`aspis-receipt-pda-funs-v1` all passed with zero swap and peak RSS values
2,478,332 KiB, 2,454,044 KiB, and 2,495,056 KiB respectively.

Focused proof gate `aspis-receipt-pda-proof-v3` passed with one Lean thread,
`MemoryMax=14G`, `MemorySwapMax=0`, 44.51 seconds wall time, 6,367,436 KiB
peak RSS reported by `/usr/bin/time`, and zero swap.  All twenty printed
declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`;
`byteOfGenerated_toNat` and `bytes32List_injective` omit
`Classical.choice`.  There are no `sorry`, `admit`, project axioms,
conclusion-shaped premises, or `#exit`.

The raw Aeneas hashes for `Types.lean` and `Funs.lean` are respectively
`d8da61642fd0e9cce50f1dbb110cbf9ddf1ee9a6994fb818c6f1ce22493d9c53`
and `c8410109368a52fe7d51f416108496d8bff480c197efc22506ea9e95f6ae51e1`.
Reverse-normalizing the scoped Lean 4.32 import lines reproduces both raw
hashes exactly.

### PDA-input artifact hashes

- `extraction/AuthorizationReceiptPdaInputs.llbc`:
  `46edecba07a8a5305414c73b5b7d8441dee2e8c6cc0032f9067663a573c2930c`.
- `generated/AuthorizationReceiptPdaInputs/Types.lean`:
  `45361aa7ca0e1606257af7ee6e287c19698bf865f7869856b0f185be058e651b`.
- `generated/AuthorizationReceiptPdaInputs/Funs.lean`:
  `872d64f30de7ce6fb3353ffd3799702cee2594706668d378b795fe7992f45280`.
- `generated/AuthorizationReceiptPdaInputs/FunsExternal.lean`:
  `e8fb4166f5f095404a9ad091e983ff160d50d0910b7ab6b545eab8061903e8d5`.
- `proof/AuthorizationReceiptPdaInputsSourceBridge.lean`:
  `7c646e32f90a051dc06aa3cf5cfae60247ae28371b0ccd4762c2a9942199e295`.

The smallest remaining production boundary is the separate public
`pool_v1_authorization_receipt_request_digest_v1` root at
`authorization_receipt_account.rs:214:0-223:1`.  It transitively contains the
variable-length ASVQ request encoder and its SHA callback and is intentionally
excluded from this checkpoint.

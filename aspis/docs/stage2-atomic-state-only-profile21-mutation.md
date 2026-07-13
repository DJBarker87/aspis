# Atomic state-only profile 21 mutation closure

Status: implementation wired; literal proof fixture and on-chain measurement pending.

This note freezes the account-transition wrapper around the single integrated
profile-21 proof parser. It does not splice profile-20 and masked-switch proof
bytes, and it does not treat a CU projection as an integrated result.

## Append-only instructions

- Tag 50, `VerifyAtomicStateOnlyProfile21V3`, is read-only. Its diagnostic bit
  changes only the transcript-bound PoW predicate.
- Tag 51, `ApplyAtomicStateOnlyProfile21V3`, is the production mutation wire.
  It has no diagnostic bit. Default builds return
  `ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED` before account access.
- Tag 52, `MeasureAtomicStateOnlyProfile21MutationV3`, exists only in the
  nondefault local-validator feature
  `diagnostic-unmined-profile21-mutation`. It uses the exact tag-50 parser and
  may bypass only PoW.

The production candidate feature is `profile21-mutation-candidate`. Enabling
it does not make an unmined fixture production-valid: tag 51 invokes the
no-bypass verifier and must reject before the first CPI or account write.

## Frozen algebra and proof seam

The wrapper hard-binds the shared q16 logical-to-natural basis fingerprint
`0xceb35dd3ee50e051` both at compile time and at the verifier call boundary.
It imports the generated basis from `aspis-core`; it defines no second
transform.

All three instructions call one profile-21 parser/verifier API over one proof
byte string. The statement is reconstructed from the pool key, pool sequence,
current anchor, nullifier, output commitment, output anchor, asset id, and fee.
No out-of-band terminal or masked-switch claim enters the acceptance predicate.

## Mutation ordering

The existing atomic kernel remains the only mutation implementation:

1. Validate the proof, pool, canonical nullifier PDA, payer, and System Program.
2. Decode the current pool and reject a spent or malformed marker.
3. Reconstruct and hash the exact atomic statement.
4. Verify the complete profile-21 proof.
5. Create the marker PDA only when it was absent and System-owned.
6. Reborrow and recheck both mutable accounts.
7. Copy the final marker and next pool images with no fallible operation after
   the first copy.

Thus proof, PoW, statement, and account failures occur before mutation.
Solana writable locking on both pool and nullifier PDA serializes races.

## Required literal artifact

`stage2-atomic-profile21-mutation` consumes the exact proof SHA and tag-50 CU
from `atomic_state_only_profile21_acceptance.json`, then measures both:

- a program-owned, correctly sized, zeroed marker; and
- canonical zero-lamport System-owned PDA creation.

Each path emits an overlap-free ledger containing transaction setup, account
validation, statement decode/digest, the exact profile-21 verifier, marker
preparation/CPI, mutable-state recheck, final writes, and post-marker return
work. The bucket sum must equal the transaction simulation total.

The teeth are: corrupted-proof rollback; exact one-step pool sequence and
anchor update; exact marker bytes; duplicate rejection without a second write;
production tag-51 rejection of the unmined proof without mutation; and a
two-signer System-path race in which exactly one transaction commits.

## Production gate

CU fit is necessary but insufficient. Tag 51 remains disabled in default
builds until all of these are independently green:

- the literal tag-50 integrated verifier and proof KAT;
- the profile-21 soundness reduction in the selected q16/rate-1/512 regime;
- the complete-view HVZK simulator, including proof bytes and public receipt;
- private-leaf commitment binding and mask-generation assumptions;
- production PoW for the final proof; and
- both literal mutation paths and every rollback/race tooth above.

The measurement artifact records the soundness and privacy booleans but cannot
override them.

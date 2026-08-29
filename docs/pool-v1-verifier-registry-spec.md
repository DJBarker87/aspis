# Pool V1 verifier-registry specification

Date: 25 August 2026

Status: P0 base-format/read-only authorization, the P3c/P3d verifier-dispatch
byte/planning contract, the P3e library-only read-only CPI/capture source and
the P3f selected-verifier handler for the frozen same-path Tag-73 profile are
implemented. The first P3f SVM attempt failed before handler entry and did not
close the CU/return-data gate. Future Pool historical/P4 profile semantics, SVM integration/CU
evidence, registry governance and atomic source/runtime composition remain
open and are not yet security-claimed.

## Decision

Pool V1 must not embed one exact verifier release in the append-only pool
state. Doing so would require a state migration or a second tree when a later
proof profile is admitted, contradicting the requirement that V7, V8 and later
profiles share one asset pool, vault and anonymity set.

The 104-byte draft `VerifierBindingV1` state slot is therefore a provisional
format and must be replaced before P0/P1 are frozen by a stable
`VerifierPolicyV1`:

```text
magic/version/flags/reserved     8 bytes
registry program                32 bytes
registry authority              32 bytes
policy binding                  32 bytes
                              --------
                                104 bytes
```

The policy binding commits the registry format, activation/revocation rules,
statement fields and verifier-result interface. It is not an individual proof
release hash. The current implementation authenticates this 32-byte value but
does not derive it from, or compare it with, a canonical launch-policy manifest
preimage. The value alone therefore does not enforce the intended governance,
upgradeability or verifier-result rules.

## Canonical accounts

One registry is derived for each pool:

```text
[b"aspis-verifier-registry-v1", pool]
```

One entry is derived for each exact profile and release:

```text
[b"aspis-verifier-entry-v1", pool, profile_binding, release_binding]
```

Every registry and entry load must check the owning program, exact PDA,
discriminator, version, byte length, reserved bytes and pool identity.

An entry contains at least:

```text
pool
verifier program
profile binding
release binding
statement version
activation slot
optional retirement slot
active/paused state
```

Adding or retiring an entry changes no pool identity, note commitment,
nullifier, tree node, historical root or vault account.

## Runtime acceptance order

Before invoking a verifier or applying a spend, the pool program must:

1. authenticate the canonical Pool state and registry policy;
2. derive and authenticate the exact registry-entry PDA named by the spend;
3. require an active entry for the supplied verifier program, profile and
   release at the current slot;
4. require the proof statement/transcript to bind the pool address, deployment
   domain, asset, statement version, verifier program, profile and release;
5. invoke only that verifier implementation and authenticate its exact success
   result, including the returning program id for CPI return data; and
6. only then reserve the nullifier and apply the bound Pool transition.

No public raw-append path may exist. A registry entry authorizes a proof
implementation, not arbitrary state writes.

## Governance and continuity

Registry mutation is a security authority and must be explicit. The launch
policy must use a multisig and a nonzero activation delay for new verifier
entries. Emergency pause and retirement rules must be documented, monitored
and included in the policy binding.

Retiring a release must not strand notes. At least one active verifier must
accept the frozen Pool V1 note/nullifier/tree formats and the same spend
relation before an older entry can be retired. Because notes do not encode a
verifier version, any active compatible verifier can spend any valid Pool V1
note.

## Formal obligations

The pure model must prove:

```text
accepted_entry_is_exact_and_active
accepted_spend_binds_entry_and_pool
adding_profile_preserves_pool_identity
adding_profile_preserves_tree_and_vault
retiring_profile_does_not_reinterpret_existing_state
no_registry_entry_implies_no_spend_state_change
```

The source bridge must cover PDA derivation, account parsing, slot checks,
verifier dispatch/result authentication and fail-closed control flow. Registry
governance, program upgradeability and CPI/runtime correctness remain named
trust boundaries unless separately discharged.

The implemented authorization slice covers canonical PDA derivation,
read-only owner/type/version/length/reserved-byte parsing, mutable/immutable
authority consistency, registry pause, the entry active interval and exact
verifier/profile/release/statement selection. It deliberately does not create
or mutate registry accounts, enforce activation delay at governance time,
authenticate registry-program upgrade authority or bind `policy_binding` to a
canonical policy manifest. P3e now supplies a separate read-only CPI/result
source path, but the selected verifier handler and atomic state composition
remain P3 obligations. Governance items remain P7 obligations.

P3c/P3d freeze an `ASVQ` image comprising a 384-byte binding prefix plus
the exact `1..640` byte profile-specific statement payload, and an exact
384-byte `ASVS` success image. Bytes 380..384 of both prefixes carry the
payload length; `ASVS` echoes the length and derived digest but not the payload.
The Pool computes the statement digest from the frozen v1 domain, selected
profile/release, exact payload length and exact payload bytes; a caller cannot
supply a separate digest. The slice checks the selected executable-program and
sealed proof-account identities/owners/privileges, and provides a pure
authenticator for an already-snapshotted return-data `(program_id, bytes)`
pair. The result repeats every request binding and uses exact success code
`0x41530001`. Payload semantics remain profile-dispatched: neither the current
same-path Tag-73 payload nor a future 1-to-2 relation is silently assigned the
historical Pool profile. Payload substitution reduces to the explicit approved
SHA-256 collision boundary; hash injectivity is not assumed.

P3e constructs that plan locally, rechecks the actual verifier/proof account
identities and privileges, and invokes only the selected verifier. Its exact
instruction meta list is one nonsigning read-only proof account; the CPI info
list adds only the executable verifier program account. It explicitly clears
Pool return data, performs CPI and captures return data on the next operation,
then authenticates the exact writer and ASVS bytes. Missing data, a callee
error, wrong writer and any changed result fail closed. No Pool, registry,
marker, tree, vault, proof or verifier account is written, and the path has no
public entrypoint.

P3f adds an opt-in verifier-side ASVQ handler only for the already-frozen
same-path Tag-73 `AtomicPaymentStatementV4` relation. It does not claim the
Pool historical-anchor relation or future P4 1-to-2 semantics. The exact
392-byte profile is frozen in `docs/pool-v1-v7-tag73-readonly-profile.md`; it
checks an exact-size sealed proof account, recomputes every derivable digest
and emits ASVS only after full verification. Loader code/upgrade authenticity,
successful real SVM return-data behavior/CU, future profile semantics and atomic
composition with nullifier/output/vault writes remain open.

## Compute gate

The final architecture may use an in-program versioned verifier branch or CPI
to an allowlisted verifier program, but it must be measured with the complete
append/nullifier/token transition. The current V7 transaction has only 42,041
CU of preferred 1.3M headroom, so registry lookup, CPI and append-only Poseidon
work cannot be assumed to fit. If the full atomic path exceeds the hard Solana
limit, verification receipts and settlement become an immediate architecture
requirement rather than a later throughput optimization.

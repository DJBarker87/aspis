# Aspis Pool V1 operator runbook

Date: 25 August 2026

Status: pre-mainnet draft. This runbook does not authorize deployment or any
mainnet transaction.

## Fixed roles and separation

- The verifier-registry authority is a threshold multisig address. No relayer,
  indexer, RPC credential or hot fee payer may control it.
- The Pool and registry program upgrade authorities are separately recorded in
  the signed deployment manifest. A frozen launch sets them to the reviewed
  governance choice; an immutable launch records the absence of an authority.
- The relayer fee payer is a low-balance operational signer. It cannot mutate
  the registry and is never accepted as wallet viewing or spending material.
- The finalized indexer is read-only. Its durable public cursor contains no
  viewing key, spending key, note opening or ciphertext.

## Startup gate

An operator must refuse startup unless all of the following agree with one
signed release manifest:

1. cluster genesis hash and RPC endpoint set;
2. Pool, registry and selected verifier program ids;
3. deployed loader identities, executable hashes and upgrade authorities;
4. Pool format, deployment domain, asset mint/id and canonical vault PDA;
5. registry policy binding, authority, generation and activation delay;
6. an active, nonretired entry for the exact profile/release/statement version;
7. the local relayer-policy id, operator fee payer and minimum reserve;
8. finalized indexer checkpoint, Pool-state SHA-256 and root sequence; and
9. the final reproducible-build and devnet-lifecycle evidence hashes.

The process remains paused when any value is absent, supplied at less than
finalized commitment, or differs between configured providers. Mainnet startup
also requires the user's separate explicit authorization after every technical
gate has closed.

## Relayer admission

For every unsigned request, the service must:

1. fetch and canonically decode a finalized Pool state;
2. construct `RelayerSnapshotV1` from its slot, root sequence and exact account
   SHA-256;
3. rebuild the instruction with `validate_pool_instruction_v1`;
4. derive the request id and apply `admit_relayer_plan_v1`;
5. atomically persist the request id, policy id and returned rate-window
   transition before invoking a signer;
6. simulate the exact assembled transaction against the pinned program ids;
7. sign only if the simulation succeeds within the release CU/fee limits; and
8. reconcile the exact signature through finalized confirmation or a recorded
   terminal failure.

Duplicate request ids are idempotent. A different request under an existing
id, a stale/future snapshot, policy mismatch, queue/inflight saturation,
rate-window exhaustion, fee-cap violation or insufficient post-fee reserve is
a hard rejection. Per-origin/IP abuse controls are additional privacy-aware
service policy; they never replace the global library gate.

## Native proof authorization sequence

For a private transfer or withdrawal, use the shared native Tag-73 profile and
execute the unsigned builder outputs in this order:

1. create the exact `40 + proof_body_length` verifier-owned proof account;
2. initialize its `ASPU` header and upload every ordered 960-byte chunk;
3. initialize the canonical pending authorization receipt with Tag 74 while
   the upload authority is still present;
4. seal the proof account with Tag 62;
5. run Tag 75 with the identical 600-byte `ASVQ`, producing a finalized
   verifier-owned receipt only after full proof acceptance;
6. pass that exact receipt address into `ASPP`, then execute or cancel the
   state-bound prepared plan; and
7. close/refund the proof and receipt only when their evidence-retention policy
   permits it. Receipt closure must not precede the Pool call that consumes it.

Every transaction must be simulated before signing. A request/profile/release,
proof account, body digest/length, statement kind, receipt PDA, upload authority
or pending-image mismatch is terminal; operators must rebuild from authenticated
inputs rather than edit bytes or retry under a compatibility profile.

## Registry governance sequence

Registry instructions must come from the exact unsigned governance builders.
Initialize with the signed policy binding and nonzero activation delay, schedule
the pinned native Tag-73 profile/release, wait through that on-chain delay, and
activate only after the release evidence is complete. Release rotation schedules
and activates a same-profile replacement before retiring the old release.
Pause/unpause and freeze use the stored generation exactly; stale generations
are never automatically retried. Freeze is irreversible and must follow the
Pool-policy coordination rule in the registry program's release documentation.

## Required monitoring

Alert and automatically pause new signing on:

- finalized-slot lag or a skipped/unavailable backfill range;
- provider disagreement in blockhash, transaction bytes, loaded addresses,
  Pool account hash, root page or deployed program bytes;
- an indexer root/cursor mismatch or rollback deeper than the retained window;
- registry generation, pause state, authority, policy binding or selected-entry
  drift;
- unexpected program upgrade/loader state;
- a simulation/execution result mismatch, CU regression, missing/wrong return
  data or any successful transaction whose receipt cannot be authenticated;
- fee-payer reserve below policy, sustained queue/inflight saturation, or
  abnormal rate-limit/duplicate/nullifier rejection rates; and
- vault balance disagreement with authenticated deposits and withdrawals.

Monitoring records contain public ids, slots, hashes, decision codes and
amounts only. They must never log viewing/spending keys, plaintext openings,
HPKE randomness or decrypted note payloads.

## Incident actions

1. Pause the local relayer immediately; do not delete queued requests, proofs,
   scan checkpoints or evidence.
2. Stop registry activation/retirement operations and notify the registry
   multisig signers through the independent incident channel.
3. Record the last agreed finalized slot, Pool/root-page hashes, registry
   generation, program hashes, transaction signatures and policy id.
4. Determine whether the fault is RPC/indexer-only, relayer-only, a registry
   selection fault, a deployed-program mismatch or an accepted invalid state
   transition.
5. For a retained Solana fork, apply the indexer's exact rollback ids and
   cursor rollback atomically with note-store invalidation, then backfill from
   the common ancestor.
6. Resume only after two configured providers agree, the complete startup gate
   passes again and the incident disposition is signed. A cryptographic or
   deployed-program fault requires a new reviewed release; it is never cleared
   by an operator override.

## Verifier release continuity

New entries are scheduled no earlier than the registry's nonzero activation
delay. Retirement is allowed only after an active replacement is demonstrated
to accept the same Pool V1 note/nullifier/tree format and spend relation, so
existing notes cannot be stranded. Emergency pause blocks new proof-authorized
spends; it does not reinterpret state, erase nullifiers or enable raw append.

The on-chain registry mutation program, reproducible SBF candidate and focused
LiteSVM governance lifecycle are implemented. Its multisig transaction
templates, final deployment/upgrade-authority evidence and finalized devnet
lifecycle remain release gates.

# Aspis Pool V1 verifier-registry governance

This crate is the native Solana mutation program for the canonical 128-byte
`ASRG` registry and 192-byte `ASRE` entry images defined by
`aspis_statement::pool_v1`. It implements the governance transitions modeled
in `AspisFormal/Pool/VerifierRegistryV1.lean`; it does not verify proofs, move
assets, mutate Pool/tree/history/nullifier/vault state, or expose a raw append.

The crate declares no static program id. The runtime program id is the sole
PDA domain:

```text
[b"aspis-verifier-registry-v1", pool]
[b"aspis-verifier-entry-v1", pool, profile_binding, release_binding]
```

Every load checks the exact owner, PDA, data length, magic, version, flags or
status, reserved bytes and Pool identity. Instructions reject extra accounts,
extra bytes, nonzero reserved bytes, duplicate account keys, privilege
promotion and demotion, and stale generations. The authority must be the
exact stored nonzero key, read-only, nonexecutable and a runtime signer. This
supports a threshold-multisig PDA signing through CPI without trusting its
owner program merely because an address was supplied.

## State transitions

- `Initialize` creates the canonical registry PDA with generation `0`, a
  nonzero authority and policy binding, and a nonzero minimum delay.
- `ScheduleProfile` creates a pending canonical entry only when
  `activation_slot >= current_slot + minimum_activation_delay_slots`.
- `Pause` and `Unpause` alter only the global registry pause flag. A no-op is
  rejected rather than consuming a generation.
- `Activate` changes a pending entry to active at or after its scheduled slot.
- `Retire` changes one live active entry to retired at the current slot only
  when a distinct replacement is active at that slot.
- `Freeze` sets the existing immutable flag, zeroes the authority and can
  never be reversed.

Every successful post-initialization transition requires an exact
`expected_generation`, checks `generation + 1` for overflow, and writes the
new generation exactly once. Every semantic check and fixed-width encoding
finishes before mutable byte images are committed; multi-account commits
acquire both mutable borrows before changing either image.

Registry pause gates Pool proof authorization, not governance recovery. It
therefore does not block scheduling, activation, retirement or freeze. A
frozen paused registry is an intentional permanent shutdown and cannot be
unpaused.

## Exact v1 compatibility rule

The formal model deliberately leaves `Compatible : Entry -> Prop` to the
policy-bound release manifest. The frozen entry image has no separate
compatibility field. This program uses a conservative concrete refinement:

```text
same pool
same policy_binding
same profile_binding
same statement_version
different release_binding
replacement active at the retirement slot
```

A profile binding is thus treated as the identifier of one exact spend
relation and statement contract. Governance cannot retire across profiles,
even if an off-chain manifest claims they are compatible. The remaining
explicit trust boundary is authenticating that the policy/profile binding
really names the reviewed manifest (including the approved SHA-256 collision
boundary); the program does not invent or parse a second manifest format.

## Wire and accounts

Every instruction begins with `ASRM || version=1 || opcode || zero[2]`.

| Opcode | Bytes | Payload after the 8-byte header | Exact accounts |
| --- | ---: | --- | --- |
| Initialize `0` | 80 | pool, policy binding, minimum delay `u64` | registry(w), authority(s), payer(sw), System Program |
| Schedule `1` | 128 | expected generation, verifier/profile/release, statement version, zero[7], activation slot | registry(w), new entry(w), authority(s), payer(sw), System Program |
| Pause `2` | 16 | expected generation | registry(w), authority(s) |
| Unpause `3` | 16 | expected generation | registry(w), authority(s) |
| Activate `4` | 16 | expected generation | registry(w), entry(w), authority(s) |
| Retire `5` | 16 | expected generation | registry(w), retiring entry(w), replacement entry(read-only), authority(s) |
| Freeze `6` | 16 | expected generation | registry(w), authority(s) |

The payer is a separate System-owned signer so the governance authority can
remain a read-only multisig PDA. Fresh PDAs may be System-owned/data-empty
(including prefunded accounts) or exact-size, program-owned and all-zero. The
System Program path uses canonical PDA signer seeds and rent-exempt sizing.

## Freeze coordination and runtime boundary

Pool V1's stable policy requires exact equality between its immutable flag and
authority and the registry image. Therefore a mutable Pool policy cannot be
silently converted after Pool initialization. An immutable launch must finish
registry population, activation and freeze before freezing/initializing the
matching Pool policy; freezing an already-live mutable policy intentionally
makes Pool authorization fail closed until a separately versioned migration
exists.

Host tests use preallocated program-owned zero accounts and prove rejected
calls leave registry and entry lamports/data byte-identical. For System-owned
PDA creation, Solana transaction atomicity remains the boundary that rolls
back a successful intermediate System CPI if a later borrow/write fails. A
final release still needs a runtime lifecycle test; this crate performs no
deployment or transaction itself. The focused SBF build is recorded separately
as release evidence.

Run the focused host suite with:

```sh
NO_DNA=1 cargo test -p aspis-registry --lib
```

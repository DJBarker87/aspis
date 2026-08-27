# V7 eight-lane one-terminal Pool plumbing

Status: production-inactive behind `pair-forest-account-evidence`.

## Compact verifier transport

The full semantic statement remains canonical `ASF8` (1,880 bytes), but it is
not transaction or CPI instruction data. `ASQ8` is exactly 320 bytes:

- bytes 0..8: magic, version, transition kind, digest version, reserved zero;
- bytes 8..40: registry profile binding;
- bytes 40..72: registry release binding;
- bytes 72..104: Pool program id;
- bytes 104..320: exact `ASCP` or `ASWP` payment public input.

The selected verifier receives fixed read-only CPI accounts
`[proof, master, retained_checkpoint, selected_lane]`. It must authenticate
the Pool program owner/PDA/codec of the last three accounts, verify the staged
proof, reconstruct the exact `ASF8` object from those account bytes and the
proof-carried candidate afterstate, and return exact 792-byte `ASR8`. The Pool
independently reconstructs the same `ASF8` and accepts the result only if every
result binding matches it.

The active Tag-73 verifier does not yet implement this `ASQ8` handler. That is
a hard integration boundary: this branch is executable plumbing evidence, not
a deployable verifier release.

## Pool settlement accounts

Same-page/genesis private transfer uses:

`[master, checkpoint, selected_lane, current_page, marker, registry, entry,
verifier, proof]`.

Rollover inserts one fresh, preallocated next root page after `current_page`.
Withdrawal appends `[mint, vault, destination, vault_authority, token_program]`.

The caller authenticates the immutable retained checkpoint, deterministic
output lane, exact live lane snapshot, active registry profile/release, sealed
proof framing and immediate selected-verifier return. It writes only the
selected lane, its chronological history page and the master-scoped nullifier
marker. Withdrawal additionally performs the existing PDA-signed legacy SPL
`TransferChecked` and checks exact vault/destination balance deltas before any
Pool-owned byte write.

No Pool-side Poseidon call occurs. CU is unmeasured because no active verifier
implements `ASQ8`, and this work did not build or deploy SBF.

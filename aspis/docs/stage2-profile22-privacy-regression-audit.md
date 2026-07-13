# Profile 22 privacy regression audit

Date: 2026-07-13

Status: **the executable privacy regression surface is green.  These tests
are guards, not an HVZK proof.**  The canonical affine-containment theorem and
the EPRO/private-Merkle simulation remain the primary privacy argument.

No proof byte, verifier rule, Fiat--Shamir label, or on-chain instruction was
changed by this audit.

## Typed proof-byte inventory

`profile22_public_proof_byte_inventory_is_complete_and_exact` assigns every
byte of the committed 56,686-byte proof to exactly one public-view type.  It
fails on both gaps and overlaps.

| public byte type | bytes |
|---|---:|
| header | 16 |
| public mask/attempt nonce | 32 |
| five Merkle roots | 160 |
| initial mask claim | 16 |
| masked sumcheck | 4,480 |
| statement evaluations | 1,344 |
| OOD values | 128 |
| four relation sumchecks | 448 |
| final polynomial | 64 |
| six work nonces | 48 |
| five record/frontier count pairs | 30 |
| opened field values | 11,776 |
| opened leaf salts | 2,560 |
| Merkle frontier nodes | 35,584 |
| **total** | **56,686** |

For proof-accounting purposes this is:

```text
non-hash affine field view       18,256
nonce/root/salt/frontier view    38,336
framing and work records             94
                                 ------
                                 56,686
```

Fiat--Shamir challenges and query indices are derived from these bytes and
the public statement; they are not separately serialized proof bytes.

This inventory is complete only for the proof payload.  The complete system
view additionally contains the public statement, instruction/account
framing, program logs, mutation account images, fee/rent deltas, release
variant and boundary time.  Those objects belong to the program/fixed-release
audits and must not be silently counted as covered by this byte test.

## Added guards

The new test-only module is
`crates/aspis-prover/src/state_only_profile22_privacy_regressions.rs`.

Fast default guards:

1. `profile22_public_proof_byte_inventory_is_complete_and_exact` pins the
   typed inventory above with no dark bytes.
2. `profile22_fixture_proof_does_not_literally_serialize_private_witness_blocks`
   scans the complete proof for every raw 32-byte private digest, every raw
   Merkle sibling and one packed private scalar block.  This is deliberately
   the dumb first distinguisher; it does not test affine or computational
   leakage.
3. `profile22_all_five_private_sections_bind_roots_values_salts_and_frontiers`
   mutates the root, first value, first salt and first frontier node of each
   of C1, C2, W1, W2 and W3.  All twenty mutations reject.
4. `profile22_transcript_order_binds_roots_values_and_work_before_their_challenges`
   pins these exact dependencies:
   - C1 root before `lambda`;
   - C2 root after `lambda,chi` and before zerocheck batching;
   - batch-work nonce before `gamma`;
   - round-zero OOD value before its mixing challenge;
   - W1 root after `alpha_0` and before the next OOD point;
   - final polynomial before the final grinding state and q16;
   - final nonce after that state and before q16.

Early-root mutations use a parser-valid zero-polynomial prefix because
mutating an early root in the real fixture correctly invalidates its already
serialized masked-sumcheck proof.  Later-order teeth use the real fixture.

One full prover guard is ignored by the default debug suite and is run
explicitly in release mode:

5. `profile22_fresh_attempt_rerandomizes_commitments_and_burned_nonce_reuse_fails_closed`
   builds the same statement and witness under independent test entropy.  It
   checks that all five roots change, all eighty disclosed salts are unique
   within an attempt and disjoint across attempts, and rebuilding under the
   already burned public nonce fails with `ReusedMaskNonce`.

The release-mode run completed green in 96.69 seconds on the audit host.

## Existing fixed-release and reuse teeth

The fixed-release core already had the required typed public observation:
one channel call at the chosen boundary containing either `Proof(bytes)` or
payload-free `Abort`.  Its five tests are green and cover:

- selected Good22 attempt 1 through 16 producing the same channel shape and
  boundary time;
- all-bad, entropy/build/decision errors producing one identical abort;
- early, exact-boundary, late and absent completions;
- scrubbing non-production and dropped buffered candidates;
- hiding the private completion time behind the injected boundary clock.

The entropy module separately pins durable nonce reuse across reopen and
across statements, plus exactly one winner under concurrent reservation.

These unit tests do not prove that a wallet integration has no filesystem,
scheduler, power, telemetry, RPC or hardware side channel.  The wallet must
make the fixed-release channel its sole externally observable worker edge;
those environmental terms remain in `epsilon_side`.

## Deliberate limitations

A same-public-statement pair of distinct valid spend witnesses is not
available for this fixture: the anchor, nullifier and output commitment bind
all witness components, so constructing such a pair would require a hash or
commitment collision.  The audit does not substitute two different public
statements and call that a same-statement hiding test.  Instead it uses:

- the formal physical-difference containment theorem for arbitrary legal
  same-statement differences;
- a same-statement, same-witness fresh-randomness full-prover regression;
- a literal-secret scanner as a weak first distinguisher.

Byte histograms and a handful of deterministic transcripts would not be a
privacy proof and are intentionally not promoted as one.  The remaining
claim continues to stand or fall on exact containment plus the EPRO and
fixed-release arguments.

## Commands

```text
NO_DNA=1 cargo test -q -p aspis-prover \
  state_only_profile22_privacy_regressions

NO_DNA=1 cargo test --release -q -p aspis-prover \
  state_only_profile22_privacy_regressions::profile22_fresh_attempt_rerandomizes_commitments_and_burned_nonce_reuse_fails_closed \
  -- --ignored

NO_DNA=1 cargo test -q -p aspis-prover \
  state_only_profile22_release::tests
```

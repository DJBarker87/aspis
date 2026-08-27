# V7 Pool C2 multiplex and proof-carried afterstate audit

Date: 2026-08-27

Status: the layout-only `7 -> 4` C2 fusion is rejected.  The conservative
one-terminal design keeps seven C2 lanes, a 34,658-byte maximum proof body, and a
minimal 680-byte verified afterstate payload.  No SBF build was run for this
audit.

## Result

The four late QM31 trace lanes cannot be spatially multiplexed with the three
existing C2 helper lanes without changing the hiding and terminal mathematics.
The collision already exists in the 1,024-row message tables, before circle
encoding:

- production constructs C2 as exactly `(H1, G, D)` in
  `crates/aspis-prover/src/v6_onefold_prover.rs`;
- `G` is expanded as an independent QM31 value at every one of the 1,024
  rows and then has one copy-inactive balancing value adjusted;
- `D` is independently expanded at every row and has the same one-value
  inactive-sum adjustment;
- `H1` contains the copy helper on every active row, while every inactive row
  except one receives independent padding before the balancing adjustment;
- the late append trace occupies rows `544..864`; its twenty append blocks
  also contribute copy endpoints, so late rows are not an H1-free region.

At a late row the existing three lanes can carry twelve independent M31
coordinates, while the four late lanes carry sixteen more.  Four QM31 lanes
have room for only sixteen M31 coordinates.  A selector-based sum or another
compression would therefore discard independently required data unless the
protocol changes the masking distributions and terminal equations.

Circle-code density is not the primary obstruction.  Message-level spatial
multiplexing can be encoded after the merge when supports really are
disjoint.  Here they are not disjoint before encoding.

Any future attempt to force four total lanes must be treated as a new
cryptographic construction.  It needs, at minimum, a new full-view hiding-rank
proof, new point-claim equations, new gamma batching, new terminal/source
bridges, and a new soundness inventory.  It is not a safe CU or wire-only
optimization.

## Exact wire consequences

The frozen 30,504-byte Tag-73 body has three C2 columns.  The conservative
proof-carried append adds four columns and twelve fixed QM31 point claims:

```text
C2 columns                         3 -> 7
C2 bytes per query               186 -> 434
sixteen query-record delta              3,968
fixed point-claim delta                    186
maximum proof body            30,504 -> 34,658
total delta                                4,154
```

For comparison only, a sound four-total-lane design would still be 31,542
bytes, not 30,504 bytes:

```text
C2 bytes per query               186 -> 248   (+62)
sixteen query-record delta                       992
fixed values                     641 -> 644
packed fixed-field bytes       9,936 -> 9,982   (+46)
proof body                    30,504 -> 31,542 (+1,038)
```

This hypothetical saves 3,116 bytes against the conservative seven-lane body,
but it is not available under the current hiding construction.

## Minimal one-terminal afterstate

The verifier need not return the output-pair digest and the Pool must not
recompute any Poseidon parent.  Once the selected verifier has checked the
twenty late append equations against the exact locked source snapshot, the
only state bytes needed by the Pool are:

```text
  8  next pair index (also next root sequence)
 32  next root
640  twenty next-frontier digests
---
680  bytes
```

An eight-byte `ASJA` type/version/status envelope makes the exact return data
688 bytes.  It is below Solana's 1,024-byte return-data ceiling.  The pure
codec is in `crates/aspis-statement/src/pool_v1/pair_terminal.rs` and rejects
trailing bytes, invalid versions/status, an out-of-range next index, and every
non-canonical digest limb.

The Pool derives all redundant values from its locked prestate plus the
verified next index:

- first and second output note indices;
- retained-root sequence;
- root-history page and slot;
- whether rollover is required; and
- the next Pool state image.

It must additionally check `returned.next_pair_index = live.next_pair_index +
1`.  The immediate Solana return-data program id authenticates the selected
verifier.  Profile, release, proof-account and statement bindings stay in the
request and registry policy; they need not be echoed in the result.

## Smallest source/interface delta

1. Extend the selected-verifier CPI accounts with the pair Pool state, passed
   read-only to the verifier.  The outer Pool instruction retains the writable
   lock.  The verifier derives the canonical 800-byte live snapshot from this
   exact account and absorbs it after `lambda, chi`; the snapshot need not be
   copied into CPI instruction data.
2. Add the conservative pair Tag-73 proof parser and verifier geometry: seven
   C2 lanes, 653 fixed QM31 values, 869-byte query records and an exact
  34,658-byte maximum body.
3. On success set exactly the 688-byte `ASJA` result.  On every verifier error,
   return no success data.
4. In the Pool, replace the execution-time append call with an authenticated
   afterstate token constructed only by the immediate CPI return parser.
5. Check source-account identity, exact current state, `next = current + 1`,
   capacity, canonical result bytes, current chronological history and marker
   freshness before the CPI or write phase as appropriate.
6. After successful verification, perform only byte writes: next Pool state,
   one chronological history root (including pre-created rollover page), one
   marker, optional custody CPI/delta check, then the Pool receipt.
7. Keep the execution-time append experiment source for negative evidence,
   but do not dispatch its `ASJP` instruction from the production entrypoint.

The exact literal Poseidon SBF measurement supplied by the integration lane is
decisive negative evidence for the alternative route: twenty
`pool_v1_tree_parent` calls cost 469,798 CU and twenty-one cost 493,270 CU.
That work cannot fit inside the 141,987-CU headroom of the current verifier.

## Remaining boundaries

- the seven-lane prover/verifier and late-snapshot schedule do not yet exist in
  production Rust;
- accepted proof to exact 680-byte afterstate still needs the cryptographic
  Lean theorem and Rust-to-Lean source bridge;
- the Pool-side opaque authenticated-afterstate token and byte-only mutation
  suffix now exist as a production-inactive prototype; the account-level test
  covers two sequential same-page transitions plus replay/stale rollback, but
  the real selected verifier does not yet construct that token and no
  production instruction dispatch enables it;
- honest and accepted maximum-frontier staged-verifier CU are unmeasured;
- byte-only same-page/rollover suffix measurement and real combined
  same-page/rollover/withdrawal LiteSVM runs remain required.

The current source experiment is therefore not a production authorization
path and makes no claim that the one-terminal transaction already fits.

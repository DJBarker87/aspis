# V7 Pool pair-tree design gates

Date: 2026-08-27

Status: production-inactive source and Lean design gate. This checkpoint does
not register a verifier profile, enable dispatch, mutate a Pool account, or
authorize a deployment.

## Outcome

The proposed pair-tree profile now has exact, source-pinned answers to the
three protocol questions which had to be settled before production
integration:

1. an empty second slot is algebraically unspendable;
2. historical membership and the current append state have different root
   roles; and
3. the complete candidate relation occupies 976 of 1,024 rows, leaves exactly
   48 rows unused, and retains the existing degree-27 cap.

The row schedule was also rotated from local path bases `0,2,4,6` to
`1,3,5,7`. This preserves the six-block path geometry while leaving local rows
`0` and `12` relation-free in each full path block. The corresponding exact
full-view masking-rank gate is recorded below.

## Occupied versus empty slots

A pair leaf commits to two ordered eight-limb note commitments. The first slot
is always occupied. The second slot has a private field bit `occupied`, a
sentinel inverse, and the following algebraic constraints:

```text
occupied * (occupied - 1) = 0
sentinel * inverse = occupied
(1 - occupied) * inverse = 0
(1 - occupied) * commitment[j] = 0       for j = 0..7
selected_second * (1 - occupied) = 0
```

Consequently, `occupied = 0` forces the complete second commitment and inverse
to zero. Selecting the second slot forces `occupied = 1`. Empty-slot
unspendability therefore follows from the spend relation itself; it does not
assume that a chosen Poseidon digest has no preimage.

For an occupied second commitment, its fixed sentinel limb must be nonzero.
An honest note whose salted commitment has a zero sentinel is retried during
note construction. That is an explicit liveness event, not a soundness
assumption.

The exact selected-side copy is source-pinned from trace cell `(865,0)`—the
level-zero private membership direction—to trace cell `(969,10)`, where the
occupancy residual is evaluated. This prevents the occupancy check from being
fed by an unrelated or stale path row.

## Historical membership versus live append

The profile gives the two root roles distinct types and transcript positions:

```text
stable statement
  -> Stage-A commitment
  -> lambda
  -> chi
  -> exact live append snapshot
  -> Stage-B commitment
  -> remaining batching challenges
```

The membership root may be a retained historical anchor. The live append
snapshot contains the current Pool identity, deployment domain, sequence,
next pair index, current root, and all 20 frontier nodes. It is encoded in an
exact 800-byte canonical format and is absorbed only after `lambda` and `chi`.

This avoids requiring the expensive historical-membership portion of the
proof to bind the current append root. Stage A contains the stable spend,
membership, nullifier, recipient, change, and output-pair work. Stage B
contains the 20 live append-path hashes.

The design is one atomic settlement transaction, in addition to ordinary
proof-account upload transactions. It is not a prepared multi-transaction
state transition. If another settlement changes the Pool after a prover has
fixed its live snapshot, the stale settlement fails without changing state;
the stable Stage-A work remains reusable, while the live Stage-B suffix must
be rebuilt. This is optimistic concurrency, not wait-free concurrency.

## Exact trace and degree inventory

| Region | Blocks | Rows |
| --- | ---: | ---: |
| Stable Poseidon work | 34 | 544 |
| Live append Poseidon work | 20 | 320 |
| Private path auxiliaries | 6 | 96 |
| Value and occupancy auxiliaries | 1 | 16 |
| Unused tail | 3 | 48 |
| Total | 64 | 1,024 |

The 54 Poseidon blocks end at row 864. Path auxiliaries occupy rows 864–959,
value and occupancy auxiliaries occupy rows 960–975, and every row 976–1023
is untouched. Lean proves both the arithmetic count and the cardinality of the
literal untouched-row interval.

All new occupancy, empty-slot, selection, cursor, frontier, and child-ordering
residuals have intrinsic degree at most two. The existing two-round Poseidon
residual remains the maximum at degree 25. Adding the existing selector and
outer zerocheck overheads gives exactly degree 27, so the pair-tree design does
not raise the deployed sumcheck degree.

## Exact row and masking inventory

The production-inactive Rust inventory pins:

- 126 ordered copy-row links;
- 199 distinct active copy rows;
- 4,334 relation-free mask cells;
- copy schedule fingerprint `0x97985fb30cdd807d`;
- active-row fingerprint `0x56e6c3e3f386f273`; and
- relation-free-mask fingerprint `0x6a86249a2d85591f`.

The fixed full-field schedule test uses non-base-subfield QM31 challenges and
checks the complete root/message observation map. Its result must be read as
one explicit nonzero full-rank witness for this exact layout. It does not, by
itself, establish an all-schedule determinant-liveness probability theorem.

The optimized exact finite-field run passed:

- test: `pool_pair_exact_layout_spans_complete_root_message_view`;
- raw mask dimension: 2,244;
- source constraint rank: 1,080 of 1,084 rows;
- complete observed-view rank: 4,092 of 4,360 coordinates;
- ambient deficit: 268, with the physical, legal, and helper projections all
  reported full rank;
- wall time: 833.21 seconds;
- maximum resident set size: 1,978,974,208 bytes; and
- swaps: 0.

This is one explicit nonzero full-rank witness for the exact frozen layout,
not an all-challenge determinant-liveness theorem.

## Lean replay

The focused module is
`AspisFormal/AspisFormal/Pool/V7PairTreeTraceGeometry.lean`. Its NUC replay
completed successfully under unit `aspis-pair-geometry-root-05`:

- exit status: 0;
- wall time: 12.15 seconds;
- peak RSS: 6,732,836 KiB;
- swap: 0.

The exact row/cell theorems use no axioms. The polynomial semantic and degree
theorems report only Lean's standard `propext`, `Classical.choice`, and
`Quot.sound`; there is no `sorry`, `admit`, `sorryAx`, `native_decide`, or
project-specific axiom.

## Remaining production work

This checkpoint deliberately freezes a candidate profile without activating
it. Production readiness still requires:

1. compiling the literal tuple/residual registry and terminal for this exact
   row schedule;
2. generating the prover and verifier source paths for the staged transcript;
3. proving the Rust-to-Lean/Aeneas bridge to the source contract;
4. integrating one atomic Pool settlement path with exact account and
   registry bindings;
5. measuring proof size and CU on populated states; and
6. completing reproducible SBF, finalized devnet lifecycle, and release audit
   evidence before any mainnet authorization.

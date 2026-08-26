# V7 Pool V1 payment-relation foundation

Status: the exact ABI conversion, routed 1,024-row trace, semantic registry,
copy helper and executable three-view semantic oracle are implemented;
Tag-73 prover/deployed-verifier/profile integration is **not** implemented by
this work.

## Exact custody relations

The two Pool V1 relations use the already frozen primitives without a new
cryptographic domain:

- owner key: `derive_owner_key(nullifier_key)`;
- nullifier: `pool_v1_nullifier(nullifier_key, input_salt)`;
- input and output leaves: `pool_v1_note_commitment(owner_key, value,
  asset_id, salt)` under the ordinary spendable-note domain;
- membership: exactly 20 binary levels using
  `pool_v1_tree_parent = merkle_node_compress_v3`;
- every hidden value is an integer in `[0, 2^30)`;
- all additions use checked `u32` arithmetic before equality is accepted;
- Pool, deployment domain, asset, retained root sequence and retained root are
  compared to an independently authenticated runtime binding;
- the derived nullifier must be absent from the supplied spent-marker set.

The private-transfer equation is

```text
input_value = recipient_value + change_value
```

and both public output commitments must open to the corresponding hidden
owner key, value and salt.

The withdrawal equation is

```text
input_value = change_value + public_withdrawal_amount
```

where the amount is nonzero and below `2^30`; the public destination must be a
nonzero 32-byte token-account address; and the public change commitment must
open to the hidden change note.

Pool V1 is deliberately fee-free. Its canonical custody fee is exactly zero
and there is no caller-selectable fee in either relation. ASCP bytes 148..152
remain zero; ASWP uses those four bytes for the withdrawal amount. Relayer
pricing is outside the custody relation and cannot redirect an output or
change conservation. A nonzero in-note fee requires a future versioned
statement and verifier profile.

## Byte-exact public statements

Both public types encode to the existing 216-byte Pool payloads:

| Offset | Bytes | Private transfer (`ASCP`) | Withdrawal (`ASWP`) |
|---:|---:|---|---|
| 0 | 4 | `ASCP` | `ASWP` |
| 4 | 1 | version 1 | version 1 |
| 5 | 1 | kind 1 | kind 2 |
| 6 | 1 | digest encoding 1 | digest encoding 1 |
| 7 | 1 | zero | zero |
| 8 | 32 | Pool | Pool |
| 40 | 32 | deployment domain | deployment domain |
| 72 | 8 | retained-root sequence | retained-root sequence |
| 80 | 32 | retained root | retained root |
| 112 | 32 | nullifier | nullifier |
| 144 | 4 | asset id | asset id |
| 148 | 4 | zero/canonical fee | withdrawal amount |
| 152 | 32 | recipient commitment | destination token account |
| 184 | 32 | change commitment | change commitment |

The focused integration test compares each relation encoder directly with the
statement slice produced by the production Pool instruction encoder. It also
round-trips that exact slice through both independent decoders. No adapter
hash or lossy field map sits between the proof statement and the bytes the
Pool applies.

## Routed trace and semantic registry

Both variants now compile into the existing 1,024-row, sixteen-column C1
geometry. The Poseidon schedule occupies blocks 0 through 48. Five auxiliary
path blocks encode all 20 Merkle levels as `(bit, current, sibling, left,
right)` tuples, and block 54 carries the three transfer values or the two
withdrawal values plus their 30-bit decompositions and conservation sources.
Unused rows and columns are canonical zero padding.

The generated registry has 78 copy links for private transfer and 75 for
withdrawal. It connects the hidden preimages, every Poseidon carry, all Merkle
path inputs and outputs, the 30-bit source values, and the conservation
aliases. No link relies on a prose-only equality.

The non-Poseidon semantic oracle has 94 base residuals:

| Residual class | Lanes |
|---|---:|
| initial-state, domain separation and unused auxiliary zeroes | 16 |
| absorption and permutation-local padding zeroes | 16 |
| Merkle direction and ordering | 17 |
| direct 30-bit range and recomposition | 33 |
| value conservation | 2 |
| public digest bindings | 8 |
| public scalar bindings | 2 |
| **base total** | **94** |

Those M31-valued Boolean-row residuals pack into 24 QM31 lanes. The copy
LogUp residual is lane 25. Together with the four existing Poseidon lanes,
the relation therefore consumes exactly the frozen 29-lane theta composition
and adds no serialized proof claim. This is an executable host/compiler fact;
it does not become an on-chain Tag-73 claim until the same oracle and terminal
constants are wired into the prover and deployed verifier.

## Logical lane and constraint inventory

The following is an implementation screen, not a compiled registry count.
One digest is eight M31 lanes and every Poseidon invocation is the frozen
22-round Poseidon2-M31 construction.

| Component | Private transfer | Withdrawal |
|---|---:|---:|
| owner-key hashes | 1 | 1 |
| input-note hashes | 3 permutations | 3 permutations |
| depth-20 v3 Merkle parents | 20 | 20 |
| nullifier hashes | 2 permutations | 2 permutations |
| recipient-note hashes | 3 permutations | 0 |
| change-note hashes | 3 permutations | 3 permutations |
| **total Poseidon permutations** | **32** | **29** |
| hidden values | 3 | 2 |
| 10-bit range limbs | 9 | 6 |
| path sibling lanes | 160 | 160 |
| path direction bits | 20 | 20 |
| path-index reconstruction equalities | 1 | 1 |
| checked conservation equalities | 1 | 1 |
| public algebraic lanes | 33 | 26 |

The 33 private-transfer public algebraic lanes are anchor 8, nullifier 8,
asset 1, recipient commitment 8 and change commitment 8. The 26 withdrawal
lanes are anchor 8, nullifier 8, asset 1, amount 1 and change commitment 8.
Pool/domain/sequence and withdrawal destination are transcript and Pool-state
bindings, not hidden-preimage lanes. The Pool separately checks the withdrawal
destination against the actual token account before its CPI.

Before structural aliases, an explicit trace layout would have 232 logical
private M31 occurrences for transfer and 215 for withdrawal:

```text
input preimage                 17  (key 8 + salt 8 + value 1)
path                          181  (siblings 160 + index 1 + bits 20)
each output preimage           17  (owner 8 + salt 8 + value 1)
transfer total        17 + 181 + 34 = 232
withdrawal total      17 + 181 + 17 = 215
```

The state marker freshness predicate, historical-root account authentication,
Pool identity comparison, destination-account comparison and exact SPL-token
delta remain program/state predicates. The proof must derive the same public
nullifier, root, asset and output values that those predicates consume.

Because all private values are below `2^30`, the sum of two such values is at
most `2^31 - 2`, strictly below the M31 modulus `2^31 - 1`. Consequently, after
the range constraints, the M31 conservation equality is also exact integer
conservation; modular wraparound cannot satisfy it. The Rust oracle still uses
checked integer addition and has explicit overflow rejection teeth.

## V7 proof-size screen

The current same-path atomic relation uses 49 sixteen-row Poseidon blocks, or
784 of the 1,024 logical rows. A direct Pool transfer schedule needs 32 blocks
(512 rows) and withdrawal needs 29 blocks (464 rows). Even after adding the
third value's three range limbs for transfer, the row screen has substantial
headroom. No extra committed column is evident at the semantic-oracle stage.

The Pool payload remains exactly 216 bytes. If the new trace is compiled into
the current 26-M31-C1 plus three-QM31-C2 geometry with the same claim count,
degree schedule, q16 query grammar, 208-bit digests and two 203-node
frontiers, the proof-body wire remains exactly the frozen V7 size:

```text
9,936 fixed packed-field bytes
+   52 roots
+   24 work nonces
+ 16 * 621 query bytes
+ 2 * 203 * 26 frontier bytes
= 30,504 bytes
```

This is still a feasibility result, not a Pool proof-size measurement. The
exact trace, registry and lane packing now show that the existing geometry and
grammar suffice at the semantic-oracle boundary. A prover or verifier change
that adds serialized claims, columns, sumcheck coefficients or query openings
would still change the wire, so 30,504 bytes must be confirmed from an actual
Pool proof before it is a release measurement.

## Mutation evidence and honest boundary

Focused tests currently establish:

- honest transfer and withdrawal traces make all 95 semantic residuals zero
  at every one of the 1,024 Boolean rows;
- the copy helper has zero terminal sum for both honest variants;
- changing the public withdrawal amount is detected at its exact routed row;
- honest transfer and withdrawal acceptance;
- v3 membership-root parity with the existing atomic v3 reference;
- byte-exact ASCP/ASWP encoding parity with the production Pool encoder;
- public-output, anchor/path, conservation, range, overflow and spent-nullifier
  rejection;
- zero destination and malformed/noncanonical statement rejection;
- nonzero ASCP fee/reserved-word rejection and ASWP trailing-fee rejection;
- destination, Pool and deployment-domain mutations change the exact dispatch
  digest; Pool/domain mutations also fail the independent runtime binding.

A changed nonzero destination can define a different valid relation with the
same private witness. That is intentional: the note owner chooses the public
withdrawal destination. Security requires the proof transcript to bind the
exact destination bytes and the Pool to compare those bytes with the actual
destination account. The focused digest test checks the first property at the
statement boundary; the existing Pool withdrawal planner checks the second.

## Remaining Tag-73/compiler work

This foundation must not be advertised as a Pool Tag-73 proof until all of the
following are complete:

1. Independently formalize and replay the routed layout, copy registry,
   Poseidon schedule, path ordering, range reconstruction, conservation and
   public bindings in Lean and through the accepted Rust/Aeneas source bridge.
2. Prove that the nine-limb transfer and six-limb withdrawal range systems
   have the required lookup/masking rank and zero-knowledge factorization.
3. Bind every public algebraic lane to the exact ASCP/ASWP payload and every
   transcript-only byte to the profile statement digest.
4. Add prover trace construction, terminal constants, accepted-kernel/source
   bridges, Aeneas replay and Lean semantic/composition theorems.
5. Create a new registry profile/release. The current
   `v7_pool_dispatch.rs` profile is explicitly the old same-path
   `AtomicPaymentStatementV4`, accepts only private-transfer kind and cannot
   authorize either relation defined here.
6. Run proof-level mutation coverage, exact proof-size measurement, SBF/CU
   profiling and the real Pool lifecycle with the non-mock verifier.

Until those gates close, the Pool program and executable oracle are useful
plumbing and specification evidence, not end-to-end private-transfer or
withdrawal authorization.

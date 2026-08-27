# V7 Pool eight-lane one-terminal concurrency gate

Date: 2026-08-27

Status: production-inactive candidate. The exact arithmetic/layout gate is
Lean-checked. The complete-view masking-rank gate is still required before
this design may enter the prover or verifier.

## Decision target

Retain one terminal spend transaction while replacing the single mutable
append tip with eight independently writable depth-20 pair-tree lanes. A
spend proves old-note membership under one retained historical global root
and appends its output pair against the current state of exactly one selected
lane.

This does not make contention impossible. It gives the exact and narrower
staleness condition:

- a successful write to another lane does not invalidate the proof-bound live
  state;
- a successful write to the selected lane may invalidate it;
- a withdrawal may still contend on the shared SPL vault account, but vault
  scheduling does not invalidate the proof unless a vault balance is
  incorrectly included in the proof statement.

For independent uniformly selected honest lanes, append-induced proof
survival changes from approximately `exp(-lambda*T)` to
`exp(-lambda*T/8)`. This is an honest-load model, not an anti-DoS theorem:
an adversary can deliberately create same-lane traffic.

## Exact relation geometry

The existing selected pair relation allocates 976 of 1,024 trace rows. A
private lane-root-to-global-root membership path has depth three. At sixteen
rows per Poseidon parent, the additional path consumes exactly 48 rows.

The logical membership directions are:

1. direction 0 selects the occupied commitment inside the pair leaf;
2. directions 1 through 20 prove the depth-20 lane-tree path;
3. directions 21 through 23 prove the private depth-three lane-root path
   under the historical global root.

This consumes all 24 direction slots already available in six four-direction
auxiliary blocks. The profile remains a 1,024-row trace with degree 27,
26 C1 columns, 3 C2 columns, 641 fixed QM31 values, and a 30,504-byte maximum
proof body.

The literal layout which retained all old rows and placed the new Poseidon
parents in blocks 61 through 63 is rejected: its exact raw-C1 masking rank was
72 where 76 is required. The selected candidate permutes only the same
ten-block physical tail:

| Blocks | Rows | Role |
|---|---:|---|
| 0 through 53 | 0 through 863 | Existing Poseidon schedule |
| 54 through 56 | 864 through 911 | Three global-super-root parents |
| 57 through 62 | 912 through 1007 | All 24 private direction gadgets |
| 63 | 1008 through 1023 | Existing value/occupancy auxiliaries |

Within every direction block, base rows are local rows 1, 5, 9 and 13;
successor rows are 2, 6, 10 and 14; sibling rows are 3, 7, 11 and 15. This
leaves complete local rows 0, 4, 8 and 12 available to the mask inventory.
The exact candidate contains 136 copy links, 214 copy-active rows and 3,611
relation-free mask cells.

## State and transaction model

The master Pool owns eight lane PDAs. Each lane stores its own root, append
index, frontier, sequence number and lane-root history. A normal private spend
uses:

- the retained historical global root as the public input-membership anchor;
- private lane identity, three super-root siblings and three directions for
  the input note;
- the exact current root/index/frontier of one writable output lane as the
  proof-bound append source;
- the proof-derived next state for that same lane;
- one master-Pool-scoped nullifier-marker PDA, so nullifier uniqueness is not
  partitioned by lane.

The Pool derives the output lane deterministically from the canonical public
nullifier encoding, initially `nullifier_limb_0 & 7`, and checks that the
provided writable lane PDA has that index. Because the nullifier is already
public, this reveals no additional input-note information. The input lane
remains private. In particular, private directions 21 through 23 are the
input note's historical super-root path and are not constrained to equal the
nullifier-derived output lane. Deposits need their own deterministic
assignment rule, such as the low three bits of a canonical commitment digest.
In the frozen digest
encoding this helper is equivalently
`encode_digest_canonical(nullifier)[0] & 7`; program, wallet and indexer must
call one shared implementation rather than reproduce the conversion.

No global mutable sequence, current global root or vault balance may be bound
into the spend proof. Such a binding would recreate cross-lane proof
staleness even if the corresponding account only caused a scheduler lock.

The current single-tree account and statement bytes must not be reinterpreted
as this forest. The production implementation needs new master, lane,
checkpoint, statement, receipt and selected-lane live-snapshot versions. The
master remains the stable public Pool identity and namespaces the vault,
verifier registry and nullifier markers. The selected lane PDA, not the
master, supplies the proof-bound current root/index/frontier. Transfer spends
therefore read the master and checkpoint but write only the selected lane,
its current history page, the unique marker, payer/proof accounts and any
custody accounts required by the transition.

## Coherent historical checkpoints

A permissionless checkpoint instruction receives all eight canonical lane
PDAs in fixed order as read-only accounts, recomputes the seven typed
Poseidon parents on-chain, and appends the resulting global root to global
history. The eight accounts must be read by the same Solana transaction.
Independently timed RPC reads are not a coherent checkpoint.

Solana account locking makes the snapshot precise: a checkpoint cannot read a
lane concurrently with a spend writing that lane. It therefore observes
either the complete state before that spend or the complete state after it.
A later lane update does not invalidate the retained historical global root.

Each global-history record binds at least the master, deployment domain,
monotone checkpoint sequence, global root and the eight lane sequence numbers.
The first implementation should use an immutable checkpoint PDA derived from
the master and checkpoint sequence. Lane histories or canonical ledger replay
then recover the exact component roots and witness data. After genesis, the
checkpoint instruction requires componentwise nondecreasing lane sequences
and at least one strict increase. This rejects duplicate/no-progress records
and prevents a caller from aging useful roots out of one overwritten `latest`
account. Old immutable checkpoints remain valid spend anchors indefinitely.

A newly appended note is not spendable until a checkpoint including its new
lane root is finalized. This is an asynchronous anchoring delay, not a second
preparation or settlement transaction for the original spend: the spend
itself still verifies and applies atomically in one terminal transaction.

Deposits have no nullifier. Their lane is derived from the canonical deposited
commitment. A deposit computes its append from the lane state while executing,
so same-lane deposits are serialized by the runtime rather than requiring an
expensive preconstructed proof to be regenerated.

## Required gates

1. Complete-view masking rank for the exact physical layout.
2. Exact three-parent Poseidon relation and copy-registry integration using
   the frozen `merkle_node_compress_v3` parent byte-for-byte, with fixed lane
   ordering and layer roles proved at the statement boundary.
3. Terminal equality, masking-rank and final-vector factorization with the
   extra private siblings and directions.
4. Source checks for canonical lane PDA derivation, nullifier-to-lane mapping,
   exact locked `ASPLIVE1` snapshot transport and same-lane stale rejection.
5. Source checks that a checkpoint reads the eight canonical lane PDAs in one
   instruction, fixes their order, recomputes all seven parents and updates
   global history monotonically and idempotently.
6. Honest prover/verifier round trip, same-lane stale rejection,
   different-lane survival, global nullifier replay rejection, rollback on
   every late failure, and one-terminal SBF CU measurement.
7. Aeneas caller bridges and the end-to-end K1.2--K1.6 composition.

The design is accepted only if these gates preserve the existing cryptographic
parameters and wire size. Exact arithmetic fit alone is not acceptance.

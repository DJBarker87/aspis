# Atomic payment state v1 / statement v3

Date: 2026-07-13

Status: **the v3 trace, prover, read-only tag 46, and account-transition kernel
are integrated and measured; default tags 38 and 47 remain fail-closed.** No
default/production instruction can mutate payment state while complete-view
hiding remains open.

## Selected state model: private same-path replacement

The pool is a fixed-capacity depth-20 note tree. A spend does not append at a
public index. The proof privately carries the input note's existing path and
index and proves both equations over the same siblings and direction bits:

```text
RootV3(input_note, private_path, private_index)  = current_anchor
RootV3(output_note, private_path, private_index) = output_anchor
```

The program locks the pool, checks `current_anchor`, verifies the complete
proof, consumes the canonical nullifier PDA, and writes the proof-bound
`output_anchor`. No Poseidon tree hash executes on chain. `pool.sequence`
increments as replay/concurrency/version metadata; it is not a leaf index.

The public statement binds:

1. current root;
2. nullifier;
3. spendable output-note commitment;
4. replacement root;
5. asset ID and public fee;
6. pool public key and pre-transition sequence.

`value` and `value_out` remain private. SpendV0 binds them through note
commitments, ranges, and `value_out + fee = value`.

## V3 node compression

V2 internal nodes used the rate-8 length-committing sponge on sixteen M31
input limbs. That takes two Poseidon2 permutations per level. V3 uses the
fixed-purpose ordered compression

```text
state = left[0..8] || right[0..8]
state[15] += 0x41531005
node = Poseidon2M31(state)[0..8]
```

It is never reused for leaves or variable-length messages. Leaves remain the
length-committing `DOMAIN_NOTE` sponge. The node tweak, ordered input, and v3
statement/tree version prevent silent reuse of v2 roots.

Security assumption: for the fixed tweaked permutation and ordered 16-limb
input, truncating a width-16 Poseidon2-M31 permutation to eight M31 output
limbs has collision security of approximately `|M31|^4`, about 124 bits.
The payment target is 100 bits. This is a new explicit tree-compression
assumption; the differential/KAT tests establish implementation identity, not
cryptographic security.

The pinned KAT for left limbs `100+17i` and right limbs `700+19i` is:

```text
[1586466362, 2103727270, 1374732293, 1933136693,
 1396290158, 1930786489, 128900489, 1701436969]
```

`merkle_node_compress_v3` is different from the v2 node sponge, changes when
left/right are swapped, and changes when either input is mutated.

## Trace layout and CU effect

The old input-membership path occupied 20 levels times two permutation blocks,
40 permutations. V3 input membership occupies 20 one-permutation blocks. The
freed 20 blocks carry the output replacement path. Therefore:

```text
old statement: input path 40 permutations
v3 statement:  input path 20 + output path 20 = 40 permutations
```

The surrounding owner/note/nullifier/output work is unchanged, so the full
hash schedule remains 49 permutations, `log_rows=10`, and 16 state columns.
The second path must alias exactly the existing private siblings and direction
bits; separate path witnesses would permit an arbitrary replacement root.

### Frozen 49-block migration schedule

The state-only atomic trace keeps the existing 49-permutation budget and
assigns blocks as follows:

| blocks | invocation | permutations |
| --- | --- | ---: |
| 0 | owner-key sponge | 1 |
| 1..3 | input-note sponge | 3 |
| 4..23 | v3 input membership path, levels 0..19 | 20 |
| 24..43 | v3 output replacement path, levels 0..19 | 20 |
| 44..45 | nullifier sponge | 2 |
| 46..48 | spendable output-note sponge | 3 |

Every v3 node block reuses the existing state-only two-round transition
oracle without another point or a degree increase. For ordered inputs
`left || right`, the physical rows are:

```text
row 0  = 0[0..8] || right[0..8], then add the v3 tweak to lane 15
row 12 = left[0..8] || 0[0..8]
```

The already-frozen leading transition adds row 12 into the first eight lanes
of row 0, applies the initial external layer, and then evaluates the 22
Poseidon rounds. It therefore enters the permutation on exactly
`left || right` with the lane-15 tweak. Rows 1..10 remain committed
two-round boundaries and row 11 remains the committed final digest source.
The degree-27 zerocheck and the three point set `(z,succ(z),xor12(z))` are
unchanged.

For each level, one private path bit selects `(current,sibling)` into
`(left,right)`. The input and output paths consume the same committed sibling
and bit cells; only their starting current digests differ. The public final
bindings are block 23 -> `current_anchor`, block 43 -> `output_anchor`, block
45 -> `nullifier`, and block 48 -> `output_commitment`. The four digest
families can remain aggregated into the existing eight public-digest
constraint lanes, so this schedule adds neither a theta lane nor a committed
column.

The current v4/state-only copy registry is not reusable. The migration must
generate all left/right selections, both path continuations, and the
cross-path sibling/bit aliases from this schedule. Its exact `m`, active-row
selector, routing rank, and layout/factor fingerprints are outputs of the
generator, not assumed to remain 102 or rank 51.

Required migration teeth are: mutate every sibling and direction bit in only
one path; swap a left/right node; change the tweak; change either start leaf;
change either public root; and verify that the other path is unchanged while
the complete statement rejects. Random off-domain optimized/reference
identity testing must cover the regenerated routing and terminal constants.

Exact SBF endpoints in `results/stage2/poseidon2_probe.json` on validator
2.3.0 are:

| lazy M31 permutations | total CU | incremental over zero |
| ---: | ---: | ---: |
| 20 | 463,451 | 462,893 |
| 40 | 926,356 | 925,798 |

The 462,905-CU difference is why the v3 compression creates enough trace
capacity for replacement without growing the domain. These are direct
software-permutation prices, not verifier savings: the selected program does
not evaluate either path directly.

## Binding lemma

Assume:

1. the complete state-only verifier is sound for the exact v3 statement;
2. both path computations use the same constrained siblings and index bits;
3. the v3 compression has the collision bound stated above;
4. the canonical statement SHA-256 is collision resistant.

If the atomic instruction succeeds, then the locked pre-root contains the
spent note, the nullifier is consumed once, the replacement leaf is the
proof-constrained spendable output note, and the only root written is the root
obtained by replacing that same private leaf. Any accepted different leaf,
path, or post-root violates proof soundness or yields a compression/hash
collision.

Absorbing `output_anchor` into Fiat--Shamir without the second path equation
does not prove this lemma. The program closure therefore receives both the
decoded `AtomicPaymentStatementV3` and its digest, and its contract explicitly
requires the algebraic replacement check.

## Spendable output fix

The audit also found that pre-v2 outputs used `DOMAIN_OUTPUT` while future
input membership used `DOMAIN_NOTE`. Such outputs are unspendable absent a
collision. Production `output_commitment` now exactly equals the future input
note commitment under `DOMAIN_NOTE`; the retired behavior exists only in a
test helper. `HashInvocationKind::Output` remains distinct trace provenance.

## Canonical statement digest

`crates/aspis-statement/src/atomic_statement.rs` provides the no-std v3
encoding. Every field digest is eight canonical little-endian M31 limbs;
noncanonical limbs/asset IDs and fees at least `2^30` reject.

Domain: `aspis/atomic-payment-statement/v3`. Payload, 184 bytes:

```text
version=3 || tree_depth=20 || zero[6] || pool_pubkey || sequence_le ||
current_anchor || nullifier || output_commitment || output_anchor ||
asset_id_le || fee_le
```

Pinned SHA-256 KAT:
`a16419a33eafc69cd9b923ae8fb1d5400cf969b0c81656a339ec31f6688dca86`.

## Rejected state models

### Direct depth-20 update

The retained v2 reference checks empty-leaf insertion by recomputing both
roots on chain. It needs 80 software permutations. The exact 40-permutation
endpoint is already 926,356 CU; 80 exceeds the entire transaction cap. Tag 38
fails before invoking this reference path.

### O(1) SHA append chain

`new = SHA256(domain, old, output_leaf, index)` cheaply binds one append, and
the implementation has old-root/leaf/index mutation teeth. It does not give a
logarithmic membership proof: proving that an old leaf reaches the current
head requires replaying every later append. A per-root receipt makes membership
O(1) but reveals the exact creation transaction for a one-output spend and
breaks the hiding goal. The append chain is therefore a priced negative
control, not a pool accumulator.

The exact SBF kernel probe on validator 2.3.0 measured 256 chained appends at
63,134 CU total and 62,612 CU incremental over the zero kernel, or 244.578125
CU per append. This confirms that compute cost is not the rejection reason;
private logarithmic membership and unlinkability are.

### Solana Poseidon syscall

The locally fetched official `solana-poseidon` source exposes only
`Parameters::Bn254X5`, 32-byte BN254 field inputs, and at most twelve inputs.
It cannot evaluate the pinned width-16 M31 Poseidon2 permutation. SHA-256 and
Keccak syscalls are cheap byte hashes but replacing the tree hash with either
would require a new, expensive bitwise membership statement. No available
syscall is an acceptance-equivalent M31 node primitive.

## Atomic accounts and ordering

Tag 38 uses five accounts: read-only program-owned proof, writable
program-owned 48-byte pool state, writable canonical nullifier PDA, writable
signing payer, and canonical System Program. The nullifier address is

```text
PDA("aspis-nullifier-v1", nullifier)
```

The pool stores magic `ASPS`, version 1, zero reserved bytes, sequence `u64`,
and the 32-byte root. The 72-byte marker stores magic `ASPN`, version 1, pool
key, and nullifier.

Ordering is fixed: validate all accounts/prestate; canonically derive the v3
statement; verify the complete proof; create the marker if absent; reacquire
and recheck both mutable states; then copy the final marker and pool images
with no fallible operation remaining. Writable locks serialize concurrent
root changes and duplicate nullifiers.

## Tests and remaining gate

Green tests cover canonical encoding/KAT, every public-field digest mutation,
v3 compression differential/KAT/order/domain teeth, invalid proof with no
mutation, successful injected transition, duplicate rejection, anchor
mismatch, every atomic public-field mutation with no mutation, exact account
layouts, and fail-closed tag 38 dispatch.

The trace/terminal migration, sibling/direction same-path wiring, atomic
layout/factor pins, actual 56,044-byte prover, complete q16 read-only verifier,
and literal SBF ledger are now complete. Tag 46 binds every public atomic field
and verifies in 1,179,451 CU, leaving 220,549 CU under the cap; see
`docs/stage2-atomic-state-only-profile20-acceptance.md`.

The account closure is now measured separately on SBF. A pre-owned zeroed
marker costs 1,189,180 CU end-to-end and canonical System-owned PDA creation
costs 1,191,513 CU; corrupt-proof rollback, duplicate rejection, exact account
images, and a two-signer concurrency race are green. See
`docs/stage2-atomic-state-only-profile20-mutation.md`.

Default tag 47 nevertheless remains fail-closed: profile 20 is sound but its
complete transcript-view hiding rank is red. The no-bypass production closure
exists only behind a nondefault candidate feature and rejects the committed
unmined proof before mutation.

Profile 21 now has append-only wrapper allocations: read-only tag 50,
no-bypass production mutation tag 51, and local-validator diagnostic tag 52.
All three are wired to one integrated proof parser and the frozen q16 basis
fingerprint `0xceb35dd3ee50e051`; default builds keep tags 50--52 fail-closed.
Tag 52's literal two-path measurement and rollback/race harness is implemented
and awaits the first self-verifying integrated proof fixture. See
`docs/stage2-atomic-state-only-profile21-mutation.md`. A measured CU fit cannot
enable tag 51 until the independent soundness, complete-view HVZK, private
Merkle, and production-PoW gates are green. Tag 38 remains permanently
fail-closed at `0x41531003`.

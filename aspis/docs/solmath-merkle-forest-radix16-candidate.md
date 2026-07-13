# SolMath staggered-forest and dense radix-16 Merkle candidates

Status: experimental and production-neutral.  The current profile-15 roots,
wire format, transcript, and verifier remain radix-4.

## Measured object and fixed geometry

Profile 15 samples 36 distinct indices from `2^12` layer-zero fibers.  The
proof authenticates five independent trees:

| commitment | binary depth | opened indices | unique leaves in current fixture |
|---|---:|---|---:|
| C1 | 12 | `q` | 36 |
| C2 | 12 | `q` | 36 |
| fold 1 | 10 | `unique(q >> 2)` | 34 |
| fold 2 | 8 | `unique(q >> 4)` | 33 |
| fold 3 | 6 | `unique(q >> 6)` | 27 |

The current fixture then has 13, 4, and 1 unique parent indices at the next
three global radix-4 levels.  Its current frontier counts are exactly
`301, 301, 201, 103, 28`, or 934 hashes / 29,888 bytes in total.

## Candidate A: acceptance-equivalent staggered forest traversal

`crates/aspis-core/src/merkle_forest.rs` walks the public index geometry once
while keeping all cryptographic objects independent.  Every lane retains:

- its own leaf digests;
- its own frontier stream and full-consumption check;
- its own SHA-256 call for every occupied parent;
- its own root equality check.

Only parent-index grouping and present-slot discovery are shared.  The hash
call count remains 365 and no proof byte or transcript field changes.  The
acceptance argument is pointwise: for every lane and every level, the shared
walk presents the same four ordered children to `node_hash4` as the existing
standalone verifier.  Therefore each lane's final digest and frontier cursor
are identical to an independent call to
`verify_radix4_minimal_subtree_bytes`.

The independent differential suite covers the production stagger
`[0, 0, 1, 2, 3]`.  It compares the forest result to five standalone
verifiers and rejects a mutation of every lane's frontier, root, or leaf, as
well as truncated/extended frontiers, unsorted/duplicate/out-of-range base
indices, and the wrong stagger.

This candidate changes no commitment assumption, WHIR/circle proximity
lemma, Fiat--Shamir order, soundness term, or hiding view.  Its CU effect must
be measured on SBF because it trades repeated control flow for additional
simultaneously live digest vectors.

## Candidate B: one dense radix-16 supernode per tree

The actual profile-15 geometry makes one fixed arity-16 level attractive.
Each schedule below replaces the same two adjacent global radix-4 levels,
where 13 child groups currently reduce to four parents:

| binary depth | current arities | candidate arities |
|---:|---|---|
| 12 | `4,4,4,4,4,4` | `4,4,4,16,4` |
| 10 | `4,4,4,4,4` | `4,4,16,4` |
| 8 | `4,4,4,4` | `4,16,4` |
| 6 | `4,4,4` | `16,4` |

For each of the five trees, the replacement changes 17 parent calls
(`13 + 4`) into four arity-16 calls.  It adds exactly nine frontier hashes
because a completely absent four-child subtree can no longer be represented
by one intermediate digest.  Summed over C1, C2, and the three fold trees:

| quantity | radix-4 | dense radix-16 | delta |
|---|---:|---:|---:|
| parent calls | 365 | 300 | -65 |
| frontier hashes | 934 | 979 | +45 |
| frontier bytes | 29,888 | 31,328 | +1,440 |
| parent preimage bytes | 47,085 | 46,380 | -705 |
| SHA-256 compression blocks | 1,095 | 1,020 | -75 |
| Agave v2.3 SHA meter | 54,385 CU | 48,540 CU | -5,845 CU |

The meter line follows Agave v2.3.0 exactly: SHA-256 charges an 85-CU base
plus `max(10, floor(slice_len / 2))` for each slice.  A packed 129-byte
radix-4 parent therefore costs 149 CU; a packed 513-byte radix-16 parent
costs 341 CU.  A scatter form (`domain || 16 child slices`) costs 351 CU but
avoids copying a 512-byte child array into a second 513-byte buffer.  Packed
and scatter forms must both be measured on SBF.

Radix-16 requires a new domain byte, fixed schedule framing, new roots, a
wire/profile version, regenerated prover trees/frontiers, transcript KATs,
and all existing Merkle corruption teeth.  Under SHA-256 collision
resistance it changes the commitment representation, not the PCS proximity
or hiding argument.  It must never be selected adaptively after queries are
drawn; the schedule is part of the committed profile.

## Other exact hash primitives to A/B

1. `node_hash4_scatter`: hash the domain byte and four existing child slices
   directly.  Agave charges only 10 CU more than the packed form, while SBF
   avoids the 128-byte repack.  This is digest-identical and protocol-neutral.
2. `sha256v_raw_sbf`: call `sol_sha256` into `[u8; 32]` directly instead of
   returning through `solana_program::hash::Hash`.  LLVM may already erase
   the wrapper, so only an isolated A/B can establish a saving.
3. A fused hash-and-canonical-decode cache for opened leaves.  Current Merkle
   authentication checks canonical limbs and query recombination decodes the
   same limbs again.  Caching all decoded profile-15 leaves is roughly 39 KiB,
   above the default 32-KiB heap, so a full cache is not viable as stated.
   A nine-query segment cache or streaming prepared leaf should be probed
   instead; acceptance stays exact if canonical rejection remains before use.

## Co-committing C1 and C2 is not an exact candidate

C1 is committed and absorbed before `lambda` and `chi`.  The prover then
constructs the challenge-dependent C2 helpers and commits C2.  A single
pre-challenge C1/C2 root is circular; a single post-challenge root lets the
prover choose C1 after seeing the challenges.  Keeping the early C1 root and
adding C1 into the late C2 tree retains both trees and is strictly more work.

Hypothetically merging the trees would remove one 301-hash frontier (9,632
bytes), one root (32 bytes), 112 radix-4 parent hashes, and 3,420 CU of leaf
SHA metering.  Those savings are not available without replacing the
Fiat--Shamir phase-binding construction and its proof.

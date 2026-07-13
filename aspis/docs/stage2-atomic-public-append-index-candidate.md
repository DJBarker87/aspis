# Atomic state-only public append-index candidate

Date: 2026-07-13

Status: **rejected for the current aligned 1,024-row / 16-semantic-column
layout; not integrated and not included in any CU or soundness claim.**  The
public-index idea is sound as statement metadata, but the complete relation
needs a third depth-20 hash chain which the current layout cannot contain.

## Objective

Keep the spent-note membership path private, but bind the output insertion
position to the pool account's public monotone `sequence`.  The output
insertion siblings remain private.  The proof must establish both equations
over the same sibling vector:

```text
Root(empty, sequence, siblings) = current_anchor
Root(output_commitment, sequence, siblings) = output_anchor.
```

The program checks `current_anchor` against the locked pool account before
verification, binds the pool key and sequence into Fiat--Shamir, verifies the
complete proof, consumes the canonical nullifier PDA, and writes
`(sequence + 1, output_anchor)` only after every fallible verification step.

## Why the index may be public

The insertion position is state-transition metadata, not note ownership,
value, salt, or the spent note's membership index.  It is already determined
by the pool's append counter.  Publishing it does not reveal the private
spent-note path.  The sibling path remains a masked witness.

This changes the atomic-v3 layout: no private output-path direction bit is
admitted as a witness cell, and no copy constraint may alias such a bit.
Every left/right ordering selector is the public bit
`(sequence >> level) & 1`.

## Soundness obligations

1. The statement digest binds the program id/pool key, pre-state sequence,
   current anchor, nullifier, output commitment, output anchor, asset id, and
   fee before any proof challenge derived from the statement.
2. Both insertion equations use the same 20 siblings and the same public
   sequence bits under the pinned ordered M31 Poseidon2 node compression.
3. The output commitment in the second equation is exactly the commitment
   constrained by the shielded-spend statement.
4. The pool account is writable and locked, its sequence/current anchor are
   rechecked after proof verification, and the nullifier PDA is canonical.
5. No account write or CPI occurs before complete proof acceptance.  After
   the first final data copy, no fallible operation remains.
6. The generated copy registry contains no output-path bit-alias family and
   hard-fails if the old atomic-v3 registry/fingerprint is reused.

## Capacity ruling

The old atomic-v3 host trace is a **replacement** shape, not an append shape.
Its two depth-20 chains prove

```text
Root(spent_note, private_index, private_siblings) = current_anchor
Root(output_commitment, private_index, private_siblings) = output_anchor.
```

Changing only the second chain's direction bits to the public `sequence`
does not prove that the sequence leaf was empty in `current_anchor`.  A full
shielded append must retain the private spent-note membership chain and add
both insertion chains:

```text
20 spent-note membership hashes
+ 20 empty-at-sequence hashes
+ 20 output-at-sequence hashes
+  9 owner/note/nullifier/output hashes
= 69 Poseidon2 permutations.
```

The current oracle assigns 16 aligned rows to each permutation.  Sixty-nine
permutations therefore require 1,104 rows, while the complete multilinear
domain has only 1,024 rows.  This exceeds the domain by 80 rows **before** any
auxiliary, direct-range, copy-helper, or hiding cells are allocated.  The
existing fixed layout begins its auxiliary region at row 784, so it has only
49 permutation blocks in practice.

This is an exact structural rejection, not a CU projection.  No host copy
registry, routing tensor, generated constants, hiding repin, or SBF tag is
valid for the complete candidate under the current layout.  Emitting those
objects for the cheaper two-chain relation would silently omit one of the
three root equations.

The executable guard is
`crates/aspis-statement/tests/atomic_public_append_capacity.rs`.  It pins the
69/1,104 count and exercises every public sequence bit, every private append
sibling, output-leaf binding, and the same-sibling requirement.

## Retired two-chain structural delta (must not be implemented)

The retired private-index registry has 183 copy terms: 23 non-path links, 40
path-current links, 80 path-selection terms, and 40 path-bit aliases.  The
public-index construction deletes the 40 bit aliases.  Public constant
ordering should also collapse the selection family, but no CU or term-count
credit may be taken: that recount describes only two chains and omits the
empty-at-sequence chain.  It is retained here solely to prevent the same
incomplete registry from being proposed again.

The construction deliberately does not compute 20 Poseidon2 hashes directly
in the Solana program.  The existing SBF probe measures roughly 463K CU for
20 optimized software permutations, so that alternative cannot fit the
remaining transaction budget.

## Required teeth

- flip every public sequence bit independently;
- use different siblings in the empty and output paths;
- swap left/right order at every level;
- alter the output commitment, current anchor, output anchor, pool key, or
  sequence after proof creation;
- reuse a nullifier and race two transactions against the same pool state;
- inject old private-index registry constants or fingerprints;
- fail proof verification and assert byte-identical pool/nullifier accounts;
- run at least 50 fresh random-QM31 compiled/reference identity points plus
  the existing padding, lambda-zero, and cross-residual corpus.

Promotion requires a new trace construction which first fits all 69
permutations plus auxiliary cells (or a separately proved accumulator
transition that removes a hash chain).  Only after that gate may an exact
registry/rank artifact, complete hiding proof, mined work, PDA mutation, and
integrated SBF measurement be generated.

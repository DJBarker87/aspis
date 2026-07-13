# Profile-21 high-coefficient switch carry

Date: 2026-07-13

Status: **universal q16 carry lemma proved; target-free rank diagnostic and
production splice still being integrated.** This note closes the discrete-q
gap for the switch's own `q+1` complement. It does not by itself prove the
remaining baseline masked-sumcheck/PCS `Good(schedule)` minors, the q-only
source-binding reduction, or complete EPRO HVZK.

## Frozen candidate View

The candidate removes `tX` and `muF`. After nonzero `delta`, it discloses
`U=F+delta X`; the prover derives and serializes

```text
tau = L(phi(U))
```

from public `U` and the public schedule before committing W1. The transcript
absorbs the serialized value and the selected SBF verifier uses it directly;
the verifier deliberately does **not** recompute `tau`. For an honest privacy
View, `tau` is a deterministic copy of a linear form already present in `U`,
so the affine rank model quotients it out rather than counting it as an
independent observation. Soundness against a prover that serializes a
different value is supplied by the q16 binding equations, not by verifier-side
recomputation.

For `q=16` and source dimension `d=35`, the exact scalar field View is

```text
U[35], A X[16], A F[16].
```

The identity `AF=A(U-delta X)=AU-delta AX` is retained in the matrix rather
than pre-deleted. The map has rank `35+16=51` over QM31. Its kernel has
dimension `70-51=19`: choose any `dX` in `ker(A)` and set
`dF=-delta dX`.

The source randomness space remains

```text
R = (x^2+1) P_<16.
```

Its query matrix is

```text
diag(q_i^2+1) * Vandermonde(q_0,...,q_15),
```

which is invertible for every accepted distinct q tuple. Therefore projection
of `ker(A)` onto the 19-dimensional source message complement is an
isomorphism. Removing the two target rows removes the former
`c|ker(E_q)` condition completely.

## Basis change

The old diagnostic carried natural line coefficient 1 through root zero and
used coefficients `0,2,...,18` at root one. The candidate instead carries

```text
root zero:  natural coefficient 18 (trace row 4*18 = 72)
root one:   natural coefficients 0..17.
```

This is a permutation of the same 19 old-View message coordinates. It changes
neither source dimension, U length, opened-leaf width nor query count. The
logical degree-below-35 mask-code basis is unchanged; only the map from its
19 message coordinates to the carried old View is reordered.

## Universal q-plus-carry lemma

Let `V=P_<19` in the natural line basis `B_0,...,B_18`. For any accepted q16
tuple, let `x_0,...,x_15` be the corresponding distinct root-one M31
abscissae and let

```text
E_q : V -> M31^16,
E_q(p) = (p(x_0),...,p(x_15)).
```

Let `ell_18(p)` be the natural coefficient of `B_18`. Then

```text
rank(E_q, ell_18) = 17                         (1)
```

for every accepted tuple.

Proof. Distinctness gives `rank(E_q)=16` by ordinary Vandermonde evaluation,
because the natural/monomial conversion is triangular with nonzero diagonal.
Put

```text
g_q(X) = product_i (X-x_i).
```

The degree-18 polynomial `X^2 g_q(X)` lies in `ker(E_q)`. It is monic, so its
natural coefficient 18 is the inverse of the nonzero leading coefficient of
`B_18`; in particular it is nonzero. Thus `ell_18` is not in the row span of
`E_q`, proving (1). QED.

The 16 rows in (1) are the selected root-one symbols already authenticated in
the main q loop. The seventeenth row is supplied by the pre-alpha p0 image of
the sole root-zero coordinate. Later root-one coordinates have zero p0 image,
so selecting coefficient 18 makes that p0 functional a nonzero scalar
multiple of `ell_18`. Any continuous-schedule zero of that scalar is a field-
challenge `Good(schedule)` event independent of the discrete q tuple; it is
not an identically bad q family.

Consequently the target-free switch kernel supplies exactly 17 QM31 (68 M31)
directions to the old PCS quotient for every accepted q16 tuple, once the
production quotient is differentially pinned to the displayed 16 query rows
plus one p0 row.

## Executable certificate

`profile21_high_switch_carry_certificate` builds the exact natural basis,
derives the production root-one abscissae, constructs `X^2 g_q`, verifies all
16 zeros and its nonzero natural coefficient 18, and independently computes
rank 17. The regression covers the frozen tuple, consecutive queries, an odd
stride, a same-coset tuple, a complete `T_16` fiber, and 64 deterministic
distinct tuples.

The high-switch full diagnostic additionally compares the real sparse circle
fold columns for natural coefficients `0..18` against this 17-row
certificate before running the complete M31 quotient. This catches a row,
normalization or coefficient-order drift that the abstract polynomial proof
would not catch.

## Remaining gates

Before this becomes a production claim:

1. replay the exact target-free profile-21 rank matrix and pin `51` source-
   observation rank, `19`-dimensional kernel and `68` complement pivots;
2. show the 68 production pivots are exactly 16 complete QM31 query groups
   plus one complete p0 group, with no OOD/final substitution;
3. differential-test row 72 through the root-zero relation, root-one
   coefficient map, disclosed U basis, q evaluator and verifier splice;
4. keep `tau` derived from U by the prover, serialize and transcript-absorb it,
   let the selected SBF verifier use it without recomputation, and pin the q16
   binding test that rejects a falsely serialized value; the privacy model
   must still quotient honest `tau` rather than count it as independent mask
   entropy;
5. separately close the remaining baseline terminal, masked-sumcheck and PCS
   nonzero-polynomial/containment minors for every q tuple; and
6. supply the q-only low-degree/source-binding reduction and the complete
   private-Merkle/EPRO simulator.

The basis permutation itself has zero expected verifier-CU and byte delta.
That statement must be remeasured only if integration materializes another
lane, target or commitment; none is authorized by this note.

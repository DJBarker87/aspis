# Profile-22 full-code mask: conditional lemma and corrected source-map ruling

Date: 2026-07-13

Status: **the historical 712-to-716 quotient is invalidated; the corrected
physical q16 replay is GREEN at 712/712 without X.**  The translation lemma
below remains algebraically valid under `C1` and `C2`, but a full-native X
lane is unnecessary for this target and adds no rank.  This fixed-schedule
result does not yet prove all-schedule containment, complete EPRO hiding, or
one-transaction completion, and it books no CU.

## Corrected physical replay

The historical screen paired an unbalanced C1 raw unit with a PCS tail cached
in the copy-inactive-balanced space.  Its reported 712-to-716 quotient was
not a polynomial image of any one physical source and is discarded.

The corrected source map was replayed on the frozen atomic-v3 q16 schedule.
For each semantic column with inactive dependent `d_c`, it uses

```text
active r                 -> e_r,
inactive r != d_c        -> e_r - e_d_c,
r = d_c                  -> 0
```

in the raw, terminal and PCS coordinates consistently.  Row zero remains
excluded as the fixed owner-key pre-absorb row.  The replay covers 16,352
physical M31 source directions and every legal zero-initial-claim sumcheck
direction.  It returns:

```text
baseline selected PCS rank                  712 M31
physical semantic augmented rank            712 M31
legal-sumcheck augmented rank                712 M31
compatibility rank                             4 M31
semantic pivots                                   []
legal-sumcheck pivots                             []
```

The full-native-X A/B on the same corrected target returns:

```text
native X variables                         1024 QM31
rank(R_c,tX)                                  65 QM31
ker(R_c,tX)                                  959 QM31
rank after complete native-X kernel          712 M31
physical semantic augmented rank             712 M31
new native-X pivots                              []
```

Thus the old four-M31 target disappears before X is inserted.  The native X
lane is rank-neutral and cannot be credited as the repair.  The independent
old projection tooth now fails its `compatibility_kernel` assertion, which
is the expected negative tooth: the old representatives do not belong to the
corrected physical compatibility kernel.

A separately labelled unbalanced upper-oracle control remains RED at
712-to-716, with pivots `1084..1087`. It is internally coherent, unlike the
historical splice, but it is not physical: production balancing never emits
an isolated inactive `e_r`. It is retained only as a stress test and does not
change the 712/712 same-statement ruling.

### Root cause of the historical quotient

The old semantic loop used `c1_raw_difference(rows,row,None)`, the raw image
of `e_r`, while `rows[row].pcs_tail` represented `e_r-e_d` on inactive rows.
Gaussian elimination can assign a rank to this concatenated vector, but no
single encoded message has that public view.  The four compatibility rows
and the later/p0 pivot were consequences of that splice.

For each semantic unit, the diagnostic first quotients its C1 raw opening by
the per-column raw mask echelon.  It then quotients the masked-sumcheck view.
Finally, a rank-four compatibility echelon combines sources so that the
*external zerocheck initial-claim* remainder vanishes.  The compatibility
pivots are `c0r1,c0r2,c0r3,c0r4`; the surviving representatives are
`c0r5,c1r1,c2r1,c3r1` with the nonzero compatibility coefficients recorded in
the semantic-quotient audit.  Those four appended coordinates are
bookkeeping for an external sumcheck relation.  They are not coordinates of
a root-zero main message, and zero compatibility remainder does not imply
the separate main-relation target equation `L_c(d)=0`.

Consequently the conditional lemma's implication

```text
A_c r + b_c(s) = 0  =>  O_c(d_c(r,s)) = 0
```

was never reached by the historical matrix and must not be declared false.
On the corrected fixed schedule there is no residual on which to test it.

### Historical rows 276--279

These rows do not recur after correction.  Their coordinate interpretation
is retained only to explain the discarded artifact.  The joint
post-sumcheck PCS coordinate order begins with 67 `QM31` H
observations: 64 layer-zero symbols and three terminal values.  Hence M31
rows `0..267` are H raw/terminal coordinates.  Rows `276..279` are literally
the four M31 coordinates at PCS-tail offset 8, an early later-opening value,
after Gaussian reduction by the 712-dimensional baseline.

They are not the physical serialized location of `p0.c4`.  An independent
H-raw-plus-p0 projection places the same invariant quotient at rows
`284..287`, exactly coefficient `c4` of the seven-coefficient round-zero
relation polynomial.  In the full PCS echelon, fold/relation dependencies
move that class to the earlier canonical representative `276..279`.  The
boundary identity `B4(p0)=4(c0+c4)` identifies it as one unconstrained
`QM31` early-p0 boundary carry.  The two row lists are therefore different
representatives of the same quotient, not conflicting diagnoses.

## Unselected protocol shape

The now-unselected candidate would have used the uncompressed profile-20 relation:

- retain the 84 statement claims and the existing width-28 `gamma` batch;
- widen the shared C2 leaf by one native `QM31` lane `X`;
- sample honest `X` uniformly from the complete 1,024-coordinate root-zero
  message space, rather than a slot-zero line subcode;
- after the X root, `z`, `kappa`, the 84 claims and `gamma` are fixed, disclose
  the exact scalar

  ```text
  tX = L_c(X);
  ```

- check and absorb the outer-group work witness, then sample fresh nonzero
  `epsilon`; and
- run the ordinary relation and all ordinary folds on

  ```text
  W0* = F_gamma + epsilon X.
  ```

Here `L_c` is the literal profile-20 initial relation functional.  It includes
all three point weights `[1,kappa,kappa^2]` and the atomic copy-inactive
indicator.  Omitting the inactive term is a different and invalid map.

There is no source polynomial `F`, disclosed `U`, source code switch, affine
multiplier, translated first-later root, standalone source MCA event, or
standalone source-query event.

Its proposed causal order was:

1. bind the statement, profile and layout registry;
2. commit C1 and the shared C2 tree containing `(H,G,X)`;
3. finish the masked zerocheck and bind `z` and all 84 original claims;
4. position the existing work witness and sample `gamma` and `kappa` in the
   frozen profile order;
5. disclose and absorb `tX=L_c(X)`;
6. check and absorb a post-`tX` outer-group work witness;
7. sample nonzero `epsilon`;
8. run the ordinary OOD relation, commitments and folds on `W0*`;
9. position the final work witness and derive q16 without replacement; and
10. authenticate the ordinary C1/C2 fibers, including all four native X
    symbols in every queried fiber, and check the ordinary fold path.

Those ordering requirements remain necessary for the conditional algebra,
but they cannot repair the failed containment premise.

## Exact spaces and maps

Let

```text
F = M31,
K = QM31,
V = K^1024.
```

`V` is the complete natural root-zero message space used by the existing
rate-1/512 circle code.  For one fixed valid public verifier schedule `c`,
define three K-linear maps.

### Exact raw-and-target map

Let

```text
R_c : V -> K^(4q)
```

return the literal four authenticated layer-zero symbols in every selected
query fiber.  At q16 its codomain has 64 `K` coordinates.  It is not the
post-fold one-symbol shorthand.

Define

```text
L_c(v)
  = v(z)
  + kappa v(succ(z))
  + kappa^2 v(xor12(z))
  + sum_{r in copy-inactive(c)} v_r.
```

The last term uses the exact atomic-v3 inactive mask registry.  Put

```text
O_c = (R_c,L_c) : V -> K^(4q+1).
```

### Complete main-PCS tail map

Let

```text
P_c : V -> T_c
```

be the complete K-linear continuation of one root-zero message after the
fields in `O_c`: every round-zero relation-polynomial coefficient, all circle
and line OOD values, every later-layer queried fiber, every later relation
polynomial and all final coefficients.  For fixed challenges, encoding,
relation construction and all folds are K-linear, so this is one linear map.

Merkle roots, salts and frontier hashes are deliberately not coordinates of
`P_c`; they are covered by the private-Merkle/EPRO hybrid, not field rank.

### Existing-mask residual map

Let `r` denote all existing profile-20 mask coins, and let `s` be any valid
same-statement witness difference from the conservative semantic space.  Let

```text
A_c r + b_c(s)
```

be their complete non-X public field difference before the main PCS tail:
separate authenticated C1/C2 raw values, all 84 claims and the external
masked-sumcheck wire.  Let

```text
d_c(r,s) in V
```

be the corresponding difference of the `gamma`-combined root-zero message.

The production maps must satisfy the following commuting identities:

```text
A_c r + b_c(s) = 0  =>  O_c(d_c(r,s)) = 0,       (C1)

residual main-PCS field view = P_c(d_c(r,s)).     (C2)
```

`C1` is not a heuristic rank statement.  Its raw part says that gamma
combination commutes with the separately authenticated four-symbol leaves.
Its target part says that the exact weighted combination of the canceled 84
claims is `L_c(d)`, while every original honest combined word and every
allowed existing-mask difference has copy-inactive target zero.  `C2` is
linearity of the literal relation and fold implementation.

## Conditional translation lemma (valid but not needed for this target)

**Lemma.**  Fix any parser-valid schedule `c` and any nonzero
`epsilon in K`.  Assume `C1` and `C2`.  If the existing masks cancel the
non-X field difference for a same-statement witness difference, then the
native full-code X mask cancels its entire residual main-PCS field view.

**Proof.**  Choose existing-mask translation `r` with

```text
A_c r + b_c(s) = 0
```

and put `d=d_c(r,s)`.  By `C1`, `O_c(d)=0`.  Since honest `X` ranges over all
of `V`, translate its coins by

```text
Delta X = -epsilon^-1 d.
```

This is a bijection of uniform `V`.  Linearity gives

```text
O_c(Delta X) = -epsilon^-1 O_c(d) = 0,
```

so every authenticated X opening and the disclosed `tX` remain unchanged.
By `C2`, the change in the main PCS continuation is

```text
epsilon P_c(Delta X) = -P_c(d),
```

which cancels the complete residual tail.  The external masked-sumcheck view
does not depend on X and was already canceled by `r`.  Therefore the complete
field views agree.  QED.

The argument does not divide by a query determinant and does not assume that
`O_c` has full row rank.  It remains true for every challenge value and every
query tuple for which the production parser and arithmetic are defined.  The
only new scalar condition is the already-enforced `epsilon != 0`.

If `C1` and `C2` held for the target residual, the abstract closure would
have:

```text
bad-rank probability       0,
Good(schedule) retry       none,
rank-availability term     none.
```

The corrected per-column-balanced replay has no post-elimination semantic
residual, so this conditional conclusion is not needed for the fixed q16
target.  It remains a reusable algebraic lemma only if some independently
validated residual later satisfies `C1` and `C2`.

## Why source dimension is not decisive

The conditional proof would use `d in V` itself as the X-coin translation,
so widening beyond a slot-zero line was a necessary stress test.  The exact
full-space result shows it is not sufficient: the obstruction is a mismatch
between the compatibility/target maps, not a shortage of X entropy.

The exact d19 affine candidate

```text
p(t)=t-u,  X in K[t]_<19
```

was tested on the frozen profile-20 q16 schedule with the literal compact
unbalanced target and complete sparse/dense PCS tail.  Its local identities
passed, its raw rank was 16, `raw+tX` rank was 17 and its conditioned kernel
had dimension two over K.  Nevertheless it added no PCS pivot:

```text
compact helper PCS             444 M31
after d19 affine lean X         444 M31
semantic/legal target           448 M31
new X pivots                         []
semantic pivots                 [5,4,6,7].
```

The switch-minor fingerprint was `0xd19e59fbae3824de`, the affine multiplier
fingerprint was `0x54a13d17fd4b9a42`, and the product-basis fingerprint was
`0x48138d6a98a90be8`.  Thus a nonvanishing pointwise multiplier and two hidden
K directions do not imply containment.  Widening to the full message space
confirms, rather than avoids, that dimension-count error.

## Conditional soundness boundary

Had containment passed, honest `X` would be a uniform element of `V` and its encoded word would be in
the same exact circle code as every main semantic column.  Raising X from a
line subcode to full `V` changes no verifier leaf width or query count: one
native X value was already present per C2 codeword symbol.

A malicious prover is not trusted to choose a low-degree/full-message X.  The
soundness route is instead:

1. the existing `gamma` MCA binds the width-28 inner combination `F_gamma`;
2. the post-`tX` generator `(1,epsilon)` binds `(F_gamma,X)` through the exact
   circle Johnson MCA result and the ordinary query-consistency checks; and
3. a false `tX` is fixed before fresh nonzero `epsilon`, so its discrepancy is
   an independently charged degree-one local event.

No soundness or Johnson credit is booked while privacy containment is under
re-audit.  The drafted outer-generator ledger remains only a conditional
sensitivity analysis, not an active construction.

## Compact consequence

The same abstract lemma could cover the compact 61-claim design only if its
exact maps satisfied

```text
L_compact(d)
  = delta*tau*S_gamma(z)
  + delta*kappa*S_gamma(succ(z))
  + delta*kappa^2*S_gamma(xor12(z))
  + tau*AUX_gamma(z)
  + A_tail
  + inactive(d)
  = 0
```

whenever the compact public fields cancel.  That version adds `A_tail`,
`tau`, `delta`, a three-group outer generator and their causal checks.

The uncompressed source-map mismatch removes the basis for integrating this
compact variant.  Compact/full-X is not promoted without a physically
coherent uncompressed replay and then its own exact map/rank replay.  No CU
saving is booked.

## Required diagnostic teeth before any reconsideration

Any successor based on the conditional lemma must first turn the failed
residual-map assumption into an executable guard.  At minimum:

1. **Full-space encoder.**  Exercise all 1,024 natural message unit rows in
   all four K tower coordinates.  The X encoder must be the K-linear extension
   of the same root-zero `CircleEncoder`; it must not silently retain the
   slot-zero source embedding.
2. **Raw commutation.**  On random messages and every queried slot, compare
   the separately encoded/gamma-combined symbol with encoding the combined
   message.  Test all four raw symbols, not only the normalized fold.
3. **Target commutation.**  Compare the production `tX` routine to a dense
   dot with `[1,kappa,kappa^2]` plus the exact atomic inactive indicator.
   Omit/flip one inactive row as a rejecting tooth.
4. **Complete tail parity.**  For unit rows and random dense messages, compare
   sparse row-map combination against the independent incremental-relation
   path through p0, all OOD values, every fold/opening and final coefficients.
5. **Translation tooth.**  Construct random `d in ker O_c`, random nonzero
   `epsilon`, and random X.  Check byte-for-byte field equality between
   `(X,tail)` and `(X-epsilon^-1 d,tail+d)` on all four tower rotations.
6. **Residual-map tooth.**  If a future target has a residual, export an actual main-message candidate
   `d` alongside the exact semantic/mask elimination and report separately
   `R_c(d)`, `L_c(d)`, the four external compatibility coordinates, and
   `carry-P_c(d)`.  A quotient vector alone is not evidence of that identity.
7. **Ordering teeth.**  Reorder X root, `tX`, outer work and `epsilon`; each
   weakened schedule must change the transcript or reject.  Zero epsilon is
   rejected canonically.
8. **Corruption teeth.**  Corrupt each X raw slot, `tX`, p0, each OOD block,
   one later fiber and one final coefficient independently.  The production
   verifier must reject.
9. **Layout binding.**  The shared-C2 width, X slot, full-message basis,
   inactive mask registry and all compiled constants enter the layout hash;
   a stale rank/layout artifact must fail the build.
10. **Complete-view boundary.**  Proof-account bytes, logs, salts, Merkle
    roots/paths, retry/abort behavior and atomic mutation are appended through
    the private-Merkle/EPRO simulator.  They are not declared hidden by this
    field identity alone.

## Ruling and successor requirement

The corrected physical target is already contained, so no X repair is needed
for this quotient.  The remaining work is the all-schedule containment proof,
the independent EPRO/complete-view surfaces, atomic mutation and integrated
CU.  Any different nonzero residual must be validated with a coherent source
map before it can define a repair gate.

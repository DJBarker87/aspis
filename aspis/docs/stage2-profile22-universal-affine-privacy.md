# Profile 22: universal affine-privacy reduction

Date: 2026-07-13

Status: **the physical source-map defect is closed, but the all-schedule
root-neutral sumcheck lemma is refuted.**  Exact M31 elimination leaves a
nonzero legal-wire deficit under both the selected factor schedule and the
`G=L_0^23` complete-shared-power candidate.  The all-schedule structural
route is therefore closed; production acceptance remains disabled.

## Exact physical module

Let `F=M31`, `K=QM31`, and let `I` be the atomic-v3 copy-inactive row set.
For each semantic column `c`, production balancing chooses an inactive
dependent `d_c`.  The same-statement source used by the rank gate is exactly

```text
B_c = span_F({e_r : r active, r != 0}
             union {e_r-e_d_c : r inactive, r != d_c}).
```

Consequently every `b in B_c` has zero inactive sum.  The basis is applied
identically to the C1 query symbols, the three terminal evaluations, and the
complete encoded continuation.  This is the source emitted by the physical
trace/balancing code.  An isolated inactive `e_r` is not in `B_c`.

For a fixed public schedule `s`, let

```text
O_s : K^1024 -> K^(4q+3)
```

be the four authenticated root symbols per q16 fiber and three terminal
evaluations, and let

```text
T_s : V0 -> P_s,
V0 = {v in K^1024 : sum_{r in I} v_r = 0},
```

be the complete later-query/OOD/relation/final-coefficient continuation.
The C2 encoder, `StateOnlyIncrementalRelation`, and every fold are K-linear,
so `T_s` is one K-linear map for every parser-valid schedule.  The independent
dense C2 execution guard now checks the sparse implementation against this
literal map.

This immediately proves two schedule-independent facts:

1. every physical semantic difference is in `V0`; and
2. if a mask-coin translation makes the gamma-combined root message
   difference zero, then every PCS/fold/OOD field difference is zero because
   `T_s(0)=0`.

It also explains the retired four-limb result.  The old diagnostic paired
raw `e_r` with a PCS image cached as `e_r-e_d_c`.  That splice was not one
polynomial source.  The internally consistent unbalanced control remains
red, but production never emits it.

## Query block proved for every distinct q16

All sixteen semantic supports contain rows `896..=1023`, with row 1023 as
the balancing coordinate.  In the circle tensor basis this is a nonzero
common prefix times four sectors over the 32-dimensional natural `t=T_2(x)`
basis.  For every distinct q16 tuple the 64 queried circle symbols have rank
64.  Their kernel is

```text
g_q(t) h(t),  deg(g_q)=16,
```

in each of the four sectors.  Since `g_q(1) != 0`, imposing the inactive-sum
hyperplane does not change this classification.

After quotienting those 64 symbols, natural input degrees `12..15` map
triangularly to output blocks `28..31`.  The diagonal depends only on frozen
natural-basis leading coefficients, not on q.  The challenge assignment

```text
z = [1,1,1,1,1,1,0,1,i,u]
```

makes the remaining three-terminal map rank 12.  Hence, for **every**
distinct q16 tuple, the terminal determinant is a nonzero polynomial in the
M31 limbs of z.  There is no discrete-query retry term for this block.  This
does not say that the terminal rank is 12 at every z.

In particular `z=(0,...,0)` is not a physical privacy counterexample.  On
`B_c`, all three terminal functionals then vanish (they select fixed Boolean
rows 0, 1, and 12), so both the mask and physical target raw images have rank
64.  The executable guard below pins that distinction between full ambient
rank and containment.

## Refuted root-neutral lemma

Write `R_s` for the separate raw-opening map of the 16 semantic columns, ten
full-domain M31 mask-only columns, and full-domain QM31 `G`.  Write `S_s` for
the degree-27 masked-sumcheck wire, and

```text
Gamma_gamma(m) = sum_j gamma^j m_j
```

for the combined root message.  Let `M` be the frozen physical mask module.
The missing statement is the following source-level surjectivity theorem.

The proposed statement was:

**Root-neutral sumcheck lemma.**  For every distinct q16 schedule and every
accepted nonzero `eta` and `gamma`, the image of

```text
(R_s, S_s, Gamma_gamma) : M -> Raw_s x SC_s x V0
```

contains the corresponding image of every physical semantic source
`direct_sum_c B_c` and every legal zero-initial-claim sumcheck difference.

Equivalently, after the semantic masks cancel the separate C1 raw view, the
ten full-domain mask-only tables and `G` must be able to cancel both the
remaining legal sumcheck wire and the gamma-combined root message.  Once
this holds, PCS containment is schedule-independent by K-linearity of
`T_s`; no 712-row PCS determinant or PCS Schwartz--Zippel term is needed.

The existing `masked_sumcheck_rank=1080` alone is insufficient: it proves
surjectivity after quotienting raw openings but does not require the
sumcheck translation to be root-neutral.  Likewise one numeric 712/712
minor does not prove this lemma for all q.

The lemma is now refuted by the exact reduced map below.

For a C1 source `U_j` at generator index `j`, nonzero gamma permits the
pointwise elimination

```text
G_j = -gamma^(j-27) U_j.
```

This makes the gamma-combined root message identically zero.  Because the
C1 and G raw maps are restrictions of the same K-linear evaluation map,
`O_s(U_j)=0` implies `O_s(G_j)=0`.  The probe then quotients each separate
raw block, conditions the one shared initial QM31 claim exactly once, and
ranks the remaining 270 QM31 / 1080 M31 legal sumcheck coordinates.  No PCS
minor or sampled determinant appears in this reduction.

## Exact negative ranks

The exact ranks are:

```text
factor schedule            z schedule          mask-only  +semantic  +H1   target
selected production        frozen q16              976       1072   1076    1080
selected production        affine-degenerate z     844        900    912    1080
G=L0^23 complete powers    frozen q16              884       1058   1062    1080
G=L0^23 complete powers    affine-degenerate z     772        870    882    1080
```

The H1 column above is the literal inactive-balanced H1 source paired with
G, with zero direct unmasked-oracle image.  This is not an invented source:
the checked terminal identity shows that `theta=mu=0` removes every H1
contribution to the unmasked oracle.  Those values are algebraically allowed
by the current challenge samplers; only `eta` and `gamma` are required
nonzero.  Thus the final column gives an explicit permitted challenge-class
counterexample to the claimed universal statement.  Even it remains four
M31 dimensions short on the frozen z and much farther short on the explicit
affine-degenerate z.

The affine-degenerate point is

```text
z = [-(32+i)/9, 1, 1, 1, 1, 1, 0, 1, i, u].
```

It satisfies `sum_(v=0)^8 (9-v)z_v=0`, making the last-round `L_16`
affine form proportional to `L_0`.  Assigning G the previously missing
shared power `L_0^23` does not repair the root-neutral map; it lowers the
rank in both tested schedules.

There is also a direct full-gate tooth which retains the fixture's nonzero
front, OOD, fold, and q16 challenges and mutates only z to the point above.
On the last-round line `t=x_9`, the two forms satisfy the exact identity

```text
L0  = C0  + 201 t,
L16 = C16 + 1625 t,
201 C16 - 1625 C0 = 5600 sum_(v=0)^8 (9-v)z_v.
```

Thus `L16=(1625/201)L0` at the selected point and production's
`1+L16^26` falls into `span{1,L0^26}`.  The complete conservative gate
reaches the raw quotient, then fails exactly with

```text
MaskedSumcheckRank { got: 916, want: 1080 }.
```

This is a parser-valid public challenge assignment, not a claimed observed
Fiat--Shamir transcript.  It is enough to refute universal containment.

The bounded one-lane repair scan is also negative.  Replacing production G
with `L0^23` gives 1066/1080 on frozen z and 886/1080 on the affine point.
Retaining production G and adding a full-domain QM31 G2 lane gives:

```text
G2 factor                         frozen z    affine point
shared family 0, L^23             1080          928
independent family 17, L^23        --            928
independent family 17, 1+L^26      --            928
```

The frozen shared-G2 run retains physical and legal containment at 712/712,
but each scanned G2 restores only 12 of the affine point's missing 164 M31
directions.  Exponent coverage is therefore not a universal argument: the
source-support and raw-kernel coupling is load-bearing.

## Selected Good22 gate

Because the universal lemma is false, profile 22 selects the minimal
privacy-only public predicate, containment itself:

```text
Good22(s) iff rank(A_s) = rank([A_s | D_phys,s]),
```

where `A_s` is the complete mask map for every non-hash public field byte and
`D_phys,s` is the frozen physical basis `direct_sum B_c` plus the legal
sumcheck and active-helper differences.  Both matrices are canonical
functions only of the layout fingerprint and public verifier schedule.  The
predicate must not inspect the witness, realized masks, Merkle salts, roots,
or a prover-selected minor.  Full raw/SC/PCS ranks may be used as a stronger
operational gate, but they are not the minimal predicate and can reject a
schedule such as Boolean z even when exact containment still holds.

`Good22` is honest-prover-only unless a failed rank also affects soundness.
Failed attempts burn their nonce and publish no root, proof byte, retry
count, log, or timing class.  Conditioning on `Good22` then gives exact
affine-view equality for emitted proofs; its bad-schedule probability is an
availability term, not a privacy error.

### Termination ledger

The q-uniform raw certificate still supports the conservative mixed-M31 bound

```text
beta_raw <= 3,240 / (2^31-1) < 2^-19.33.
```

The former raw-only six/seven-attempt conclusion is no longer usable because
its structural root-neutral premise is false.

If instead a q-uniform nonzero-polynomial theorem is proved for the canonical
1080-row sumcheck minor, the current conservative degree is

```text
3,240 + 37,800 = 41,040,
beta_raw+sc <= 41,040 / (2^31-1) < 2^-15.67,
```

so retry caps 7 and 9 suffice for 100- and 128-bit completeness.  These are
ordinary M31 bounds because the determinants are taken after tower-coordinate
expansion; `|QM31|` is not a valid denominator.

Without the root-neutral lemma, retaining the frozen 712-row PCS determinant
gives the conditional no-source degree

```text
3,240 + 37,800 + 6,044,880 = 6,085,920,
beta <= 6,085,920 / (2^31-1) < 2^-8.46,
```

and retry caps 12 and 16.  This last numerical bound is **not yet usable**:
the required every-q nonzero-polynomial premise for the residual sumcheck/PCS
minor has not been proved.  A frozen nonzero minor cannot supply it.

The displayed affine-degenerate family is one nontrivial K-linear equation
in independently uniform `z_0..z_8`.  In the random-oracle model its exact
probability is `1/|QM31|`, approximately `2^-124`.  This bounds only that
known family.  It is not an upper bound for every `Good22` failure and is not
a termination theorem for the selected gate.

## Executable guards

```text
NO_DNA=1 cargo test -q -p aspis-prover --test profile21_hvzk_privacy \
  all_q_semantic_kernel_terminal12_has_a_query_independent_certificate

NO_DNA=1 cargo test -q -p aspis-prover --test profile21_hvzk_privacy \
  boolean_zero_terminal_collapse_is_not_a_physical_containment_counterexample

NO_DNA=1 cargo test -q -p aspis-prover --test profile21_hvzk_privacy \
  final_round_mask_linear_forms_have_an_explicit_affine_degeneracy

NO_DNA=1 cargo test -q -p aspis-prover --test profile21_hvzk_privacy -- \
  --ignored final_round_affine_degeneracy_drops_masked_sumcheck_rank_to_916

NO_DNA=1 cargo test --release -q -p aspis-prover \
  --test profile21_hvzk_privacy -- --ignored \
  one_additive_g2_lane_does_not_repair_the_affine_degeneracy

NO_DNA=1 target/release/examples/profile21_good_schedule_probe witness-consecutive
NO_DNA=1 target/release/examples/profile21_good_schedule_probe witness-unit-front
NO_DNA=1 target/release/examples/profile21_good_schedule_probe witness-unit-folds
NO_DNA=1 target/release/examples/profile21_good_schedule_probe \
  g2shared23-last-round-affine-degenerate
```

The exact root-neutral rank commands are:

```text
NO_DNA=1 cargo build --release -q -p aspis-prover \
  --example state_only_hiding_rank_gate

NO_DNA=1 target/release/examples/state_only_hiding_rank_gate \
  results/stage2/proofs/atomic_state_only_profile22_v3_unmined.bin \
  52e96f99756fe8fd2d8b7a700019b143d7eb549af1bf1ae987e99a75cadcd4c9 \
  <mode>
```

with each mode:

```text
atomic-root-neutral-sumcheck
atomic-root-neutral-sumcheck-bad-affine
atomic-root-neutral-complete23
atomic-root-neutral-complete23-bad-affine
```

The H1 identity tooth is:

```text
NO_DNA=1 cargo test -q -p aspis-statement \
  zero_theta_and_mu_remove_every_h1_sumcheck_contribution
```

The complete sparse/dense physical projection guard remains mandatory.  The
unbalanced upper-oracle run remains a negative tooth and must never decide
same-statement physical containment.

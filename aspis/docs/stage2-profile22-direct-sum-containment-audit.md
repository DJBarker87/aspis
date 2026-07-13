# Profile 22: literal direct-sum containment audit

Date: 2026-07-13

## Result

The frozen actual q16 schedule is **red** for the documented physical
direct-sum target.  Exact block Gaussian elimination gives

```text
mask view       = 2244 raw + 1080 sumcheck + 712 PCS = 4036
+ physical D    =                                      4040
+ legal SC      =                                      4040
+ active helper =                                      4040
```

The four-direction deficit is not repaired by either of the already-modelled
sources checked here:

* the corrected lean native full-X affine replay is `4296 -> 4300`: the 260
  M31 dimensions of `(64 raw X symbols,tX)` are counted in the View and
  `ker(R_q,tX)` is inserted into the PCS mask before target augmentation;
* one full-domain QM31 G2 lane with factor `Shared0Pow23` changes the ranks to
  `4304 -> 4308`.  Its complete 268-M31 raw block shifts both sides equally
  and preserves the same deficit.

These are host-only rank diagnostics.  No proof wire, transcript, production
mask sampler, or verifier predicate changes in this audit.

The repair search is now frozen.  The selected proof route is the narrower
terminal-compatible valid-View theorem on full-sumcheck schedules, whose
coupled no-wire compatibility result is `712/712`.  The independent
direct-sum results below remain deliberately stronger negative stress tests;
they are not the classifier used by that theorem.

## Which target is being tested

The target frozen in the hiding note is the direct sum of:

1. the physical per-semantic-column source spaces `B_c` emitted by the actual
   sampler;
2. all 1,080 independently allowed zero-initial-claim sumcheck coordinates;
3. active helper differences.

For a block view ordered as raw, sumcheck, PCS, containment is

```text
rank(A) = rank([A | D_phys]).
```

The implementation first quotients every target through the exact raw block.
A target that then creates a sumcheck pivot is retained as a new public-view
direction.  Only a true sumcheck kernel is allowed to continue into the PCS
quotient.  This is ordinary block Gaussian elimination and does not assume
that a deficient sumcheck block is full.

## Why the previous green was false

The historical diagnostic first discarded target sumcheck remainders and
compared only their PCS carries.  On the last-round affine counterexample it
reported

```text
masked sumcheck rank       = 790 / 1080
legacy semantic PCS rank   = 712
legacy legal PCS rank      = 712
compatibility remainder    = 294
```

The equality `712 = 712` is not containment.  Literal elimination gives

```text
mask view       = 2244 + 790 + 712 = 3746
+ physical D    =                     3891
+ legal SC      =                     4040
+ active helper =                     4040
```

The omitted 294-dimensional compatibility remainder is exactly why the old
PCS-only classifier could turn red into green.  The `witness_direct_sum_*`
fields are now the only fields in this report that classify the documented
direct-sum target.

It may be possible to define a smaller *coupled* witness-difference source in
which semantic and sumcheck differences obey additional equations.  That is
a different theorem and a different definition fingerprint.  It must be
defined and proved before it can replace `D_phys`; this audit does not promote
the legacy compatibility-kernel interpretation.

## Frozen actual-source probes

### Baseline and native full-X

The original native-X diagnostic left the literal direct-sum fields at their
pre-X values and was therefore not an exact negative.  The corrected probe
conditions the complete 1,024-QM31 X message on its independently public
minimal wire—64 authenticated q symbols plus `tX`—and inserts that kernel's
PCS image before the physical target.  On the actual transcript:

```text
masked_sumcheck_rank = 1080
joint_pcs_rank       = 712
X observation rank   = 65 QM31; conditioned kernel = 959 QM31
direct_sum ranks     = mask 4296, physical 4300, legal 4300, helper 4300
native-X conditioned = 712
native-X semantic    = 712
```

Native-X is therefore still not a repair for the conservative direct-sum
target, but the ruling now comes from the exact affine View rather than the
mechanically unchanged baseline fields.

Two controls pin the boundary.  Omitting `tX` (an unsound wire) gives one
extra QM31 PCS direction, `712 -> 716`, yet the physical augmentation still
moves `4296 -> 4300`.  The bound reduced switch
`span{B18} direct-sum (x^2+1)P_<16`, with shared-C2 X/F fibers and disclosed
`U=F+delta X`, likewise has observation rank 33/34 and one-QM31 kernel, but
returns `4172 -> 4176`.  Both close the older compatibility quotient while
remaining red for this deliberately stronger direct-sum source.

These negatives do not refute the narrower terminal-compatible valid-View
theorem: on full-sumcheck schedules that theorem uses the coupled legal
source, for which the no-wire compatibility result is `712/712`.  The
direct-sum rows remain conservative stress tests and are not a replacement
for that theorem.

### Shared0Pow23 G2

The exact G2 probe retains the actual source map, factor, gamma exponent,
raw/terminal openings, and PCS image:

```text
tail basis           = 4092 M31
tail raw kernel      = 3824 M31
tail raw rank        = 268 M31
masked_sumcheck_rank = 1080
joint_pcs_rank       = 712
direct_sum ranks     = mask 4304, physical 4308, legal 4308, helper 4308
```

It also remains red.  The other proposed G2 factors were not scanned after
this literal failure: the task was to test whether an existing source family
closed the direct-sum gap, not to accumulate PCS-only near misses.

## Executable guards

The earlier adversarial schedule is pinned by:

```sh
NO_DNA=1 cargo test --release -q -p aspis-prover \
  --test profile21_hvzk_privacy \
  single_last_round_exclusion_is_red_for_documented_minimal_containment \
  -- --ignored
```

The frozen actual baseline/native-X result is pinned by:

```sh
NO_DNA=1 cargo test --release -q -p aspis-prover \
  --test profile21_hvzk_privacy \
  frozen_actual_direct_sum_is_red_and_native_x_does_not_repair_it \
  -- --ignored
```

The raw-only X and reduced natural-B18 controls are pinned by:

```sh
NO_DNA=1 cargo test --release -q -p aspis-prover \
  --test profile21_hvzk_privacy \
  frozen_actual_native_x_raw_only_control_localizes_the_tx_obstruction \
  -- --ignored

NO_DNA=1 cargo test --release -q -p aspis-prover \
  --test profile21_hvzk_privacy \
  frozen_actual_reduced_natural18_switch_tests_literal_direct_sum \
  -- --ignored
```

The exact G2 result is pinned by:

```sh
NO_DNA=1 cargo test --release -q -p aspis-prover \
  --test profile21_hvzk_privacy \
  frozen_actual_shared0_pow23_g2_preserves_the_direct_sum_deficit \
  -- --ignored
```

## Verdict

Freeze full-X, its raw-only control, reduced d17, and G2 as direct-sum
negatives.  Do not integrate any of them and do not continue repair scans.
The selected no-wire route proves containment for the coupled
terminal-compatible valid View on full-sumcheck schedules.  These literal
direct-sum tests remain regression guards against accidentally claiming the
stronger independent-source theorem.

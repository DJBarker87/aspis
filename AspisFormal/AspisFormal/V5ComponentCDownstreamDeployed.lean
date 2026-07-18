import AspisFormal.V5ComponentCRelationTailCodec

/-!
# v5 Component C: the universal deployed downstream-evaluator seam

`V5ComponentCConcreteDownstream` fixes one complete Component-C schedule and the
map `concreteDownstream schedule enc`, and names the remaining Rust obligation as
`UnmetDeployment.RustConcreteDownstreamCorresponds`.  That obligation is a bare
`∀ free, rustDownstream free = concreteDownstream schedule enc (encodeFree free)`:
it already assumes a `CompleteFixedSchedule` (with its alpha-agreement field) and
hides all branch/order/dedup structure behind bundled linear-map composition.

This leaf closes that seam down to a single, fully specified code/model function
equality.  Concretely it:

* packages a supplied `DeployedRuntimeSchedule` model into a
  `CompleteFixedSchedule`, discharging relation/FRI alpha agreement *by
  construction* rather than as a caller premise;
* defines `deployedEvaluate`, an explicit flat-row evaluator in a canonical
  schedule-sized view order — round OOD reads, degree-six relation polynomial rows (dual
  fold, division by four), the arity-four codeword folds, the schedule-sized
  deduplicated later rows, then the four final coefficients;
* proves `deployedEvaluate rt enc = concreteDownstream (decodeSchedule rt) enc`
  for **arbitrary supplied schedule records**, not one frozen tuple;
* reduces `RustConcreteDownstreamCorresponds` to the single premise
  `RustDownstreamEvaluatorEqualsDeployed`, an exact function equality
  `rustEvaluate = fun free => deployedEvaluate rt enc (encodeFree free)`.

## The runtime shape, and the two divergent Rust layouts

The deployed released view is the *deduplicated* later layout used by the runtime
prover and verifier:

* `crates/aspis-prover/src/v5_real_host_proof.rs` `build_v5_real_host_artifact`
  opens `opening_indices.later[layer]`;
* `programs/aspis-verifier/src/v5_fri_checks.rs` `check_v5_fri_queries` iterates
  exactly those `openings.indices.later[layer]` sets;
* `crates/aspis-core/src/circle_line_merkle.rs`
  `derive_circle_line_query_indices_for_count` builds each set by
  `sort_unstable; dedup` on `query >> [2,4,6]`, so the three counts are variable
  (its unit test yields lengths `4, 3, 2`, not `18, 18, 18`).

The offline generator `crates/aspis-prover/src/v5_component_c_fmat.rs` uses a
distinct, non-representative layout: `schedule.base.later_fibres : [[u32; 18]; 3]`
with the compile-time assertion `V5_C_FMAT_ROWS == 256`.  That array **cannot**
represent dedup counts other than eighteen.  This file therefore models the
schedule-sized deduplicated view and proves, rather than silently assuming, that
the frozen `256`-row shape is the `n1 + n2 + n3 = 54` corner; with the explicit
runtime bounds `n_i <= 18`, this is equivalent to `(n1,n2,n3)=(18,18,18)`.
The exact transcript-to-schedule derivation remains outside this leaf.

## Honest boundary

The 58-field/928-byte relation tail is not re-proved here: the byte codec of
`V5ComponentCRelationTailCodec` is reused verbatim.  The circle encoder `enc` and
the free-coordinate encoder `encodeFree` remain the model's separate, pre-existing
correspondence seams and are carried as parameters.  Lean cannot inspect Rust
object code, so the evaluator edge is the one named function equality.  Binding
the supplied schedule record to the transcript-derived, sorted/deduplicated Rust
indices is a separate code/model obligation.  No C-DEC, transport, HVZK, or
deployed-zero-knowledge claim is made.
-/

namespace AspisV5ComponentCDownstreamDeployed

open AspisV5ComponentCConcreteFoldLinearity
open AspisV5ComponentCRelationRowLinearity
open AspisV5ComponentCConcreteDownstream
open AspisV5ComponentCRelationTailCodec

/-! ## The runtime-shaped schedule model (not a Rust parser) -/

/-- A normalized mathematical record containing every public value needed by
the Component-C downstream map.

There is a **single** `alpha` vector, shared by the relation coefficient folds and
the FRI fold challenges; this is the load-bearing agreement between
`v5_real_host_proof.rs` `alphas` (used by `relation.fold`) and the FRI folds
`fold_candidate_codeword_round_for_domain_log`.  `ood0` is the round-0 circle-OOD
covector pair (`add_circle_tensor`, domain width `1024`); `ood1..ood3` are the
rounds `1..3` line-OOD covector pairs (`add_line_tensor`, widths `256, 64, 16`).
`later{1,2,3}Count` and `later{1,2,3}Fibre` have the shape of the per-layer
deduplicated runtime lists.  This structure deliberately does not assert that
they were produced by `derive_circle_line_query_indices_for_count`, are sorted
and distinct, or have count at most eighteen.  Those facts belong to the
remaining transcript/schedule correspondence; the algebra below is universal
for any supplied record. -/
structure DeployedRuntimeSchedule (F K : Type*)
    [Field F] [Field K] [Algebra F K] where
  /-- The four common relation/FRI fold challenges. -/
  alpha : Fin 4 → K
  /-- Round-0 circle-OOD covector pair (full `1024`-coefficient domain). -/
  ood0 : Fin 2 → Fin 1024 → K
  /-- Round-1 line-OOD covector pair (`256`-coefficient folded domain). -/
  ood1 : Fin 2 → Fin 256 → K
  /-- Round-2 line-OOD covector pair (`64`-coefficient folded domain). -/
  ood2 : Fin 2 → Fin 64 → K
  /-- Round-3 line-OOD covector pair (`16`-coefficient folded domain). -/
  ood3 : Fin 2 → Fin 16 → K
  /-- Round-0 post-OOD polynomial weight table (`WeightAccumulator`). -/
  poly0 : Fin 1024 → K
  poly1 : Fin 256 → K
  poly2 : Fin 64 → K
  poly3 : Fin 16 → K
  /-- Circle-to-line twiddle inverse tables for layer 0. -/
  circleInv2x : Fin layer1Symbols → F
  circleInv2y : Fin layer1Symbols → F
  /-- Line fold inverse tables for the later rounds. -/
  line1Inverse : Fin layer2Symbols → Fin 3 → F
  line2Inverse : Fin layer3Symbols → Fin 3 → F
  line3Inverse : Fin layer4Symbols → Fin 3 → F
  /-- Supplied later-fibre counts.  Runtime bounds are a separate predicate. -/
  later1Count : Nat
  later2Count : Nat
  later3Count : Nat
  /-- Supplied later-fibre order. -/
  later1Fibre : Fin later1Count → Fin layer2Symbols
  later2Fibre : Fin later2Count → Fin layer3Symbols
  later3Fibre : Fin later3Count → Fin layer4Symbols
  /-- Terminal circle points for the final tensor transition. -/
  finalX : Fin layer4Symbols → F

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- The FRI half of the supplied schedule model. -/
def decodeFriSchedule (rt : DeployedRuntimeSchedule F K) : FixedSchedule F K where
  alpha := rt.alpha
  circleInv2x := rt.circleInv2x
  circleInv2y := rt.circleInv2y
  line1Inverse := rt.line1Inverse
  line2Inverse := rt.line2Inverse
  line3Inverse := rt.line3Inverse
  later1Count := rt.later1Count
  later2Count := rt.later2Count
  later3Count := rt.later3Count
  later1Fibre := rt.later1Fibre
  later2Fibre := rt.later2Fibre
  later3Fibre := rt.later3Fibre
  finalX := rt.finalX

/-- The relation half of the supplied schedule model.  Its `alpha` is the *same* field. -/
def decodeRelationSchedule (rt : DeployedRuntimeSchedule F K) :
    FixedRelationSchedule K where
  alpha := rt.alpha
  ood0 := rt.ood0
  ood1 := rt.ood1
  ood2 := rt.ood2
  ood3 := rt.ood3
  poly0 := rt.poly0
  poly1 := rt.poly1
  poly2 := rt.poly2
  poly3 := rt.poly3

@[simp] theorem decodeFriSchedule_alpha (rt : DeployedRuntimeSchedule F K) :
    (decodeFriSchedule rt).alpha = rt.alpha := rfl
@[simp] theorem decodeRelationSchedule_alpha (rt : DeployedRuntimeSchedule F K) :
    (decodeRelationSchedule rt).alpha = rt.alpha := rfl
@[simp] theorem decodeFriSchedule_later1Count (rt : DeployedRuntimeSchedule F K) :
    (decodeFriSchedule rt).later1Count = rt.later1Count := rfl
@[simp] theorem decodeFriSchedule_later2Count (rt : DeployedRuntimeSchedule F K) :
    (decodeFriSchedule rt).later2Count = rt.later2Count := rfl
@[simp] theorem decodeFriSchedule_later3Count (rt : DeployedRuntimeSchedule F K) :
    (decodeFriSchedule rt).later3Count = rt.later3Count := rfl

/-- **The schedule packager.**  It constructs a complete mathematical schedule and
discharges relation/FRI alpha agreement by construction: both halves read the same
`rt.alpha`, so `alphas_agree` is definitional.  It does not parse or validate a
Rust transcript. -/
def decodeSchedule (rt : DeployedRuntimeSchedule F K) : CompleteFixedSchedule F K where
  fri := decodeFriSchedule rt
  relation := decodeRelationSchedule rt
  alphas_agree := rfl

@[simp] theorem decodeSchedule_fri (rt : DeployedRuntimeSchedule F K) :
    (decodeSchedule rt).fri = decodeFriSchedule rt := rfl
@[simp] theorem decodeSchedule_relation (rt : DeployedRuntimeSchedule F K) :
    (decodeSchedule rt).relation = decodeRelationSchedule rt := rfl

/-- The shared record field discharges the previously named alpha-agreement interface. -/
theorem decode_relationAndFriAlphasAgree (rt : DeployedRuntimeSchedule F K) :
    AspisV5ComponentCRelationRowLinearity.UnmetDeployment.RelationAndFriAlphasAgree
      (decodeRelationSchedule rt) (decodeFriSchedule rt) :=
  rfl

/-- The output dimension is genuinely runtime-sized: `40 + 4 (n1 + n2 + n3)`,
never a hard-coded constant. -/
theorem deployed_output_dimension (rt : DeployedRuntimeSchedule F K) :
    fRows (decodeFriSchedule rt) =
      40 + 4 * (rt.later1Count + rt.later2Count + rt.later3Count) := by
  rw [fRows_formula]
  simp only [decodeFriSchedule_later1Count, decodeFriSchedule_later2Count,
    decodeFriSchedule_later3Count]

/-! ## The canonical schedule-sized evaluator order

The offline fixed-matrix generator's `pack_f_view` uses this logical segment
order, but production Rust currently releases the corresponding relation fields,
later openings, and final coefficients in distinct protocol sections rather than
through one schedule-sized flat function.  `fTaggedIndexEquiv` is therefore the
canonical mathematical normalization of that view, not a claim that a runtime
serializer with this signature already exists.  The evaluator below dispatches
each flat row through `fTaggedIndexEquiv.symm`; equality to production behaviour
remains the explicit premise below. -/

/-- Value of one relation row, split into its OOD read (`roundOodRows`, a public
covector dot product) or its degree-six polynomial coefficient
(`roundPolynomialRows`, the `polynomial_for_extension` dual fold with the
`[w0,w3,w2,w1]/4` order). -/
def deployedRelationTaggedValue (rt : DeployedRuntimeSchedule F K) (c : CWord K) :
    RelationTaggedIndex → K :=
  fun tr =>
    match tr.2 with
    | .inl sample => roundOodRows (decodeRelationSchedule rt) tr.1 c sample
    | .inr degree => roundPolynomialRows (decodeRelationSchedule rt) tr.1 c degree

/-- Value of one canonical flat tag, in the six-segment model order:
36 relation rows (OOD then degree-six polynomial), the three schedule-sized later
blocks (arity-four codeword folds through `layer{1,2,3}Map`), then four final
coefficients (`finalCoefficientMap`, the `1024 -> 256 -> 64 -> 16 -> 4`
coefficient folds). -/
def deployedTaggedValue (rt : DeployedRuntimeSchedule F K)
    (enc : CWord K →ₗ[K] Layer0Word K) (c : CWord K) :
    FTaggedIndex (decodeFriSchedule rt) → K :=
  fun index =>
    match index with
    | .inl r => deployedRelationTaggedValue rt c (relationTaggedIndexEquiv.symm r)
    | .inr (.inl (.inl l)) => later1ReadMap (decodeFriSchedule rt) enc c l
    | .inr (.inl (.inr (.inl l))) => later2ReadMap (decodeFriSchedule rt) enc c l
    | .inr (.inl (.inr (.inr l))) => later3ReadMap (decodeFriSchedule rt) enc c l
    | .inr (.inr j) => finalCoefficientMap (decodeFriSchedule rt) c j

/-- **The canonical downstream evaluator.**  A flat mathematical vector computed
row-by-row from the supplied schedule record, including its arbitrary later
counts and order. -/
def deployedEvaluate (rt : DeployedRuntimeSchedule F K)
    (enc : CWord K →ₗ[K] Layer0Word K) (c : CWord K) :
    Fin (fRows (decodeFriSchedule rt)) → K :=
  fun row =>
    deployedTaggedValue rt enc c ((fTaggedIndexEquiv (decodeFriSchedule rt)).symm row)

/-! ## The universal commuting theorem -/

/-- The relation segment: a tagged relation index lands at `roundOodRows` /
`roundPolynomialRows`, forcing the non-definitional `relationRows_at_ood` /
`relationRows_at_polynomial` reindexing lemmas. -/
theorem concreteDownstream_relation_tagged (rt : DeployedRuntimeSchedule F K)
    (enc : CWord K →ₗ[K] Layer0Word K) (c : CWord K) (tr : RelationTaggedIndex) :
    concreteDownstream (decodeSchedule rt) enc c
        (fTaggedIndexEquiv (decodeFriSchedule rt) (.inl (relationTaggedIndexEquiv tr)))
      = deployedRelationTaggedValue rt c tr := by
  obtain ⟨round, w⟩ := tr
  rcases w with sample | degree
  · change concreteDownstream (decodeSchedule rt) enc c
          (fTaggedIndexEquiv (decodeFriSchedule rt)
            (.inl (round, finSumFinEquiv (m := 2) (n := 7) (.inl sample))))
        = roundOodRows (decodeRelationSchedule rt) round c sample
    exact concreteDownstream_relation_ood (decodeSchedule rt) enc c round sample
  · change concreteDownstream (decodeSchedule rt) enc c
          (fTaggedIndexEquiv (decodeFriSchedule rt)
            (.inl (round, finSumFinEquiv (m := 2) (n := 7) (.inr degree))))
        = roundPolynomialRows (decodeRelationSchedule rt) round c degree
    exact concreteDownstream_relation_polynomial (decodeSchedule rt) enc c round degree

/-- Every canonical flat tag agrees with `concreteDownstream` at its flat row.
The case split verifies the exact segment order and dedup routing; no branch is a
rename, because the relation branch travels through the reindexing lemmas above. -/
theorem concreteDownstream_at_tag_eq_deployed (rt : DeployedRuntimeSchedule F K)
    (enc : CWord K →ₗ[K] Layer0Word K) (c : CWord K)
    (tag : FTaggedIndex (decodeFriSchedule rt)) :
    concreteDownstream (decodeSchedule rt) enc c
        (fTaggedIndexEquiv (decodeFriSchedule rt) tag)
      = deployedTaggedValue rt enc c tag := by
  rcases tag with r | rest
  · have h := concreteDownstream_relation_tagged rt enc c
        (relationTaggedIndexEquiv.symm r)
    rw [Equiv.apply_symm_apply] at h
    exact h
  · rcases rest with later | final
    · rcases later with l1 | rest2
      · rw [concreteDownstream_def]
        exact concreteF_later1_coordinate (decodeFriSchedule rt) enc
          (relationRows (decodeRelationSchedule rt)) c l1
      · rcases rest2 with l2 | l3
        · rw [concreteDownstream_def]
          exact concreteF_later2_coordinate (decodeFriSchedule rt) enc
            (relationRows (decodeRelationSchedule rt)) c l2
        · rw [concreteDownstream_def]
          exact concreteF_later3_coordinate (decodeFriSchedule rt) enc
            (relationRows (decodeRelationSchedule rt)) c l3
    · rw [concreteDownstream_def]
      exact concreteF_final_coordinate (decodeFriSchedule rt) enc
        (relationRows (decodeRelationSchedule rt)) c final

/-- **Universal commuting theorem.**  For an arbitrary supplied schedule record, the
fully specified deployed evaluator equals the model map `concreteDownstream`
composed with the schedule decoder.  This is not a definitional rename: the
relation rows are routed through `relationRows_at_ood`/`_at_polynomial`, and the
flat/tag correspondence through `fTaggedIndexEquiv` coherence. -/
theorem deployedEvaluate_eq_concreteDownstream (rt : DeployedRuntimeSchedule F K)
    (enc : CWord K →ₗ[K] Layer0Word K) (c : CWord K) :
    deployedEvaluate rt enc c = concreteDownstream (decodeSchedule rt) enc c := by
  funext row
  have h := concreteDownstream_at_tag_eq_deployed rt enc c
      ((fTaggedIndexEquiv (decodeFriSchedule rt)).symm row)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-! ### Exact evaluator-order read-offs

These pin, as separate theorems, the six segments in deployed order: the two
round OOD reads, the seven degree-six relation polynomial rows (dual fold), the
three deduplicated later blocks (arity-four codeword folds), and the four final
coefficient values. -/

theorem deployed_row_relation_ood (rt : DeployedRuntimeSchedule F K)
    (enc : CWord K →ₗ[K] Layer0Word K) (c : CWord K) (round : Fin 4) (sample : Fin 2) :
    deployedEvaluate rt enc c
        (fTaggedIndexEquiv (decodeFriSchedule rt)
          (.inl (round, finSumFinEquiv (m := 2) (n := 7) (.inl sample))))
      = roundOodRows (decodeRelationSchedule rt) round c sample := by
  rw [deployedEvaluate_eq_concreteDownstream]
  exact concreteDownstream_relation_ood (decodeSchedule rt) enc c round sample

theorem deployed_row_relation_polynomial (rt : DeployedRuntimeSchedule F K)
    (enc : CWord K →ₗ[K] Layer0Word K) (c : CWord K) (round : Fin 4) (degree : Fin 7) :
    deployedEvaluate rt enc c
        (fTaggedIndexEquiv (decodeFriSchedule rt)
          (.inl (round, finSumFinEquiv (m := 2) (n := 7) (.inr degree))))
      = roundPolynomialRows (decodeRelationSchedule rt) round c degree := by
  rw [deployedEvaluate_eq_concreteDownstream]
  exact concreteDownstream_relation_polynomial (decodeSchedule rt) enc c round degree

theorem deployed_row_later1 (rt : DeployedRuntimeSchedule F K)
    (enc : CWord K →ₗ[K] Layer0Word K) (c : CWord K)
    (l : Fin (decodeFriSchedule rt).later1Count × Fin 4) :
    deployedEvaluate rt enc c
        (fTaggedIndexEquiv (decodeFriSchedule rt) (.inr (.inl (.inl l))))
      = later1ReadMap (decodeFriSchedule rt) enc c l := by
  rw [deployedEvaluate_eq_concreteDownstream, concreteDownstream_def]
  exact concreteF_later1_coordinate (decodeFriSchedule rt) enc
    (relationRows (decodeRelationSchedule rt)) c l

theorem deployed_row_later2 (rt : DeployedRuntimeSchedule F K)
    (enc : CWord K →ₗ[K] Layer0Word K) (c : CWord K)
    (l : Fin (decodeFriSchedule rt).later2Count × Fin 4) :
    deployedEvaluate rt enc c
        (fTaggedIndexEquiv (decodeFriSchedule rt) (.inr (.inl (.inr (.inl l)))))
      = later2ReadMap (decodeFriSchedule rt) enc c l := by
  rw [deployedEvaluate_eq_concreteDownstream, concreteDownstream_def]
  exact concreteF_later2_coordinate (decodeFriSchedule rt) enc
    (relationRows (decodeRelationSchedule rt)) c l

theorem deployed_row_later3 (rt : DeployedRuntimeSchedule F K)
    (enc : CWord K →ₗ[K] Layer0Word K) (c : CWord K)
    (l : Fin (decodeFriSchedule rt).later3Count × Fin 4) :
    deployedEvaluate rt enc c
        (fTaggedIndexEquiv (decodeFriSchedule rt) (.inr (.inl (.inr (.inr l)))))
      = later3ReadMap (decodeFriSchedule rt) enc c l := by
  rw [deployedEvaluate_eq_concreteDownstream, concreteDownstream_def]
  exact concreteF_later3_coordinate (decodeFriSchedule rt) enc
    (relationRows (decodeRelationSchedule rt)) c l

theorem deployed_row_final (rt : DeployedRuntimeSchedule F K)
    (enc : CWord K →ₗ[K] Layer0Word K) (c : CWord K) (j : Fin 4) :
    deployedEvaluate rt enc c
        (fTaggedIndexEquiv (decodeFriSchedule rt) (.inr (.inr j)))
      = finalCoefficientMap (decodeFriSchedule rt) c j := by
  rw [deployedEvaluate_eq_concreteDownstream, concreteDownstream_def]
  exact concreteF_final_coordinate (decodeFriSchedule rt) enc
    (relationRows (decodeRelationSchedule rt)) c j

/-! ## The single residual premise and the seam closure -/

/-- **The remaining evaluator code/model edge for a supplied schedule.**
Production Rust does not currently expose one flat function of this signature;
`rustEvaluate` denotes its normalized mathematical behaviour.  The exact function
equality is therefore a refinement obligation, not a theorem that such a Rust
helper already exists.  It binds evaluator branch/order/dedup behaviour for `rt`.
Showing that `rt` itself is the transcript-derived sorted/deduplicated schedule is
a separate code/model obligation. -/
def RustDownstreamEvaluatorEqualsDeployed (rt : DeployedRuntimeSchedule F K)
    (encodeFree : FreeCoordinateVector K →ₗ[K] CWord K)
    (enc : CWord K →ₗ[K] Layer0Word K)
    (rustEvaluate : FreeCoordinateVector K → Fin (fRows (decodeFriSchedule rt)) → K) :
    Prop :=
  rustEvaluate = fun free => deployedEvaluate rt enc (encodeFree free)

/-- **Seam closure.**  From the single premise above, the pre-existing seam
`RustConcreteDownstreamCorresponds` on the decoded schedule is fully discharged. -/
theorem rustConcreteDownstreamCorresponds_of_deployedMatch
    (rt : DeployedRuntimeSchedule F K)
    (encodeFree : FreeCoordinateVector K →ₗ[K] CWord K)
    (enc : CWord K →ₗ[K] Layer0Word K)
    (rustEvaluate : FreeCoordinateVector K → Fin (fRows (decodeFriSchedule rt)) → K)
    (h : RustDownstreamEvaluatorEqualsDeployed rt encodeFree enc rustEvaluate) :
    UnmetDeployment.RustConcreteDownstreamCorresponds (decodeSchedule rt)
      encodeFree enc rustEvaluate := by
  intro free
  rw [h]
  exact deployedEvaluate_eq_concreteDownstream rt enc (encodeFree free)

/-! ## Non-vacuity -/

/-- The residual premise is satisfiable: the deployed evaluator itself witnesses
it.  Hence the premise is not vacuously unsatisfiable. -/
theorem rustDownstreamEvaluatorEqualsDeployed_nonvacuous
    (rt : DeployedRuntimeSchedule F K)
    (encodeFree : FreeCoordinateVector K →ₗ[K] CWord K)
    (enc : CWord K →ₗ[K] Layer0Word K) :
    RustDownstreamEvaluatorEqualsDeployed rt encodeFree enc
      (fun free => deployedEvaluate rt enc (encodeFree free)) :=
  rfl

/-- A complete non-vacuous instance: the model evaluator discharges the decoded
schedule's `RustConcreteDownstreamCorresponds` seam. -/
theorem rustConcreteDownstreamCorresponds_nonvacuous
    (rt : DeployedRuntimeSchedule F K)
    (encodeFree : FreeCoordinateVector K →ₗ[K] CWord K)
    (enc : CWord K →ₗ[K] Layer0Word K) :
    UnmetDeployment.RustConcreteDownstreamCorresponds (decodeSchedule rt)
      encodeFree enc (fun free => deployedEvaluate rt enc (encodeFree free)) :=
  rustConcreteDownstreamCorresponds_of_deployedMatch rt encodeFree enc _ rfl

/-! ## Reuse of the 58-field/928-byte relation-tail codec

The relation segment is the witness-dependent part of the 58-field tail
(`encode_relation_tail`: OOD values at fields 10..17, sumcheck coefficients at
26..53).  Its byte codec is not re-proved: `V5ComponentCRelationTailCodec` is
reused verbatim. -/

/-- Reuse of `physicalRustRelationTailCorresponds_of_pinned_codec`: the pinned
928-byte encoder and the 58-to-36 extraction decode the runtime tail bytes to the
decoded schedule's relation rows. -/
theorem deployed_relation_tail_corresponds_of_pinned_codec
    (rt : DeployedRuntimeSchedule F K)
    (e : AspisV5ComponentCRejectionSampler.QM31Limbs ≃ K)
    (rustTailBytes : CWord K → RelationTailBytes)
    (modelTail : CWord K → Fin physicalRelationTailFieldCount → K)
    (hbytes : RustRelationTailEncoderMatchesPinnedCodec e rustTailBytes modelTail)
    (hmodel : ModelRelationTailMatchesSchedule (decodeSchedule rt) modelTail) :
    UnmetDeployment.PhysicalRustRelationTailCorresponds (decodeSchedule rt)
      rustTailBytes (decodeRelationTailValues e) :=
  physicalRustRelationTailCorresponds_of_pinned_codec (decodeSchedule rt) e
    rustTailBytes modelTail hbytes hmodel

/-- The reuse is load-bearing: the decoded tail bytes reproduce exactly the OOD
relation rows the deployed evaluator reads (round-0 circle / rounds 1..3 line). -/
theorem deployed_relation_ood_row_from_tail (rt : DeployedRuntimeSchedule F K)
    (e : AspisV5ComponentCRejectionSampler.QM31Limbs ≃ K)
    (rustTailBytes : CWord K → RelationTailBytes)
    (hcorr : UnmetDeployment.PhysicalRustRelationTailCorresponds (decodeSchedule rt)
      rustTailBytes (decodeRelationTailValues e))
    (c : CWord K) (round : Fin 4) (sample : Fin 2) :
    reorderPhysicalRelationTail (decodeRelationTailValues e (rustTailBytes c))
        (round, finSumFinEquiv (m := 2) (n := 7) (.inl sample))
      = roundOodRows (decodeRelationSchedule rt) round c sample := by
  rw [hcorr c]
  exact relationRows_at_ood (decodeSchedule rt).relation c round sample

/-! ## The old fixed-256 F-matrix shape is not reintroduced

`v5_component_c_fmat.rs` hard-asserts `V5_C_FMAT_ROWS == 256` with a fixed
`[[u32; 18]; 3]` later layout.  Here the output dimension is `40 + 4 (n1+n2+n3)`.
Without runtime bounds, `256` says only that the total is `54`; under the actual
per-layer bounds `n_i <= 18`, it forces all three counts to be eighteen. -/

/-- The exact unconditional arithmetic fact: 256 rows iff the three supplied
later counts sum to 54. -/
theorem deployed_frozen_256_iff_total_later_count_54
    (rt : DeployedRuntimeSchedule F K) :
    fRows (decodeFriSchedule rt) = maxFRowsCount ↔
      rt.later1Count + rt.later2Count + rt.later3Count = 54 := by
  rw [fRows_formula]
  simp only [decodeFriSchedule_later1Count, decodeFriSchedule_later2Count,
    decodeFriSchedule_later3Count, maxFRowsCount]
  omega

/-- The count-only part of runtime validity used by the no-dedup-loss reading.
Sortedness, distinctness, and derivation from base queries remain in the
transcript/schedule correspondence. -/
def RuntimeLaterCountBounds (rt : DeployedRuntimeSchedule F K) : Prop :=
  rt.later1Count ≤ 18 ∧ rt.later2Count ≤ 18 ∧ rt.later3Count ≤ 18

/-- Under the actual per-layer count bounds, the frozen 256-row shape is
equivalent to all three deduplicated lists retaining all eighteen entries. -/
theorem deployed_frozen_256_iff_no_dedup_loss
    (rt : DeployedRuntimeSchedule F K) (hbounds : RuntimeLaterCountBounds rt) :
    fRows (decodeFriSchedule rt) = maxFRowsCount ↔
      rt.later1Count = 18 ∧ rt.later2Count = 18 ∧ rt.later3Count = 18 := by
  rw [deployed_frozen_256_iff_total_later_count_54]
  rcases hbounds with ⟨h1, h2, h3⟩
  omega

/-- A concrete runtime schedule with the dedup counts of the
`derive_circle_line_query_indices_for_count` unit test (`4, 3, 2`) has `76` rows,
not `256`: the frozen matrix shape is genuinely absent. -/
theorem deployed_output_dimension_differs_from_frozen_256
    (rt : DeployedRuntimeSchedule F K)
    (h1 : rt.later1Count = 4) (h2 : rt.later2Count = 3) (h3 : rt.later3Count = 2) :
    fRows (decodeFriSchedule rt) = 76 ∧ fRows (decodeFriSchedule rt) ≠ maxFRowsCount := by
  have hrows : fRows (decodeFriSchedule rt) = 76 := by
    rw [fRows_formula]
    simp only [decodeFriSchedule_later1Count, decodeFriSchedule_later2Count,
      decodeFriSchedule_later3Count, h1, h2, h3]
  refine ⟨hrows, ?_⟩
  rw [hrows]
  decide

/-! ## Negative teeth

Three observability witnesses for the deployed evaluator's mutation classes:
wrong arity-four fold slot order, wrong twiddle/inverse, and wrong later-fibre
dedup count/order. -/

/-- **Wrong later-fibre dedup count is observable.**  The evaluator output
dimension is strictly determined by the deduplicated later counts, so any two
schedules whose total dedup count differs produce differently sized outputs — the
frozen `[[u32;18];3]` array cannot silently absorb the difference. -/
theorem deployed_distinct_dedup_counts_change_dimension
    (rt rt' : DeployedRuntimeSchedule F K)
    (h : rt.later1Count + rt.later2Count + rt.later3Count
        ≠ rt'.later1Count + rt'.later2Count + rt'.later3Count) :
    fRows (decodeFriSchedule rt) ≠ fRows (decodeFriSchedule rt') := by
  rw [fRows_formula, fRows_formula]
  simp only [decodeFriSchedule_later1Count, decodeFriSchedule_later2Count,
    decodeFriSchedule_later3Count]
  omega

/-- **Wrong later-fibre order is observable.**  The later reads are
`readFibres later_fibre ∘ layer_map`; permuting the deduplicated fibre order
changes which fibre is read at a given ordinal.  Here the ordinal-0 read differs
between fibre orders `[0,1]` and `[1,0]`. -/
theorem deployed_later_fibre_order_is_observable :
    (readFibres (K := ℚ)
        ![(⟨0, by norm_num [layer2Symbols]⟩ : Fin layer2Symbols),
          ⟨1, by norm_num [layer2Symbols]⟩]
        (fun i : Fin (4 * layer2Symbols) => (i.val : ℚ))) (0, 0)
      ≠ (readFibres (K := ℚ)
        ![(⟨1, by norm_num [layer2Symbols]⟩ : Fin layer2Symbols),
          ⟨0, by norm_num [layer2Symbols]⟩]
        (fun i : Fin (4 * layer2Symbols) => (i.val : ℚ))) (0, 0) := by
  simp only [readFibres_apply, Matrix.cons_val_zero, childIndex_val]
  norm_num

section MutationTeeth

local instance : Fact (Nat.Prime 31) := ⟨by norm_num⟩

def deployedFoldValues : Fin 4 → ZMod 31 := ![1, 4, 9, 16]
def deployedFoldSwapped : Fin 4 → ZMod 31 := ![1, 9, 4, 16]

/-- **Wrong arity-four fold slot order is observable.**  Swapping the two middle
codeword slots changes the deployed line/circle fold (`lineFoldValue`, the value
folded by `layer{1,2,3}Map`). -/
theorem deployed_fold_slot_order_is_load_bearing :
    lineFoldValue (2 : ZMod 31) 3 5 7 deployedFoldValues ≠
      lineFoldValue (2 : ZMod 31) 3 5 7 deployedFoldSwapped := by
  have hinv : (2 : ZMod 31)⁻¹ = 16 :=
    ZMod.inv_eq_of_mul_eq_one 31 2 16 (by decide)
  norm_num [lineFoldValue, pairFoldValue, deployedFoldValues, deployedFoldSwapped,
    Matrix.cons_val_two, Matrix.cons_val_three, div_eq_mul_inv, hinv]
  decide

/-- **Wrong twiddle/inverse is observable.**  Changing the layer-0 circle twiddle
`inv_2x` changes the deployed circle fold (`circleFoldValue`, the value folded by
`layer1Map`). -/
theorem deployed_circle_twiddle_is_load_bearing :
    circleFoldValue (2 : ZMod 31) 7 5 deployedFoldValues ≠
      circleFoldValue (2 : ZMod 31) 8 5 deployedFoldValues := by
  have hinv : (2 : ZMod 31)⁻¹ = 16 :=
    ZMod.inv_eq_of_mul_eq_one 31 2 16 (by decide)
  norm_num [circleFoldValue, lineFoldValue, pairFoldValue, deployedFoldValues,
    Matrix.cons_val_two, Matrix.cons_val_three, div_eq_mul_inv, hinv]
  decide

end MutationTeeth

/-! ## Axiom audit -/

#print axioms decode_relationAndFriAlphasAgree
#print axioms deployed_output_dimension
#print axioms concreteDownstream_relation_tagged
#print axioms concreteDownstream_at_tag_eq_deployed
#print axioms deployedEvaluate_eq_concreteDownstream
#print axioms deployed_row_relation_ood
#print axioms deployed_row_relation_polynomial
#print axioms deployed_row_later1
#print axioms deployed_row_later2
#print axioms deployed_row_later3
#print axioms deployed_row_final
#print axioms rustConcreteDownstreamCorresponds_of_deployedMatch
#print axioms rustDownstreamEvaluatorEqualsDeployed_nonvacuous
#print axioms rustConcreteDownstreamCorresponds_nonvacuous
#print axioms deployed_relation_tail_corresponds_of_pinned_codec
#print axioms deployed_relation_ood_row_from_tail
#print axioms deployed_frozen_256_iff_total_later_count_54
#print axioms deployed_frozen_256_iff_no_dedup_loss
#print axioms deployed_output_dimension_differs_from_frozen_256
#print axioms deployed_distinct_dedup_counts_change_dimension
#print axioms deployed_later_fibre_order_is_observable
#print axioms deployed_fold_slot_order_is_load_bearing
#print axioms deployed_circle_twiddle_is_load_bearing

end AspisV5ComponentCDownstreamDeployed

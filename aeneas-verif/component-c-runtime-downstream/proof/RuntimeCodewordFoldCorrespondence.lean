import RuntimeSquareInstantiation
import RuntimeCoefficientFoldCorrespondence

set_option autoImplicit false

open Aeneas Aeneas.Std Result ControlFlow

namespace aspis_prover.ComponentCRuntimeCodewordFoldCorrespondence

open aspis_prover
open ComponentCRuntimeFoldPrimitiveInstantiation
open ComponentCRuntimeSquareInstantiation

abbrev RawQM31 := aspis_core.field.QM31
abbrev RawM31 := aspis_core.field.M31

/-- Exact source-control-flow bridge for one circle fibre.  The hypotheses are
the concrete outputs of the extracted public coordinate generator and its two
`inverse_double` calls; all fold arithmetic below them is unconditional. -/
theorem generated_circle_fibre_fold_exact
    (v0 v1 v2 v3 alpha : RawQM31)
    (domainLog : Std.U32) (fibre : Std.Usize)
    (point : aspis_core.circle_fri.BaseCirclePoint)
    (inv2x inv2y : RawM31)
    (hv0 : runtimeCanonicalQM31 v0)
    (hv1 : runtimeCanonicalQM31 v1)
    (hv2 : runtimeCanonicalQM31 v2)
    (hv3 : runtimeCanonicalQM31 v3)
    (halpha : runtimeCanonicalQM31 alpha)
    (hinv2x : runtimeCanonicalM31 inv2x)
    (hinv2y : runtimeCanonicalM31 inv2y)
    (hpoint :
      aspis_core.circle_fri.circle_fiber_point_for_domain_log domainLog fibre =
        ok (core.result.Result.Ok point))
    (hinvY :
      aspis_core.circle_fri.inverse_double point.y
          aspis_core.circle_fri.FoldDenominator.CircleY =
        ok (core.result.Result.Ok inv2y))
    (hinvX :
      aspis_core.circle_fri.inverse_double point.x
          aspis_core.circle_fri.FoldDenominator.CircleX =
        ok (core.result.Result.Ok inv2x)) :
    ∃ out,
      aspis_core.circle_fri.normalized_circle_to_line_arity4_at_fiber_for_domain_log
          (Array.make 4#usize [v0, v1, v2, v3]) alpha domainLog fibre =
        ok (core.result.Result.Ok out) ∧
      runtimeCanonicalQM31 out ∧
      runtimeQM31View out =
        AspisV5ComponentCConcreteFoldLinearity.circleFoldValue
          (runtimeQM31View alpha) (runtimeM31View inv2x)
          (runtimeM31View inv2y)
          (ComponentCRuntimeFoldPrimitiveReduction.orderedFour
            (runtimeQM31View v0) (runtimeQM31View v1)
            (runtimeQM31View v2) (runtimeQM31View v3)) := by
  obtain ⟨alphaSquared, hsquare, hcanonicalSquared, hexactSquared⟩ :=
    runtime_qm31_square_corresponds alpha halpha
  obtain ⟨out, hfold, hcanonical, hexact⟩ :=
    extracted_prepared_circle_fold_exact v0 v1 v2 v3 alpha alphaSquared
      inv2x inv2y hv0 hv1 hv2 hv3 halpha hcanonicalSquared hinv2x hinv2y
      hexactSquared
  refine ⟨out, ?_, hcanonical, hexact⟩
  unfold
    aspis_core.circle_fri.normalized_circle_to_line_arity4_at_fiber_for_domain_log
    aspis_core.circle_fri.normalized_circle_to_line_arity4
    aspis_core.circle_fri.normalized_circle_to_line_arity4_prepared
  rw [hpoint]
  simp only [bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch]
  rw [hinvY]
  simp only [bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch]
  rw [hinvX]
  simp only [bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch]
  rw [hsquare]
  simp only [bind_tc_ok]
  rw [hfold]
  rfl

/-- Exact source-control-flow bridge for one later line fibre. -/
theorem generated_line_fibre_fold_exact
    (v0 v1 v2 v3 alpha : RawQM31)
    (domainLog : Std.U32) (layer : Std.U8) (fibre : Std.Usize)
    (coordinates : aspis_core.circle_fri.LineArity4Coordinates)
    (inv0 inv1 inv2 : RawM31)
    (hv0 : runtimeCanonicalQM31 v0)
    (hv1 : runtimeCanonicalQM31 v1)
    (hv2 : runtimeCanonicalQM31 v2)
    (hv3 : runtimeCanonicalQM31 v3)
    (halpha : runtimeCanonicalQM31 alpha)
    (hinv0 : runtimeCanonicalM31 inv0)
    (hinv1 : runtimeCanonicalM31 inv1)
    (hinv2 : runtimeCanonicalM31 inv2)
    (hcoordinates :
      aspis_core.circle_fri.line_fold_coordinates_for_circle
          domainLog layer fibre = ok (core.result.Result.Ok coordinates))
    (hinv0Call :
      aspis_core.circle_fri.inverse_double coordinates.first_pair_x
          aspis_core.circle_fri.FoldDenominator.LineFirstPairX =
        ok (core.result.Result.Ok inv0))
    (hinv1Call :
      aspis_core.circle_fri.inverse_double coordinates.second_pair_x
          aspis_core.circle_fri.FoldDenominator.LineSecondPairX =
        ok (core.result.Result.Ok inv1))
    (hinv2Call :
      aspis_core.circle_fri.inverse_double coordinates.second_fold_x
          aspis_core.circle_fri.FoldDenominator.LineSecondFoldX =
        ok (core.result.Result.Ok inv2)) :
    ∃ out,
      aspis_core.circle_fri.normalized_line_arity4_at_fiber_for_domain_log
          (Array.make 4#usize [v0, v1, v2, v3]) alpha domainLog layer fibre =
        ok (core.result.Result.Ok out) ∧
      runtimeCanonicalQM31 out ∧
      runtimeQM31View out =
        AspisV5ComponentCConcreteFoldLinearity.lineFoldValue
          (runtimeQM31View alpha) (runtimeM31View inv0)
          (runtimeM31View inv1) (runtimeM31View inv2)
          (ComponentCRuntimeFoldPrimitiveReduction.orderedFour
            (runtimeQM31View v0) (runtimeQM31View v1)
            (runtimeQM31View v2) (runtimeQM31View v3)) := by
  obtain ⟨alphaSquared, hsquare, hcanonicalSquared, hexactSquared⟩ :=
    runtime_qm31_square_corresponds alpha halpha
  obtain ⟨out, hfold, hcanonical, hexact⟩ :=
    extracted_prepared_line_fold_exact v0 v1 v2 v3 alpha alphaSquared
      inv0 inv1 inv2 hv0 hv1 hv2 hv3 halpha hcanonicalSquared
      hinv0 hinv1 hinv2 hexactSquared
  refine ⟨out, ?_, hcanonical, hexact⟩
  unfold
    aspis_core.circle_fri.normalized_line_arity4_at_fiber_for_domain_log
    aspis_core.circle_fri.normalized_line_arity4
    aspis_core.circle_fri.normalized_line_arity4_prepared
  rw [hcoordinates]
  simp only [bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch]
  rw [hinv0Call]
  simp only [bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch]
  rw [hinv1Call]
  simp only [bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch]
  rw [hinv2Call]
  simp only [bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch]
  rw [hsquare]
  simp only [bind_tc_ok]
  rw [hfold]
  rfl

local instance : Inhabited RawQM31 := ⟨aspis_core.field.QM31.ZERO⟩

def RuntimeCanonicalList (values : List RawQM31) : Prop :=
  ∀ value ∈ values, runtimeCanonicalQM31 value

def generatedFibreCall
    (v0 v1 v2 v3 alpha : RawQM31)
    (round : Std.Usize) (domainLog : Std.U32) (fibre : Std.Usize) :
    Result (core.result.Result RawQM31
      aspis_core.circle_fri.CircleFriError) :=
  if round = 0#usize then
    aspis_core.circle_fri.normalized_circle_to_line_arity4_at_fiber_for_domain_log
      (Array.make 4#usize [v0, v1, v2, v3]) alpha domainLog fibre
  else
    do
      let layer ← lift (UScalar.cast .U8 round)
      aspis_core.circle_fri.normalized_line_arity4_at_fiber_for_domain_log
        (Array.make 4#usize [v0, v1, v2, v3]) alpha domainLog layer fibre

def GeneratedFibreFoldContract
    (values : Slice RawQM31) (alpha : RawQM31)
    (round : Std.Usize) (domainLog : Std.U32) (n : Nat)
    (expected : Fin n → ExactQM31) : Prop :=
  ∀ (fibre : Fin n) (rawFibre : Std.Usize), rawFibre.val = fibre.val → ∃ out,
    generatedFibreCall
        values.val[4 * fibre.val]!
        values.val[4 * fibre.val + 1]!
        values.val[4 * fibre.val + 2]!
        values.val[4 * fibre.val + 3]!
        alpha round domainLog rawFibre = ok (core.result.Result.Ok out) ∧
    runtimeCanonicalQM31 out ∧
    runtimeQM31View out = expected fibre

private theorem slice_index_run
    (values : Slice RawQM31) (index : Std.Usize)
    (hindex : index.val < values.val.length) :
    Slice.index_usize values index = ok values.val[index.val] := by
  unfold Slice.index_usize
  rw [Slice.getElem?_Usize_eq]
  simp [hindex]

private theorem wrapping_add_exact
    (left right : Std.Usize)
    (hsum : left.val + right.val < UScalar.size .Usize) :
    (Std.Usize.wrapping_add left right).val = left.val + right.val := by
  rw [Std.Usize.wrapping_add_val_eq, Nat.mod_eq_of_lt hsum]

private theorem wrapping_mul_exact
    (left right : Std.Usize)
    (hproduct : left.val * right.val < UScalar.size .Usize) :
    (Std.Usize.wrapping_mul left right).val = left.val * right.val := by
  rw [Std.Usize.wrapping_mul_val_eq, Nat.mod_eq_of_lt hproduct]

private theorem getElem_bang_eq
    (values : List RawQM31) (index : Nat) (hindex : index < values.length) :
    values[index]! = values[index] := by
  apply List.getElem!_of_getElem?
  simp [hindex]

private theorem appended_prefix_get
    (xs : List RawQM31) (value : RawQM31) (index : Nat)
    (hindex : index < xs.length) :
    (xs ++ [value])[index]! = xs[index]! := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD]
  rw [List.getElem?_append_left hindex]

private theorem appended_last_get
    (xs : List RawQM31) (value : RawQM31) :
    (xs ++ [value])[xs.length]! = value := by
  rw [List.getElem!_eq_getElem?_getD]
  simp

/-- Exact whole-vector theorem for the generated codeword fold loop, parameterized
only by the already source-authentic per-fibre contract.  It proves the runtime
loop adds no permutation, omission, duplicated fibre, or error-state shortcut. -/
theorem extracted_codeword_fold_loop_exact
    (values : Slice RawQM31) (alpha : RawQM31)
    (round : Std.Usize) (domainLog : Std.U32)
    (n k : Nat)
    (hvaluesLength : values.val.length = 4 * n)
    (hn : n ≤ 131072)
    (hk : k ≤ n)
    (hvaluesCanonical : RuntimeCanonicalList values.val)
    (expected : Fin n → ExactQM31)
    (hcontract : GeneratedFibreFoldContract
      values alpha round domainLog n expected)
    (folded : alloc.vec.Vec RawQM31)
    (hfoldedLength : folded.val.length = k)
    (hfoldedCanonical : RuntimeCanonicalList folded.val)
    (hfoldedExact : ∀ j (hj : j < k),
      runtimeQM31View folded.val[j]! =
        expected ⟨j, Nat.lt_of_lt_of_le hj hk⟩)
    (fibre : Std.Usize) (hfibre : fibre.val = k) :
    ∃ out,
      circle_candidate.fold_candidate_codeword_round_for_domain_log_loop
          values alpha round domainLog folded fibre none = ok (out, none) ∧
      out.val.length = n ∧
      RuntimeCanonicalList out.val ∧
      ∀ j (hj : j < n),
        runtimeQM31View out.val[j]! = expected ⟨j, hj⟩ := by
  obtain ⟨parentCount, hdiv, hparentValue⟩ :=
    UScalar.div_spec values.len
      (y := circle_candidate.FIBER_SLOTS) (by
        simp [circle_candidate.FIBER_SLOTS])
  have hparent : parentCount.val = n := by
    have hp := hparentValue
    simp only [Slice.len_val] at hp
    unfold circle_candidate.FIBER_SLOTS at hp
    norm_num at hp
    rw [hvaluesLength] at hp
    omega
  by_cases hmore : k < n
  · have hfibreLt : fibre < parentCount := by
      rw [UScalar.lt_equiv, hfibre, hparent]
      exact hmore
    have herrorNone : core.option.Option.is_none
        (none : Option circle_candidate.CircleCandidateError) = true := rfl
    let start := Std.Usize.wrapping_mul circle_candidate.FIBER_SLOTS fibre
    have hsmall : 4 * fibre.val + 4 < UScalar.size .Usize := by
      have hsize : 524289 < UScalar.size .Usize := by
        have h := (524289#usize).hSize
        scalar_tac
      rw [hfibre]
      omega
    have hstart : start.val = 4 * k := by
      unfold start circle_candidate.FIBER_SLOTS
      rw [wrapping_mul_exact 4#usize fibre (show
        (4#usize : Std.Usize).val * fibre.val < UScalar.size .Usize by
          change 4 * fibre.val < UScalar.size .Usize
          omega), hfibre]
      norm_num
    let i1 := Std.Usize.wrapping_add start 1#usize
    let i2 := Std.Usize.wrapping_add start 2#usize
    let i3 := Std.Usize.wrapping_add start 3#usize
    have hi1 : i1.val = 4 * k + 1 := by
      unfold i1
      rw [wrapping_add_exact start 1#usize (show
        start.val + (1#usize : Std.Usize).val < UScalar.size .Usize by
          change start.val + 1 < UScalar.size .Usize
          omega), hstart]
      norm_num
    have hi2 : i2.val = 4 * k + 2 := by
      unfold i2
      rw [wrapping_add_exact start 2#usize (show
        start.val + (2#usize : Std.Usize).val < UScalar.size .Usize by
          change start.val + 2 < UScalar.size .Usize
          omega), hstart]
      norm_num
    have hi3 : i3.val = 4 * k + 3 := by
      unfold i3
      rw [wrapping_add_exact start 3#usize (show
        start.val + (3#usize : Std.Usize).val < UScalar.size .Usize by
          change start.val + 3 < UScalar.size .Usize
          omega), hstart]
      norm_num
    have h0 : start.val < values.val.length := by omega
    have h1 : i1.val < values.val.length := by omega
    have h2 : i2.val < values.val.length := by omega
    have h3 : i3.val < values.val.length := by omega
    have read0 := slice_index_run values start h0
    have read1 := slice_index_run values i1 h1
    have read2 := slice_index_run values i2 h2
    have read3 := slice_index_run values i3 h3
    have hkFin : k < n := hmore
    obtain ⟨value, hvalueCall, cvalue, evalue⟩ :=
      hcontract ⟨k, hkFin⟩ fibre (by simpa [hfibre])
    have hb0 := getElem_bang_eq values.val (4 * k) (by omega)
    have hb1 := getElem_bang_eq values.val (4 * k + 1) (by omega)
    have hb2 := getElem_bang_eq values.val (4 * k + 2) (by omega)
    have hb3 := getElem_bang_eq values.val (4 * k + 3) (by omega)
    have hvalueCall' :
        generatedFibreCall values.val[start.val] values.val[i1.val]
          values.val[i2.val] values.val[i3.val] alpha round domainLog fibre =
            ok (core.result.Result.Ok value) := by
      simpa only [hstart, hi1, hi2, hi3, hb0, hb1, hb2, hb3]
        using hvalueCall
    have hcapacity : folded.val.length < Std.Usize.max := by
      rw [hfoldedLength]
      have hmax : 131073 < Std.Usize.max := by
        have h := (131074#usize).hSize
        scalar_tac
      omega
    obtain ⟨foldedNext, hpush, hfoldedNext⟩ := Aeneas.Std.WP.spec_imp_exists
      (alloc.vec.Vec.push_spec folded value hcapacity)
    let fibreNext := Std.Usize.wrapping_add fibre 1#usize
    have hfibreNext : fibreNext.val = k + 1 := by
      unfold fibreNext
      rw [wrapping_add_exact fibre 1#usize (show
        fibre.val + (1#usize : Std.Usize).val < UScalar.size .Usize by
          change fibre.val + 1 < UScalar.size .Usize
          have hsize : 131074 < UScalar.size .Usize := by
            have h := (131074#usize).hSize
            scalar_tac
          rw [hfibre]
          omega), hfibre]
      norm_num
    have hbody :
        circle_candidate.fold_candidate_codeword_round_for_domain_log_loop.body
            values alpha round domainLog folded fibre none =
          ok (cont (foldedNext, fibreNext, none)) := by
      unfold circle_candidate.fold_candidate_codeword_round_for_domain_log_loop.body
      dsimp only
      rw [hdiv]
      simp only [bind_tc_ok]
      rw [if_pos hfibreLt, herrorNone]
      simp only [bind_tc_ok]
      rw [if_pos True.intro]
      simp only [Std.lift, bind_tc_ok]
      rw [read0]
      simp only [bind_tc_ok]
      rw [read1]
      simp only [bind_tc_ok]
      rw [read2]
      simp only [bind_tc_ok]
      rw [read3]
      simp only [bind_tc_ok]
      by_cases hround : round = 0#usize
      · rw [if_pos hround]
        unfold generatedFibreCall at hvalueCall'
        rw [if_pos hround] at hvalueCall'
        rw [hvalueCall']
        simp only [bind_tc_ok]
        rw [hpush]
        rfl
      · rw [if_neg hround]
        unfold generatedFibreCall at hvalueCall'
        rw [if_neg hround] at hvalueCall'
        simp only [Std.lift, bind_tc_ok] at hvalueCall'
        rw [hvalueCall']
        simp only [bind_tc_ok]
        rw [hpush]
        rfl
    have hnextLength : foldedNext.val.length = k + 1 := by
      rw [hfoldedNext, List.length_append]
      simp [hfoldedLength]
    have hnextCanonical : RuntimeCanonicalList foldedNext.val := by
      intro x hx
      rw [hfoldedNext] at hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hfoldedCanonical x hx
      · have hxEq : x = value := List.mem_singleton.mp hx
        subst x
        exact cvalue
    have hnextExact : ∀ j (hj : j < k + 1),
        runtimeQM31View foldedNext.val[j]! =
          expected ⟨j, Nat.lt_of_lt_of_le hj (by omega)⟩ := by
      intro j hj
      rw [hfoldedNext]
      by_cases hjk : j < k
      · rw [appended_prefix_get folded.val value j (by omega)]
        exact hfoldedExact j hjk
      · have hjEq : j = k := by omega
        subst j
        have hlast := appended_last_get folded.val value
        rw [hfoldedLength] at hlast
        rw [hlast, evalue]
    rw [circle_candidate.fold_candidate_codeword_round_for_domain_log_loop,
      loop.eq_1]
    simp only [Prod.fst, Prod.snd]
    rw [hbody]
    simp only [bind_tc_ok]
    obtain ⟨out, hout, houtLength, houtCanonical, houtExact⟩ :=
      extracted_codeword_fold_loop_exact values alpha round domainLog
        n (k + 1) hvaluesLength hn (by omega) hvaluesCanonical expected
        hcontract foldedNext hnextLength hnextCanonical hnextExact fibreNext
        hfibreNext
    have hout' :
        loop
          (fun state =>
            circle_candidate.fold_candidate_codeword_round_for_domain_log_loop.body
              values alpha round domainLog state.1 state.2.1 state.2.2)
          (foldedNext, fibreNext, none) = ok (out, none) := by
      simpa only [circle_candidate.fold_candidate_codeword_round_for_domain_log_loop]
        using hout
    rw [hout']
    exact ⟨out, rfl, houtLength, houtCanonical, houtExact⟩
  · have hkEq : k = n := by omega
    have hfibreDone : ¬ fibre < parentCount := by
      rw [UScalar.lt_equiv, hfibre, hparent]
      omega
    have hbody :
        circle_candidate.fold_candidate_codeword_round_for_domain_log_loop.body
            values alpha round domainLog folded fibre none =
          ok (done (folded, none)) := by
      unfold circle_candidate.fold_candidate_codeword_round_for_domain_log_loop.body
      dsimp only
      rw [hdiv]
      simp only [bind_tc_ok]
      rw [if_neg hfibreDone]
    rw [circle_candidate.fold_candidate_codeword_round_for_domain_log_loop,
      loop.eq_1]
    simp only [Prod.fst, Prod.snd]
    rw [hbody]
    refine ⟨folded, rfl, ?_, hfoldedCanonical, ?_⟩
    · omega
    · intro j hj
      exact hfoldedExact j (by omega)
termination_by n - k
decreasing_by omega

/-- The public generated round wrapper contributes no extra arithmetic or
indexing freedom: once its source-authentic layer-length computation accepts,
the wrapper returns exactly the vector characterized by the per-fibre
contract.  This includes the generated round bound, exact input-length check,
capacity construction, quotient by four, loop initialization, and final error
dispatch. -/
theorem extracted_codeword_fold_public_exact
    (values : Slice RawQM31) (alpha : RawQM31)
    (round : Std.Usize) (domainLog : Std.U32)
    (n : Nat) (layerLen : Std.Usize)
    (hround : round.val < 4)
    (hlayerCall :
      circle_candidate.candidate_layer_len_for_domain_log domainLog round =
        ok (core.result.Result.Ok layerLen))
    (hlayerLen : layerLen.val = 4 * n)
    (hvaluesLength : values.val.length = 4 * n)
    (hn : n ≤ 131072)
    (hvaluesCanonical : RuntimeCanonicalList values.val)
    (expected : Fin n → ExactQM31)
    (hcontract : GeneratedFibreFoldContract
      values alpha round domainLog n expected) :
    ∃ out,
      circle_candidate.fold_candidate_codeword_round_for_domain_log
          values alpha round domainLog = ok (core.result.Result.Ok out) ∧
      out.val.length = n ∧
      RuntimeCanonicalList out.val ∧
      ∀ j (hj : j < n),
        runtimeQM31View out.val[j]! = expected ⟨j, hj⟩ := by
  have hfixed :
      UScalar.cast .Usize aspis_core.circle_fri.FIXED_ARITY4_ROUNDS =
        4#usize := by
    unfold aspis_core.circle_fri.FIXED_ARITY4_ROUNDS
    apply UScalar.eq_of_val_eq
    rw [UScalar.cast_val_eq]
    rcases System.Platform.numBits_eq with h | h <;> norm_num [h]
  have hroundNotGe : ¬ round ≥ (4#usize : Std.Usize) := by
    scalar_tac
  have hsliceLen : Slice.len values = layerLen := by
    apply UScalar.eq_of_val_eq
    change values.val.length = layerLen.val
    omega
  obtain ⟨parentCount, hdiv, _hparentValue⟩ :=
    UScalar.div_spec (Slice.len values)
      (y := circle_candidate.FIBER_SLOTS) (by
        simp [circle_candidate.FIBER_SLOTS])
  let initial := alloc.vec.Vec.with_capacity RawQM31 parentCount
  have hinitialLength : initial.val.length = 0 := by
    rfl
  have hinitialCanonical : RuntimeCanonicalList initial.val := by
    intro value hmem
    simpa [initial, alloc.vec.Vec.with_capacity] using hmem
  have hinitialExact : ∀ j (hj : j < 0),
      runtimeQM31View initial.val[j]! =
        expected ⟨j, Nat.lt_of_lt_of_le hj (Nat.zero_le n)⟩ := by
    omega
  obtain ⟨out, hloop, houtLength, houtCanonical, houtExact⟩ :=
    extracted_codeword_fold_loop_exact values alpha round domainLog n 0
      hvaluesLength hn (Nat.zero_le n) hvaluesCanonical expected hcontract
      initial hinitialLength hinitialCanonical hinitialExact 0#usize rfl
  refine ⟨out, ?_, houtLength, houtCanonical, houtExact⟩
  unfold circle_candidate.fold_candidate_codeword_round_for_domain_log
  rw [hfixed]
  simp only [Std.lift, bind_tc_ok]
  rw [if_neg hroundNotGe, hlayerCall]
  simp only [bind_tc_ok,
    core.result.Result.Insts.CoreOpsTry.branch]
  have hnotLengthNe : ¬ (Slice.len values != layerLen) = true := by
    simp [hsliceLen]
  rw [if_neg hnotLengthNe]
  rw [hdiv]
  simp only [bind_tc_ok]
  change (do
      let pair ←
        circle_candidate.fold_candidate_codeword_round_for_domain_log_loop
          values alpha round domainLog initial 0#usize none
      match pair.2 with
      | none => ok (core.result.Result.Ok pair.1)
      | some error => ok (core.result.Result.Err error)) =
    ok (core.result.Result.Ok out)
  rw [hloop]
  rfl

#print axioms generated_circle_fibre_fold_exact
#print axioms generated_line_fibre_fold_exact
#print axioms extracted_codeword_fold_loop_exact
#print axioms extracted_codeword_fold_public_exact

end aspis_prover.ComponentCRuntimeCodewordFoldCorrespondence

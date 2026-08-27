import V7K13FoldResidual.Funs

/-!
# Literal source trace for the sixteen Tag-73 one-fold answers

This proof consumes successful execution of the Charon/Aeneas translation of
`fold_v6_onefold_queries`.  It exposes the preparatory alpha arithmetic and
every one of the sixteen ordered circle-fold results returned in the array.
No pointwise comparison with `final256` is stated here: production performs
only the later rho-batched check.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

open Aeneas Aeneas.Std Result ControlFlow Error
open V7K13FoldResidualGenerated

namespace AspisV7K13FoldedValuesTrace

abbrev RawQM31 := field.QM31
abbrev Coordinates := v6_onefold.V6OneFoldCoordinates
abbrev Prepared := field.PreparedQm31Multiplier

/-- One literal generated callback-body call, before `array::from_fn` packages
the sixteen results. -/
def sourceFoldAt
    (combined : Array (Array RawQM31 4#usize) 16#usize)
    (alphaPowers : Array Prepared 3#usize)
    (coordinates : Coordinates) (ordinal : Std.Usize) : Result RawQM31 := do
  let fibre ← Array.index_usize combined ordinal
  let inv2x ← Array.index_usize coordinates.inv_2x ordinal
  let inv2y ← Array.index_usize coordinates.inv_2y ordinal
  circle_fri.normalized_circle_to_line_arity4_prepared_polynomial_refs
    fibre alphaPowers inv2x inv2y

theorem generated_callback_is_sourceFoldAt
    (combined : Array (Array RawQM31 4#usize) 16#usize)
    (alphaPowers : Array Prepared 3#usize)
    (coordinates : Coordinates) (ordinal : Std.Usize) :
    v6_onefold.fold_v6_onefold_queries.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut
        (combined, alphaPowers, coordinates) ordinal =
      (do
        let value ← sourceFoldAt combined alphaPowers coordinates ordinal
        ok (value, (combined, alphaPowers, coordinates))) := by
  simp [sourceFoldAt,
    v6_onefold.fold_v6_onefold_queries.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31.call_mut]

/-- Exact same-run data returned by the translated production fold.  The
sixteen scalar fields avoid hiding order behind a choice function or an
opaque array predicate. -/
structure AcceptedFoldedValuesTrace
    (combined : Array (Array RawQM31 4#usize) 16#usize)
    (coordinates : Coordinates) (alpha : RawQM31)
    (output : Array RawQM31 16#usize) : Type where
  alphaSquared : RawQM31
  preparedAlpha : Prepared
  preparedAlphaSquared : Prepared
  alphaCubed : RawQM31
  preparedAlphaCubed : Prepared
  alphaSquaredSuccess : field.QM31.square alpha = ok alphaSquared
  preparedAlphaSuccess :
    field.PreparedQm31Multiplier.new alpha = ok preparedAlpha
  preparedAlphaSquaredSuccess :
    field.PreparedQm31Multiplier.new alphaSquared = ok preparedAlphaSquared
  alphaCubedSuccess : field.QM31.mul alphaSquared alpha = ok alphaCubed
  preparedAlphaCubedSuccess :
    field.PreparedQm31Multiplier.new alphaCubed = ok preparedAlphaCubed
  value0 : RawQM31
  value1 : RawQM31
  value2 : RawQM31
  value3 : RawQM31
  value4 : RawQM31
  value5 : RawQM31
  value6 : RawQM31
  value7 : RawQM31
  value8 : RawQM31
  value9 : RawQM31
  value10 : RawQM31
  value11 : RawQM31
  value12 : RawQM31
  value13 : RawQM31
  value14 : RawQM31
  value15 : RawQM31
  value0Success : sourceFoldAt combined
    (Array.make 3#usize [preparedAlpha, preparedAlphaSquared,
      preparedAlphaCubed]) coordinates 0#usize = ok value0
  value1Success : sourceFoldAt combined
    (Array.make 3#usize [preparedAlpha, preparedAlphaSquared,
      preparedAlphaCubed]) coordinates 1#usize = ok value1
  value2Success : sourceFoldAt combined
    (Array.make 3#usize [preparedAlpha, preparedAlphaSquared,
      preparedAlphaCubed]) coordinates 2#usize = ok value2
  value3Success : sourceFoldAt combined
    (Array.make 3#usize [preparedAlpha, preparedAlphaSquared,
      preparedAlphaCubed]) coordinates 3#usize = ok value3
  value4Success : sourceFoldAt combined
    (Array.make 3#usize [preparedAlpha, preparedAlphaSquared,
      preparedAlphaCubed]) coordinates 4#usize = ok value4
  value5Success : sourceFoldAt combined
    (Array.make 3#usize [preparedAlpha, preparedAlphaSquared,
      preparedAlphaCubed]) coordinates 5#usize = ok value5
  value6Success : sourceFoldAt combined
    (Array.make 3#usize [preparedAlpha, preparedAlphaSquared,
      preparedAlphaCubed]) coordinates 6#usize = ok value6
  value7Success : sourceFoldAt combined
    (Array.make 3#usize [preparedAlpha, preparedAlphaSquared,
      preparedAlphaCubed]) coordinates 7#usize = ok value7
  value8Success : sourceFoldAt combined
    (Array.make 3#usize [preparedAlpha, preparedAlphaSquared,
      preparedAlphaCubed]) coordinates 8#usize = ok value8
  value9Success : sourceFoldAt combined
    (Array.make 3#usize [preparedAlpha, preparedAlphaSquared,
      preparedAlphaCubed]) coordinates 9#usize = ok value9
  value10Success : sourceFoldAt combined
    (Array.make 3#usize [preparedAlpha, preparedAlphaSquared,
      preparedAlphaCubed]) coordinates 10#usize = ok value10
  value11Success : sourceFoldAt combined
    (Array.make 3#usize [preparedAlpha, preparedAlphaSquared,
      preparedAlphaCubed]) coordinates 11#usize = ok value11
  value12Success : sourceFoldAt combined
    (Array.make 3#usize [preparedAlpha, preparedAlphaSquared,
      preparedAlphaCubed]) coordinates 12#usize = ok value12
  value13Success : sourceFoldAt combined
    (Array.make 3#usize [preparedAlpha, preparedAlphaSquared,
      preparedAlphaCubed]) coordinates 13#usize = ok value13
  value14Success : sourceFoldAt combined
    (Array.make 3#usize [preparedAlpha, preparedAlphaSquared,
      preparedAlphaCubed]) coordinates 14#usize = ok value14
  value15Success : sourceFoldAt combined
    (Array.make 3#usize [preparedAlpha, preparedAlphaSquared,
      preparedAlphaCubed]) coordinates 15#usize = ok value15
  outputExact : output = Array.make 16#usize
    [value0, value1, value2, value3, value4, value5, value6, value7,
     value8, value9, value10, value11, value12, value13, value14, value15]

/-! The decomposition theorem is below the generated definitions rather than
inside a source interface: every witness is forced by the one successful
translated call. -/

theorem accepted_fold_exposes_exact_sixteen_values
    (combined : Array (Array RawQM31 4#usize) 16#usize)
    (coordinates : Coordinates) (alpha : RawQM31)
    (output : Array RawQM31 16#usize)
    (success : v6_onefold.fold_v6_onefold_queries combined coordinates alpha =
      ok output) :
    Nonempty (AcceptedFoldedValuesTrace combined coordinates alpha output) := by
  unfold v6_onefold.fold_v6_onefold_queries at success
  cases hsquare : field.QM31.square alpha <;> simp [hsquare] at success
  rename_i alphaSquared
  cases hprepareAlpha : field.PreparedQm31Multiplier.new alpha <;>
    simp [hprepareAlpha] at success
  rename_i preparedAlpha
  cases hprepareSquared :
      field.PreparedQm31Multiplier.new alphaSquared <;>
    simp [hprepareSquared] at success
  rename_i preparedAlphaSquared
  cases hcubed : field.QM31.mul alphaSquared alpha <;>
    simp [hcubed] at success
  rename_i alphaCubed
  cases hprepareCubed : field.PreparedQm31Multiplier.new alphaCubed <;>
    simp [hprepareCubed] at success
  rename_i preparedAlphaCubed
  let powers : Array Prepared 3#usize :=
    Array.make 3#usize [preparedAlpha, preparedAlphaSquared,
      preparedAlphaCubed]
  have hfromFn :
      core.array.from_fn 16#usize
          v6_onefold.fold_v6_onefold_queries.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
          (combined, powers, coordinates) = ok output := by
    simpa [powers] using success
  unfold core.array.from_fn at hfromFn
  simp only [dif_pos rfl] at hfromFn
  rw [generated_callback_is_sourceFoldAt] at hfromFn
  cases h0 : sourceFoldAt combined powers coordinates 0#usize <;>
    simp [h0] at hfromFn
  rename_i value0
  rw [generated_callback_is_sourceFoldAt] at hfromFn
  cases h1 : sourceFoldAt combined powers coordinates 1#usize <;>
    simp [h1] at hfromFn
  rename_i value1
  rw [generated_callback_is_sourceFoldAt] at hfromFn
  cases h2 : sourceFoldAt combined powers coordinates 2#usize <;>
    simp [h2] at hfromFn
  rename_i value2
  rw [generated_callback_is_sourceFoldAt] at hfromFn
  cases h3 : sourceFoldAt combined powers coordinates 3#usize <;>
    simp [h3] at hfromFn
  rename_i value3
  rw [generated_callback_is_sourceFoldAt] at hfromFn
  cases h4 : sourceFoldAt combined powers coordinates 4#usize <;>
    simp [h4] at hfromFn
  rename_i value4
  rw [generated_callback_is_sourceFoldAt] at hfromFn
  cases h5 : sourceFoldAt combined powers coordinates 5#usize <;>
    simp [h5] at hfromFn
  rename_i value5
  rw [generated_callback_is_sourceFoldAt] at hfromFn
  cases h6 : sourceFoldAt combined powers coordinates 6#usize <;>
    simp [h6] at hfromFn
  rename_i value6
  rw [generated_callback_is_sourceFoldAt] at hfromFn
  cases h7 : sourceFoldAt combined powers coordinates 7#usize <;>
    simp [h7] at hfromFn
  rename_i value7
  rw [generated_callback_is_sourceFoldAt] at hfromFn
  cases h8 : sourceFoldAt combined powers coordinates 8#usize <;>
    simp [h8] at hfromFn
  rename_i value8
  rw [generated_callback_is_sourceFoldAt] at hfromFn
  cases h9 : sourceFoldAt combined powers coordinates 9#usize <;>
    simp [h9] at hfromFn
  rename_i value9
  rw [generated_callback_is_sourceFoldAt] at hfromFn
  cases h10 : sourceFoldAt combined powers coordinates 10#usize <;>
    simp [h10] at hfromFn
  rename_i value10
  rw [generated_callback_is_sourceFoldAt] at hfromFn
  cases h11 : sourceFoldAt combined powers coordinates 11#usize <;>
    simp [h11] at hfromFn
  rename_i value11
  rw [generated_callback_is_sourceFoldAt] at hfromFn
  cases h12 : sourceFoldAt combined powers coordinates 12#usize <;>
    simp [h12] at hfromFn
  rename_i value12
  rw [generated_callback_is_sourceFoldAt] at hfromFn
  cases h13 : sourceFoldAt combined powers coordinates 13#usize <;>
    simp [h13] at hfromFn
  rename_i value13
  rw [generated_callback_is_sourceFoldAt] at hfromFn
  cases h14 : sourceFoldAt combined powers coordinates 14#usize <;>
    simp [h14] at hfromFn
  rename_i value14
  rw [generated_callback_is_sourceFoldAt] at hfromFn
  cases h15 : sourceFoldAt combined powers coordinates 15#usize <;>
    simp [h15] at hfromFn
  rename_i value15
  have outputExact : output = Array.make 16#usize
      [value0, value1, value2, value3, value4, value5, value6, value7,
       value8, value9, value10, value11, value12, value13, value14, value15] := by
    simpa using hfromFn.symm
  refine ⟨{
    alphaSquared := alphaSquared
    preparedAlpha := preparedAlpha
    preparedAlphaSquared := preparedAlphaSquared
    alphaCubed := alphaCubed
    preparedAlphaCubed := preparedAlphaCubed
    alphaSquaredSuccess := hsquare
    preparedAlphaSuccess := hprepareAlpha
    preparedAlphaSquaredSuccess := hprepareSquared
    alphaCubedSuccess := hcubed
    preparedAlphaCubedSuccess := hprepareCubed
    value0 := value0
    value1 := value1
    value2 := value2
    value3 := value3
    value4 := value4
    value5 := value5
    value6 := value6
    value7 := value7
    value8 := value8
    value9 := value9
    value10 := value10
    value11 := value11
    value12 := value12
    value13 := value13
    value14 := value14
    value15 := value15
    value0Success := by simpa [powers] using h0
    value1Success := by simpa [powers] using h1
    value2Success := by simpa [powers] using h2
    value3Success := by simpa [powers] using h3
    value4Success := by simpa [powers] using h4
    value5Success := by simpa [powers] using h5
    value6Success := by simpa [powers] using h6
    value7Success := by simpa [powers] using h7
    value8Success := by simpa [powers] using h8
    value9Success := by simpa [powers] using h9
    value10Success := by simpa [powers] using h10
    value11Success := by simpa [powers] using h11
    value12Success := by simpa [powers] using h12
    value13Success := by simpa [powers] using h13
    value14Success := by simpa [powers] using h14
    value15Success := by simpa [powers] using h15
    outputExact := outputExact }⟩

#print axioms generated_callback_is_sourceFoldAt
#print axioms accepted_fold_exposes_exact_sixteen_values

end AspisV7K13FoldedValuesTrace

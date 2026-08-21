import CheckV5FriQueries.Funs

open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxRecDepth 3000

namespace AspisV5FriConsumerExactProof

open V5FriConsumerExact

private theorem slice_index_run
    {T : Type} [Inhabited T]
    (values : Slice T) (index : Std.Usize)
    (hindex : index.val < values.val.length) :
    Slice.index_usize values index = .ok values.val[index.val]! := by
  unfold Slice.index_usize
  rw [Slice.getElem?_Usize_eq]
  simp [hindex]

private theorem wrapping_succ_exact
    {T : Type} (values : Slice T) (index : Std.Usize)
    (hindex : index.val < values.val.length) :
    (Std.Usize.wrapping_add index 1#usize).val = index.val + 1 := by
  rw [Std.Usize.wrapping_add_val_eq]
  apply Nat.mod_eq_of_lt
  have hlength := Slice.length_ineq values
  change index.val + 1 < UScalar.size .Usize
  rw [UScalar.size_UScalarTyUsize]
  have hsize := Usize.size_scalarTac_eq
  omega

private theorem core_slice_get_run
    {T : Type} [Inhabited T]
    (values : Slice T) (index : Std.Usize)
    (hindex : index.val < values.val.length) :
    core.slice.Slice.get
        (core.slice.index.SliceIndexUsizeSlice T) values index =
      .ok (some values.val[index.val]!) := by
  unfold core.slice.Slice.get core.slice.index.SliceIndexUsizeSlice
    core.slice.index.Usize.get
  change ok values.val[index.val]? = ok (some values.val[index.val]!)
  simp [hindex]

/-- Exact `enumerate()` step for the immutable slice iterator used by all
four production FRI loops.  The enumerated ordinal and the slice position
advance together; neither is supplied by a model-side trace. -/
private theorem enumerate_slice_next_run
    {T : Type} [Inhabited T]
    (values : Slice T) (position : Std.Usize)
    (hposition : position.val < values.val.length) :
    ∃ nextCount : Std.Usize,
      nextCount.val = position.val + 1 ∧
      core.iter.adapters.enumerate.IteratorEnumerate.next
          (core.iter.traits.iterator.IteratorSliceIter T)
          { iter := { slice := values, i := position.val }, count := position } =
        .ok (some (position, values[position.val]),
          { iter := { slice := values, i := position.val + 1 },
            count := nextCount }) := by
  have hactive : position.val < values.len.val := by simpa using hposition
  have hinner :
      (core.iter.traits.iterator.IteratorSliceIter T).next
          ({ slice := values, i := position.val } : core.slice.iter.Iter T) =
        .ok (some values[position.val],
          ({ slice := values, i := position.val + 1 } :
            core.slice.iter.Iter T)) := by
    change core.slice.iter.IteratorSliceIter.next
        ({ slice := values, i := position.val } : core.slice.iter.Iter T) = _
    unfold core.slice.iter.IteratorSliceIter.next
    rw [dif_pos hactive]
  unfold core.iter.adapters.enumerate.IteratorEnumerate.next
  rw [hinner]
  simp only [bind_tc_ok]
  have hadd := @UScalar.add_equiv .Usize position 1#usize
  split at hadd
  · rename_i nextCount hcount
    refine ⟨nextCount, ?_, ?_⟩
    · exact hadd.2.1
    · simp only [hcount, bind_tc_ok]
      rfl
  · simp [UScalar.inBounds] at hadd
    have hlength := Slice.length_ineq values
    exfalso
    scalar_tac
  · contradiction

def enumerateSliceAt {T : Type} (values : Slice T)
    (position : Std.Usize) :
    core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter T) :=
  { iter := { slice := values, i := position.val }, count := position }

private theorem enumerate_slice_at_next_run
    {T : Type} [Inhabited T]
    (values : Slice T) (position : Std.Usize)
    (hposition : position.val < values.val.length) :
    ∃ nextPosition : Std.Usize,
      nextPosition.val = position.val + 1 ∧
      core.iter.adapters.enumerate.IteratorEnumerate.next
          (core.iter.traits.iterator.IteratorSliceIter T)
          (enumerateSliceAt values position) =
        .ok (some (position, values[position.val]),
          enumerateSliceAt values nextPosition) := by
  obtain ⟨nextPosition, hnextValue, hnext⟩ :=
    enumerate_slice_next_run values position hposition
  refine ⟨nextPosition, hnextValue, ?_⟩
  unfold enumerateSliceAt
  simpa [hnextValue] using hnext

/-- A Rust `?` residual can return an error or fail translation-side, but it
cannot manufacture the `Continue` constructor of an enclosing loop.  Keeping
this lemma polymorphic avoids assigning any semantic meaning to the external
error-conversion callback. -/
private theorem result_bind_done_ne_cont
    {A B C : Type} (action : Result A) (finish : A → B) (state : C) :
    (do let value ← action; ok (.done (finish value))) ≠
      (ok (.cont state) : Result (ControlFlow C B)) := by
  cases action <;> simp

/-- The unchanged production `while` loop stops at the requested entry when
the target is present and every entry between the carried ordinal and the
target is smaller.  This is the exact Aeneas translation of the Rust loop,
not the earlier temporary recursive spelling. -/
theorem production_monotone_loop_hits
    (indices : Slice Std.U32) (ordinal target : Std.Usize)
    (index : Std.U32)
    (horder : ordinal.val ≤ target.val)
    (htargetBound : target.val < indices.val.length)
    (hbefore : ∀ position,
      ordinal.val ≤ position → position < target.val →
        indices.val[position]!.val < index.val)
    (htarget : indices.val[target.val]! = index) :
    V5FriConsumerExact.fri_checks.opening_value_for_monotone_index_loop
        indices ordinal index = .ok target := by
  unfold
    V5FriConsumerExact.fri_checks.opening_value_for_monotone_index_loop
  rw [loop.eq_def]
  unfold
    V5FriConsumerExact.fri_checks.opening_value_for_monotone_index_loop.body
  have hordBound : ordinal.val < indices.val.length := by omega
  have hactive : ordinal < Slice.len indices := by scalar_tac
  rw [if_pos hactive]
  rw [slice_index_run indices ordinal hordBound]
  simp only [bind_tc_ok]
  by_cases heq : ordinal.val = target.val
  · have hordTarget : ordinal = target := UScalar.eq_of_val_eq heq
    subst target
    have hat : indices.val[ordinal.val]! = index := htarget
    rw [hat]
    rw [if_neg (lt_irrefl index)]
  · have hstrict : ordinal.val < target.val := by omega
    have hltNat := hbefore ordinal.val (by omega) hstrict
    have hlt : indices.val[ordinal.val]! < index := by scalar_tac
    rw [if_pos hlt]
    simp only [Std.lift, bind_tc_ok]
    let next := Std.Usize.wrapping_add ordinal 1#usize
    have hnextVal : next.val = ordinal.val + 1 :=
      wrapping_succ_exact indices ordinal hordBound
    apply production_monotone_loop_hits indices next target index
    · rw [hnextVal]
      omega
    · exact htargetBound
    · intro position hnextLe hposition
      apply hbefore position
      · rw [hnextVal] at hnextLe
        omega
      · exact hposition
    · exact htarget
termination_by target.val - ordinal.val
decreasing_by
  rw [hnextVal]
  omega

/-- The complete unchanged production helper returns the byte slice at that
exact ordinal.  In particular, the production `while` loop cannot substitute
a neighbouring authenticated opening. -/
theorem production_opening_value_for_monotone_index_hits
    (opening :
      V5FriConsumerExact.aspis_core.state_only_private_openings.StateOnlyPrivateOpening)
    (indices : Slice Std.U32) (ordinal target : Std.Usize)
    (index : Std.U32) (layer : Std.U8) (value : Slice Std.U8)
    (hloop :
      V5FriConsumerExact.fri_checks.opening_value_for_monotone_index_loop
        indices ordinal index = .ok target)
    (htargetBound : target.val < indices.val.length)
    (htarget : indices.val[target.val]! = index)
    (hvalue :
      V5FriConsumerExact.aspis_core.state_only_private_openings.StateOnlyPrivateOpening.value
        opening target = .ok (some value)) :
    V5FriConsumerExact.fri_checks.opening_value_for_monotone_index
        opening indices ordinal index layer =
      .ok (.Ok value, target) := by
  unfold V5FriConsumerExact.fri_checks.opening_value_for_monotone_index
  rw [hloop]
  simp only [bind_tc_ok]
  rw [core_slice_get_run indices target htargetBound]
  simp only [bind_tc_ok]
  rw [htarget]
  simp [V5FriConsumerExact.core.option.OptionShared0T.copied,
    V5FriConsumerExact.core.option.Option.Insts.CoreCmpPartialEqOption.eq,
    core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
    hvalue, V5FriConsumerExact.core.option.Option.ok_or]

abbrev Opening :=
  V5FriConsumerExact.aspis_core.state_only_private_openings.StateOnlyPrivateOpening

abbrev OpeningOffsets :=
  V5FriConsumerExact.aspis_core.state_only_private_openings.StateOnlyPrivateOpeningOffsets

abbrev VerifiedOpenings :=
  V5FriConsumerExact.private_openings.VerifiedV5PrivateOpenings

def checkedC1 (openings : VerifiedOpenings) (count valueWidth : Std.Usize)
    (offsets : OpeningOffsets) : Opening :=
  { openings.c1 with count, value_width := valueWidth, offsets }

def checkedC2 (openings : VerifiedOpenings) (count valueWidth : Std.Usize)
    (offsets : OpeningOffsets) : Opening :=
  { openings.c2 with count, value_width := valueWidth, offsets }

/-- The three opening reads made before a successful layer-zero iteration can
continue.  The equations name the exact generated accessor/helper calls, so
the witness cannot be satisfied by a reordered or neighbouring read. -/
structure LayerZeroBodyReadEvidence
    (openings : VerifiedOpenings) (c1Count c1Width : Std.Usize)
    (c1Offsets : OpeningOffsets) (c2Count c2Width : Std.Usize)
    (c2Offsets : OpeningOffsets) (later : Array Opening 3#usize)
    (laterIndices : Array (alloc.vec.Vec Std.U32) 3#usize)
    (claims powers : alloc.vec.Vec aspis_core.field.QM31)
    (weights : Array (Array Std.U32 4#usize) 16#usize)
    (multipliers : Array aspis_core.field.PreparedQm31Multiplier 3#usize)
    (coordinates : aspis_core.circle_fri.DerivedCircleQueryFoldInverses)
    (alphaPowers : Array
      (Array aspis_core.field.PreparedQm31Multiplier 3#usize) 4#usize)
    (iterNext iterOut : core.iter.adapters.enumerate.Enumerate
      (core.slice.iter.Iter Std.U32))
    (ordinal carried : Std.Usize) (query : Std.U32) : Type where
  c1Value : Slice Std.U8
  c2Value : Slice Std.U8
  parentValue : Slice Std.U8
  parentOrdinal : Std.Usize
  c1Read :
    (checkedC1 openings c1Count c1Width c1Offsets).value ordinal =
      .ok (some c1Value)
  c2Read :
    (checkedC2 openings c2Count c2Width c2Offsets).value ordinal =
      .ok (some c2Value)
  combined : Array aspis_core.field.QM31 4#usize
  combineCall :
    fri_checks.gamma_combine_v5_layer0_exact c1Value c2Value
        { inner := { claims := claims, powers := powers },
          c1_weight_limbs := weights,
          c2_multipliers := multipliers } =
      .ok (.Ok combined)
  circlePair : Array aspis_core.field.M31 2#usize
  circleRead :
    core.slice.Slice.get
        (core.slice.index.SliceIndexUsizeSlice
          (Array aspis_core.field.M31 2#usize))
        (alloc.vec.Vec.deref coordinates.circle) ordinal =
      .ok (some circlePair)
  inv2x : aspis_core.field.M31
  inv2y : aspis_core.field.M31
  inv2xRead : Array.index_usize circlePair 0#usize = .ok inv2x
  inv2yRead : Array.index_usize circlePair 1#usize = .ok inv2y
  alpha : Array aspis_core.field.PreparedQm31Multiplier 3#usize
  alphaRead : Array.index_usize alphaPowers 0#usize = .ok alpha
  foldedValue : aspis_core.field.QM31
  foldCall :
    aspis_core.circle_fri.normalized_circle_to_line_arity4_prepared_polynomial_refs
        combined alpha inv2x inv2y = .ok foldedValue
  parentOpening : Opening
  parentIndices : alloc.vec.Vec Std.U32
  parentOpeningAt : Array.index_usize later 0#usize = .ok parentOpening
  parentIndicesAt :
    Array.index_usize laterIndices 0#usize = .ok parentIndices
  parentRead :
    fri_checks.opening_value_for_monotone_index parentOpening
        (alloc.vec.Vec.deref parentIndices) carried
        (Std.U32.wrapping_shr query 2#u32) 1#u8 =
      .ok (.Ok parentValue, parentOrdinal)
  selectedSlice : Slice Std.U8
  selectedSliceRead :
    core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) parentValue
        { start := Std.Usize.wrapping_mul
            (UScalar.cast .Usize (query &&& 3#u32)) 16#usize,
          «end» := Std.Usize.wrapping_add
            (Std.Usize.wrapping_mul
              (UScalar.cast .Usize (query &&& 3#u32)) 16#usize) 16#usize } =
      .ok selectedSlice
  decodedParent : aspis_core.field.QM31
  decodeParentCall :
    aspis_core.field.QM31.from_le_bytes selectedSlice =
      .ok (some decodedParent)
  acceptedEqualityCall :
    core.cmp.PartialEq.ne.trait_default
        aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
        foldedValue decodedParent = .ok false
  iterOutExact : iterOut = iterNext

/-- Inversion of the unchanged extracted layer-zero loop body.  If an
iteration continues, the C1 and C2 accessors were called at the iterator's
ordinal and the layer-one parent helper was called with `query >> 2` and the
carried monotone ordinal.  Opaque arithmetic may decide whether the iteration
continues, but it cannot alter these already-evaluated call arguments. -/
theorem production_layerZero_body_cont_reads
    (openings : VerifiedOpenings) (c1Count c1Width : Std.Usize)
    (c1Offsets : OpeningOffsets) (c2Count c2Width : Std.Usize)
    (c2Offsets : OpeningOffsets) (later : Array Opening 3#usize)
    (laterIndices : Array (alloc.vec.Vec Std.U32) 3#usize)
    (claims powers : alloc.vec.Vec aspis_core.field.QM31)
    (weights : Array (Array Std.U32 4#usize) 16#usize)
    (multipliers : Array aspis_core.field.PreparedQm31Multiplier 3#usize)
    (finalPolynomial : Array aspis_core.field.QM31 4#usize)
    (coordinates : aspis_core.circle_fri.DerivedCircleQueryFoldInverses)
    (alphaPowers : Array
      (Array aspis_core.field.PreparedQm31Multiplier 3#usize) 4#usize)
    (iter iterNext iterOut :
      core.iter.adapters.enumerate.Enumerate
        (core.slice.iter.Iter Std.U32))
    (folded foldedOut : aspis_core.field.QM31)
    (carried carriedOut ordinal : Std.Usize) (query : Std.U32)
    (hnext :
      core.iter.adapters.enumerate.IteratorEnumerate.next
          (core.iter.traits.iterator.IteratorSliceIter Std.U32) iter =
        .ok (some (ordinal, query), iterNext))
    (hrun :
      fri_checks.check_v5_fri_queries_loop0.body openings c1Count c1Width
          c1Offsets c2Count c2Width c2Offsets later laterIndices claims powers
          weights multipliers finalPolynomial coordinates alphaPowers iter
          folded carried =
        .ok (.cont (iterOut, foldedOut, carriedOut))) :
    Nonempty (LayerZeroBodyReadEvidence openings c1Count c1Width c1Offsets
      c2Count c2Width c2Offsets later laterIndices claims powers weights
      multipliers coordinates alphaPowers iterNext iterOut ordinal carried
      query) := by
  unfold fri_checks.check_v5_fri_queries_loop0.body at hrun
  rw [hnext] at hrun
  simp only [bind_tc_ok] at hrun
  generalize hc1 :
      ({ count := c1Count
         value_width := c1Width
         records := openings.c1.records
         frontier := openings.c1.frontier
         offsets := c1Offsets } : Opening).value ordinal = c1Result at hrun
  cases c1Result with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
  | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
  | ok c1Option =>
    cases c1Option with
    | none => simp [V5FriConsumerExact.core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame, core.convert.FromSame.from] at hrun
    | some c1Value =>
      simp only [V5FriConsumerExact.core.option.Option.ok_or, bind_tc_ok,
        core.result.Result.Insts.CoreOpsTry.branch] at hrun
      generalize hc2 :
          ({ count := c2Count
             value_width := c2Width
             records := openings.c2.records
             frontier := openings.c2.frontier
             offsets := c2Offsets } : Opening).value ordinal = c2Result at hrun
      cases c2Result with
      | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
      | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
      | ok c2Option =>
        cases c2Option with
        | none => simp [V5FriConsumerExact.core.option.Option.ok_or,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame, core.convert.FromSame.from] at hrun
        | some c2Value =>
          simp only [V5FriConsumerExact.core.option.Option.ok_or, bind_tc_ok,
            core.result.Result.Insts.CoreOpsTry.branch] at hrun
          generalize hcombine :
              fri_checks.gamma_combine_v5_layer0_exact c1Value c2Value
                { inner := { claims, powers },
                  c1_weight_limbs := weights,
                  c2_multipliers := multipliers } = combineResult at hrun
          cases combineResult with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
          | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
          | ok combineInner =>
            cases combineInner with
            | Err error =>
              simp only [bind_tc_ok,
                core.result.Result.Insts.CoreOpsTry.branch] at hrun
              exfalso
              exact result_bind_done_ne_cont _ (fun value => some value)
                (iterOut, foldedOut, carriedOut) hrun
            | Ok combined =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch,
                bind_tc_ok] at hrun
              generalize hcircle :
                  core.slice.Slice.get
                    (core.slice.index.SliceIndexUsizeSlice
                      (Array aspis_core.field.M31 2#usize))
                    (alloc.vec.Vec.deref coordinates.circle) ordinal =
                    circleResult at hrun
              cases circleResult with
              | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
              | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
              | ok circleOption =>
                cases circleOption with
                | none =>
                  simp only [V5FriConsumerExact.core.option.Option.ok_or, bind_tc_ok,
                    core.result.Result.Insts.CoreOpsTry.branch] at hrun
                  exfalso
                  exact result_bind_done_ne_cont _ (fun value => some value)
                    (iterOut, foldedOut, carriedOut) hrun
                | some circlePair =>
                  simp only [V5FriConsumerExact.core.option.Option.ok_or, bind_tc_ok,
                    core.result.Result.Insts.CoreOpsTry.branch] at hrun
                  generalize hinvX :
                      Array.index_usize circlePair 0#usize = invXResult at hrun
                  cases invXResult with
                  | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
                  | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
                  | ok invX =>
                    simp only [bind_tc_ok] at hrun
                    generalize hinvY :
                        Array.index_usize circlePair 1#usize = invYResult at hrun
                    cases invYResult with
                    | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
                    | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
                    | ok invY =>
                      simp only [bind_tc_ok] at hrun
                      generalize halpha :
                          Array.index_usize alphaPowers 0#usize = alphaResult
                        at hrun
                      cases alphaResult with
                      | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
                      | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
                      | ok alpha =>
                        simp only [bind_tc_ok] at hrun
                        generalize hfold :
                            aspis_core.circle_fri.normalized_circle_to_line_arity4_prepared_polynomial_refs
                              combined alpha invX invY = foldResult at hrun
                        cases foldResult with
                        | fail error =>
                          simp [Bind.bind, Aeneas.Std.bind] at hrun
                        | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
                        | ok foldedValue =>
                          simp only [bind_tc_ok, Std.lift] at hrun
                          generalize hopening :
                              Array.index_usize later 0#usize = openingResult
                            at hrun
                          cases openingResult with
                          | fail error =>
                            simp [Bind.bind, Aeneas.Std.bind] at hrun
                          | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
                          | ok parentOpening =>
                            simp only [bind_tc_ok] at hrun
                            generalize hindices :
                                Array.index_usize laterIndices 0#usize =
                                  indicesResult at hrun
                            cases indicesResult with
                            | fail error =>
                              simp [Bind.bind, Aeneas.Std.bind] at hrun
                            | div =>
                              simp [Bind.bind, Aeneas.Std.bind] at hrun
                            | ok parentIndices =>
                              simp only [bind_tc_ok] at hrun
                              generalize hparent :
                                  fri_checks.opening_value_for_monotone_index
                                    parentOpening
                                    (alloc.vec.Vec.deref parentIndices) carried
                                    (Std.U32.wrapping_shr query 2#u32) 1#u8 =
                                      parentResult at hrun
                              cases parentResult with
                              | fail error =>
                                simp [Bind.bind, Aeneas.Std.bind] at hrun
                              | div =>
                                simp [Bind.bind, Aeneas.Std.bind] at hrun
                              | ok parentPair =>
                                rcases parentPair with ⟨parentInner,
                                  parentOrdinal⟩
                                cases parentInner with
                                | Err error =>
                                  simp only [bind_tc_ok,
                                    core.result.Result.Insts.CoreOpsTry.branch]
                                    at hrun
                                  exfalso
                                  exact result_bind_done_ne_cont _
                                    (fun value => some value)
                                    (iterOut, foldedOut, carriedOut) hrun
                                | Ok parentValue =>
                                  generalize hsliced :
                                      core.slice.index.Slice.index
                                        (core.slice.index.SliceIndexRangeUsizeSlice
                                          Std.U8) parentValue
                                        { start := Std.Usize.wrapping_mul
                                            (UScalar.cast .Usize
                                              (query &&& 3#u32)) 16#usize,
                                          «end» := Std.Usize.wrapping_add
                                            (Std.Usize.wrapping_mul
                                              (UScalar.cast .Usize
                                                (query &&& 3#u32))
                                              16#usize) 16#usize } =
                                      sliceResult at hrun
                                  cases sliceResult with
                                  | fail error =>
                                    simp_all [Bind.bind, Aeneas.Std.bind]
                                  | div =>
                                    simp_all [Bind.bind, Aeneas.Std.bind]
                                  | ok sliceValue =>
                                    simp only [bind_tc_ok] at hrun
                                    generalize hdecode :
                                        aspis_core.field.QM31.from_le_bytes
                                          sliceValue = decodeResult at hrun
                                    cases decodeResult with
                                    | fail error =>
                                      simp_all [Bind.bind, Aeneas.Std.bind]
                                    | div =>
                                      simp_all [Bind.bind, Aeneas.Std.bind]
                                    | ok decodedOption =>
                                      cases decodedOption with
                                      | none =>
                                        simp_all [V5FriConsumerExact.core.option.Option.ok_or,
                                          core.result.Result.Insts.CoreOpsTry.branch,
                                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                          core.convert.FromSame,
                                          core.convert.FromSame.from]
                                      | some decoded =>
                                        simp_all only [hdecode,
                                          V5FriConsumerExact.core.option.Option.ok_or, bind_tc_ok,
                                          core.result.Result.Insts.CoreOpsTry.branch]
                                        generalize hequal :
                                            core.cmp.PartialEq.ne.trait_default
                                              aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
                                              foldedValue decoded = equalResult
                                          at hrun
                                        cases equalResult with
                                        | fail error =>
                                          simp_all [Bind.bind, Aeneas.Std.bind]
                                        | div =>
                                          simp_all [Bind.bind, Aeneas.Std.bind]
                                        | ok differs =>
                                          simp only [bind_tc_ok] at hrun
                                          cases differs with
                                          | true => simp at hrun
                                          | false =>
                                            generalize hadd :
                                                aspis_core.field.QM31.add folded
                                                  foldedValue = addResult at hrun
                                            cases addResult with
                                            | fail error =>
                                              simp_all [Bind.bind,
                                                Aeneas.Std.bind]
                                            | div =>
                                              simp_all [Bind.bind,
                                                Aeneas.Std.bind]
                                            | ok sum =>
                                              rw [if_neg (by decide :
                                                ¬(false = true))] at hrun
                                              simp only [bind_tc_ok,
                                                Result.ok.injEq,
                                                ControlFlow.cont.injEq,
                                                Prod.mk.injEq] at hrun
                                              exact ⟨{
                                                c1Value := c1Value
                                                c2Value := c2Value
                                                parentValue := parentValue
                                                parentOrdinal := parentOrdinal
                                                c1Read := by
                                                  simpa [checkedC1] using hc1
                                                c2Read := by
                                                  simpa [checkedC2] using hc2
                                                combined := combined
                                                combineCall := hcombine
                                                circlePair := circlePair
                                                circleRead := hcircle
                                                inv2x := invX
                                                inv2y := invY
                                                inv2xRead := hinvX
                                                inv2yRead := hinvY
                                                alpha := alpha
                                                alphaRead := halpha
                                                foldedValue := foldedValue
                                                foldCall := hfold
                                                parentOpening := parentOpening
                                                parentIndices := parentIndices
                                                parentOpeningAt := hopening
                                                parentIndicesAt := hindices
                                                parentRead := hparent
                                                selectedSlice := sliceValue
                                                selectedSliceRead := hsliced
                                                decodedParent := decoded
                                                decodeParentCall := hdecode
                                                acceptedEqualityCall := hequal
                                                iterOutExact := hrun.1.symm }⟩

/-- Reads which must have occurred before a non-terminal later-layer
iteration can continue. -/
structure LaterBodyReadEvidence
    (later : Array Opening 3#usize)
    (laterIndices : Array (alloc.vec.Vec Std.U32) 3#usize)
    (coordinates : aspis_core.circle_fri.DerivedCircleQueryFoldInverses)
    (alphaPowers : Array
      (Array aspis_core.field.PreparedQm31Multiplier 3#usize) 4#usize)
    (layer ordinal carried : Std.Usize) (index : Std.U32) : Type where
  incomingOpening : Opening
  incomingValue : Slice Std.U8
  incomingOpeningAt :
    Array.index_usize later layer = .ok incomingOpening
  incomingRead : incomingOpening.value ordinal = .ok (some incomingValue)
  coordinateArray : alloc.vec.Vec (Array aspis_core.field.M31 3#usize)
  coordinate : Array aspis_core.field.M31 3#usize
  coordinateArrayAt :
    Array.index_usize coordinates.later layer = .ok coordinateArray
  coordinateRead :
    core.slice.Slice.get
        (core.slice.index.SliceIndexUsizeSlice
          (Array aspis_core.field.M31 3#usize))
        (alloc.vec.Vec.deref coordinateArray) ordinal = .ok (some coordinate)
  parentOpening : Opening
  parentIndices : alloc.vec.Vec Std.U32
  parentValue : Slice Std.U8
  parentOrdinal : Std.Usize
  parentOpeningAt :
    Array.index_usize later (Std.Usize.wrapping_add layer 1#usize) =
      .ok parentOpening
  parentIndicesAt :
    Array.index_usize laterIndices
        (Std.Usize.wrapping_add layer 1#usize) = .ok parentIndices
  parentRead :
    fri_checks.opening_value_for_monotone_index parentOpening
        (alloc.vec.Vec.deref parentIndices) carried
        (Std.U32.wrapping_shr index 2#u32)
        (Std.U8.wrapping_add (UScalar.cast .U8 layer) 2#u8) =
      .ok (.Ok parentValue, parentOrdinal)
  alpha : Array aspis_core.field.PreparedQm31Multiplier 3#usize
  alphaRead :
    Array.index_usize alphaPowers (Std.Usize.wrapping_add layer 1#usize) =
      .ok alpha
  transitionCall :
    aspis_core.circle_query.check_fixed_line_transition_prepared_polynomial_powers
        incomingValue parentValue (UScalar.cast .Usize index)
        (Std.U8.wrapping_add (UScalar.cast .U8 layer) 1#u8)
        coordinate alpha = .ok (.Ok ())

/-- Inversion of either non-terminal production later-layer body. -/
theorem production_later_body_cont_reads
    (later : Array Opening 3#usize)
    (laterIndices : Array (alloc.vec.Vec Std.U32) 3#usize)
    (finalPolynomial : Array aspis_core.field.QM31 4#usize)
    (coordinates : aspis_core.circle_fri.DerivedCircleQueryFoldInverses)
    (alphaPowers : Array
      (Array aspis_core.field.PreparedQm31Multiplier 3#usize) 4#usize)
    (layer : Std.Usize) (hlayer : layer < 2#usize)
    (pending : Option
      (core.result.Result fri_checks.V5FriCheckSink fri_checks.V5FriCheckError))
    (iter iterNext iterOut :
      core.iter.adapters.enumerate.Enumerate
        (core.slice.iter.Iter Std.U32))
    (carried carriedOut ordinal : Std.Usize) (index : Std.U32)
    (hnext :
      core.iter.adapters.enumerate.IteratorEnumerate.next
          (core.iter.traits.iterator.IteratorSliceIter Std.U32) iter =
        .ok (some (ordinal, index), iterNext))
    (hrun :
      fri_checks.check_v5_fri_queries_loop0_loop0_loop0.body later
          laterIndices finalPolynomial coordinates alphaPowers layer pending
          iter carried = .ok (.cont (iterOut, carriedOut))) :
    Nonempty (LaterBodyReadEvidence later laterIndices coordinates alphaPowers
      layer ordinal carried index) := by
  unfold fri_checks.check_v5_fri_queries_loop0_loop0_loop0.body at hrun
  rw [hnext] at hrun
  simp only [bind_tc_ok] at hrun
  generalize hopening : Array.index_usize later layer = openingResult at hrun
  cases openingResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
  | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
  | ok incomingOpening =>
    simp only [bind_tc_ok] at hrun
    generalize hincoming : incomingOpening.value ordinal = incomingResult
      at hrun
    cases incomingResult with
    | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
    | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
    | ok incomingOption =>
      cases incomingOption with
      | none => simp [V5FriConsumerExact.core.option.Option.ok_or,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame, core.convert.FromSame.from, Std.lift] at hrun
      | some incomingValue =>
        simp only [V5FriConsumerExact.core.option.Option.ok_or, bind_tc_ok,
          core.result.Result.Insts.CoreOpsTry.branch, Std.lift] at hrun
        generalize hcoordinateArray :
            Array.index_usize coordinates.later layer = coordinateArrayResult
          at hrun
        cases coordinateArrayResult with
        | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
        | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
        | ok coordinateArray =>
          simp only [bind_tc_ok] at hrun
          generalize hcoordinate :
              core.slice.Slice.get
                (core.slice.index.SliceIndexUsizeSlice
                  (Array aspis_core.field.M31 3#usize))
                (alloc.vec.Vec.deref coordinateArray) ordinal =
                  coordinateResult at hrun
          cases coordinateResult with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
          | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
          | ok coordinateOption =>
            cases coordinateOption with
            | none => simp [V5FriConsumerExact.core.option.Option.ok_or,
                core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame, core.convert.FromSame.from] at hrun
            | some coordinate =>
              simp only [V5FriConsumerExact.core.option.Option.ok_or, bind_tc_ok,
                core.result.Result.Insts.CoreOpsTry.branch] at hrun
              rw [if_pos hlayer] at hrun
              generalize hparentOpening :
                  Array.index_usize later
                    (Std.Usize.wrapping_add layer 1#usize) =
                      parentOpeningResult at hrun
              cases parentOpeningResult with
              | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
              | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
              | ok parentOpening =>
                simp only [bind_tc_ok] at hrun
                generalize hparentIndices :
                    Array.index_usize laterIndices
                      (Std.Usize.wrapping_add layer 1#usize) =
                        parentIndicesResult at hrun
                cases parentIndicesResult with
                | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
                | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
                | ok parentIndices =>
                  simp only [bind_tc_ok, Std.lift] at hrun
                  generalize hparent :
                      fri_checks.opening_value_for_monotone_index parentOpening
                        (alloc.vec.Vec.deref parentIndices) carried
                        (Std.U32.wrapping_shr index 2#u32)
                        (Std.U8.wrapping_add (UScalar.cast .U8 layer) 2#u8) =
                          parentResult at hrun
                  cases parentResult with
                  | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
                  | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
                  | ok parentPair =>
                    rcases parentPair with ⟨parentInner, parentOrdinal⟩
                    cases parentInner with
                    | Err error =>
                      simp only [bind_tc_ok,
                        core.result.Result.Insts.CoreOpsTry.branch] at hrun
                      exfalso
                      exact result_bind_done_ne_cont _
                        (fun value => (coordinates, some value, 0#u32))
                        (iterOut, carriedOut) hrun
                    | Ok parentValue =>
                      simp only [
                        core.result.Result.Insts.CoreOpsTry.branch,
                        bind_tc_ok, Std.lift] at hrun
                      generalize halpha :
                          Array.index_usize alphaPowers
                            (Std.Usize.wrapping_add layer 1#usize) =
                              alphaResult at hrun
                      cases alphaResult with
                      | fail error =>
                        simp [Bind.bind, Aeneas.Std.bind] at hrun
                      | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
                      | ok alpha =>
                        simp only [bind_tc_ok] at hrun
                        generalize htransition :
                            aspis_core.circle_query.check_fixed_line_transition_prepared_polynomial_powers
                              incomingValue parentValue
                              (UScalar.cast .Usize index)
                              (Std.U8.wrapping_add
                                (UScalar.cast .U8 layer) 1#u8)
                              coordinate alpha = transitionResult at hrun
                        cases transitionResult with
                        | fail error =>
                          simp [Bind.bind, Aeneas.Std.bind] at hrun
                        | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
                        | ok transitionInner =>
                          cases transitionInner with
                          | Err error =>
                            simp only [bind_tc_ok,
                              core.result.Result.Insts.CoreOpsTry.branch]
                              at hrun
                            exfalso
                            exact result_bind_done_ne_cont _
                              (fun value =>
                                (coordinates, some value, 0#u32))
                              (iterOut, carriedOut) hrun
                          | Ok unit =>
                            cases unit
                            simp only [
                              core.result.Result.Insts.CoreOpsTry.branch,
                              bind_tc_ok, Result.ok.injEq,
                              ControlFlow.cont.injEq, Prod.mk.injEq] at hrun
                            exact ⟨{
                              incomingOpening := incomingOpening
                              incomingValue := incomingValue
                              incomingOpeningAt := hopening
                              incomingRead := hincoming
                              coordinateArray := coordinateArray
                              coordinate := coordinate
                              coordinateArrayAt := hcoordinateArray
                              coordinateRead := hcoordinate
                              parentOpening := parentOpening
                              parentIndices := parentIndices
                              parentValue := parentValue
                              parentOrdinal := parentOrdinal
                              parentOpeningAt := hparentOpening
                              parentIndicesAt := hparentIndices
                              parentRead := hparent
                              alpha := alpha
                              alphaRead := halpha
                              transitionCall := htransition }⟩

/-- The opening read which must occur before a terminal-layer iteration can
continue.  The terminal polynomial and inverse-coordinate operations happen
after this exact read and therefore cannot change its ordinal. -/
structure TerminalBodyReadEvidence
    (later : Array Opening 3#usize)
    (finalPolynomial : Array aspis_core.field.QM31 4#usize)
    (coordinates : aspis_core.circle_fri.DerivedCircleQueryFoldInverses)
    (alphaPowers : Array
      (Array aspis_core.field.PreparedQm31Multiplier 3#usize) 4#usize)
    (layer ordinal : Std.Usize) (index : Std.U32) : Type where
  incomingOpening : Opening
  incomingValue : Slice Std.U8
  incomingOpeningAt :
    Array.index_usize later layer = .ok incomingOpening
  incomingRead : incomingOpening.value ordinal = .ok (some incomingValue)
  coordinateArray : alloc.vec.Vec (Array aspis_core.field.M31 3#usize)
  coordinate : Array aspis_core.field.M31 3#usize
  coordinateArrayAt :
    Array.index_usize coordinates.later layer = .ok coordinateArray
  coordinateRead :
    core.slice.Slice.get
        (core.slice.index.SliceIndexUsizeSlice
          (Array aspis_core.field.M31 3#usize))
        (alloc.vec.Vec.deref coordinateArray) ordinal = .ok (some coordinate)
  finalX : aspis_core.field.M31
  finalXRead :
    core.slice.Slice.get
        (core.slice.index.SliceIndexUsizeSlice aspis_core.field.M31)
        (alloc.vec.Vec.deref coordinates.final_x) ordinal = .ok (some finalX)
  alpha : Array aspis_core.field.PreparedQm31Multiplier 3#usize
  alphaRead : Array.index_usize alphaPowers 3#usize = .ok alpha
  transitionCall :
    aspis_core.circle_query.check_fixed_terminal_transition_prepared_polynomial_refs
        incomingValue finalPolynomial (UScalar.cast .Usize index)
        coordinate finalX alpha = .ok (.Ok ())

theorem production_terminal_body_cont_reads
    (later : Array Opening 3#usize)
    (laterIndices : Array (alloc.vec.Vec Std.U32) 3#usize)
    (finalPolynomial : Array aspis_core.field.QM31 4#usize)
    (coordinates : aspis_core.circle_fri.DerivedCircleQueryFoldInverses)
    (alphaPowers : Array
      (Array aspis_core.field.PreparedQm31Multiplier 3#usize) 4#usize)
    (layer : Std.Usize) (hlayer : ¬layer < 2#usize)
    (pending : Option
      (core.result.Result fri_checks.V5FriCheckSink fri_checks.V5FriCheckError))
    (iter iterNext iterOut :
      core.iter.adapters.enumerate.Enumerate
        (core.slice.iter.Iter Std.U32))
    (carried carriedOut ordinal : Std.Usize) (index : Std.U32)
    (hnext :
      core.iter.adapters.enumerate.IteratorEnumerate.next
          (core.iter.traits.iterator.IteratorSliceIter Std.U32) iter =
        .ok (some (ordinal, index), iterNext))
    (hrun :
      fri_checks.check_v5_fri_queries_loop0_loop0_loop0.body later
          laterIndices finalPolynomial coordinates alphaPowers layer pending
          iter carried = .ok (.cont (iterOut, carriedOut))) :
    Nonempty (TerminalBodyReadEvidence later finalPolynomial coordinates
      alphaPowers layer ordinal index) := by
  unfold fri_checks.check_v5_fri_queries_loop0_loop0_loop0.body at hrun
  rw [hnext] at hrun
  simp only [bind_tc_ok] at hrun
  generalize hopening : Array.index_usize later layer = openingResult at hrun
  cases openingResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
  | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
  | ok incomingOpening =>
    simp only [bind_tc_ok] at hrun
    generalize hincoming : incomingOpening.value ordinal = incomingResult
      at hrun
    cases incomingResult with
    | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
    | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
    | ok incomingOption =>
      cases incomingOption with
      | none => simp [V5FriConsumerExact.core.option.Option.ok_or,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame, core.convert.FromSame.from, Std.lift] at hrun
      | some incomingValue =>
        simp only [V5FriConsumerExact.core.option.Option.ok_or, bind_tc_ok,
          core.result.Result.Insts.CoreOpsTry.branch, Std.lift] at hrun
        generalize hcoordinateArray :
            Array.index_usize coordinates.later layer = coordinateArrayResult
          at hrun
        cases coordinateArrayResult with
        | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
        | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
        | ok coordinateArray =>
          simp only [bind_tc_ok] at hrun
          generalize hcoordinate :
              core.slice.Slice.get
                (core.slice.index.SliceIndexUsizeSlice
                  (Array aspis_core.field.M31 3#usize))
                (alloc.vec.Vec.deref coordinateArray) ordinal =
                  coordinateResult at hrun
          cases coordinateResult with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
          | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
          | ok coordinateOption =>
            cases coordinateOption with
            | none => simp [V5FriConsumerExact.core.option.Option.ok_or,
                core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame, core.convert.FromSame.from] at hrun
            | some coordinate =>
              simp only [V5FriConsumerExact.core.option.Option.ok_or, bind_tc_ok,
                core.result.Result.Insts.CoreOpsTry.branch] at hrun
              rw [if_neg hlayer] at hrun
              generalize hfinalX :
                  core.slice.Slice.get
                    (core.slice.index.SliceIndexUsizeSlice
                      aspis_core.field.M31)
                    (alloc.vec.Vec.deref coordinates.final_x) ordinal =
                      finalXResult at hrun
              cases finalXResult with
              | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
              | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
              | ok finalXOption =>
                cases finalXOption with
                | none => simp [V5FriConsumerExact.core.option.Option.ok_or,
                    core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                    core.convert.FromSame, core.convert.FromSame.from] at hrun
                | some finalX =>
                  simp only [V5FriConsumerExact.core.option.Option.ok_or, bind_tc_ok,
                    core.result.Result.Insts.CoreOpsTry.branch, Std.lift]
                    at hrun
                  generalize halpha :
                      Array.index_usize alphaPowers 3#usize = alphaResult
                    at hrun
                  cases alphaResult with
                  | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
                  | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
                  | ok alpha =>
                    simp only [bind_tc_ok] at hrun
                    generalize htransition :
                        aspis_core.circle_query.check_fixed_terminal_transition_prepared_polynomial_refs
                          incomingValue finalPolynomial
                          (UScalar.cast .Usize index) coordinate finalX alpha =
                            transitionResult at hrun
                    cases transitionResult with
                    | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
                    | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
                    | ok transitionInner =>
                      cases transitionInner with
                      | Err error =>
                        simp only [bind_tc_ok,
                          core.result.Result.Insts.CoreOpsTry.branch] at hrun
                        exfalso
                        exact result_bind_done_ne_cont _
                          (fun value => (coordinates, some value, 0#u32))
                          (iterOut, carriedOut) hrun
                      | Ok unit =>
                        cases unit
                        simp only [
                          core.result.Result.Insts.CoreOpsTry.branch,
                          bind_tc_ok, Result.ok.injEq,
                          ControlFlow.cont.injEq, Prod.mk.injEq] at hrun
                        exact ⟨{
                          incomingOpening := incomingOpening
                          incomingValue := incomingValue
                          incomingOpeningAt := hopening
                          incomingRead := hincoming
                          coordinateArray := coordinateArray
                          coordinate := coordinate
                          coordinateArrayAt := hcoordinateArray
                          coordinateRead := hcoordinate
                          finalX := finalX
                          finalXRead := hfinalX
                          alpha := alpha
                          alphaRead := halpha
                          transitionCall := htransition }⟩

/-- An active layer-zero iteration has no source branch which returns an
accepted sink.  Acceptance is constructed only after the iterator is
exhausted and the three later-layer loops have completed. -/
theorem production_layerZero_active_body_ne_accepting_done
    (openings : VerifiedOpenings) (c1Count c1Width : Std.Usize)
    (c1Offsets : OpeningOffsets) (c2Count c2Width : Std.Usize)
    (c2Offsets : OpeningOffsets) (later : Array Opening 3#usize)
    (laterIndices : Array (alloc.vec.Vec Std.U32) 3#usize)
    (claims powers : alloc.vec.Vec aspis_core.field.QM31)
    (weights : Array (Array Std.U32 4#usize) 16#usize)
    (multipliers : Array aspis_core.field.PreparedQm31Multiplier 3#usize)
    (finalPolynomial : Array aspis_core.field.QM31 4#usize)
    (coordinates : aspis_core.circle_fri.DerivedCircleQueryFoldInverses)
    (alphaPowers : Array
      (Array aspis_core.field.PreparedQm31Multiplier 3#usize) 4#usize)
    (iter iterNext :
      core.iter.adapters.enumerate.Enumerate
        (core.slice.iter.Iter Std.U32))
    (folded : aspis_core.field.QM31) (carried ordinal : Std.Usize)
    (query : Std.U32) (sink : fri_checks.V5FriCheckSink)
    (hnext :
      core.iter.adapters.enumerate.IteratorEnumerate.next
          (core.iter.traits.iterator.IteratorSliceIter Std.U32) iter =
        .ok (some (ordinal, query), iterNext)) :
    fri_checks.check_v5_fri_queries_loop0.body openings c1Count c1Width
        c1Offsets c2Count c2Width c2Offsets later laterIndices claims powers
        weights multipliers finalPolynomial coordinates alphaPowers iter
        folded carried ≠ .ok (.done (some (.Ok sink))) := by
  intro hrun
  unfold fri_checks.check_v5_fri_queries_loop0.body at hrun
  rw [hnext] at hrun
  simp only [bind_tc_ok] at hrun
  generalize hc1 :
      ({ count := c1Count
         value_width := c1Width
         records := openings.c1.records
         frontier := openings.c1.frontier
         offsets := c1Offsets } : Opening).value ordinal = c1Result at hrun
  cases c1Result with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
  | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
  | ok c1Option =>
    cases c1Option with
    | none =>
      simp [V5FriConsumerExact.core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame, core.convert.FromSame.from] at hrun
    | some c1Value =>
      simp only [V5FriConsumerExact.core.option.Option.ok_or, bind_tc_ok,
        core.result.Result.Insts.CoreOpsTry.branch] at hrun
      generalize hc2 :
          ({ count := c2Count
             value_width := c2Width
             records := openings.c2.records
             frontier := openings.c2.frontier
             offsets := c2Offsets } : Opening).value ordinal = c2Result at hrun
      cases c2Result with
      | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
      | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
      | ok c2Option =>
        cases c2Option with
        | none =>
          simp [V5FriConsumerExact.core.option.Option.ok_or,
            core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame, core.convert.FromSame.from] at hrun
        | some c2Value =>
          simp only [V5FriConsumerExact.core.option.Option.ok_or, bind_tc_ok,
            core.result.Result.Insts.CoreOpsTry.branch] at hrun
          generalize hcombine :
              fri_checks.gamma_combine_v5_layer0_exact c1Value c2Value
                { inner := { claims, powers },
                  c1_weight_limbs := weights,
                  c2_multipliers := multipliers } = combineResult at hrun
          cases combineResult with
          | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
          | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
          | ok combineInner =>
            cases combineInner with
            | Err error =>
              simp [core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                fri_checks.V5FriCheckError.Insts.CoreConvertFromCirclePcsDecodeError,
                fri_checks.V5FriCheckError.Insts.CoreConvertFromCirclePcsDecodeError.from]
                at hrun
            | Ok combined =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch,
                bind_tc_ok] at hrun
              generalize hcircle :
                  core.slice.Slice.get
                    (core.slice.index.SliceIndexUsizeSlice
                      (Array aspis_core.field.M31 2#usize))
                    (alloc.vec.Vec.deref coordinates.circle) ordinal =
                      circleResult at hrun
              cases circleResult with
              | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
              | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
              | ok circleOption =>
                cases circleOption with
                | none =>
                  simp [V5FriConsumerExact.core.option.Option.ok_or,
                    core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                    core.convert.FromSame, core.convert.FromSame.from] at hrun
                | some circlePair =>
                  simp only [V5FriConsumerExact.core.option.Option.ok_or, bind_tc_ok,
                    core.result.Result.Insts.CoreOpsTry.branch] at hrun
                  generalize hinvX :
                      Array.index_usize circlePair 0#usize = invXResult at hrun
                  cases invXResult with
                  | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
                  | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
                  | ok invX =>
                    simp only [bind_tc_ok] at hrun
                    generalize hinvY :
                        Array.index_usize circlePair 1#usize = invYResult at hrun
                    cases invYResult with
                    | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
                    | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
                    | ok invY =>
                      simp only [bind_tc_ok] at hrun
                      generalize halpha :
                          Array.index_usize alphaPowers 0#usize = alphaResult
                        at hrun
                      cases alphaResult with
                      | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
                      | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
                      | ok alpha =>
                        simp only [bind_tc_ok] at hrun
                        generalize hfold :
                            aspis_core.circle_fri.normalized_circle_to_line_arity4_prepared_polynomial_refs
                              combined alpha invX invY = foldResult at hrun
                        cases foldResult with
                        | fail error =>
                          simp [Bind.bind, Aeneas.Std.bind] at hrun
                        | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
                        | ok foldedValue =>
                          simp only [bind_tc_ok, Std.lift] at hrun
                          generalize hopening :
                              Array.index_usize later 0#usize = openingResult
                            at hrun
                          cases openingResult with
                          | fail error =>
                            simp [Bind.bind, Aeneas.Std.bind] at hrun
                          | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
                          | ok parentOpening =>
                            simp only [bind_tc_ok] at hrun
                            generalize hindices :
                                Array.index_usize laterIndices 0#usize =
                                  indicesResult at hrun
                            cases indicesResult with
                            | fail error =>
                              simp [Bind.bind, Aeneas.Std.bind] at hrun
                            | div =>
                              simp [Bind.bind, Aeneas.Std.bind] at hrun
                            | ok parentIndices =>
                              simp only [bind_tc_ok] at hrun
                              generalize hparent :
                                  fri_checks.opening_value_for_monotone_index
                                    parentOpening
                                    (alloc.vec.Vec.deref parentIndices) carried
                                    (Std.U32.wrapping_shr query 2#u32) 1#u8 =
                                      parentResult at hrun
                              cases parentResult with
                              | fail error =>
                                simp [Bind.bind, Aeneas.Std.bind] at hrun
                              | div =>
                                simp [Bind.bind, Aeneas.Std.bind] at hrun
                              | ok parentPair =>
                                rcases parentPair with ⟨parentInner,
                                  parentOrdinal⟩
                                cases parentInner with
                                | Err error =>
                                  simp [core.result.Result.Insts.CoreOpsTry.branch,
                                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                    core.convert.FromSame, core.convert.FromSame.from]
                                    at hrun
                                | Ok parentValue =>
                                  simp only [
                                    core.result.Result.Insts.CoreOpsTry.branch,
                                    bind_tc_ok, Std.lift] at hrun
                                  generalize hsliced :
                                      core.slice.index.Slice.index
                                        (core.slice.index.SliceIndexRangeUsizeSlice
                                          Std.U8) parentValue
                                        { start := Std.Usize.wrapping_mul
                                            (UScalar.cast .Usize
                                              (query &&& 3#u32)) 16#usize,
                                          «end» := Std.Usize.wrapping_add
                                            (Std.Usize.wrapping_mul
                                              (UScalar.cast .Usize
                                                (query &&& 3#u32)) 16#usize)
                                            16#usize } = sliceResult at hrun
                                  cases sliceResult with
                                  | fail error =>
                                    simp [Bind.bind, Aeneas.Std.bind] at hrun
                                  | div =>
                                    simp [Bind.bind, Aeneas.Std.bind] at hrun
                                  | ok sliceValue =>
                                    simp only [bind_tc_ok] at hrun
                                    generalize hdecode :
                                        aspis_core.field.QM31.from_le_bytes
                                          sliceValue = decodeResult at hrun
                                    cases decodeResult with
                                    | fail error =>
                                      simp [Bind.bind, Aeneas.Std.bind] at hrun
                                    | div =>
                                      simp [Bind.bind, Aeneas.Std.bind] at hrun
                                    | ok decodedOption =>
                                      cases decodedOption with
                                      | none =>
                                        simp [V5FriConsumerExact.core.option.Option.ok_or,
                                          core.result.Result.Insts.CoreOpsTry.branch,
                                          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                                          core.convert.FromSame,
                                          core.convert.FromSame.from] at hrun
                                      | some decoded =>
                                        simp only [V5FriConsumerExact.core.option.Option.ok_or,
                                          bind_tc_ok,
                                          core.result.Result.Insts.CoreOpsTry.branch]
                                          at hrun
                                        generalize hequal :
                                            core.cmp.PartialEq.ne.trait_default
                                              aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
                                              foldedValue decoded = equalResult
                                          at hrun
                                        cases equalResult with
                                        | fail error =>
                                          simp [Bind.bind, Aeneas.Std.bind]
                                            at hrun
                                        | div =>
                                          simp [Bind.bind, Aeneas.Std.bind]
                                            at hrun
                                        | ok differs =>
                                          cases differs with
                                          | true => simp at hrun
                                          | false =>
                                            generalize hadd :
                                                aspis_core.field.QM31.add
                                                  folded foldedValue =
                                                    addResult at hrun
                                            cases addResult <;>
                                              simp [Bind.bind, Aeneas.Std.bind]
                                                at hrun

/-- Peeling one active iteration from an accepted production layer-zero
loop yields an actual continuation and therefore the exact reads proved
above.  The recursive loop equation is the one generated by Aeneas for the
unchanged Rust `for` loop. -/
theorem production_layerZero_accepted_loop_head
    (openings : VerifiedOpenings) (c1Count c1Width : Std.Usize)
    (c1Offsets : OpeningOffsets) (c2Count c2Width : Std.Usize)
    (c2Offsets : OpeningOffsets) (later : Array Opening 3#usize)
    (laterIndices : Array (alloc.vec.Vec Std.U32) 3#usize)
    (claims powers : alloc.vec.Vec aspis_core.field.QM31)
    (weights : Array (Array Std.U32 4#usize) 16#usize)
    (multipliers : Array aspis_core.field.PreparedQm31Multiplier 3#usize)
    (finalPolynomial : Array aspis_core.field.QM31 4#usize)
    (coordinates : aspis_core.circle_fri.DerivedCircleQueryFoldInverses)
    (alphaPowers : Array
      (Array aspis_core.field.PreparedQm31Multiplier 3#usize) 4#usize)
    (iter iterNext :
      core.iter.adapters.enumerate.Enumerate
        (core.slice.iter.Iter Std.U32))
    (folded : aspis_core.field.QM31) (carried ordinal : Std.Usize)
    (query : Std.U32) (sink : fri_checks.V5FriCheckSink)
    (hnext :
      core.iter.adapters.enumerate.IteratorEnumerate.next
          (core.iter.traits.iterator.IteratorSliceIter Std.U32) iter =
        .ok (some (ordinal, query), iterNext))
    (hloop :
      fri_checks.check_v5_fri_queries_loop0 openings iter c1Count c1Width
          c1Offsets c2Count c2Width c2Offsets later laterIndices claims powers
          weights multipliers finalPolynomial coordinates alphaPowers folded
          carried = .ok (some (.Ok sink))) :
    ∃ foldedNext carriedNext,
      fri_checks.check_v5_fri_queries_loop0.body openings c1Count c1Width
          c1Offsets c2Count c2Width c2Offsets later laterIndices claims powers
          weights multipliers finalPolynomial coordinates alphaPowers iter
          folded carried = .ok (.cont (iterNext, foldedNext, carriedNext)) ∧
      fri_checks.check_v5_fri_queries_loop0 openings iterNext c1Count c1Width
          c1Offsets c2Count c2Width c2Offsets later laterIndices claims powers
          weights multipliers finalPolynomial coordinates alphaPowers
          foldedNext carriedNext = .ok (some (.Ok sink)) ∧
      Nonempty (LayerZeroBodyReadEvidence openings c1Count c1Width c1Offsets
        c2Count c2Width c2Offsets later laterIndices claims powers weights
        multipliers coordinates alphaPowers iterNext iterNext ordinal carried
        query) := by
  unfold fri_checks.check_v5_fri_queries_loop0 at hloop
  rw [loop.eq_def] at hloop
  simp only at hloop
  generalize hbody :
      fri_checks.check_v5_fri_queries_loop0.body openings c1Count c1Width
        c1Offsets c2Count c2Width c2Offsets later laterIndices claims powers
        weights multipliers finalPolynomial coordinates alphaPowers iter
        folded carried = bodyResult at hloop
  cases bodyResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at hloop
  | div => simp [Bind.bind, Aeneas.Std.bind] at hloop
  | ok flow =>
    cases flow with
    | cont nextState =>
      rcases nextState with ⟨nextIter, foldedNext, carriedNext⟩
      simp only [bind_tc_ok] at hloop
      change fri_checks.check_v5_fri_queries_loop0 openings nextIter c1Count
        c1Width c1Offsets c2Count c2Width c2Offsets later laterIndices claims
        powers weights multipliers finalPolynomial coordinates alphaPowers
        foldedNext carriedNext = .ok (some (.Ok sink)) at hloop
      have hevidence := production_layerZero_body_cont_reads openings c1Count
        c1Width c1Offsets c2Count c2Width c2Offsets later laterIndices claims
        powers weights multipliers finalPolynomial coordinates alphaPowers iter
        iterNext nextIter folded foldedNext carried carriedNext ordinal query
        hnext hbody
      obtain ⟨evidence⟩ := hevidence
      have hiter : nextIter = iterNext := evidence.iterOutExact
      subst nextIter
      refine ⟨foldedNext, carriedNext, ?_, hloop, ⟨evidence⟩⟩
      simpa using hbody
    | done output =>
      simp only [bind_tc_ok, Result.ok.injEq] at hloop
      subst output
      exact (production_layerZero_active_body_ne_accepting_done openings
        c1Count c1Width c1Offsets c2Count c2Width c2Offsets later laterIndices
        claims powers weights multipliers finalPolynomial coordinates
        alphaPowers iter iterNext folded carried ordinal query sink hnext hbody).elim

/-- Every position between the current iterator cursor and the target is
actually visited by an accepted unchanged production layer-zero loop.  This
is the loop-level theorem missing from the earlier body-only extraction. -/
theorem production_layerZero_accepted_loop_reads_target
    (openings : VerifiedOpenings) (c1Count c1Width : Std.Usize)
    (c1Offsets : OpeningOffsets) (c2Count c2Width : Std.Usize)
    (c2Offsets : OpeningOffsets) (later : Array Opening 3#usize)
    (laterIndices : Array (alloc.vec.Vec Std.U32) 3#usize)
    (claims powers : alloc.vec.Vec aspis_core.field.QM31)
    (weights : Array (Array Std.U32 4#usize) 16#usize)
    (multipliers : Array aspis_core.field.PreparedQm31Multiplier 3#usize)
    (finalPolynomial : Array aspis_core.field.QM31 4#usize)
    (coordinates : aspis_core.circle_fri.DerivedCircleQueryFoldInverses)
    (alphaPowers : Array
      (Array aspis_core.field.PreparedQm31Multiplier 3#usize) 4#usize)
    (values : Slice Std.U32) (current target : Std.Usize)
    (folded : aspis_core.field.QM31) (carried : Std.Usize)
    (sink : fri_checks.V5FriCheckSink)
    (horder : current.val ≤ target.val)
    (htarget : target.val < values.val.length)
    (hloop :
      fri_checks.check_v5_fri_queries_loop0 openings
          (enumerateSliceAt values current) c1Count c1Width c1Offsets c2Count
          c2Width c2Offsets later laterIndices claims powers weights
          multipliers finalPolynomial coordinates alphaPowers folded carried =
        .ok (some (.Ok sink))) :
    ∃ carriedAt nextPosition,
      nextPosition.val = target.val + 1 ∧
      Nonempty (LayerZeroBodyReadEvidence openings c1Count c1Width c1Offsets
        c2Count c2Width c2Offsets later laterIndices claims powers weights
        multipliers coordinates alphaPowers
        (enumerateSliceAt values nextPosition)
        (enumerateSliceAt values nextPosition) target carriedAt
        values[target.val]) := by
  have hcurrent : current.val < values.val.length := by omega
  obtain ⟨nextPosition, hnextValue, hnext⟩ :=
    enumerate_slice_at_next_run values current hcurrent
  obtain ⟨foldedNext, carriedNext, _hbody, hloopNext, hevidence⟩ :=
    production_layerZero_accepted_loop_head openings c1Count c1Width c1Offsets
      c2Count c2Width c2Offsets later laterIndices claims powers weights
      multipliers finalPolynomial coordinates alphaPowers
      (enumerateSliceAt values current) (enumerateSliceAt values nextPosition)
      folded carried current values[current.val] sink hnext hloop
  by_cases heq : current.val = target.val
  · have hscalar : current = target := UScalar.eq_of_val_eq heq
    subst target
    exact ⟨carried, nextPosition, hnextValue, hevidence⟩
  · apply production_layerZero_accepted_loop_reads_target openings c1Count
      c1Width c1Offsets c2Count c2Width c2Offsets later laterIndices claims
      powers weights multipliers finalPolynomial coordinates alphaPowers values
      nextPosition target foldedNext carriedNext sink
    · rw [hnextValue]
      omega
    · exact hloopNext
termination_by target.val - current.val
decreasing_by
  rw [hnextValue]
  omega

/-- Every continuation of an active later-layer body uses exactly the
iterator returned by the production `enumerate().next()` call. -/
theorem production_later_cont_iter_exact
    (later : Array Opening 3#usize)
    (laterIndices : Array (alloc.vec.Vec Std.U32) 3#usize)
    (finalPolynomial : Array aspis_core.field.QM31 4#usize)
    (coordinates : aspis_core.circle_fri.DerivedCircleQueryFoldInverses)
    (alphaPowers : Array
      (Array aspis_core.field.PreparedQm31Multiplier 3#usize) 4#usize)
    (layer : Std.Usize)
    (pending : Option
      (core.result.Result fri_checks.V5FriCheckSink fri_checks.V5FriCheckError))
    (iter iterNext iterOut :
      core.iter.adapters.enumerate.Enumerate
        (core.slice.iter.Iter Std.U32))
    (carried carriedOut ordinal : Std.Usize) (index : Std.U32)
    (hnext :
      core.iter.adapters.enumerate.IteratorEnumerate.next
          (core.iter.traits.iterator.IteratorSliceIter Std.U32) iter =
        .ok (some (ordinal, index), iterNext))
    (hrun :
      fri_checks.check_v5_fri_queries_loop0_loop0_loop0.body later
          laterIndices finalPolynomial coordinates alphaPowers layer pending
          iter carried = .ok (.cont (iterOut, carriedOut))) :
    iterOut = iterNext := by
  unfold fri_checks.check_v5_fri_queries_loop0_loop0_loop0.body at hrun
  rw [hnext] at hrun
  simp only [bind_tc_ok] at hrun
  repeat' first
    | split at hrun
    | simp_all [Bind.bind, Aeneas.Std.bind, Std.lift,
        V5FriConsumerExact.core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame, core.convert.FromSame.from]

/-- An active later-layer body can reject or continue, but the production
source assigns completion flag one only after the iterator is exhausted. -/
theorem production_inner_active_body_ne_completed
    (later : Array Opening 3#usize)
    (laterIndices : Array (alloc.vec.Vec Std.U32) 3#usize)
    (finalPolynomial : Array aspis_core.field.QM31 4#usize)
    (coordinates coordinatesOut :
      aspis_core.circle_fri.DerivedCircleQueryFoldInverses)
    (alphaPowers : Array
      (Array aspis_core.field.PreparedQm31Multiplier 3#usize) 4#usize)
    (layer : Std.Usize)
    (pending pendingOut : Option
      (core.result.Result fri_checks.V5FriCheckSink fri_checks.V5FriCheckError))
    (iter iterNext :
      core.iter.adapters.enumerate.Enumerate
        (core.slice.iter.Iter Std.U32))
    (carried ordinal : Std.Usize) (index : Std.U32)
    (hnext :
      core.iter.adapters.enumerate.IteratorEnumerate.next
          (core.iter.traits.iterator.IteratorSliceIter Std.U32) iter =
        .ok (some (ordinal, index), iterNext)) :
    fri_checks.check_v5_fri_queries_loop0_loop0_loop0.body later
        laterIndices finalPolynomial coordinates alphaPowers layer pending
        iter carried ≠ .ok (.done (coordinatesOut, pendingOut, 1#u32)) := by
  intro hrun
  unfold fri_checks.check_v5_fri_queries_loop0_loop0_loop0.body at hrun
  rw [hnext] at hrun
  simp only [bind_tc_ok] at hrun
  repeat' first
    | split at hrun
    | simp_all [Bind.bind, Aeneas.Std.bind, Std.lift,
        V5FriConsumerExact.core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame, core.convert.FromSame.from]

/-- Peeling an active iteration from a later-layer loop which eventually
completes proves that the body continued with the exact next iterator. -/
theorem production_inner_completed_loop_head
    (later : Array Opening 3#usize)
    (laterIndices : Array (alloc.vec.Vec Std.U32) 3#usize)
    (finalPolynomial : Array aspis_core.field.QM31 4#usize)
    (coordinates coordinatesOut :
      aspis_core.circle_fri.DerivedCircleQueryFoldInverses)
    (alphaPowers : Array
      (Array aspis_core.field.PreparedQm31Multiplier 3#usize) 4#usize)
    (layer : Std.Usize)
    (pending pendingOut : Option
      (core.result.Result fri_checks.V5FriCheckSink fri_checks.V5FriCheckError))
    (iter iterNext :
      core.iter.adapters.enumerate.Enumerate
        (core.slice.iter.Iter Std.U32))
    (carried ordinal : Std.Usize) (index : Std.U32)
    (hnext :
      core.iter.adapters.enumerate.IteratorEnumerate.next
          (core.iter.traits.iterator.IteratorSliceIter Std.U32) iter =
        .ok (some (ordinal, index), iterNext))
    (hloop :
      fri_checks.check_v5_fri_queries_loop0_loop0_loop0 iter later
          laterIndices finalPolynomial coordinates alphaPowers layer carried
          pending = .ok (coordinatesOut, pendingOut, 1#u32)) :
    ∃ carriedNext,
      fri_checks.check_v5_fri_queries_loop0_loop0_loop0.body later
          laterIndices finalPolynomial coordinates alphaPowers layer pending
          iter carried = .ok (.cont (iterNext, carriedNext)) ∧
      fri_checks.check_v5_fri_queries_loop0_loop0_loop0 iterNext later
          laterIndices finalPolynomial coordinates alphaPowers layer
          carriedNext pending = .ok (coordinatesOut, pendingOut, 1#u32) := by
  unfold fri_checks.check_v5_fri_queries_loop0_loop0_loop0 at hloop
  rw [loop.eq_def] at hloop
  simp only at hloop
  generalize hbody :
      fri_checks.check_v5_fri_queries_loop0_loop0_loop0.body later
        laterIndices finalPolynomial coordinates alphaPowers layer pending iter
        carried = bodyResult at hloop
  cases bodyResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at hloop
  | div => simp [Bind.bind, Aeneas.Std.bind] at hloop
  | ok flow =>
    cases flow with
    | cont nextState =>
      rcases nextState with ⟨nextIter, carriedNext⟩
      simp only [bind_tc_ok] at hloop
      have hiter := production_later_cont_iter_exact later laterIndices
        finalPolynomial coordinates alphaPowers layer pending iter iterNext
        nextIter carried carriedNext ordinal index hnext hbody
      subst nextIter
      refine ⟨carriedNext, ?_, hloop⟩
      simpa using hbody
    | done output =>
      rcases output with ⟨coordinatesDone, pendingDone, flagDone⟩
      simp only [bind_tc_ok, Result.ok.injEq, Prod.mk.injEq] at hloop
      have hflag : flagDone = 1#u32 := hloop.2.2
      have hdone :
          fri_checks.check_v5_fri_queries_loop0_loop0_loop0.body later
            laterIndices finalPolynomial coordinates alphaPowers layer pending
            iter carried =
              .ok (.done (coordinatesDone, pendingDone, 1#u32)) := by
        simpa [hflag] using hbody
      exact (production_inner_active_body_ne_completed later laterIndices
        finalPolynomial coordinates coordinatesDone alphaPowers layer pending
        pendingDone iter iterNext carried ordinal index hnext hdone).elim

/-- Every active query in either non-terminal later-layer pass is actually
visited, and both its incoming opening and requested parent opening are read. -/
theorem production_later_completed_loop_reads_target
    (later : Array Opening 3#usize)
    (laterIndices : Array (alloc.vec.Vec Std.U32) 3#usize)
    (finalPolynomial : Array aspis_core.field.QM31 4#usize)
    (coordinates coordinatesOut :
      aspis_core.circle_fri.DerivedCircleQueryFoldInverses)
    (alphaPowers : Array
      (Array aspis_core.field.PreparedQm31Multiplier 3#usize) 4#usize)
    (layer : Std.Usize) (hlayer : layer < 2#usize)
    (pending pendingOut : Option
      (core.result.Result fri_checks.V5FriCheckSink fri_checks.V5FriCheckError))
    (values : Slice Std.U32) (current target : Std.Usize)
    (carried : Std.Usize)
    (horder : current.val ≤ target.val)
    (htarget : target.val < values.val.length)
    (hloop :
      fri_checks.check_v5_fri_queries_loop0_loop0_loop0
          (enumerateSliceAt values current) later laterIndices finalPolynomial
          coordinates alphaPowers layer carried pending =
        .ok (coordinatesOut, pendingOut, 1#u32)) :
    ∃ carriedAt : Std.Usize, ∃ nextPosition : Std.Usize,
      nextPosition.val = target.val + 1 ∧
      Nonempty (LaterBodyReadEvidence later laterIndices coordinates alphaPowers
        layer target carriedAt values[target.val]) := by
  have hcurrent : current.val < values.val.length := by omega
  obtain ⟨nextPosition, hnextValue, hnext⟩ :=
    enumerate_slice_at_next_run values current hcurrent
  obtain ⟨carriedNext, hbody, hloopNext⟩ :=
    production_inner_completed_loop_head later laterIndices finalPolynomial
      coordinates coordinatesOut alphaPowers layer pending pendingOut
      (enumerateSliceAt values current) (enumerateSliceAt values nextPosition)
      carried current values[current.val] hnext hloop
  have hevidence := production_later_body_cont_reads later laterIndices
    finalPolynomial coordinates alphaPowers layer hlayer pending
    (enumerateSliceAt values current) (enumerateSliceAt values nextPosition)
    (enumerateSliceAt values nextPosition) carried carriedNext current
    values[current.val] hnext hbody
  by_cases heq : current.val = target.val
  · have hscalar : current = target := UScalar.eq_of_val_eq heq
    subst target
    exact ⟨carried, nextPosition, hnextValue, hevidence⟩
  · apply production_later_completed_loop_reads_target later laterIndices
      finalPolynomial coordinates coordinatesOut alphaPowers layer hlayer
      pending pendingOut values nextPosition target carriedNext
    · rw [hnextValue]
      omega
    · exact hloopNext
termination_by target.val - current.val
decreasing_by
  rw [hnextValue]
  omega

/-- Every active query in the terminal later-layer pass is actually visited
and its incoming authenticated opening is read at the enumerated ordinal. -/
theorem production_terminal_completed_loop_reads_target
    (later : Array Opening 3#usize)
    (laterIndices : Array (alloc.vec.Vec Std.U32) 3#usize)
    (finalPolynomial : Array aspis_core.field.QM31 4#usize)
    (coordinates coordinatesOut :
      aspis_core.circle_fri.DerivedCircleQueryFoldInverses)
    (alphaPowers : Array
      (Array aspis_core.field.PreparedQm31Multiplier 3#usize) 4#usize)
    (layer : Std.Usize) (hlayer : ¬layer < 2#usize)
    (pending pendingOut : Option
      (core.result.Result fri_checks.V5FriCheckSink fri_checks.V5FriCheckError))
    (values : Slice Std.U32) (current target : Std.Usize)
    (carried : Std.Usize)
    (horder : current.val ≤ target.val)
    (htarget : target.val < values.val.length)
    (hloop :
      fri_checks.check_v5_fri_queries_loop0_loop0_loop0
          (enumerateSliceAt values current) later laterIndices finalPolynomial
          coordinates alphaPowers layer carried pending =
        .ok (coordinatesOut, pendingOut, 1#u32)) :
    ∃ nextPosition : Std.Usize,
      nextPosition.val = target.val + 1 ∧
      Nonempty (TerminalBodyReadEvidence later finalPolynomial coordinates
        alphaPowers layer target values[target.val]) := by
  have hcurrent : current.val < values.val.length := by omega
  obtain ⟨nextPosition, hnextValue, hnext⟩ :=
    enumerate_slice_at_next_run values current hcurrent
  obtain ⟨carriedNext, hbody, hloopNext⟩ :=
    production_inner_completed_loop_head later laterIndices finalPolynomial
      coordinates coordinatesOut alphaPowers layer pending pendingOut
      (enumerateSliceAt values current) (enumerateSliceAt values nextPosition)
      carried current values[current.val] hnext hloop
  have hevidence := production_terminal_body_cont_reads later laterIndices
    finalPolynomial coordinates alphaPowers layer hlayer pending
    (enumerateSliceAt values current) (enumerateSliceAt values nextPosition)
    (enumerateSliceAt values nextPosition) carried carriedNext current
    values[current.val] hnext hbody
  by_cases heq : current.val = target.val
  · have hscalar : current = target := UScalar.eq_of_val_eq heq
    subst target
    exact ⟨nextPosition, hnextValue, hevidence⟩
  · apply production_terminal_completed_loop_reads_target later laterIndices
      finalPolynomial coordinates coordinatesOut alphaPowers layer hlayer
      pending pendingOut values nextPosition target carriedNext
    · rw [hnextValue]
      omega
    · exact hloopNext
termination_by target.val - current.val
decreasing_by
  rw [hnextValue]
  omega

#print axioms production_monotone_loop_hits
#print axioms production_opening_value_for_monotone_index_hits
#print axioms production_layerZero_body_cont_reads
#print axioms production_later_body_cont_reads
#print axioms production_terminal_body_cont_reads
#print axioms production_layerZero_active_body_ne_accepting_done
#print axioms production_layerZero_accepted_loop_head
#print axioms production_layerZero_accepted_loop_reads_target
#print axioms production_later_cont_iter_exact
#print axioms production_inner_active_body_ne_completed
#print axioms production_inner_completed_loop_head
#print axioms production_later_completed_loop_reads_target
#print axioms production_terminal_completed_loop_reads_target

end AspisV5FriConsumerExactProof

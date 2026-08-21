import V5FriFoldSemantics

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 10000

/-!
# Exact semantics of the accepted production V5 FRI transition helpers

The lower-level arithmetic and fold files prove the values computed by the
unchanged field helpers.  This file performs the next source-shaped step: it
inverts successful executions of the extracted line and terminal comparison
helpers.  Decoder results remain explicit inputs here so that byte decoding
can be joined separately to the independently extracted decoder proof.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5FriTransitionSemantics

open AspisV5FriArithmeticSemantics
open AspisV5FriPreparedSumSemantics
open AspisV5FriFoldSemantics

namespace Fresh
open V5FriArithmeticExact

abbrev M31 := field.M31
abbrev QM31 := field.QM31
abbrev Prepared := field.PreparedQm31Multiplier
abbrev CircleQueryError := circle_query.CircleQueryError

end Fresh

@[simp] private theorem from_residual_ne_ok
    {T E F : Type} (convert : core.convert.From F E)
    (residual : core.result.Result core.convert.Infallible E) (value : T) :
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        T convert residual ≠ .ok (.Ok value) := by
  cases residual with
  | Ok impossible => exact core.convert.Infallible.rec _ impossible
  | Err error =>
    unfold
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
    cases hconvert : convert.from error <;> simp [hconvert]

private theorem bitand_three_lt_four (index : Std.Usize) :
    (index &&& 3#usize).val < 4 := by
  rw [UScalar.val_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)

private theorem qm31_generated_ne_false_iff (left right : Fresh.QM31) :
    core.cmp.PartialEq.ne.trait_default
        V5FriArithmeticExact.field.QM31.Insts.CoreCmpPartialEqQM31
        left right = .ok false ↔ left = right := by
  rcases left with ⟨⟨left0, left1⟩, ⟨left2, left3⟩⟩
  rcases right with ⟨⟨right0, right1⟩, ⟨right2, right3⟩⟩
  by_cases h0 : left0 = right0 <;>
    by_cases h1 : left1 = right1 <;>
    by_cases h2 : left2 = right2 <;>
    by_cases h3 : left3 = right3 <;>
  simp [core.cmp.PartialEq.ne.trait_default,
    core.cmp.PartialEq.ne.default,
    V5FriArithmeticExact.field.QM31.Insts.CoreCmpPartialEqQM31.eq,
    V5FriArithmeticExact.field.CM31.Insts.CoreCmpPartialEqCM31.eq,
    V5FriArithmeticExact.field.M31.Insts.CoreCmpPartialEqM31.eq,
    h0, h1, h2, h3]

/-- Exact value semantics required from the two byte readers called by the
line-transition helpers.  This is intentionally decoder-only: the functions
on the left are the extracted production readers and the function on the
right is the independently proved little-endian byte interpretation. -/
structure LaterLeafDecoderSemantics
    (decoded : Slice Std.U8 → Fin 4 → ExactQM31) : Prop where
  full : ∀ leaf layer values,
    V5FriArithmeticExact.circle_query.decode_later_leaf leaf layer =
        .ok (.Ok values) →
      CanonicalQM31Array4 values ∧
      ∀ slot : Fin 4, qm31View values.val[slot.val]! = decoded leaf slot
  selected : ∀ leaf layer slot value,
    V5FriArithmeticExact.circle_query.decode_selected_later_slot
        leaf layer (Std.Usize.ofNatCore slot.val (by scalar_tac)) =
          .ok (.Ok value) →
      canonicalQM31 value ∧ qm31View value = decoded leaf slot

/-- A successful call to the extracted circle helper returns the maintained
circle fold, after the already-proved primitive arithmetic semantics. -/
theorem accepted_circle_transition_corresponds
    (values : Array Fresh.QM31 4#usize)
    (alphaPowers : Array Fresh.Prepared 3#usize)
    (inv2x inv2y : Fresh.M31)
    (output : Fresh.QM31)
    (alpha : ExactQM31)
    (hValues : CanonicalQM31Array4 values)
    (hInv2x : canonicalM31 inv2x)
    (hInv2y : canonicalM31 inv2y)
    (hAlphaPowers : PreparedArrayRepresents alphaPowers
      (fun i => alpha ^ (i + 1)))
    (hAccepted :
      V5FriArithmeticExact.circle_fri.normalized_circle_to_line_arity4_prepared_polynomial_refs
          values alphaPowers inv2x inv2y = .ok output) :
    qm31View output =
      AspisV5ComponentCConcreteFoldLinearity.circleFoldValue alpha
        (m31View inv2x) (m31View inv2y)
        (fun i => qm31View values.val[i.val]!) := by
  rcases normalized_circle_to_line_corresponds values alphaPowers inv2x
      inv2y alpha hValues hInv2x hInv2y hAlphaPowers with
    ⟨expected, hRun, _hCanonical, hExact⟩
  rw [hAccepted] at hRun
  injection hRun with hOutput
  simpa [hOutput] using hExact

/-- A successful extracted non-terminal transition compares the exact line
fold with the exact selected word decoded from the parent leaf.  No arithmetic
result is supplied as a premise. -/
theorem accepted_line_transition_corresponds
    (incomingLeaf outgoingLeaf : Slice Std.U8)
    (incomingLeafIndex : Std.Usize) (layer : Std.U8)
    (inverses : Array Fresh.M31 3#usize)
    (alphaPowers : Array Fresh.Prepared 3#usize)
    (incomingValues : Array Fresh.QM31 4#usize)
    (outgoingValue : Fresh.QM31)
    (alpha : ExactQM31)
    (hIncomingDecode :
      V5FriArithmeticExact.circle_query.decode_later_leaf incomingLeaf layer =
        .ok (.Ok incomingValues))
    (hOutgoingDecode :
      V5FriArithmeticExact.circle_query.decode_selected_later_slot
          outgoingLeaf (Std.U8.wrapping_add layer 1#u8)
          (incomingLeafIndex &&& 3#usize) = .ok (.Ok outgoingValue))
    (hIncomingCanonical : CanonicalQM31Array4 incomingValues)
    (hOutgoingCanonical : canonicalQM31 outgoingValue)
    (hInverses : CanonicalM31Array3 inverses)
    (hAlphaPowers : PreparedArrayRepresents alphaPowers
      (fun i => alpha ^ (i + 1)))
    (hAccepted :
      V5FriArithmeticExact.circle_query.check_fixed_line_transition_prepared_polynomial_powers
          incomingLeaf outgoingLeaf incomingLeafIndex layer inverses
          alphaPowers = .ok (.Ok ())) :
    AspisV5ComponentCConcreteFoldLinearity.lineFoldValue alpha
        (m31View inverses.val[0]!) (m31View inverses.val[1]!)
        (m31View inverses.val[2]!)
        (fun i => qm31View incomingValues.val[i.val]!) =
      qm31View outgoingValue := by
  rcases normalized_line_corresponds incomingValues alphaPowers inverses
      alpha hIncomingCanonical hInverses hAlphaPowers with
    ⟨folded, hFold, hFoldCanonical, hFoldExact⟩
  unfold
    V5FriArithmeticExact.circle_query.check_fixed_line_transition_prepared_polynomial_powers
    at hAccepted
  rw [hIncomingDecode] at hAccepted
  simp only [bind_tc_ok,
    core.result.Result.Insts.CoreOpsTry.branch, Std.lift] at hAccepted
  rw [hOutgoingDecode] at hAccepted
  simp only [bind_tc_ok,
    core.result.Result.Insts.CoreOpsTry.branch, Std.lift] at hAccepted
  rw [hFold] at hAccepted
  simp only [bind_tc_ok] at hAccepted
  generalize hNe :
      core.cmp.PartialEq.ne.trait_default
        V5FriArithmeticExact.field.QM31.Insts.CoreCmpPartialEqQM31
        outgoingValue folded = neResult at hAccepted
  cases neResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at hAccepted
  | div => simp [Bind.bind, Aeneas.Std.bind] at hAccepted
  | ok differs =>
    cases differs
    · have hRaw : folded = outgoingValue :=
        (qm31_generated_ne_false_iff outgoingValue folded).mp hNe |>.symm
      rw [← hFoldExact, hRaw]
    · simp at hAccepted

/-- The same non-terminal theorem stated only in terms of accepted production
bytes.  Successful execution itself supplies the two decoder results; the
decoder interface turns them into the exact values authenticated by those
bytes. -/
theorem accepted_line_transition_on_decoded_bytes
    (decoded : Slice Std.U8 → Fin 4 → ExactQM31)
    (hDecoder : LaterLeafDecoderSemantics decoded)
    (incomingLeaf outgoingLeaf : Slice Std.U8)
    (incomingLeafIndex : Std.Usize) (layer : Std.U8)
    (inverses : Array Fresh.M31 3#usize)
    (alphaPowers : Array Fresh.Prepared 3#usize)
    (alpha : ExactQM31)
    (hInverses : CanonicalM31Array3 inverses)
    (hAlphaPowers : PreparedArrayRepresents alphaPowers
      (fun i => alpha ^ (i + 1)))
    (hAccepted :
      V5FriArithmeticExact.circle_query.check_fixed_line_transition_prepared_polynomial_powers
          incomingLeaf outgoingLeaf incomingLeafIndex layer inverses
          alphaPowers = .ok (.Ok ())) :
    AspisV5ComponentCConcreteFoldLinearity.lineFoldValue alpha
        (m31View inverses.val[0]!) (m31View inverses.val[1]!)
        (m31View inverses.val[2]!) (decoded incomingLeaf) =
      decoded outgoingLeaf
        ⟨(incomingLeafIndex &&& 3#usize).val,
          bitand_three_lt_four incomingLeafIndex⟩ := by
  have hAcceptedSource := hAccepted
  unfold
    V5FriArithmeticExact.circle_query.check_fixed_line_transition_prepared_polynomial_powers
    at hAccepted
  generalize hIncomingDecode :
      V5FriArithmeticExact.circle_query.decode_later_leaf incomingLeaf layer =
        incomingResult at hAccepted
  cases incomingResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at hAccepted
  | div => simp [Bind.bind, Aeneas.Std.bind] at hAccepted
  | ok incomingResult =>
    cases incomingResult with
    | Err error =>
      simp [Bind.bind, Aeneas.Std.bind,
        core.result.Result.Insts.CoreOpsTry.branch,
        from_residual_ne_ok] at hAccepted
    | Ok incomingValues =>
      simp only [bind_tc_ok,
        core.result.Result.Insts.CoreOpsTry.branch, Std.lift] at hAccepted
      generalize hOutgoingDecode :
          V5FriArithmeticExact.circle_query.decode_selected_later_slot
              outgoingLeaf (Std.U8.wrapping_add layer 1#u8)
              (incomingLeafIndex &&& 3#usize) = outgoingResult at hAccepted
      cases outgoingResult with
      | fail error => simp [Bind.bind, Aeneas.Std.bind] at hAccepted
      | div => simp [Bind.bind, Aeneas.Std.bind] at hAccepted
      | ok outgoingResult =>
        cases outgoingResult with
        | Err error =>
          simp [Bind.bind, Aeneas.Std.bind,
            core.result.Result.Insts.CoreOpsTry.branch,
            from_residual_ne_ok] at hAccepted
        | Ok outgoingValue =>
          simp only [bind_tc_ok,
            core.result.Result.Insts.CoreOpsTry.branch, Std.lift] at hAccepted
          let selectedSlot : Fin 4 :=
            ⟨(incomingLeafIndex &&& 3#usize).val,
              bitand_three_lt_four incomingLeafIndex⟩
          have hSelectedUsize :
              Std.Usize.ofNatCore selectedSlot.val (by scalar_tac) =
                (incomingLeafIndex &&& 3#usize) := by
            apply UScalar.eq_of_val_eq
            rfl
          obtain ⟨hIncomingCanonical, hIncomingExact⟩ :=
            hDecoder.full incomingLeaf layer incomingValues hIncomingDecode
          obtain ⟨hOutgoingCanonical, hOutgoingExact⟩ :=
            hDecoder.selected outgoingLeaf (Std.U8.wrapping_add layer 1#u8)
              selectedSlot outgoingValue (by
                rw [hSelectedUsize]
                exact hOutgoingDecode)
          have hFold := accepted_line_transition_corresponds incomingLeaf
            outgoingLeaf incomingLeafIndex layer inverses alphaPowers
            incomingValues outgoingValue alpha hIncomingDecode hOutgoingDecode
            hIncomingCanonical hOutgoingCanonical hInverses hAlphaPowers
            hAcceptedSource
          have hIncomingFunction :
              (fun i : Fin 4 => qm31View incomingValues.val[i.val]!) =
                decoded incomingLeaf := funext hIncomingExact
          rw [hIncomingFunction] at hFold
          change _ = decoded outgoingLeaf selectedSlot
          exact hFold.trans hOutgoingExact

/-- A successful extracted terminal transition compares the exact last line
fold with the exact natural-line tensor evaluation. -/
theorem accepted_terminal_transition_corresponds
    (incomingLeaf : Slice Std.U8)
    (finalPolynomial : Array Fresh.QM31 4#usize)
    (finalIndex : Std.Usize)
    (inverses : Array Fresh.M31 3#usize)
    (finalX : Fresh.M31)
    (alphaPowers : Array Fresh.Prepared 3#usize)
    (incomingValues : Array Fresh.QM31 4#usize)
    (alpha : ExactQM31)
    (hIncomingDecode :
      V5FriArithmeticExact.circle_query.decode_later_leaf incomingLeaf 3#u8 =
        .ok (.Ok incomingValues))
    (hIncomingCanonical : CanonicalQM31Array4 incomingValues)
    (hFinalCanonical : CanonicalQM31Array4 finalPolynomial)
    (hInverses : CanonicalM31Array3 inverses)
    (hFinalX : canonicalM31 finalX)
    (hAlphaPowers : PreparedArrayRepresents alphaPowers
      (fun i => alpha ^ (i + 1)))
    (hAccepted :
      V5FriArithmeticExact.circle_query.check_fixed_terminal_transition_prepared_polynomial_refs
          incomingLeaf finalPolynomial finalIndex inverses finalX alphaPowers =
        .ok (.Ok ())) :
    AspisV5ComponentCConcreteFoldLinearity.lineFoldValue alpha
        (m31View inverses.val[0]!) (m31View inverses.val[1]!)
        (m31View inverses.val[2]!)
        (fun i => qm31View incomingValues.val[i.val]!) =
      AspisV5ComponentCConcreteFoldLinearity.finalTensorValue
        (m31View finalX) (fun i => qm31View finalPolynomial.val[i.val]!) := by
  rcases normalized_line_corresponds incomingValues alphaPowers inverses
      alpha hIncomingCanonical hInverses hAlphaPowers with
    ⟨terminal, hFold, hTerminalCanonical, hTerminalExact⟩
  rcases evaluate_final_line_tensor_corresponds finalPolynomial finalX
      hFinalCanonical hFinalX with
    ⟨expected, hExpected, hExpectedCanonical, hExpectedExact⟩
  unfold
    V5FriArithmeticExact.circle_query.check_fixed_terminal_transition_prepared_polynomial_refs
    at hAccepted
  rw [hIncomingDecode] at hAccepted
  simp only [bind_tc_ok,
    core.result.Result.Insts.CoreOpsTry.branch, Std.lift] at hAccepted
  rw [hFold, hExpected] at hAccepted
  simp only [bind_tc_ok] at hAccepted
  generalize hNe :
      core.cmp.PartialEq.ne.trait_default
        V5FriArithmeticExact.field.QM31.Insts.CoreCmpPartialEqQM31
        expected terminal = neResult at hAccepted
  cases neResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at hAccepted
  | div => simp [Bind.bind, Aeneas.Std.bind] at hAccepted
  | ok differs =>
    cases differs
    · have hRaw : expected = terminal :=
        (qm31_generated_ne_false_iff expected terminal).mp hNe
      rw [← hTerminalExact, ← hExpectedExact, hRaw]
    · simp at hAccepted

/-- Terminal acceptance stated directly on the authenticated input bytes and
the four published final coefficients. -/
theorem accepted_terminal_transition_on_decoded_bytes
    (decoded : Slice Std.U8 → Fin 4 → ExactQM31)
    (hDecoder : LaterLeafDecoderSemantics decoded)
    (incomingLeaf : Slice Std.U8)
    (finalPolynomial : Array Fresh.QM31 4#usize)
    (finalIndex : Std.Usize)
    (inverses : Array Fresh.M31 3#usize)
    (finalX : Fresh.M31)
    (alphaPowers : Array Fresh.Prepared 3#usize)
    (alpha : ExactQM31)
    (hFinalCanonical : CanonicalQM31Array4 finalPolynomial)
    (hInverses : CanonicalM31Array3 inverses)
    (hFinalX : canonicalM31 finalX)
    (hAlphaPowers : PreparedArrayRepresents alphaPowers
      (fun i => alpha ^ (i + 1)))
    (hAccepted :
      V5FriArithmeticExact.circle_query.check_fixed_terminal_transition_prepared_polynomial_refs
          incomingLeaf finalPolynomial finalIndex inverses finalX alphaPowers =
        .ok (.Ok ())) :
    AspisV5ComponentCConcreteFoldLinearity.lineFoldValue alpha
        (m31View inverses.val[0]!) (m31View inverses.val[1]!)
        (m31View inverses.val[2]!) (decoded incomingLeaf) =
      AspisV5ComponentCConcreteFoldLinearity.finalTensorValue
        (m31View finalX) (fun i => qm31View finalPolynomial.val[i.val]!) := by
  have hAcceptedSource := hAccepted
  unfold
    V5FriArithmeticExact.circle_query.check_fixed_terminal_transition_prepared_polynomial_refs
    at hAccepted
  generalize hIncomingDecode :
      V5FriArithmeticExact.circle_query.decode_later_leaf incomingLeaf 3#u8 =
        incomingResult at hAccepted
  cases incomingResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at hAccepted
  | div => simp [Bind.bind, Aeneas.Std.bind] at hAccepted
  | ok incomingResult =>
    cases incomingResult with
    | Err error =>
      simp [Bind.bind, Aeneas.Std.bind,
        core.result.Result.Insts.CoreOpsTry.branch,
        from_residual_ne_ok] at hAccepted
    | Ok incomingValues =>
      obtain ⟨hIncomingCanonical, hIncomingExact⟩ :=
        hDecoder.full incomingLeaf 3#u8 incomingValues hIncomingDecode
      have hTransition := accepted_terminal_transition_corresponds
        incomingLeaf finalPolynomial finalIndex inverses finalX alphaPowers
        incomingValues alpha hIncomingDecode hIncomingCanonical
        hFinalCanonical hInverses hFinalX hAlphaPowers hAcceptedSource
      have hIncomingFunction :
          (fun i : Fin 4 => qm31View incomingValues.val[i.val]!) =
            decoded incomingLeaf := funext hIncomingExact
      simpa only [hIncomingFunction] using hTransition

#print axioms accepted_line_transition_corresponds
#print axioms accepted_line_transition_on_decoded_bytes
#print axioms accepted_terminal_transition_corresponds
#print axioms accepted_terminal_transition_on_decoded_bytes

end AspisV5FriTransitionSemantics

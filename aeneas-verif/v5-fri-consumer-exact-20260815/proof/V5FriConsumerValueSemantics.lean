import V5FriConsumerEndToEndProof
import V5FriTransitionSemantics

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 10000

/-!
# Value semantics of the accepted production V5 FRI consumer

The accepted-execution proof records the exact helper call made at every
query.  This file connects those calls to the separately extracted field and
fold semantics.  The only cross-extraction input is equality of the literal
Rust helper calls after structural conversion of the duplicated generated
types; no fold equation or `ForestFriChecks` conclusion is assumed.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5FriConsumerValueSemantics

open AspisV5FriConsumerExactProof
open AspisV5FriArithmeticSemantics
open AspisV5FriPreparedSumSemantics
open AspisV5FriFoldSemantics
open AspisV5FriTransitionSemantics

namespace Consumer
open V5FriConsumerExact

abbrev M31 := aspis_core.field.M31
abbrev CM31 := aspis_core.field.CM31
abbrev QM31 := aspis_core.field.QM31
abbrev Prepared := aspis_core.field.PreparedQm31Multiplier

end Consumer

namespace Exact
open V5FriArithmeticExact

abbrev M31 := field.M31
abbrev CM31 := field.CM31
abbrev QM31 := field.QM31
abbrev Prepared := field.PreparedQm31Multiplier

end Exact

instance : Inhabited Consumer.CM31 :=
  ⟨{ a := 0#u32, b := 0#u32 }⟩

instance : Inhabited Consumer.QM31 :=
  ⟨{ c0 := default, c1 := default }⟩

def toExactCM31 (value : Consumer.CM31) : Exact.CM31 :=
  { a := value.a, b := value.b }

def toExactQM31 (value : Consumer.QM31) : Exact.QM31 :=
  { c0 := toExactCM31 value.c0, c1 := toExactCM31 value.c1 }

def mapArray {A B : Type} {N : Std.Usize} (f : A → B)
    (values : Array A N) : Array B N :=
  ⟨values.val.map f, by simpa using values.property⟩

@[simp] theorem mapArray_entry4 {A B : Type}
    [Inhabited A] [Inhabited B]
    (f : A → B) (values : Array A 4#usize) (index : Fin 4) :
    (mapArray f values).val[index.val]! = f values.val[index.val]! := by
  simp [mapArray, index.isLt]

@[simp] theorem qm31View_toExactQM31 (value : Consumer.QM31) :
    qm31View (toExactQM31 value) =
      ⟨⟨(value.c0.a.val : ExactM31), (value.c0.b.val : ExactM31)⟩,
        ⟨(value.c1.a.val : ExactM31), (value.c1.b.val : ExactM31)⟩⟩ := rfl

/-- Exact cross-extraction edge for the three Rust calls left opaque by the
consumer extraction.  Each field states equality of a concrete call after
structural conversion; it does not state any mathematical fold result. -/
structure ExactFriHelperCallEquality : Type where
  prepared : Consumer.Prepared → Exact.Prepared
  square : ∀ input output,
    canonicalQM31 (toExactQM31 input) →
      V5FriConsumerExact.aspis_core.field.QM31.square input = .ok output →
      canonicalQM31 (toExactQM31 output) ∧
        qm31View (toExactQM31 output) = qm31View (toExactQM31 input) ^ 2
  mul : ∀ left right output,
    canonicalQM31 (toExactQM31 left) →
      canonicalQM31 (toExactQM31 right) →
      V5FriConsumerExact.aspis_core.field.QM31.mul left right = .ok output →
      canonicalQM31 (toExactQM31 output) ∧
        qm31View (toExactQM31 output) =
          qm31View (toExactQM31 left) * qm31View (toExactQM31 right)
  preparedNew : ∀ input output,
    canonicalQM31 (toExactQM31 input) →
      V5FriConsumerExact.aspis_core.field.PreparedQm31Multiplier.new input =
        .ok output →
      PreparedRepresents (prepared output) (qm31View (toExactQM31 input))
  circle : ∀ values alphaPowers inv2x inv2y output,
    V5FriConsumerExact.aspis_core.circle_fri.normalized_circle_to_line_arity4_prepared_polynomial_refs
        values alphaPowers inv2x inv2y = .ok output →
      V5FriArithmeticExact.circle_fri.normalized_circle_to_line_arity4_prepared_polynomial_refs
          (mapArray toExactQM31 values) (mapArray prepared alphaPowers)
          inv2x inv2y = .ok (toExactQM31 output)
  line : ∀ incoming outgoing index layer inverses alphaPowers,
    V5FriConsumerExact.aspis_core.circle_query.check_fixed_line_transition_prepared_polynomial_powers
        incoming outgoing index layer inverses alphaPowers = .ok (.Ok ()) →
      V5FriArithmeticExact.circle_query.check_fixed_line_transition_prepared_polynomial_powers
          incoming outgoing index layer inverses
          (mapArray prepared alphaPowers) = .ok (.Ok ())
  terminal : ∀ incoming finalPolynomial index inverses finalX alphaPowers,
    V5FriConsumerExact.aspis_core.circle_query.check_fixed_terminal_transition_prepared_polynomial_refs
        incoming finalPolynomial index inverses finalX alphaPowers =
          .ok (.Ok ()) →
      V5FriArithmeticExact.circle_query.check_fixed_terminal_transition_prepared_polynomial_refs
          incoming (mapArray toExactQM31 finalPolynomial) index inverses finalX
          (mapArray prepared alphaPowers) = .ok (.Ok ())

/-- The literal closure used by `check_v5_fri_queries` prepares exactly the
first three positive powers of one source challenge. This consumes only
call-level field/preparation correspondences; it does not assume the prepared
array postcondition. -/
theorem source_preparation_closure_yields_exact_powers
    (hCalls : ExactFriHelperCallEquality)
    (input : Consumer.QM31)
    (output : Array Consumer.Prepared 3#usize)
    (hCanonical : canonicalQM31 (toExactQM31 input))
    (hCall :
      V5FriConsumerExact.fri_checks.check_v5_fri_queries.closure.Insts.CoreOpsFunctionFnMutTupleQM31ArrayPreparedQm31Multiplier3.call_mut
          () input = .ok (output, ())) :
    PreparedArrayRepresents (mapArray hCalls.prepared output)
      (fun index => qm31View (toExactQM31 input) ^ (index + 1)) := by
  unfold
    V5FriConsumerExact.fri_checks.check_v5_fri_queries.closure.Insts.CoreOpsFunctionFnMutTupleQM31ArrayPreparedQm31Multiplier3.call_mut at hCall
  generalize hSquareCall :
      V5FriConsumerExact.aspis_core.field.QM31.square input = squareResult
      at hCall
  cases squareResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at hCall
  | div => simp [Bind.bind, Aeneas.Std.bind] at hCall
  | ok squared =>
    generalize hPrepared1Call :
        V5FriConsumerExact.aspis_core.field.PreparedQm31Multiplier.new input =
          prepared1Result at hCall
    cases prepared1Result with
    | fail error =>
      simp only [bind_tc_ok, bind_tc_fail] at hCall
      cases hCall
    | div =>
      simp only [bind_tc_ok, bind_tc_div] at hCall
      cases hCall
    | ok prepared1 =>
      simp only [bind_tc_ok] at hCall
      generalize hPrepared2Call :
          V5FriConsumerExact.aspis_core.field.PreparedQm31Multiplier.new
              squared = prepared2Result at hCall
      cases prepared2Result with
      | fail error =>
        simp only [bind_tc_fail] at hCall
        cases hCall
      | div =>
        simp only [bind_tc_div] at hCall
        cases hCall
      | ok prepared2 =>
        simp only [bind_tc_ok] at hCall
        generalize hCubeCall :
            V5FriConsumerExact.aspis_core.field.QM31.mul squared input =
              cubeResult at hCall
        cases cubeResult with
        | fail error =>
          simp only [bind_tc_fail] at hCall
          cases hCall
        | div =>
          simp only [bind_tc_div] at hCall
          cases hCall
        | ok cubed =>
          simp only [bind_tc_ok] at hCall
          generalize hPrepared3Call :
              V5FriConsumerExact.aspis_core.field.PreparedQm31Multiplier.new
                  cubed = prepared3Result at hCall
          cases prepared3Result with
          | fail error =>
            simp only [bind_tc_fail] at hCall
            cases hCall
          | div =>
            simp only [bind_tc_div] at hCall
            cases hCall
          | ok prepared3 =>
            simp only [bind_tc_ok] at hCall
            have hSquared := hCalls.square input squared hCanonical hSquareCall
            have hCubed := hCalls.mul squared input cubed hSquared.1
              hCanonical hCubeCall
            have hPrepared1 := hCalls.preparedNew input prepared1 hCanonical
              hPrepared1Call
            have hPrepared2 := hCalls.preparedNew squared prepared2 hSquared.1
              hPrepared2Call
            have hPrepared3 := hCalls.preparedNew cubed prepared3 hCubed.1
              hPrepared3Call
            have hOutput : output.val = [prepared1, prepared2, prepared3] := by
              have hPair := Result.ok.inj hCall
              have hArray := congrArg Prod.fst hPair
              exact (congrArg (fun array => array.val) hArray).symm
            intro index hIndex
            have hCases : index = 0 ∨ index = 1 ∨ index = 2 := by omega
            rcases hCases with rfl | rfl | rfl
            · simpa [mapArray, hOutput] using hPrepared1
            · simpa [mapArray, hOutput, hSquared.2] using hPrepared2
            · simpa [mapArray, hOutput, hCubed.2, hSquared.2, pow_succ]
                using hPrepared3

/-- The actual four-element `array::map` call made by the production verifier
prepares the first three powers of every challenge. -/
theorem source_alpha_map_yields_exact_powers
    (hCalls : ExactFriHelperCallEquality)
    (alphas : Array Consumer.QM31 4#usize)
    (alphaPowers : Array (Array Consumer.Prepared 3#usize) 4#usize)
    (hCanonical : ∀ (layer : Nat) (hLayer : layer < 4),
      canonicalQM31 (toExactQM31
        (alphas.val.get ⟨layer, by simpa using hLayer⟩)))
    (hMap :
      V5FriConsumerExact.core.array.Array.map
          V5FriConsumerExact.fri_checks.check_v5_fri_queries.closure.Insts.CoreOpsFunctionFnMutTupleQM31ArrayPreparedQm31Multiplier3
          alphas () = .ok alphaPowers) :
    ∀ (layer : Nat) (hLayer : layer < 4),
      PreparedArrayRepresents
        (mapArray hCalls.prepared
          (alphaPowers.val.get ⟨layer, by simpa using hLayer⟩))
        (fun index =>
          qm31View (toExactQM31
            (alphas.val.get ⟨layer, by simpa using hLayer⟩)) ^
              (index + 1)) := by
  let relation : Consumer.QM31 → Array Consumer.Prepared 3#usize → Prop :=
    fun input output =>
      canonicalQM31 (toExactQM31 input) →
      PreparedArrayRepresents (mapArray hCalls.prepared output)
        (fun index => qm31View (toExactQM31 input) ^ (index + 1))
  have hForall : List.Forall₂ relation alphas.val alphaPowers.val :=
    V5FriConsumerExact.core.array.Array.map_forall₂
      V5FriConsumerExact.fri_checks.check_v5_fri_queries.closure.Insts.CoreOpsFunctionFnMutTupleQM31ArrayPreparedQm31Multiplier3
      relation alphas () alphaPowers hMap (by
        intro state input output stateNext hCall
        cases state
        cases stateNext
        intro hInputCanonical
        exact source_preparation_closure_yields_exact_powers
          hCalls input output hInputCanonical hCall)
  intro layer hLayer
  have hLayerAlpha : layer < alphas.val.length := by simpa using hLayer
  have hLayerPowers : layer < alphaPowers.val.length := by simpa using hLayer
  have hEntry := hForall.get hLayerAlpha hLayerPowers
  apply hEntry
  exact hCanonical layer hLayer

private theorem consumer_qm31_ne_false_iff
    (left right : Consumer.QM31) :
    core.cmp.PartialEq.ne.trait_default
        V5FriConsumerExact.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
        left right = .ok false ↔ left = right := by
  rcases left with ⟨⟨left0, left1⟩, ⟨left2, left3⟩⟩
  rcases right with ⟨⟨right0, right1⟩, ⟨right2, right3⟩⟩
  by_cases h0 : left0 = right0 <;>
    by_cases h1 : left1 = right1 <;>
    by_cases h2 : left2 = right2 <;>
    by_cases h3 : left3 = right3 <;>
  simp [core.cmp.PartialEq.ne.trait_default,
    core.cmp.PartialEq.ne.default,
    V5FriConsumerExact.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq,
    h0, h1, h2, h3]

/-- One accepted first-pass witness performs the maintained circle fold on
the exact four values returned by gamma combination and compares it with the
exact QM31 decoded from the selected authenticated parent slot. -/
theorem layer_zero_read_yields_circle_equation
    {openings c1Count c1Width c1Offsets c2Count c2Width c2Offsets later
      laterIndices claims powers weights multipliers coordinates alphaPowers
      iterNext iterOut ordinal carried query}
    (read : LayerZeroBodyReadEvidence openings c1Count c1Width c1Offsets
      c2Count c2Width c2Offsets later laterIndices claims powers weights
      multipliers coordinates alphaPowers iterNext iterOut ordinal carried
      query)
    (hCalls : ExactFriHelperCallEquality)
    (alpha : ExactQM31)
    (hValues : CanonicalQM31Array4 (mapArray toExactQM31 read.combined))
    (hInv2x : canonicalM31 read.inv2x)
    (hInv2y : canonicalM31 read.inv2y)
    (hAlphaPowers : PreparedArrayRepresents
      (mapArray hCalls.prepared read.alpha) (fun i => alpha ^ (i + 1))) :
    AspisV5ComponentCConcreteFoldLinearity.circleFoldValue alpha
        (m31View read.inv2x) (m31View read.inv2y)
        (fun i => qm31View (toExactQM31 read.combined.val[i.val]!)) =
      qm31View (toExactQM31 read.decodedParent) := by
  have hExactCall := hCalls.circle read.combined read.alpha read.inv2x
    read.inv2y read.foldedValue read.foldCall
  have hFold := accepted_circle_transition_corresponds
    (mapArray toExactQM31 read.combined)
    (mapArray hCalls.prepared read.alpha) read.inv2x read.inv2y
    (toExactQM31 read.foldedValue) alpha hValues hInv2x hInv2y
    hAlphaPowers hExactCall
  have hRaw : read.foldedValue = read.decodedParent :=
    (consumer_qm31_ne_false_iff read.foldedValue read.decodedParent).mp
      read.acceptedEqualityCall
  rw [hRaw] at hFold
  simpa only [mapArray_entry4] using hFold.symm

/-- One accepted middle-pass witness performs the maintained line fold on
the exact little-endian values decoded from its incoming and parent leaves. -/
theorem later_read_yields_line_equation
    {later laterIndices coordinates alphaPowers layer ordinal carried index}
    (read : LaterBodyReadEvidence later laterIndices coordinates alphaPowers
      layer ordinal carried index)
    (hCalls : ExactFriHelperCallEquality)
    (decoded : Slice Std.U8 → Fin 4 → ExactQM31)
    (hDecoder : LaterLeafDecoderSemantics decoded)
    (alpha : ExactQM31)
    (hInverses : CanonicalM31Array3 read.coordinate)
    (hAlphaPowers : PreparedArrayRepresents
      (mapArray hCalls.prepared read.alpha) (fun i => alpha ^ (i + 1))) :
    AspisV5ComponentCConcreteFoldLinearity.lineFoldValue alpha
        (m31View read.coordinate.val[0]!) (m31View read.coordinate.val[1]!)
        (m31View read.coordinate.val[2]!) (decoded read.incomingValue) =
      decoded read.parentValue
        ⟨((UScalar.cast .Usize index) &&& 3#usize).val, by
          rw [UScalar.val_and]
          exact Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)⟩ := by
  have hExactCall := hCalls.line read.incomingValue read.parentValue
    (UScalar.cast .Usize index)
    (Std.U8.wrapping_add (UScalar.cast .U8 layer) 1#u8) read.coordinate
    read.alpha read.transitionCall
  exact accepted_line_transition_on_decoded_bytes decoded hDecoder
    read.incomingValue read.parentValue (UScalar.cast .Usize index)
    (Std.U8.wrapping_add (UScalar.cast .U8 layer) 1#u8) read.coordinate
    (mapArray hCalls.prepared read.alpha) alpha hInverses hAlphaPowers
    hExactCall

/-- One accepted terminal-pass witness performs the last line fold and
compares it with the maintained natural-line polynomial evaluation. -/
theorem terminal_read_yields_final_equation
    {later finalPolynomial coordinates alphaPowers layer ordinal index}
    (read : TerminalBodyReadEvidence later finalPolynomial coordinates
      alphaPowers layer ordinal index)
    (hCalls : ExactFriHelperCallEquality)
    (decoded : Slice Std.U8 → Fin 4 → ExactQM31)
    (hDecoder : LaterLeafDecoderSemantics decoded)
    (alpha : ExactQM31)
    (hFinalCanonical : CanonicalQM31Array4
      (mapArray toExactQM31 finalPolynomial))
    (hInverses : CanonicalM31Array3 read.coordinate)
    (hFinalX : canonicalM31 read.finalX)
    (hAlphaPowers : PreparedArrayRepresents
      (mapArray hCalls.prepared read.alpha) (fun i => alpha ^ (i + 1))) :
    AspisV5ComponentCConcreteFoldLinearity.lineFoldValue alpha
        (m31View read.coordinate.val[0]!) (m31View read.coordinate.val[1]!)
        (m31View read.coordinate.val[2]!) (decoded read.incomingValue) =
      AspisV5ComponentCConcreteFoldLinearity.finalTensorValue
        (m31View read.finalX)
        (fun i => qm31View (toExactQM31 finalPolynomial.val[i.val]!)) := by
  have hExactCall := hCalls.terminal read.incomingValue finalPolynomial
    (UScalar.cast .Usize index) read.coordinate read.finalX read.alpha
    read.transitionCall
  simpa only [mapArray_entry4] using
    accepted_terminal_transition_on_decoded_bytes decoded hDecoder
      read.incomingValue (mapArray toExactQM31 finalPolynomial)
      (UScalar.cast .Usize index) read.coordinate read.finalX
      (mapArray hCalls.prepared read.alpha) alpha hFinalCanonical hInverses
      hFinalX hAlphaPowers hExactCall

#print axioms layer_zero_read_yields_circle_equation
#print axioms later_read_yields_line_equation
#print axioms terminal_read_yields_final_equation

end AspisV5FriConsumerValueSemantics

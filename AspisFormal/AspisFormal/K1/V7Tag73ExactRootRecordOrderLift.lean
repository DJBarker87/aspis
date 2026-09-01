import AspisFormal.K1.V7Tag73ExactFinalWorkPairControllerCompletion

/-!
# Lift strict root-query order to actor-tagged records

The exact source chronology is often stated for `(SHA input, answer)` pairs,
while controller replay consumes actor-tagged `UnifiedExposureRecord`s.  The
root projection is length- and order-preserving.  This module supplies the
generic list-map split and the exact two-coordinate lift used by q16 replay.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactRootRecordOrderLift

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFinalWorkPairControllerCompletion
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRootLookupCausalOrder
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FullCursorClientLineageLift
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73OperationalNodeCertificate
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73SchedulerTraceFactorization
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Retain the query pair of a machine-fresh record and reject every other
record kind. -/
def machineFreshPair? : UnifiedExposureRecord →
    Option (ShaInput × Digest256)
  | .machineFresh _actor input answer => some (input, answer)
  | .padding _ | .forkOutput _ _ _ _ _ | .forkAdvance _ => none

theorem projected_machine_fresh_records_map_pair
    (actor : QueryActor) :
    ∀ queries : List (ShaInput × Digest256),
      (projectedMachineFreshRecords actor queries).map machineFreshPair? =
        queries.map some := by
  intro queries
  induction queries with
  | nil => rfl
  | cons query queries ih =>
      rcases query with ⟨input, answer⟩
      simp [projectedMachineFreshRecords, machineFreshPair?, ih]

/-- The exact actor-tagged root list maps pointwise to the chronological pair
list. -/
theorem exact_root_records_map_pair
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample) :
    (exactFixedRootRecords input.package.root).map machineFreshPair? =
      (exactRootFreshQueries input).map some := by
  unfold exactFixedRootRecords fullProjectedRootRecords exactRootFreshQueries
  rw [List.map_append, projected_machine_fresh_records_map_pair,
    projected_machine_fresh_records_map_pair, List.map_append]

/-- A split in a mapped list has an exact preimage split in the source list. -/
theorem map_prefix_selected_split
    {A B : Type} (f : A → B) :
    ∀ (values : List A) (mappedPrefix suffix : List B) (selected : B),
      values.map f = mappedPrefix ++ selected :: suffix →
      ∃ before value after,
        values = before ++ value :: after ∧
        before.map f = mappedPrefix ∧
        f value = selected ∧
        after.map f = suffix := by
  intro values mappedPrefix
  induction mappedPrefix generalizing values with
  | nil =>
      intro suffix selected mapped
      cases values with
      | nil => simp at mapped
      | cons value after =>
          simp only [List.map_cons, List.nil_append, List.cons.injEq] at mapped
          exact ⟨[], value, after, rfl, rfl, mapped.1, mapped.2⟩
  | cons head restPrefix ih =>
      intro suffix selected mapped
      cases values with
      | nil => simp at mapped
      | cons value values =>
          simp only [List.map_cons, List.cons_append, List.cons.injEq] at mapped
          obtain ⟨before, chosen, after, sourceExact, beforeExact,
            chosenExact, afterExact⟩ := ih values suffix selected mapped.2
          exact ⟨value :: before, chosen, after, by simp [sourceExact],
            by simp [mapped.1, beforeExact], chosenExact, afterExact⟩

/-- Lift two ordered mapped values to two ordered source values. -/
theorem map_strict_pair_order_lift
    {A B : Type} (f : A → B)
    (values : List A) (first second : B)
    (before middle after : List B)
    (mapped : values.map f =
      before ++ first :: middle ++ second :: after) :
    ∃ beforeValues firstValue middleValues secondValue afterValues,
      values = beforeValues ++ firstValue :: middleValues ++
        secondValue :: afterValues ∧
      f firstValue = first ∧ f secondValue = second := by
  obtain ⟨beforeValues, firstValue, laterValues, sourceFirst,
    _beforeMap, firstExact, laterMap⟩ :=
    map_prefix_selected_split f values before
      (middle ++ second :: after) first (by
        simpa only [List.cons_append, List.append_assoc] using mapped)
  obtain ⟨middleValues, secondValue, afterValues, sourceSecond,
    _middleMap, secondExact, _afterMap⟩ :=
    map_prefix_selected_split f laterValues middle after second (by
      simpa only [List.append_assoc] using laterMap)
  exact ⟨beforeValues, firstValue, middleValues, secondValue, afterValues,
    by simpa only [sourceFirst, sourceSecond, List.cons_append,
      List.append_assoc], firstExact, secondExact⟩

/-- Exact production specialization: a strict pair-list order yields the
same strict order in actor-tagged root records. -/
theorem exact_root_pair_order_lifts_to_records
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (firstInput secondInput : ShaInput)
    (firstAnswer secondAnswer : Digest256)
    (before middle after : List (ShaInput × Digest256))
    (ordered : exactRootFreshQueries input =
      before ++ (firstInput, firstAnswer) :: middle ++
        (secondInput, secondAnswer) :: after) :
    ∃ beforeRecords middleRecords afterRecords
        firstActor secondActor,
      exactFixedRootRecords input.package.root =
        beforeRecords ++
          (.machineFresh firstActor firstInput firstAnswer :
            UnifiedExposureRecord) ::
          middleRecords ++
          (.machineFresh secondActor secondInput secondAnswer :
            UnifiedExposureRecord) :: afterRecords := by
  have mapped :
      (exactFixedRootRecords input.package.root).map machineFreshPair? =
        (before.map some) ++ some (firstInput, firstAnswer) ::
          (middle.map some) ++ some (secondInput, secondAnswer) ::
            (after.map some) := by
    rw [exact_root_records_map_pair input, ordered]
    simp [List.map_append, List.append_assoc]
  obtain ⟨beforeRecords, firstRecord, middleRecords, secondRecord,
    afterRecords, sourceExact, firstExact, secondExact⟩ :=
    map_strict_pair_order_lift machineFreshPair?
      (exactFixedRootRecords input.package.root)
      (some (firstInput, firstAnswer)) (some (secondInput, secondAnswer))
      (before.map some) (middle.map some) (after.map some) mapped
  obtain ⟨firstActor, firstInput', firstAnswer', firstRecordExact⟩ :=
    exact_root_records_only_machine_fresh input firstRecord (by
      rw [sourceExact]
      simp)
  obtain ⟨secondActor, secondInput', secondAnswer', secondRecordExact⟩ :=
    exact_root_records_only_machine_fresh input secondRecord (by
      rw [sourceExact]
      simp)
  subst firstRecord
  subst secondRecord
  simp only [machineFreshPair?, Option.some.injEq, Prod.mk.injEq] at firstExact
  simp only [machineFreshPair?, Option.some.injEq, Prod.mk.injEq] at secondExact
  rcases firstExact with ⟨rfl, rfl⟩
  rcases secondExact with ⟨rfl, rfl⟩
  exact ⟨beforeRecords, middleRecords, afterRecords, firstActor,
    secondActor, sourceExact⟩

#print axioms machineFreshPair?
#print axioms projected_machine_fresh_records_map_pair
#print axioms exact_root_records_map_pair
#print axioms map_prefix_selected_split
#print axioms map_strict_pair_order_lift
#print axioms exact_root_pair_order_lifts_to_records

end

end AspisK1.V7Tag73ExactRootRecordOrderLift

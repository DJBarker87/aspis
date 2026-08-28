import AspisFormal.K1.V7Tag73IncrementalSamplerControl
import AspisFormal.K1.V7Tag73Q16FirstCompactUniformity
import AspisFormal.V5QuerySamplerControl

/-!
# Operational q16 byte decoder to the ideal low-18 draw model

This module connects the literal Tag-73 `scanUniqueUntil` control to the
`firstOccurrences` sampler used by the finite q16 probability proof.  It is a
deterministic list/codec statement; it introduces no random-oracle or
independence premise.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73Q16OperationalCodecBridge

open AspisK1.V7Tag73IncrementalSamplerControl
open AspisK1.V7Tag73Q16FirstCompactUniformity
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73TranscriptSchedule
open AspisV5BoundedQuerySamplerUniformity

noncomputable section

/-! ## The two first-occurrence controls are the same -/

theorem firstOccurrences_append_singleton
    {n : Nat} (values : List (Fin n)) (value : Fin n) :
    firstOccurrences (values ++ [value]) =
      if value ∈ values then firstOccurrences values
      else firstOccurrences values ++ [value] := by
  unfold firstOccurrences
  rw [List.reverse_append]
  simp only [List.reverse_singleton, List.singleton_append]
  by_cases present : value ∈ values
  · have reversed : value ∈ values.reverse := by simpa
    rw [List.dedup_cons_of_mem reversed]
    simp [present]
  · have reversed : value ∉ values.reverse := by simpa
    rw [List.dedup_cons_of_notMem reversed]
    simp [present]

theorem firstOccurrences_eq_foldl_keepIfNew
    {n : Nat} (values : List (Fin n)) :
    firstOccurrences values =
      values.foldl (fun seen value =>
        if value ∈ seen then seen else seen ++ [value]) [] := by
  induction values using List.reverseRecOn with
  | nil => rfl
  | append_singleton values value ih =>
      rw [firstOccurrences_append_singleton, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [← ih]
      by_cases present : value ∈ values
      · have retained : value ∈ firstOccurrences values := by
          simpa [firstOccurrences] using present
        simp [present, retained]
      · have absent : value ∉ firstOccurrences values := by
          simpa [firstOccurrences] using present
        simp [present, absent]

theorem foldl_keepIfNew_map_val
    {n : Nat} (values seen : List (Fin n)) :
    (values.map Fin.val).foldl AspisV5QuerySamplerControl.keepIfNew
        (seen.map Fin.val) =
      (values.foldl (fun kept value =>
        if value ∈ kept then kept else kept ++ [value]) seen).map Fin.val := by
  induction values generalizing seen with
  | nil => rfl
  | cons value remaining ih =>
      simp only [List.map_cons, List.foldl_cons]
      have step :
          AspisV5QuerySamplerControl.keepIfNew (seen.map Fin.val) value.val =
            (if value ∈ seen then seen else seen ++ [value]).map Fin.val := by
        unfold AspisV5QuerySamplerControl.keepIfNew
        have membership : value.val ∈ seen.map Fin.val ↔ value ∈ seen := by
          constructor
          · intro mapped
            rcases List.mem_map.mp mapped with ⟨source, sourceMem, equal⟩
            have sourceEq : source = value := Fin.ext equal
            simpa [sourceEq] using sourceMem
          · intro present
            exact List.mem_map.mpr ⟨value, present, rfl⟩
        by_cases present : value ∈ seen
        · have mapped : value.val ∈ seen.map Fin.val := membership.mpr present
          rw [if_pos mapped, if_pos present]
        · have mapped : value.val ∉ seen.map Fin.val := by
            exact fun found => present (membership.mp found)
          rw [if_neg mapped, if_neg present]
          simp
      rw [step]
      exact ih _

theorem firstUnique_map_val_eq_firstOccurrences
    {n : Nat} (values : List (Fin n)) :
    AspisV5TranscriptConnection.firstUnique (values.map Fin.val) =
      (firstOccurrences values).map Fin.val := by
  rw [AspisV5QuerySamplerControl.firstUnique_eq_foldl_keepIfNew,
    firstOccurrences_eq_foldl_keepIfNew]
  exact foldl_keepIfNew_map_val values []

/-! ## Literal bounded scan equals the ideal ordered output list -/

theorem scanUniqueUntil_positions_eq_scanUntil
    (needed fuel : Nat) (words seen : List Nat)
    (wordsWithinFuel : words.length ≤ fuel)
    (seenWithinNeeded : seen.length ≤ needed) :
    (scanUniqueUntil needed fuel words seen).positions =
      AspisV5QuerySamplerControl.scanUntil needed seen
        (words.map q16Candidate) := by
  induction fuel generalizing words seen with
  | zero =>
      have empty : words = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst words
      rfl
  | succ fuel ih =>
      cases words with
      | nil => rfl
      | cons word rest =>
          have restWithin : rest.length ≤ fuel := by
            simpa using wordsWithinFuel
          by_cases complete : needed ≤ seen.length
          · have exactLength : seen.length = needed :=
              Nat.le_antisymm seenWithinNeeded complete
            simp [scanUniqueUntil, AspisV5QuerySamplerControl.scanUntil,
              exactLength]
          · have notExact : seen.length ≠ needed := by omega
            have nextWithin :
                (keepFirst seen (q16Candidate word)).length ≤ needed := by
              unfold keepFirst
              split
              · exact seenWithinNeeded
              · simp only [List.length_append, List.length_singleton]
                omega
            simp only [scanUniqueUntil, complete, ↓reduceIte, List.map_cons,
              AspisV5QuerySamplerControl.scanUntil, notExact, ↓reduceIte]
            change
              (scanUniqueUntil needed fuel rest
                (keepFirst seen (q16Candidate word))).positions =
              AspisV5QuerySamplerControl.scanUntil needed
                (keepFirst seen (q16Candidate word))
                (rest.map q16Candidate)
            exact ih rest (keepFirst seen (q16Candidate word)) restWithin
              nextWithin

def idealDrawWords (draws : Q16DrawTape) : List Nat :=
  (List.ofFn draws).map Fin.val

theorem idealDrawWords_length (draws : Q16DrawTape) :
    (idealDrawWords draws).length = 64 := by
  simp [idealDrawWords]

theorem ideal_scan_positions_eq_outputList_values (draws : Q16DrawTape) :
    (scanUniqueUntil 16 64 (idealDrawWords draws) []).positions =
      (outputList 16 draws).map Fin.val := by
  rw [scanUniqueUntil_positions_eq_scanUntil 16 64
    (idealDrawWords draws) [] (by simp [idealDrawWords]) (by simp)]
  have q16Identity :
      (idealDrawWords draws).map q16Candidate = idealDrawWords draws := by
    unfold idealDrawWords
    simp only [List.map_map]
    apply List.map_congr_left
    intro value _
    simp [q16Candidate, q16Bound, Nat.mod_eq_of_lt value.isLt]
  rw [q16Identity]
  rw [AspisV5QuerySamplerControl.scanUntil_eq_take_firstUnique]
  unfold idealDrawWords
  rw [firstUnique_map_val_eq_firstOccurrences]
  unfold outputList
  rw [List.map_take]

end


#print axioms firstOccurrences_append_singleton
#print axioms firstOccurrences_eq_foldl_keepIfNew
#print axioms foldl_keepIfNew_map_val
#print axioms firstUnique_map_val_eq_firstOccurrences
#print axioms scanUniqueUntil_positions_eq_scanUntil
#print axioms ideal_scan_positions_eq_outputList_values

end AspisK1.V7Tag73Q16OperationalCodecBridge

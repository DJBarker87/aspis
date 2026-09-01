import AspisFormal.K1.V7Tag73FinalWorkQ16CandidateController

/-!
# Exact inverse grammar of the raw q16 candidate parser

The causal candidate controller treats a parsed candidate absorb as the only
event that may start one counter's duplex chain.  These lemmas prove the
converse of the existing literal-parser theorem: successful parsing fixes
every byte of the 35-byte deployed input.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73Q16CandidateParserExact

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73FinalWorkQ16CandidateController
open AspisK1.V7Tag73SchedulerHistoryQ16Router
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- Successful counter parsing exposes the complete length/tag/counter field
inventory. -/
theorem q16_candidate_counter_parser_fields
    (input : ShaInput) (counter : Fin 64)
    (parsed : q16CandidateCounterOfInput? input = some counter) :
    input.length = 35 ∧
      input[32]? = some domAbsorb ∧
      input[33]? = some queryCandidateLabel ∧
      input[34]? = some (UInt8.ofNat counter.val) := by
  have counterLt256 : counter.val < 256 := counter.isLt.trans (by omega)
  unfold q16CandidateCounterOfInput? at parsed
  split at parsed <;>
    simp_all [← UInt8.toNat_inj, Nat.mod_eq_of_lt counterLt256] <;>
    try
      obtain ⟨_tags, _bound, finExact⟩ := parsed
      exact congrArg Fin.val finExact

/-- A successful raw counter parse is the literal deployed candidate input
with its first 32 bytes left explicit. -/
theorem q16_candidate_counter_parser_exact
    (input : ShaInput) (counter : Fin 64)
    (parsed : q16CandidateCounterOfInput? input = some counter) :
    input = input.take 32 ++
      [domAbsorb, queryCandidateLabel, UInt8.ofNat counter.val] := by
  have fields := q16_candidate_counter_parser_fields input counter parsed
  have tailExact : input.drop 32 =
      [domAbsorb, queryCandidateLabel, UInt8.ofNat counter.val] := by
    apply List.ext_getElem?
    intro index
    by_cases zero : index = 0
    · subst index
      simpa [List.getElem?_drop] using fields.2.1
    by_cases one : index = 1
    · subst index
      simpa [List.getElem?_drop] using fields.2.2.1
    by_cases two : index = 2
    · subst index
      simpa [List.getElem?_drop] using fields.2.2.2
    have atLeastThree : 3 ≤ index := by omega
    have dropLength : (input.drop 32).length = 3 := by
      simp [List.length_drop, fields.1]
    have leftNone : (input.drop 32)[index]? = none := by
      rw [List.getElem?_eq_none]
      omega
    have rightNone :
        [domAbsorb, queryCandidateLabel,
          UInt8.ofNat counter.val][index]? = none := by
      rw [List.getElem?_eq_none]
      simp
      omega
    rw [leftNone, rightNone]
  calc
    input = input.take 32 ++ input.drop 32 :=
      (List.take_append_drop 32 input).symm
    _ = input.take 32 ++
        [domAbsorb, queryCandidateLabel, UInt8.ofNat counter.val] := by
      rw [tailExact]

/-- The base-aware parser therefore has one exact preimage for each counter. -/
theorem q16_candidate_of_base_input_exact
    (base : Digest256) (input : ShaInput) (counter : Fin 64)
    (parsed : q16CandidateOfBaseInput? base input = some counter) :
    input = bytes base ++
      [domAbsorb, queryCandidateLabel, UInt8.ofNat counter.val] := by
  unfold q16CandidateOfBaseInput? at parsed
  cases counterParsed : q16CandidateCounterOfInput? input with
  | none => simp [counterParsed] at parsed
  | some parsedCounter =>
      rw [counterParsed] at parsed
      by_cases prefixExact : input.take 32 = bytes base
      · have counterExact : parsedCounter = counter := by
          simpa [prefixExact] using parsed
        subst parsedCounter
        rw [q16_candidate_counter_parser_exact input counter counterParsed,
          prefixExact]
      · simp [prefixExact] at parsed

#print axioms q16_candidate_counter_parser_fields
#print axioms q16_candidate_counter_parser_exact
#print axioms q16_candidate_of_base_input_exact

end

end AspisK1.V7Tag73Q16CandidateParserExact

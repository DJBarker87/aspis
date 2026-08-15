import AspisFormal.V5CandidateTerminalSecurity
import AspisFormal.V5RawFinalSecurityAccounting

/-!
# Raw core accounting with the cap-240 terminal term

The older raw one-proof subtotal contains the query miss, four FRI fibres, and
the four-round relation-repair event.  It does not contain the newly proved
terminal constraint argument.  This file adds the conservative cap-240
terminal term `73200 / |QM31|` exactly once.

Despite that extra term, the same conservative `2^-75` raw ideal-core endpoint
still holds.  Production source, commitment, transcript, primitive, and
runtime failures remain outside this subtotal.
-/

namespace AspisV5RefinedRawCoreAccounting

open MeasureTheory
open AspisV5CandidateTerminalSecurity
open AspisV5CryptographicAssumptions
open AspisV5FinalSecurityAccounting
open AspisV5RawFinalSecurityAccounting
open AspisSoundnessLedger

/-- Cap-240 terminal algebra and ten-round repair subtotal. -/
noncomputable def rawCandidateTerminalBound : Real :=
  (73200 : Real) / FIELD

/-- The earlier six raw terms plus the newly explicit terminal candidate
union. -/
noncomputable def refinedRawCoreSubtotal : Real :=
  rawCoreSubtotal + rawCandidateTerminalBound

theorem raw_candidate_terminal_bound_le_two_pow_neg_107 :
    rawCandidateTerminalBound ≤ (1 : Real) / 2 ^ 107 := by
  exact qm31_candidate_terminal_subtotal_le_two_pow_neg_107

/-- The exact seven-term raw arithmetic remains below `2^-75`.  This theorem
does not include any external implementation or cryptographic budget. -/
theorem refined_raw_core_subtotal_le_two_pow_neg_75 :
    refinedRawCoreSubtotal ≤ (1 : Real) / 2 ^ 75 := by
  have hquery := raw_q18_bound_le_two_pow_neg_79
  have hfri0 := raw_fri_round_zero_le_three_mul_two_pow_neg_77
  have hfri1 : rawFriFibreBound 1 ≤ (1 : Real) / 2 ^ 78 := by
    simpa [rawFriExponent] using
      (raw_fri_fibre_bound_le (1 : Fin 4))
  have hfri2 : rawFriFibreBound 2 ≤ (1 : Real) / 2 ^ 82 := by
    simpa [rawFriExponent] using
      (raw_fri_fibre_bound_le (2 : Fin 4))
  have hfri3 : rawFriFibreBound 3 ≤ (1 : Real) / 2 ^ 88 := by
    simpa [rawFriExponent] using
      (raw_fri_fibre_bound_le (3 : Fin 4))
  have hrelation := raw_relation_repair_bound_le_two_pow_neg_111
  have hterminal := raw_candidate_terminal_bound_le_two_pow_neg_107
  norm_num at hquery hfri0 hfri1 hfri2 hfri3 hrelation
  norm_num [rawCandidateTerminalBound] at hterminal
  norm_num [refinedRawCoreSubtotal, rawCoreSubtotal,
    rawCandidateTerminalBound]
  linarith

/-! ## Event-level union accounting -/

/-- The six existing raw proof-system events followed by the separate
terminal candidate event. -/
def refinedRawCoreEvents
    {Coins : Type*} (events : FinalSecurityEvents Coins)
    (terminalCandidateFailure : Set Coins) : List (Set Coins) :=
  rawOneProofCoreEvents events ++ [terminalCandidateFailure]

def refinedRawCoreFailure
    {Coins : Type*} (events : FinalSecurityEvents Coins)
    (terminalCandidateFailure : Set Coins) : Set Coins :=
  (refinedRawCoreEvents events terminalCandidateFailure).foldr (· ∪ ·) ∅

/-- The exact assumptions needed for the seven ideal core events.  The first
six are inherited unchanged; the seventh must be connected to the cap-240
candidate experiment rather than merely assigned its number. -/
structure AssumedRefinedRawCoreBounds
    {Coins : Type*} [MeasurableSpace Coins]
    (measure : Measure Coins) (events : FinalSecurityEvents Coins)
    (terminalCandidateFailure : Set Coins) : Prop where
  previous : AssumedRawOneProofCoreBounds measure events
  terminalCandidate :
    measure.real terminalCandidateFailure ≤ rawCandidateTerminalBound

/-- Union bound for the seven explicitly counted raw proof-system events. -/
theorem refined_raw_core_probability_le_subtotal
    {Coins : Type*} [MeasurableSpace Coins]
    (measure : Measure Coins) (events : FinalSecurityEvents Coins)
    (terminalCandidateFailure : Set Coins)
    (assumed : AssumedRefinedRawCoreBounds measure events
      terminalCandidateFailure) :
    measure.real (refinedRawCoreFailure events terminalCandidateFailure) ≤
      refinedRawCoreSubtotal := by
  have hunion := measureReal_foldr_union_le_sum measure
    (refinedRawCoreEvents events terminalCandidateFailure)
  have hsum :
      ((refinedRawCoreEvents events terminalCandidateFailure).map
        (fun event => measure.real event)).sum ≤ refinedRawCoreSubtotal := by
    simp only [refinedRawCoreEvents, List.map_append, List.map_cons,
      List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, add_zero]
    unfold refinedRawCoreSubtotal
    have previousSum :
        ((rawOneProofCoreEvents events).map
          (fun event => measure.real event)).sum ≤ rawCoreSubtotal := by
      simp only [rawOneProofCoreEvents, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil]
      unfold rawCoreSubtotal
      linarith [assumed.previous.queryMiss, assumed.previous.friRound0,
        assumed.previous.friRound1, assumed.previous.friRound2,
        assumed.previous.friRound3, assumed.previous.relationRepair]
    linarith [previousSum, assumed.terminalCandidate]
  exact hunion.trans hsum

#print axioms raw_candidate_terminal_bound_le_two_pow_neg_107
#print axioms refined_raw_core_subtotal_le_two_pow_neg_75
#print axioms refined_raw_core_probability_le_subtotal

end AspisV5RefinedRawCoreAccounting

import AspisFormal.K1.V7Tag73Q16FirstCompactUniformity
import AspisFormal.V6FirstCompactSampler

/-!
# Counter-zero q16 conditioning for the honest Tag-73 prover

The verifier and accepted language retain the frozen 64-candidate first-compact
rule.  The CU-oriented honest prover instead searches final-work nonces until
candidate zero already has an admitted cap-203 schedule.  This file proves the
finite distribution theorem needed for that search.

For every nonce attempt, the ideal fresh coordinates factor as a work region
and the raw bounded-draw tape for candidate zero.  Rejecting attempts whose
work predicate fails or whose candidate-zero schedule is not admitted is an
ordinary first-success sampler.  Since every q16 schedule has the same raw
bounded-draw fibre, multiplying by the same valid-work fibre preserves equal
fibres.  Consequently, for every finite nonce-attempt bound and conditioned on
success, the selected schedule is exactly uniform over admitted schedules.

The remaining deployed bridge is deliberately explicit: the Tag-73 lazy-ROM
query DAG must identify distinct final-nonce attempts with fresh product
coordinates of the form modelled here.  No claim about SHA-256 independence is
manufactured by this finite theorem.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace AspisK1.V7Tag73CounterZeroQ16Conditioning

open AspisK1.V7Tag73Q16FirstCompactUniformity

noncomputable section

/-- One honest nonce attempt: the work predicate is checked first and the
unchanged candidate-zero q16 decoder is used only on work-valid coordinates. -/
noncomputable def counterZeroCandidateOutput
    {WorkRaw : Type} (workValid : WorkRaw → Prop)
    [DecidablePred workValid]
    (raw : WorkRaw × Q16DrawTape) : Option Q16Schedule :=
  if workValid raw.1 then q16CandidateOutput raw.2 else none

/-- The raw fibre of one counter-zero attempt is the product of the common
valid-work fibre and the ordinary q16 schedule fibre. -/
noncomputable def counterZeroOutputFibreEquiv
    {WorkRaw : Type} [Fintype WorkRaw]
    (workValid : WorkRaw → Prop) [DecidablePred workValid]
    (schedule : Q16Schedule) :
    OutputFibre (counterZeroCandidateOutput workValid) schedule ≃
      {work : WorkRaw // workValid work} ×
        OutputFibre q16CandidateOutput schedule where
  toFun raw := by
    have valid : workValid raw.1.1 := by
      by_contra invalid
      have impossible := raw.2
      simp [counterZeroCandidateOutput, invalid] at impossible
    refine (⟨raw.1.1, valid⟩, ⟨raw.1.2, ?_⟩)
    simpa [counterZeroCandidateOutput, valid] using raw.2
  invFun raw := by
    refine ⟨(raw.1.1, raw.2.1), ?_⟩
    simpa [counterZeroCandidateOutput, raw.1.2] using raw.2.2
  left_inv raw := by
    apply Subtype.ext
    rfl
  right_inv raw := by
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      rfl

/-- Adding the separately positioned work predicate cannot bias one q16
schedule relative to another: both fibres acquire the same work factor. -/
theorem counterZero_output_fibres_equal
    {WorkRaw : Type} [Fintype WorkRaw]
    (workValid : WorkRaw → Prop) [DecidablePred workValid]
    (source target : Q16Schedule) :
    Fintype.card
        (OutputFibre (counterZeroCandidateOutput workValid) source) =
      Fintype.card
        (OutputFibre (counterZeroCandidateOutput workValid) target) := by
  classical
  rw [Fintype.card_congr
      (counterZeroOutputFibreEquiv workValid source),
    Fintype.card_congr (counterZeroOutputFibreEquiv workValid target),
    Fintype.card_prod, Fintype.card_prod,
    q16_output_fibres_equal source target]

/-- For any finite off-chain nonce-search bound, conditioning on finding a
work-valid attempt whose candidate zero is cap-203 leaves the selected q16
schedule exactly uniform over all cap-203 schedules. -/
theorem counterZero_search_bad_probability_eq_uniform_compact
    {WorkRaw : Type} [Fintype WorkRaw]
    (workValid : WorkRaw → Prop) [DecidablePred workValid]
    (frontierNodes : Q16Schedule → Nat)
    (bad : Finset (Fin 262144))
    (nonceAttempts : Nat)
    (reference : AdmittedResult (Cap203Admitted frontierNodes))
    (traceExists : Nonempty
      (FirstAdmittedTrace (counterZeroCandidateOutput workValid)
        (Cap203Admitted frontierNodes) nonceAttempts reference.1)) :
    firstAdmittedBadProbability (counterZeroCandidateOutput workValid)
        (Cap203Admitted frontierNodes) (AllInBad bad) nonceAttempts =
      Fintype.card
          (BadAdmittedResult (Cap203Admitted frontierNodes) (AllInBad bad)) /
        Fintype.card (AdmittedResult (Cap203Admitted frontierNodes)) := by
  apply firstAdmittedBadProbability_eq_uniform_admitted
    (counterZeroCandidateOutput workValid)
    (Cap203Admitted frontierNodes) (AllInBad bad) nonceAttempts reference
    traceExists
  intro source target
  exact counterZero_output_fibres_equal workValid source.1 target.1

/-- The counter-zero honest search and the frozen 64-candidate verifier sampler
have the same selected-schedule bad probability: both are exactly the uniform
compact-schedule ratio.  This changes prover strategy, not verifier language or
the K1.3 q16 denominator. -/
theorem counterZero_search_bad_probability_eq_frozen_first64
    {WorkRaw : Type} [Fintype WorkRaw]
    (workValid : WorkRaw → Prop) [DecidablePred workValid]
    (frontierNodes : Q16Schedule → Nat)
    (bad : Finset (Fin 262144))
    (nonceAttempts : Nat)
    (reference : AdmittedResult (Cap203Admitted frontierNodes))
    (counterZeroTraceExists : Nonempty
      (FirstAdmittedTrace (counterZeroCandidateOutput workValid)
        (Cap203Admitted frontierNodes) nonceAttempts reference.1))
    (frozenTraceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput
        (Cap203Admitted frontierNodes) 64 reference.1)) :
    firstAdmittedBadProbability (counterZeroCandidateOutput workValid)
        (Cap203Admitted frontierNodes) (AllInBad bad) nonceAttempts =
      firstAdmittedBadProbability q16CandidateOutput
        (Cap203Admitted frontierNodes) (AllInBad bad) 64 := by
  rw [counterZero_search_bad_probability_eq_uniform_compact workValid
      frontierNodes bad nonceAttempts reference counterZeroTraceExists,
    q16_first_cap203_bad_probability_eq_uniform_compact frontierNodes bad
      reference frozenTraceExists]

/-- The deterministic verifier fact used after the probabilistic search: once
candidate zero is compact, the unchanged first-compact rule selects it. -/
theorem counterZero_compact_is_frozen_first_result
    {Schedule : Type} {attempts : Nat} [NeZero attempts]
    (compact : Schedule → Prop)
    (candidates : Fin attempts → Schedule)
    (hzero : compact (candidates 0)) :
    AspisV6FirstCompactSampler.FirstCompactResult compact candidates
      (candidates 0) :=
  AspisV6FirstCompactSampler.compact_candidate_zero_is_first
    compact candidates hzero

#print axioms counterZeroOutputFibreEquiv
#print axioms counterZero_output_fibres_equal
#print axioms counterZero_search_bad_probability_eq_uniform_compact
#print axioms counterZero_search_bad_probability_eq_frozen_first64
#print axioms counterZero_compact_is_frozen_first_result

end

end AspisK1.V7Tag73CounterZeroQ16Conditioning

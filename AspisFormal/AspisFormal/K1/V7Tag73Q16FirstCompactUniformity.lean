import AspisFormal.V5BoundedQuerySamplerUniformity

/-!
# First-compact q16 selection does not bias the selected schedule

Tag-73 does not use one unconstrained q16 schedule.  It samples as many as
sixty-four bounded candidate schedules and retains the first one whose binary
Merkle frontier is at most 203 nodes.  This file proves the finite symmetry
fact needed by K1.3: if every individual schedule has an equal raw sampler
fibre, first-success selection preserves uniformity over the admitted
schedules.

The proof is deliberately independent of an iid/product slogan.  A sample is
the literal selected counter together with all candidate draw tapes.  Between
two admitted results we replace only the raw tape at that selected counter by
an exact equivalence of its output fibres.  Earlier rejected candidates and
all later candidates remain byte-for-byte unchanged.

The final specialization uses the already proved bounded-draw sampler
uniformity.  It leaves only two subsequent bridges:

* identify the admitted schedule count with the cap-203 frontier certificate;
* reindex deployed SHA-256 output blocks into the ideal low-18-bit draw tape.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace AspisK1.V7Tag73Q16FirstCompactUniformity

open AspisV5BoundedQuerySamplerUniformity
open AspisV5WithoutReplacementQuerySoundness

noncomputable section

/-! ## Generic finite first-success theorem -/

def OutputFibre {Raw Result : Type*}
    (output : Raw → Option Result) (result : Result) :=
  {raw : Raw // output raw = some result}

def RejectsEveryAdmitted {Raw Result : Type*}
    (output : Raw → Option Result) (admitted : Result → Prop)
    (raw : Raw) : Prop :=
  ∀ result, admitted result → output raw ≠ some result

def FirstAdmittedAt {Raw Result : Type*}
    (output : Raw → Option Result) (admitted : Result → Prop)
    (candidateCount : Nat) (result : Result)
    (sample : Fin candidateCount × (Fin candidateCount → Raw)) : Prop :=
  (∀ counter,
      counter.val < sample.1.val →
        RejectsEveryAdmitted output admitted (sample.2 counter)) ∧
    output (sample.2 sample.1) = some result

def FirstAdmittedTrace {Raw Result : Type*}
    (output : Raw → Option Result) (admitted : Result → Prop)
    (candidateCount : Nat) (result : Result) :=
  {sample : Fin candidateCount × (Fin candidateCount → Raw) //
    FirstAdmittedAt output admitted candidateCount result sample}

noncomputable instance outputFibreFintype
    {Raw Result : Type*} [Fintype Raw]
    (output : Raw → Option Result) (result : Result) :
    Fintype (OutputFibre output result) := by
  classical
  unfold OutputFibre
  infer_instance

noncomputable instance firstAdmittedTraceFintype
    {Raw Result : Type*} [Fintype Raw]
    (output : Raw → Option Result) (admitted : Result → Prop)
    (candidateCount : Nat) (result : Result) :
    Fintype (FirstAdmittedTrace output admitted candidateCount result) := by
  classical
  unfold FirstAdmittedTrace
  infer_instance

/-- Replacing only the selected raw candidate by an equivalence of output
fibres preserves the first-admitted counter and all preceding failures. -/
noncomputable def firstAdmittedTraceEquivOfFibreEquiv
    {Raw Result : Type*} [Fintype Raw]
    (output : Raw → Option Result) (admitted : Result → Prop)
    (candidateCount : Nat) (source target : Result)
    (fibre : OutputFibre output source ≃ OutputFibre output target) :
    FirstAdmittedTrace output admitted candidateCount source ≃
      FirstAdmittedTrace output admitted candidateCount target where
  toFun sample := by
    let counter := sample.1.1
    let candidates := sample.1.2
    let selected : OutputFibre output source :=
      ⟨candidates counter, sample.2.2⟩
    let replacement := (fibre selected).1
    refine ⟨(counter, Function.update candidates counter replacement), ?_⟩
    constructor
    · intro earlier before
      have different : earlier ≠ counter := by
        intro equal
        rw [equal] at before
        exact (Nat.lt_irrefl counter.val) before
      change RejectsEveryAdmitted output admitted
        (Function.update candidates counter replacement earlier)
      simpa [Function.update, different] using
        sample.2.1 earlier (by simpa [counter] using before)
    · change output (Function.update candidates counter replacement counter) =
        some target
      simpa [replacement] using (fibre selected).2
  invFun sample := by
    let counter := sample.1.1
    let candidates := sample.1.2
    let selected : OutputFibre output target :=
      ⟨candidates counter, sample.2.2⟩
    let replacement := (fibre.symm selected).1
    refine ⟨(counter, Function.update candidates counter replacement), ?_⟩
    constructor
    · intro earlier before
      have different : earlier ≠ counter := by
        intro equal
        rw [equal] at before
        exact (Nat.lt_irrefl counter.val) before
      change RejectsEveryAdmitted output admitted
        (Function.update candidates counter replacement earlier)
      simpa [Function.update, different] using
        sample.2.1 earlier (by simpa [counter] using before)
    · change output (Function.update candidates counter replacement counter) =
        some source
      simpa [replacement] using (fibre.symm selected).2
  left_inv sample := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext counter
      by_cases selected : counter = sample.1.1
      · subst counter
        simp
      · simp [selected]
  right_inv sample := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext counter
      by_cases selected : counter = sample.1.1
      · subst counter
        simp
      · simp [selected]

theorem firstAdmittedTrace_card_eq_of_output_fibre_card_eq
    {Raw Result : Type*} [Fintype Raw]
    (output : Raw → Option Result) (admitted : Result → Prop)
    (candidateCount : Nat) (source target : Result)
    (equalFibres : Fintype.card (OutputFibre output source) =
      Fintype.card (OutputFibre output target)) :
    Fintype.card (FirstAdmittedTrace output admitted candidateCount source) =
      Fintype.card
        (FirstAdmittedTrace output admitted candidateCount target) := by
  classical
  let fibre : OutputFibre output source ≃ OutputFibre output target :=
    Fintype.equivOfCardEq equalFibres
  exact Fintype.card_congr
    (firstAdmittedTraceEquivOfFibreEquiv output admitted candidateCount
      source target fibre)

abbrev AdmittedResult {Result : Type*} (admitted : Result → Prop) :=
  {result : Result // admitted result}

abbrev FirstAdmittedSample {Raw Result : Type*}
    (output : Raw → Option Result) (admitted : Result → Prop)
    (candidateCount : Nat) :=
  Σ result : AdmittedResult admitted,
    FirstAdmittedTrace output admitted candidateCount result.1

noncomputable instance admittedResultFintype
    {Result : Type*} [Fintype Result] (admitted : Result → Prop) :
    Fintype (AdmittedResult admitted) := by
  classical
  unfold AdmittedResult
  infer_instance

noncomputable instance firstAdmittedSampleFintype
    {Raw Result : Type*} [Fintype Raw] [Fintype Result]
    (output : Raw → Option Result) (admitted : Result → Prop)
    (candidateCount : Nat) :
    Fintype (FirstAdmittedSample output admitted candidateCount) := by
  classical
  unfold FirstAdmittedSample
  infer_instance

def FirstAdmittedBadSample {Raw Result : Type*}
    (output : Raw → Option Result) (admitted bad : Result → Prop)
    (candidateCount : Nat) :=
  {sample : FirstAdmittedSample output admitted candidateCount //
    bad sample.1.1}

noncomputable instance firstAdmittedBadSampleFintype
    {Raw Result : Type*} [Fintype Raw] [Fintype Result]
    (output : Raw → Option Result) (admitted bad : Result → Prop)
    (candidateCount : Nat) :
    Fintype (FirstAdmittedBadSample output admitted bad candidateCount) := by
  classical
  unfold FirstAdmittedBadSample
  infer_instance

abbrev BadAdmittedResult {Result : Type*}
    (admitted bad : Result → Prop) :=
  {result : AdmittedResult admitted // bad result.1}

noncomputable instance badAdmittedResultFintype
    {Result : Type*} [Fintype Result]
    (admitted bad : Result → Prop) :
    Fintype (BadAdmittedResult admitted bad) := by
  classical
  unfold BadAdmittedResult
  infer_instance

/-- With equal individual output fibres, every admitted result has the same
number of literal first-success traces, regardless of the selected counter. -/
theorem card_firstAdmittedSample_eq_mul_reference
    {Raw Result : Type*} [Fintype Raw] [Fintype Result]
    (output : Raw → Option Result) (admitted : Result → Prop)
    (candidateCount : Nat) (reference : AdmittedResult admitted)
    (equalFibres : ∀ source target : AdmittedResult admitted,
      Fintype.card (OutputFibre output source.1) =
        Fintype.card (OutputFibre output target.1)) :
    Fintype.card (FirstAdmittedSample output admitted candidateCount) =
      Fintype.card (AdmittedResult admitted) *
        Fintype.card (FirstAdmittedTrace output admitted candidateCount
          reference.1) := by
  classical
  change Fintype.card
      (Σ result : AdmittedResult admitted,
        FirstAdmittedTrace output admitted candidateCount result.1) = _
  have cardSigma :
      Fintype.card
          (Σ result : AdmittedResult admitted,
            FirstAdmittedTrace output admitted candidateCount result.1) =
        ∑ result : AdmittedResult admitted,
          Fintype.card
            (FirstAdmittedTrace output admitted candidateCount result.1) := by
    exact Fintype.card_sigma
  rw [cardSigma]
  calc
    ∑ result : AdmittedResult admitted,
        Fintype.card
          (FirstAdmittedTrace output admitted candidateCount result.1) =
        ∑ _result : AdmittedResult admitted,
          Fintype.card
            (FirstAdmittedTrace output admitted candidateCount reference.1) := by
      apply Finset.sum_congr rfl
      intro result _membership
      exact firstAdmittedTrace_card_eq_of_output_fibre_card_eq output admitted
        candidateCount result.1 reference.1 (equalFibres result reference)
    _ = Fintype.card (AdmittedResult admitted) *
        Fintype.card (FirstAdmittedTrace output admitted candidateCount
          reference.1) := by simp

theorem card_firstAdmittedBadSample_eq_mul_reference
    {Raw Result : Type*} [Fintype Raw] [Fintype Result]
    (output : Raw → Option Result) (admitted bad : Result → Prop)
    (candidateCount : Nat) (reference : AdmittedResult admitted)
    (equalFibres : ∀ source target : AdmittedResult admitted,
      Fintype.card (OutputFibre output source.1) =
        Fintype.card (OutputFibre output target.1)) :
    Fintype.card
        (FirstAdmittedBadSample output admitted bad candidateCount) =
      Fintype.card (BadAdmittedResult admitted bad) *
        Fintype.card (FirstAdmittedTrace output admitted candidateCount
          reference.1) := by
  classical
  let split : FirstAdmittedBadSample output admitted bad candidateCount ≃
      Σ result : BadAdmittedResult admitted bad,
        FirstAdmittedTrace output admitted candidateCount result.1.1 :=
    Equiv.subtypeSigmaEquiv
      (fun result : AdmittedResult admitted ↦
        FirstAdmittedTrace output admitted candidateCount result.1)
      (fun result ↦ bad result.1)
  rw [Fintype.card_congr split, Fintype.card_sigma]
  calc
    ∑ result : BadAdmittedResult admitted bad,
        Fintype.card
          (FirstAdmittedTrace output admitted candidateCount result.1.1) =
        ∑ _result : BadAdmittedResult admitted bad,
          Fintype.card
            (FirstAdmittedTrace output admitted candidateCount reference.1) := by
      apply Finset.sum_congr rfl
      intro result _membership
      exact firstAdmittedTrace_card_eq_of_output_fibre_card_eq output admitted
        candidateCount result.1.1 reference.1
          (equalFibres result.1 reference)
    _ = Fintype.card (BadAdmittedResult admitted bad) *
        Fintype.card (FirstAdmittedTrace output admitted candidateCount
          reference.1) := by simp

noncomputable def firstAdmittedBadProbability
    {Raw Result : Type*} [Fintype Raw] [Fintype Result]
    (output : Raw → Option Result) (admitted bad : Result → Prop)
    (candidateCount : Nat) : Real :=
  Fintype.card (FirstAdmittedBadSample output admitted bad candidateCount) /
    Fintype.card (FirstAdmittedSample output admitted candidateCount)

/-- Exact cancellation theorem: conditioned on finding an admitted result,
the first-success scan has the same bad-result probability as direct uniform
sampling from the admitted result set. -/
theorem firstAdmittedBadProbability_eq_uniform_admitted
    {Raw Result : Type*} [Fintype Raw] [Fintype Result]
    (output : Raw → Option Result) (admitted bad : Result → Prop)
    (candidateCount : Nat) (reference : AdmittedResult admitted)
    (traceExists : Nonempty
      (FirstAdmittedTrace output admitted candidateCount reference.1))
    (equalFibres : ∀ source target : AdmittedResult admitted,
      Fintype.card (OutputFibre output source.1) =
        Fintype.card (OutputFibre output target.1)) :
    firstAdmittedBadProbability output admitted bad candidateCount =
      Fintype.card (BadAdmittedResult admitted bad) /
        Fintype.card (AdmittedResult admitted) := by
  classical
  have tracePositive : 0 < Fintype.card
      (FirstAdmittedTrace output admitted candidateCount reference.1) := by
    rw [Fintype.card_pos_iff]
    exact traceExists
  have traceCastNonzero :
      (Fintype.card
        (FirstAdmittedTrace output admitted candidateCount reference.1) :
          Real) ≠ 0 := by
    exact_mod_cast tracePositive.ne'
  have admittedPositive : 0 < Fintype.card (AdmittedResult admitted) := by
    rw [Fintype.card_pos_iff]
    exact ⟨reference⟩
  have admittedCastNonzero :
      (Fintype.card (AdmittedResult admitted) : Real) ≠ 0 := by
    exact_mod_cast admittedPositive.ne'
  unfold firstAdmittedBadProbability
  rw [card_firstAdmittedBadSample_eq_mul_reference output admitted bad
      candidateCount reference equalFibres,
    card_firstAdmittedSample_eq_mul_reference output admitted candidateCount
      reference equalFibres,
    Nat.cast_mul, Nat.cast_mul]
  field_simp [traceCastNonzero, admittedCastNonzero]

/-! ## Exact q16 bounded-draw specialization -/

abbrev Q16DrawTape := Draws 262144 64
abbrev Q16Schedule :=
  AspisV5BoundedQuerySamplerUniformity.QuerySchedule 16 262144

noncomputable def q16CandidateOutput (draws : Q16DrawTape) : Option Q16Schedule :=
  by
  classical
  exact if success : Successful 16 draws then
      some (successfulSchedule draws success)
    else
      none

theorem q16CandidateOutput_eq_some_iff_produces
    (draws : Q16DrawTape) (schedule : Q16Schedule) :
    q16CandidateOutput draws = some schedule ↔ Produces schedule draws := by
  by_cases success : Successful 16 draws
  · simp only [q16CandidateOutput, dif_pos success, Option.some.injEq]
    constructor
    · intro equal
      rw [← equal]
      exact successfulSchedule_produced draws success
    · intro produces
      exact successfulSchedule_eq_of_produces schedule draws produces
  · constructor
    · intro impossible
      simp [q16CandidateOutput, success] at impossible
    · intro produces
      exact False.elim
        (success (successful_of_produces schedule draws produces))

noncomputable def q16OutputFibreEquivProducing (schedule : Q16Schedule) :
    OutputFibre q16CandidateOutput schedule ≃
      producingDraws (maxDraws := 64) schedule :=
  Equiv.subtypeEquivRight fun draws ↦
    q16CandidateOutput_eq_some_iff_produces draws schedule

theorem q16_output_fibres_equal (source target : Q16Schedule) :
    Fintype.card (OutputFibre q16CandidateOutput source) =
      Fintype.card (OutputFibre q16CandidateOutput target) := by
  classical
  calc
    Fintype.card (OutputFibre q16CandidateOutput source) =
        Fintype.card (producingDraws (maxDraws := 64) source) :=
      Fintype.card_congr (q16OutputFibreEquivProducing source)
    _ = Fintype.card (producingDraws (maxDraws := 64) target) :=
      producingDraws_card_eq source target
    _ = Fintype.card (OutputFibre q16CandidateOutput target) :=
      (Fintype.card_congr (q16OutputFibreEquivProducing target)).symm

def Cap203Admitted
    (frontierNodes : Q16Schedule → Nat) (schedule : Q16Schedule) : Prop :=
  frontierNodes schedule ≤ 203

def AllInBad (bad : Finset (Fin 262144)) (schedule : Q16Schedule) : Prop :=
  AllQueriesIn bad schedule

/-- The exact first-cap-203 cancellation statement for the deployed ideal
parameters.  The counter bound is literally 64.  No independence premise and
no work-normalization factor occur in this theorem. -/
theorem q16_first_cap203_bad_probability_eq_uniform_compact
    (frontierNodes : Q16Schedule → Nat)
    (bad : Finset (Fin 262144))
    (reference : AdmittedResult (Cap203Admitted frontierNodes))
    (traceExists : Nonempty
      (FirstAdmittedTrace q16CandidateOutput
        (Cap203Admitted frontierNodes) 64 reference.1)) :
    firstAdmittedBadProbability q16CandidateOutput
        (Cap203Admitted frontierNodes) (AllInBad bad) 64 =
      Fintype.card
          (BadAdmittedResult (Cap203Admitted frontierNodes) (AllInBad bad)) /
        Fintype.card (AdmittedResult (Cap203Admitted frontierNodes)) := by
  apply firstAdmittedBadProbability_eq_uniform_admitted
    q16CandidateOutput (Cap203Admitted frontierNodes) (AllInBad bad) 64
    reference traceExists
  intro source target
  exact q16_output_fibres_equal source.1 target.1

/-! ## Audit -/

#print axioms firstAdmittedTraceEquivOfFibreEquiv
#print axioms firstAdmittedTrace_card_eq_of_output_fibre_card_eq
#print axioms firstAdmittedBadProbability_eq_uniform_admitted
#print axioms q16CandidateOutput_eq_some_iff_produces
#print axioms q16_output_fibres_equal
#print axioms q16_first_cap203_bad_probability_eq_uniform_compact

end

end AspisK1.V7Tag73Q16FirstCompactUniformity

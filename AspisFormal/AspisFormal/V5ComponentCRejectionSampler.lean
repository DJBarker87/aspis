import AspisFormal.V5ComponentCSamplerKernel

/-!
# v5 Component C: bounded M31 rejection sampling

This leaf formalises the finite probability calculation used by one call to
the deployed `sample_m31` routine.  The source experiment is deliberately
explicit: sixteen independent uniform low-31-bit candidates are supplied at
once.  A candidate is accepted exactly when it is below
`P = 2^31 - 1`; hence there is exactly one rejected candidate.

No theorem below identifies this ideal raw experiment with an OS RNG, SHA,
a PRG, a Rust word source, or the deployed byte representation.  Those are
separate correspondence/entropy interfaces.
-/

namespace AspisV5ComponentCRejectionSampler

open scoped ENNReal

abbrev rawCandidateCount : Nat := 2 ^ 31
abbrev rawWordCount : Nat := 2 ^ 32
abbrev m31Modulus : Nat := rawCandidateCount - 1
abbrev retryLimit : Nat := 16

abbrev RawWord := Fin rawWordCount
abbrev RawCandidate := Fin rawCandidateCount
abbrev RawHighBit := Fin 2
abbrev M31Value := Fin m31Modulus
abbrev RawAttempts := Fin retryLimit → RawCandidate

/-- Split one 32-bit word into its low 31 bits and its high bit.  This is a
literal finite equivalence, not a randomness assumption. -/
def rawCandidateHighBitEquiv : RawCandidate × RawHighBit ≃ RawWord :=
  (Equiv.prodComm RawCandidate RawHighBit).trans
    (finProdFinEquiv.trans (finCongr (by
      norm_num [rawCandidateCount, rawWordCount])))

/-- The exact operation performed before the `< P` rejection test. -/
def low31Candidate (word : RawWord) : RawCandidate :=
  ⟨(word : Nat) % rawCandidateCount, Nat.mod_lt _ (by
    norm_num [rawCandidateCount])⟩

@[simp] theorem low31Candidate_rawCandidateHighBitEquiv
    (x : RawCandidate × RawHighBit) :
    low31Candidate (rawCandidateHighBitEquiv x) = x.1 := by
  apply Fin.ext
  simp [low31Candidate, rawCandidateHighBitEquiv, finProdFinEquiv,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt x.1.isLt]

theorem m31Modulus_pos : 0 < m31Modulus := by
  norm_num [m31Modulus, rawCandidateCount]

theorem m31Modulus_lt_rawCandidateCount : m31Modulus < rawCandidateCount := by
  norm_num [m31Modulus, rawCandidateCount]

instance : Nonempty M31Value := Fin.pos_iff_nonempty.mp m31Modulus_pos

/-- The unique raw value rejected by the deployed `< P` test. -/
def rejectedCandidate : RawCandidate :=
  ⟨m31Modulus, m31Modulus_lt_rawCandidateCount⟩

/-- A raw low-31-bit candidate is accepted exactly below `P`. -/
def Accepted (x : RawCandidate) : Prop := (x : Nat) < m31Modulus

instance (x : RawCandidate) : Decidable (Accepted x) := by
  unfold Accepted
  infer_instance

/-- Turn an accepted raw candidate into its canonical M31 residue. -/
def acceptedValue (x : RawCandidate) (h : Accepted x) : M31Value := ⟨x, h⟩

/-- Total one-attempt result: `none` is the single rejected candidate. -/
def candidateResult (x : RawCandidate) : Option M31Value :=
  if h : Accepted x then some (acceptedValue x h) else none

@[simp] theorem candidateResult_rejected : candidateResult rejectedCandidate = none := by
  simp [candidateResult, Accepted, rejectedCandidate]

theorem candidateResult_eq_none_iff (x : RawCandidate) :
    candidateResult x = none ↔ x = rejectedCandidate := by
  simp only [candidateResult]
  split_ifs with h
  · have hne : x ≠ rejectedCandidate := by
      intro hx
      subst x
      simp [Accepted, rejectedCandidate] at h
    simp [hne]
  · simp only [true_iff]
    apply Fin.ext
    have hxle : m31Modulus ≤ (x : Nat) := Nat.le_of_not_gt h
    have hxlt : (x : Nat) < rawCandidateCount := x.isLt
    have hraw : rawCandidateCount = m31Modulus + 1 := by
      norm_num [rawCandidateCount, m31Modulus]
    change (x : Nat) = m31Modulus
    have hxlt' : (x : Nat) < m31Modulus + 1 := hxlt.trans_le hraw.le
    omega

/-- The candidate space is canonically `Option M31`: the one rejected value
is `none`, and every accepted residue is `some`. -/
def candidateResultEquiv : RawCandidate ≃ Option M31Value where
  toFun := candidateResult
  invFun
    | none => rejectedCandidate
    | some y => ⟨y, lt_trans y.isLt m31Modulus_lt_rawCandidateCount⟩
  left_inv x := by
    by_cases h : Accepted x
    · simp [candidateResult, h, acceptedValue]
    · have hx : x = rejectedCandidate := (candidateResult_eq_none_iff x).mp (by
        simp [candidateResult, h])
      simp [hx]
  right_inv y := by
    cases y with
    | none => exact candidateResult_rejected
    | some y => simp [candidateResult, Accepted, acceptedValue]

/-! ## First-success semantics -/

/-- Return the first accepted value, or `none` after all attempts reject. -/
def firstSuccess : (n : Nat) → (Fin n → Option M31Value) → Option M31Value
  | 0, _ => none
  | n + 1, xs =>
      match xs 0 with
      | some y => some y
      | none => firstSuccess n (fun i => xs i.succ)

/-- The exact bounded sampler on a vector of low-31-bit candidates. -/
def boundedSample (xs : RawAttempts) : Option M31Value :=
  firstSuccess retryLimit (fun i => candidateResult (xs i))

private theorem firstSuccess_eq_none_iff (n : Nat) (xs : Fin n → Option M31Value) :
    firstSuccess n xs = none ↔ ∀ i, xs i = none := by
  induction n with
  | zero => simp [firstSuccess]
  | succ n ih =>
      cases h0 : xs 0 with
      | none =>
          simp only [firstSuccess, h0, ih]
          constructor
          · intro h i
            refine Fin.cases h0 (fun j => h j) i
          · intro h i
            exact h i.succ
      | some y =>
          constructor
          · intro h
            simp [firstSuccess, h0] at h
          · intro h
            have hz := h 0
            simp [h0] at hz

theorem boundedSample_eq_none_iff (xs : RawAttempts) :
    boundedSample xs = none ↔ ∀ i, xs i = rejectedCandidate := by
  rw [boundedSample, firstSuccess_eq_none_iff]
  simp only [candidateResult_eq_none_iff]

/-- The unique all-rejection attempt vector. -/
def allRejected : RawAttempts := fun _ => rejectedCandidate

theorem boundedSample_eq_none_iff_eq_allRejected (xs : RawAttempts) :
    boundedSample xs = none ↔ xs = allRejected := by
  rw [boundedSample_eq_none_iff]
  exact ⟨fun h => funext h, fun h i => congrFun h i⟩

/-! ## Exact abort mass -/

/-- The ideal law of sixteen mutually independent uniform low-31-bit
candidates.  Uniformity on the finite function space is the exact joint iid
law; no deployed entropy source is claimed. -/
noncomputable def rawAttemptsLaw : PMF RawAttempts :=
  PMF.uniformOfFintype RawAttempts

/-- The output law, retaining the explicit abort branch. -/
noncomputable def boundedOutputLaw : PMF (Option M31Value) :=
  rawAttemptsLaw.map boundedSample

theorem rawAttempts_card : Fintype.card RawAttempts = rawCandidateCount ^ retryLimit := by
  simp [RawAttempts]

/-- Exactly one of the `2^(31*16)` raw attempt vectors aborts. -/
theorem boundedOutputLaw_abort_exact :
    boundedOutputLaw none = ((rawCandidateCount : ℝ≥0∞) ^ retryLimit)⁻¹ := by
  classical
  rw [boundedOutputLaw, PMF.map_apply,
    tsum_eq_single allRejected]
  · rw [if_pos]
    · rw [rawAttemptsLaw, PMF.uniformOfFintype_apply, rawAttempts_card]
      simp only [Nat.cast_pow]
    · exact (boundedSample_eq_none_iff_eq_allRejected allRejected |>.2 rfl).symm
  · intro xs hxs
    rw [if_neg]
    intro hout
    exact hxs (boundedSample_eq_none_iff_eq_allRejected xs |>.1 hout.symm)

/-- Arithmetic form of the exact abort probability: `(2^-31)^16 = 2^-496`. -/
theorem boundedOutputLaw_abort_exact_pow_two :
    boundedOutputLaw none = ((2 : ℝ≥0∞) ^ 496)⁻¹ := by
  rw [boundedOutputLaw_abort_exact]
  congr 1
  have hraw : (rawCandidateCount : ℝ≥0∞) = (2 : ℝ≥0∞) ^ 31 := by
    norm_num [rawCandidateCount]
  rw [hraw]
  change (((2 : ℝ≥0∞) ^ 31) ^ 16) = (2 : ℝ≥0∞) ^ 496
  rw [← pow_mul]

/-! ## Successful output law -/

/-- Projecting either coordinate of a joint uniform finite product gives the
uniform marginal. -/
theorem uniform_prod_map_fst {A B : Type*} [Fintype A] [Nonempty A]
    [Fintype B] [Nonempty B] :
    (PMF.uniformOfFintype (A × B)).map Prod.fst = PMF.uniformOfFintype A := by
  classical
  ext a
  rw [PMF.map_apply]
  simp only [PMF.uniformOfFintype_apply]
  rw [tsum_fintype]
  rw [Fintype.sum_prod_type]
  suffices (Fintype.card B : ℝ≥0∞) *
      ((Fintype.card A : ℝ≥0∞) * (Fintype.card B : ℝ≥0∞))⁻¹ =
        (Fintype.card A : ℝ≥0∞)⁻¹ by
    simpa [Fintype.card_prod]
  have hA0 : (Fintype.card A : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hAt : (Fintype.card A : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  rw [ENNReal.mul_inv (Or.inl hA0) (Or.inl hAt)]
  calc
    (Fintype.card B : ℝ≥0∞) *
          ((Fintype.card A : ℝ≥0∞)⁻¹ * (Fintype.card B : ℝ≥0∞)⁻¹) =
        (Fintype.card A : ℝ≥0∞)⁻¹ * (Fintype.card B : ℝ≥0∞) *
          (Fintype.card B : ℝ≥0∞)⁻¹ := by ac_rfl
    _ = (Fintype.card A : ℝ≥0∞)⁻¹ := ENNReal.mul_inv_cancel_right
      (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)

/-- A genuinely uniform 32-bit word has a genuinely uniform low-31-bit
projection.  Each candidate has exactly two preimages, distinguished by the
discarded high bit. -/
theorem uniformRawWord_low31_eq_uniform :
    (PMF.uniformOfFintype RawWord).map low31Candidate =
      PMF.uniformOfFintype RawCandidate := by
  calc
    (PMF.uniformOfFintype RawWord).map low31Candidate =
        ((PMF.uniformOfFintype (RawCandidate × RawHighBit)).map
          rawCandidateHighBitEquiv).map low31Candidate := by
            rw [AspisV5RankOneOpeningHiding.uniform_map_equiv
              rawCandidateHighBitEquiv]
    _ = (PMF.uniformOfFintype (RawCandidate × RawHighBit)).map
        (low31Candidate ∘ rawCandidateHighBitEquiv) := by
          rw [PMF.map_comp]
    _ = (PMF.uniformOfFintype (RawCandidate × RawHighBit)).map Prod.fst := by
      congr 1
      funext x
      exact low31Candidate_rawCandidateHighBitEquiv x
    _ = PMF.uniformOfFintype RawCandidate := uniform_prod_map_fst

/-- Split a family of pairs into a pair of families. -/
def pointwiseProdEquiv {I A B : Type*} :
    (I → A × B) ≃ (I → A) × (I → B) where
  toFun x := (fun i => (x i).1, fun i => (x i).2)
  invFun x i := (x.1 i, x.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Every finite type is the sigma type of the fibres of a function. -/
def domainSigmaFibreEquiv {A B : Type*} (f : A → B) :
    A ≃ Σ b, {a : A // f a = b} where
  toFun a := ⟨f a, a, rfl⟩
  invFun x := x.2
  left_inv _ := rfl
  right_inv x := by
    rcases x with ⟨b, a, ha⟩
    subst b
    rfl

/-- If every fibre of `f` is equivalent to one fixed fibre, its domain is a
product of the output type with that fixed fibre. -/
def domainProdFibreEquiv {A B : Type*} (f : A → B) (b₀ : B)
    (h : ∀ b, {a : A // f a = b} ≃ {a : A // f a = b₀}) :
    A ≃ B × {a : A // f a = b₀} :=
  (domainSigmaFibreEquiv f).trans (Equiv.sigmaEquivProdOfEquiv h)

@[simp] theorem domainProdFibreEquiv_fst {A B : Type*} (f : A → B) (b₀ : B)
    (h : ∀ b, {a : A // f a = b} ≃ {a : A // f a = b₀}) (a : A) :
    (domainProdFibreEquiv f b₀ h a).1 = f a := rfl

/-- A deterministic map with pairwise-equivalent fibres carries the uniform
law to the uniform law.  This is the counting principle used below; it does
not assume surjectivity as a slogan. -/
theorem uniform_map_of_equiv_fibres {A B : Type*} [Fintype A] [Nonempty A]
    [Fintype B] [Nonempty B] (f : A → B) (b₀ : B)
    (h : ∀ b, {a : A // f a = b} ≃ {a : A // f a = b₀}) :
    (PMF.uniformOfFintype A).map f = PMF.uniformOfFintype B := by
  classical
  let a₀ : A := Classical.choice (inferInstance : Nonempty A)
  let fixed : {a : A // f a = b₀} := h (f a₀) ⟨a₀, rfl⟩
  letI : Nonempty {a : A // f a = b₀} := ⟨fixed⟩
  let e := domainProdFibreEquiv f b₀ h
  calc
    (PMF.uniformOfFintype A).map f =
        (PMF.uniformOfFintype A).map (Prod.fst ∘ e) := by
          exact congrArg (fun g => (PMF.uniformOfFintype A).map g)
            (funext fun a => (domainProdFibreEquiv_fst f b₀ h a).symm)
    _ = ((PMF.uniformOfFintype A).map e).map Prod.fst :=
      (PMF.map_comp e (PMF.uniformOfFintype A) Prod.fst).symm
    _ = (PMF.uniformOfFintype
        (B × {a : A // f a = b₀})).map Prod.fst := by
      rw [AspisV5RankOneOpeningHiding.uniform_map_equiv e]
    _ = PMF.uniformOfFintype B := uniform_prod_map_fst

abbrev ResultAttempts := Fin retryLimit → Option M31Value

/-- Coordinatewise form of the candidate bijection. -/
def resultAttemptsEquiv : RawAttempts ≃ ResultAttempts :=
  Equiv.piCongrRight fun _ => candidateResultEquiv

@[simp] theorem resultAttemptsEquiv_apply (xs : RawAttempts) (i : Fin retryLimit) :
    resultAttemptsEquiv xs i = candidateResult (xs i) := rfl

theorem boundedSample_eq_firstSuccess_resultAttemptsEquiv (xs : RawAttempts) :
    boundedSample xs = firstSuccess retryLimit (resultAttemptsEquiv xs) := rfl

/-- Applying a value permutation to every attempt commutes with choosing the
first success. -/
theorem firstSuccess_optionCongr (e : M31Value ≃ M31Value) (n : Nat)
    (xs : Fin n → Option M31Value) :
    firstSuccess n (fun i => e.optionCongr (xs i)) =
      e.optionCongr (firstSuccess n xs) := by
  induction n with
  | zero => simp [firstSuccess]
  | succ n ih =>
      cases h0 : xs 0 with
      | none => simpa [firstSuccess, h0] using ih (fun i => xs i.succ)
      | some y => simp [firstSuccess, h0]

/-- Apply the transposition `(y z)` to every accepted attempt, leaving
rejections fixed. -/
def swapResultAttempts (y z : M31Value) : ResultAttempts ≃ ResultAttempts :=
  Equiv.piCongrRight fun _ => (Equiv.swap y z).optionCongr

@[simp] theorem swapResultAttempts_apply (y z : M31Value) (xs : ResultAttempts)
    (i : Fin retryLimit) :
    swapResultAttempts y z xs i = (Equiv.swap y z).optionCongr (xs i) := rfl

theorem firstSuccess_swapResultAttempts (y z : M31Value) (xs : ResultAttempts) :
    firstSuccess retryLimit (swapResultAttempts y z xs) =
      (Equiv.swap y z).optionCongr (firstSuccess retryLimit xs) := by
  exact firstSuccess_optionCongr (Equiv.swap y z) retryLimit xs

/-- Attempt vectors on which the bounded sampler succeeds. -/
abbrev SuccessfulResultAttempts :=
  {xs : ResultAttempts // firstSuccess retryLimit xs ≠ none}

/-- Extract the value from a proved-successful attempt vector. -/
def successfulValue (xs : SuccessfulResultAttempts) : M31Value :=
  (firstSuccess retryLimit xs.1).get (Option.ne_none_iff_isSome.mp xs.2)

theorem firstSuccess_successful_eq_some (xs : SuccessfulResultAttempts) :
    firstSuccess retryLimit xs.1 = some (successfulValue xs) := by
  exact (Option.some_get _).symm

/-- Swapping accepted values preserves successful termination. -/
def swapSuccessfulResultAttempts (y z : M31Value) :
    SuccessfulResultAttempts ≃ SuccessfulResultAttempts :=
  (swapResultAttempts y z).subtypeEquiv fun xs => by
    rw [firstSuccess_swapResultAttempts]
    constructor
    · intro h hnone
      have heq : (Equiv.swap y z).optionCongr (firstSuccess retryLimit xs) =
          (Equiv.swap y z).optionCongr none := hnone
      exact h ((Equiv.swap y z).optionCongr.injective heq)
    · intro h hnone
      apply h
      rw [hnone]
      rfl

theorem successfulValue_swap (y z : M31Value) (xs : SuccessfulResultAttempts) :
    successfulValue (swapSuccessfulResultAttempts y z xs) =
      Equiv.swap y z (successfulValue xs) := by
  have h := firstSuccess_swapResultAttempts y z xs.1
  rw [firstSuccess_successful_eq_some xs] at h
  have hs := firstSuccess_successful_eq_some (swapSuccessfulResultAttempts y z xs)
  change firstSuccess retryLimit (swapResultAttempts y z xs.1) =
    some (successfulValue (swapSuccessfulResultAttempts y z xs)) at hs
  rw [hs] at h
  exact Option.some.inj h

/-- The transposition `(b b₀)` gives an explicit equivalence between every
pair of successful-output fibres. -/
def successfulValueFibreEquiv (b b₀ : M31Value) :
    {xs : SuccessfulResultAttempts // successfulValue xs = b} ≃
      {xs : SuccessfulResultAttempts // successfulValue xs = b₀} :=
  (swapSuccessfulResultAttempts b b₀).subtypeEquiv fun xs => by
    rw [successfulValue_swap]
    constructor
    · intro h
      rw [h]
      exact Equiv.swap_apply_left b b₀
    · intro h
      apply (Equiv.swap b b₀).injective
      exact h.trans (Equiv.swap_apply_left b b₀).symm

/-- A concrete accepted M31 value, used only to witness nonemptiness. -/
def firstM31Value : M31Value := ⟨0, m31Modulus_pos⟩

/-- A concrete successful attempt vector. -/
def successfulResultAttemptsExample : SuccessfulResultAttempts :=
  ⟨fun _ => some firstM31Value, by simp [firstSuccess]⟩

instance : Nonempty SuccessfulResultAttempts := ⟨successfulResultAttemptsExample⟩

/-- Conditional on at least one acceptance, the first accepted M31 value is
exactly uniform. -/
theorem successfulResultAttempts_value_uniform :
    (PMF.uniformOfFintype SuccessfulResultAttempts).map successfulValue =
      PMF.uniformOfFintype M31Value := by
  exact uniform_map_of_equiv_fibres successfulValue firstM31Value
    (fun b => successfulValueFibreEquiv b firstM31Value)

/-! ## Literal PMF conditioning of the raw experiment -/

/-- Filtering a finite uniform law on a nonempty predicate gives the uniform
law on the corresponding subtype, embedded back into the original type. -/
theorem uniform_filter_eq_uniform_subtype {A : Type*} [Fintype A] [Nonempty A]
    (s : A → Prop) [DecidablePred s] [Nonempty {a : A // s a}]
    (h : ∃ a ∈ {a : A | s a}, a ∈ (PMF.uniformOfFintype A).support) :
    (PMF.uniformOfFintype A).filter {a : A | s a} h =
      (PMF.uniformOfFintype {a : A // s a}).map Subtype.val := by
  classical
  have hA0 : (Fintype.card A : ℝ≥0∞) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hAt : (Fintype.card A : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
  have hcard : Fintype.card ↥{a : A | s a} = Fintype.card {a : A // s a} :=
    Fintype.card_congr (Equiv.refl _)
  apply PMF.ext
  intro a
  rw [PMF.filter_apply, PMF.map_apply, ← PMF.toOuterMeasure_apply,
    PMF.toOuterMeasure_uniformOfFintype_apply]
  by_cases ha : s a
  · rw [Set.indicator_of_mem (show a ∈ {a : A | s a} from ha),
      PMF.uniformOfFintype_apply,
      hcard,
      tsum_eq_single (⟨a, ha⟩ : {a : A // s a}), if_pos rfl,
      PMF.uniformOfFintype_apply,
      ENNReal.inv_div (Or.inl hAt) (Or.inl hA0), div_eq_mul_inv,
      ← mul_assoc, ENNReal.inv_mul_cancel hA0 hAt, one_mul]
    intro b hb
    exact if_neg (mt (fun hab : a = (b : A) => Subtype.ext hab.symm) hb)
  · rw [Set.indicator_of_notMem (show a ∉ {a : A | s a} from ha), zero_mul]
    refine (ENNReal.tsum_eq_zero.mpr fun b => ?_).symm
    exact if_neg fun hab : a = (b : A) => ha (by rw [hab]; exact b.2)

/-- Success predicate on the literal raw-attempt experiment. -/
def RawSucceeds (xs : RawAttempts) : Prop := boundedSample xs ≠ none

instance (xs : RawAttempts) : Decidable (RawSucceeds xs) := by
  unfold RawSucceeds
  infer_instance

abbrev SuccessfulRawAttempts := {xs : RawAttempts // RawSucceeds xs}

/-- The coordinatewise candidate bijection restricts to an equivalence of the
two successful-attempt experiments. -/
def successfulRawResultEquiv : SuccessfulRawAttempts ≃ SuccessfulResultAttempts :=
  resultAttemptsEquiv.subtypeEquiv fun xs => by
    change boundedSample xs ≠ none ↔
      firstSuccess retryLimit (resultAttemptsEquiv xs) ≠ none
    rw [boundedSample_eq_firstSuccess_resultAttemptsEquiv]

/-- Extract the first accepted residue from a proved-successful raw vector. -/
def successfulRawValue (xs : SuccessfulRawAttempts) : M31Value :=
  (boundedSample xs.1).get (Option.ne_none_iff_isSome.mp xs.2)

theorem successfulValue_successfulRawResultEquiv (xs : SuccessfulRawAttempts) :
    successfulValue (successfulRawResultEquiv xs) = successfulRawValue xs := rfl

/-- A concrete successful raw attempt vector, transported through the exact
candidate/result equivalence. -/
def successfulRawAttemptsExample : SuccessfulRawAttempts :=
  successfulRawResultEquiv.symm successfulResultAttemptsExample

instance : Nonempty SuccessfulRawAttempts := ⟨successfulRawAttemptsExample⟩

/-- Uniform raw vectors, conditioned on success at the subtype level, produce
an exactly uniform M31 value. -/
theorem successfulRawAttempts_value_uniform :
    (PMF.uniformOfFintype SuccessfulRawAttempts).map successfulRawValue =
      PMF.uniformOfFintype M31Value := by
  let e := successfulRawResultEquiv
  calc
    (PMF.uniformOfFintype SuccessfulRawAttempts).map successfulRawValue =
        (PMF.uniformOfFintype SuccessfulRawAttempts).map
          (successfulValue ∘ e) := by
      exact congrArg (fun f => (PMF.uniformOfFintype SuccessfulRawAttempts).map f)
        (funext fun xs => (successfulValue_successfulRawResultEquiv xs).symm)
    _ = ((PMF.uniformOfFintype SuccessfulRawAttempts).map e).map
        successfulValue := (PMF.map_comp e _ successfulValue).symm
    _ = (PMF.uniformOfFintype SuccessfulResultAttempts).map successfulValue := by
      rw [AspisV5RankOneOpeningHiding.uniform_map_equiv e]
    _ = PMF.uniformOfFintype M31Value := successfulResultAttempts_value_uniform

/-- A total extractor used only after filtering to success.  Its abort value
is irrelevant because the filtered law assigns the abort fibre mass zero. -/
def boundedValueOrFirst (xs : RawAttempts) : M31Value :=
  match boundedSample xs with
  | some y => y
  | none => firstM31Value

theorem boundedValueOrFirst_eq_successfulRawValue (xs : SuccessfulRawAttempts) :
    boundedValueOrFirst xs.1 = successfulRawValue xs := by
  have ho : boundedSample xs.1 = some (successfulRawValue xs) :=
    (Option.some_get _).symm
  simp [boundedValueOrFirst, ho]

/-- The success event has positive mass in the ideal raw experiment. -/
theorem successfulRawConditioningWitness :
    ∃ xs ∈ {xs : RawAttempts | RawSucceeds xs},
      xs ∈ (PMF.uniformOfFintype RawAttempts).support :=
  ⟨successfulRawAttemptsExample.1, successfulRawAttemptsExample.2,
    PMF.mem_support_uniformOfFintype _⟩

/-- Literal conditional output law of the bounded sampler under iid uniform
low-31-bit candidates. -/
noncomputable def successfulM31Law : PMF M31Value :=
  ((PMF.uniformOfFintype RawAttempts).filter
    {xs : RawAttempts | RawSucceeds xs} successfulRawConditioningWitness).map
      boundedValueOrFirst

/-- **Exact conditional sampler theorem.** Given the stated iid uniform raw
experiment, conditioning the 16-retry routine on success produces the exact
uniform law on `Fin (2^31-1)`. -/
theorem successfulM31Law_eq_uniform :
    successfulM31Law = PMF.uniformOfFintype M31Value := by
  rw [successfulM31Law,
    uniform_filter_eq_uniform_subtype RawSucceeds successfulRawConditioningWitness,
    PMF.map_comp]
  have hfun : boundedValueOrFirst ∘ (Subtype.val : SuccessfulRawAttempts → RawAttempts) =
      successfulRawValue := by
    funext xs
    exact boundedValueOrFirst_eq_successfulRawValue xs
  rw [hfun]
  exact successfulRawAttempts_value_uniform

/-! ## Independent products: QM31 and the 1023 Component-C coordinates -/

/-- Conjugate the successful-result fibre transposition back through the
literal raw-candidate equivalence. -/
def successfulRawValueFibreEquiv (b b₀ : M31Value) :
    {xs : SuccessfulRawAttempts // successfulRawValue xs = b} ≃
      {xs : SuccessfulRawAttempts // successfulRawValue xs = b₀} :=
  ((successfulRawResultEquiv.subtypeEquiv fun xs => by
      rw [successfulValue_successfulRawResultEquiv])).trans
    ((successfulValueFibreEquiv b b₀).trans
      (successfulRawResultEquiv.subtypeEquiv fun xs => by
        rw [successfulValue_successfulRawResultEquiv]).symm)

/-- A fibre of a pointwise function is the product of its coordinate fibres. -/
def pointwiseFibrePiEquiv {I S V : Type*} (f : S → V) (w : I → V) :
    {x : I → S // (fun i => f (x i)) = w} ≃
      ((i : I) → {s : S // f s = w i}) where
  toFun x i := ⟨x.1 i, congrFun x.2 i⟩
  invFun x := ⟨fun i => (x i).1, funext fun i => (x i).2⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    funext i
    apply Subtype.ext
    rfl

/-- Coordinatewise fibre equivalences induce an equivalence of the whole
pointwise-output fibres. -/
def pointwiseFibreEquiv {I S V : Type*} (f : S → V)
    (h : ∀ b b₀, {s : S // f s = b} ≃ {s : S // f s = b₀})
    (w w₀ : I → V) :
    {x : I → S // (fun i => f (x i)) = w} ≃
      {x : I → S // (fun i => f (x i)) = w₀} :=
  (pointwiseFibrePiEquiv f w).trans
    ((Equiv.piCongrRight fun i => h (w i) (w₀ i)).trans
      (pointwiseFibrePiEquiv f w₀).symm)

/-- Any finite family of independently conditioned successful M31 calls has
the exact joint product-uniform law.  Independence is represented by the
uniform law on the full function space, not inferred from marginal laws. -/
theorem successfulCalls_joint_uniform {I : Type*} [Fintype I] [Nonempty I]
    [DecidableEq I] :
    (PMF.uniformOfFintype (I → SuccessfulRawAttempts)).map
        (fun calls i => successfulRawValue (calls i)) =
      PMF.uniformOfFintype (I → M31Value) := by
  let w₀ : I → M31Value := fun _ => firstM31Value
  exact uniform_map_of_equiv_fibres
    (fun (calls : I → SuccessfulRawAttempts) i => successfulRawValue (calls i)) w₀
    (fun w => pointwiseFibreEquiv successfulRawValue successfulRawValueFibreEquiv w w₀)

abbrev qm31LimbCount : Nat := 4
abbrev QM31Limbs := Fin qm31LimbCount → M31Value
abbrev SuccessfulQM31Calls := Fin qm31LimbCount → SuccessfulRawAttempts

/-- Four independently conditioned successful M31 calls give the exact
uniform four-limb representation used to construct one QM31 coordinate. -/
theorem successfulQM31Limbs_joint_uniform :
    (PMF.uniformOfFintype SuccessfulQM31Calls).map
        (fun calls i => successfulRawValue (calls i)) =
      PMF.uniformOfFintype QM31Limbs :=
  successfulCalls_joint_uniform

/-- Number of free QM31 coordinates sampled before deriving Component C's
pivot coordinate. -/
abbrev componentCFreeCoordinateCount : Nat := 1023

/-- One independent bounded M31 call for every limb of every free QM31
coordinate. -/
abbrev ComponentCCallIndex := Fin componentCFreeCoordinateCount × Fin qm31LimbCount

abbrev SuccessfulComponentCCalls := ComponentCCallIndex → SuccessfulRawAttempts

/-- The full 1023×4 successful-call family has the exact joint uniform law;
in particular conditioning the block experiment has introduced no coordinate
correlations. -/
theorem successfulComponentCCalls_joint_uniform :
    (PMF.uniformOfFintype SuccessfulComponentCCalls).map
        (fun calls i => successfulRawValue (calls i)) =
      PMF.uniformOfFintype (ComponentCCallIndex → M31Value) :=
  successfulCalls_joint_uniform

/-- Reassociate the flat 4092-limb representation into 1023 four-limb QM31
coordinates. -/
def componentCFlatToCoordinates :
    (ComponentCCallIndex → M31Value) ≃
      (Fin componentCFreeCoordinateCount → QM31Limbs) :=
  Equiv.curry _ _ _

/-- The exact successful product law in the deployed 1023-coordinate shape. -/
theorem successfulComponentCCoordinates_joint_uniform :
    (PMF.uniformOfFintype SuccessfulComponentCCalls).map
        (fun calls coordinate limb => successfulRawValue (calls (coordinate, limb))) =
      PMF.uniformOfFintype
        (Fin componentCFreeCoordinateCount → QM31Limbs) := by
  calc
    (PMF.uniformOfFintype SuccessfulComponentCCalls).map
        (fun calls coordinate limb => successfulRawValue (calls (coordinate, limb))) =
      ((PMF.uniformOfFintype SuccessfulComponentCCalls).map
        (fun calls i => successfulRawValue (calls i))).map componentCFlatToCoordinates := by
          rw [PMF.map_comp]
          rfl
    _ = (PMF.uniformOfFintype (ComponentCCallIndex → M31Value)).map
        componentCFlatToCoordinates := by rw [successfulComponentCCalls_joint_uniform]
    _ = PMF.uniformOfFintype
        (Fin componentCFreeCoordinateCount → QM31Limbs) :=
      AspisV5RankOneOpeningHiding.uniform_map_equiv componentCFlatToCoordinates

/-! ### Literal conditioning on whole Component-C success
-/

abbrev ComponentCRawBlocks := ComponentCCallIndex → RawAttempts

/-! ### Exact `u32`-to-low31 source projection -/

abbrev RawU32Attempts := Fin retryLimit → RawWord
abbrev RawHighBitAttempts := Fin retryLimit → RawHighBit
abbrev ComponentCRawU32Blocks := ComponentCCallIndex → RawU32Attempts
abbrev ComponentCRawHighBitBlocks := ComponentCCallIndex → RawHighBitAttempts

@[simp] theorem rawCandidateHighBitEquiv_symm_fst (word : RawWord) :
    (rawCandidateHighBitEquiv.symm word).1 = low31Candidate word := by
  simpa using
    (low31Candidate_rawCandidateHighBitEquiv
      (rawCandidateHighBitEquiv.symm word)).symm

/-- Decompose all sixteen words used by one bounded call into the low-31-bit
candidates consumed by rejection sampling and the discarded high bits. -/
def rawU32AttemptsDecompositionEquiv :
    RawU32Attempts ≃ RawAttempts × RawHighBitAttempts :=
  (Equiv.piCongrRight fun _ => rawCandidateHighBitEquiv.symm).trans
    pointwiseProdEquiv

/-- Decompose the full 4092×16 preallocated `u32` experiment. -/
def componentCRawU32DecompositionEquiv :
    ComponentCRawU32Blocks ≃ ComponentCRawBlocks × ComponentCRawHighBitBlocks :=
  (Equiv.piCongrRight fun _ => rawU32AttemptsDecompositionEquiv).trans
    pointwiseProdEquiv

/-- Apply Rust's low-31-bit mask at every preallocated word slot. -/
def componentCRawU32Low31 (raw : ComponentCRawU32Blocks) : ComponentCRawBlocks :=
  fun call attempt => low31Candidate (raw call attempt)

@[simp] theorem componentCRawU32DecompositionEquiv_fst
    (raw : ComponentCRawU32Blocks) :
    (componentCRawU32DecompositionEquiv raw).1 = componentCRawU32Low31 raw := by
  funext call attempt
  exact rawCandidateHighBitEquiv_symm_fst (raw call attempt)

/-- Exact whole-experiment statement: a uniform family of 4092×16 `u32`
words maps to the joint uniform family of low-31-bit candidates.  This proves
joint independence directly on the full function space; it does not infer it
from one-word marginals. -/
theorem uniformComponentCRawU32Blocks_low31_eq_uniform :
    (PMF.uniformOfFintype ComponentCRawU32Blocks).map componentCRawU32Low31 =
      PMF.uniformOfFintype ComponentCRawBlocks := by
  calc
    (PMF.uniformOfFintype ComponentCRawU32Blocks).map componentCRawU32Low31 =
        (PMF.uniformOfFintype ComponentCRawU32Blocks).map
          (Prod.fst ∘ componentCRawU32DecompositionEquiv) := by
            exact congrArg
              (fun f => (PMF.uniformOfFintype ComponentCRawU32Blocks).map f)
              (funext fun raw =>
                (componentCRawU32DecompositionEquiv_fst raw).symm)
    _ = ((PMF.uniformOfFintype ComponentCRawU32Blocks).map
          componentCRawU32DecompositionEquiv).map Prod.fst := by
            rw [PMF.map_comp]
    _ = (PMF.uniformOfFintype
          (ComponentCRawBlocks × ComponentCRawHighBitBlocks)).map Prod.fst := by
            rw [AspisV5RankOneOpeningHiding.uniform_map_equiv
              componentCRawU32DecompositionEquiv]
    _ = PMF.uniformOfFintype ComponentCRawBlocks := uniform_prod_map_fst

/-- Every one of the 4092 preallocated bounded-call blocks succeeds. -/
def AllComponentCBlocksSucceed (raw : ComponentCRawBlocks) : Prop :=
  ∀ i, RawSucceeds (raw i)

instance (raw : ComponentCRawBlocks) : Decidable (AllComponentCBlocksSucceed raw) := by
  unfold AllComponentCBlocksSucceed
  infer_instance

abbrev SuccessfulComponentCBlockExperiment :=
  {raw : ComponentCRawBlocks // AllComponentCBlocksSucceed raw}

/-- Whole-experiment success is exactly a function assigning one successful
bounded-call block to every Component-C limb. -/
def successfulComponentCBlockEquiv :
    SuccessfulComponentCBlockExperiment ≃ SuccessfulComponentCCalls where
  toFun raw i := ⟨raw.1 i, raw.2 i⟩
  invFun calls := ⟨fun i => (calls i).1, fun i => (calls i).2⟩
  left_inv raw := by
    apply Subtype.ext
    rfl
  right_inv calls := by
    funext i
    apply Subtype.ext
    rfl

/-- Concrete whole-experiment success witness. -/
def successfulComponentCBlockExample : SuccessfulComponentCBlockExperiment :=
  successfulComponentCBlockEquiv.symm (fun _ => successfulRawAttemptsExample)

instance : Nonempty SuccessfulComponentCBlockExperiment :=
  ⟨successfulComponentCBlockExample⟩

/-- Whole-experiment success stated directly on the preallocated `u32`
words.  Only the low 31 bits affect this predicate. -/
def AllComponentCRawU32BlocksSucceed (raw : ComponentCRawU32Blocks) : Prop :=
  AllComponentCBlocksSucceed (componentCRawU32Low31 raw)

instance (raw : ComponentCRawU32Blocks) :
    Decidable (AllComponentCRawU32BlocksSucceed raw) := by
  unfold AllComponentCRawU32BlocksSucceed
  infer_instance

abbrev SuccessfulComponentCRawU32BlockExperiment :=
  {raw : ComponentCRawU32Blocks // AllComponentCRawU32BlocksSucceed raw}

/-- Conditioning the full `u32` experiment on success leaves exactly a
successful low31 experiment paired with all discarded high bits.  This is
the load-bearing product decomposition behind the literal conditioned-`u32`
capstone below. -/
def successfulComponentCRawU32DecompositionEquiv :
    SuccessfulComponentCRawU32BlockExperiment ≃
      SuccessfulComponentCBlockExperiment × ComponentCRawHighBitBlocks where
  toFun raw :=
    (⟨(componentCRawU32DecompositionEquiv raw.1).1, by
      simpa [AllComponentCRawU32BlocksSucceed] using raw.2⟩,
      (componentCRawU32DecompositionEquiv raw.1).2)
  invFun x :=
    ⟨componentCRawU32DecompositionEquiv.symm (x.1.1, x.2), by
      unfold AllComponentCRawU32BlocksSucceed
      rw [← componentCRawU32DecompositionEquiv_fst,
        componentCRawU32DecompositionEquiv.apply_symm_apply]
      exact x.1.2⟩
  left_inv raw := by
    apply Subtype.ext
    exact componentCRawU32DecompositionEquiv.symm_apply_apply raw.1
  right_inv x := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst
        (componentCRawU32DecompositionEquiv.apply_symm_apply (x.1.1, x.2))
    · change
        (componentCRawU32DecompositionEquiv
          (componentCRawU32DecompositionEquiv.symm (x.1.1, x.2))).2 = x.2
      exact congrArg Prod.snd
        (componentCRawU32DecompositionEquiv.apply_symm_apply (x.1.1, x.2))

/-- Concrete successful `u32` block experiment. -/
def successfulComponentCRawU32BlockExample :
    SuccessfulComponentCRawU32BlockExperiment :=
  successfulComponentCRawU32DecompositionEquiv.symm
    (successfulComponentCBlockExample, fun _ _ => 0)

instance : Nonempty SuccessfulComponentCRawU32BlockExperiment :=
  ⟨successfulComponentCRawU32BlockExample⟩

theorem successfulComponentCRawU32BlockConditioningWitness :
    ∃ raw ∈ {raw : ComponentCRawU32Blocks |
        AllComponentCRawU32BlocksSucceed raw},
      raw ∈ (PMF.uniformOfFintype ComponentCRawU32Blocks).support :=
  ⟨successfulComponentCRawU32BlockExample.1,
    successfulComponentCRawU32BlockExample.2,
    PMF.mem_support_uniformOfFintype _⟩

theorem successfulComponentCBlockConditioningWitness :
    ∃ raw ∈ {raw : ComponentCRawBlocks | AllComponentCBlocksSucceed raw},
      raw ∈ (PMF.uniformOfFintype ComponentCRawBlocks).support :=
  ⟨successfulComponentCBlockExample.1, successfulComponentCBlockExample.2,
    PMF.mem_support_uniformOfFintype _⟩

/-- Flat 4092-limb output of the preallocated block experiment. -/
def componentCBlockValuesOrFirst (raw : ComponentCRawBlocks) :
    ComponentCCallIndex → M31Value :=
  fun i => boundedValueOrFirst (raw i)

/-- Output of the equivalent family of proved-successful calls. -/
def successfulComponentCValues (calls : SuccessfulComponentCCalls) :
    ComponentCCallIndex → M31Value :=
  fun i => successfulRawValue (calls i)

theorem componentCBlockValues_eq_successfulValues
    (raw : SuccessfulComponentCBlockExperiment) :
    componentCBlockValuesOrFirst raw.1 =
      successfulComponentCValues (successfulComponentCBlockEquiv raw) := by
  funext i
  exact boundedValueOrFirst_eq_successfulRawValue ⟨raw.1 i, raw.2 i⟩

/-- Literal conditional law of all 4092 outputs, conditioning once on success
of the entire preallocated-block experiment. -/
noncomputable def successfulComponentCBlockLaw :
    PMF (ComponentCCallIndex → M31Value) :=
  ((PMF.uniformOfFintype ComponentCRawBlocks).filter
    {raw : ComponentCRawBlocks | AllComponentCBlocksSucceed raw}
      successfulComponentCBlockConditioningWitness).map componentCBlockValuesOrFirst

/-- Output map stated directly on the full preallocated `u32` experiment. -/
def componentCRawU32BlockValuesOrFirst (raw : ComponentCRawU32Blocks) :
    ComponentCCallIndex → M31Value :=
  componentCBlockValuesOrFirst (componentCRawU32Low31 raw)

/-- Literal law obtained by conditioning the entire preallocated `u32`
experiment once on all 4092 bounded calls succeeding. -/
noncomputable def successfulComponentCRawU32BlockLaw :
    PMF (ComponentCCallIndex → M31Value) :=
  ((PMF.uniformOfFintype ComponentCRawU32Blocks).filter
    {raw : ComponentCRawU32Blocks | AllComponentCRawU32BlocksSucceed raw}
      successfulComponentCRawU32BlockConditioningWitness).map
        componentCRawU32BlockValuesOrFirst

theorem componentCRawU32BlockValues_eq_decomposedValues
    (raw : SuccessfulComponentCRawU32BlockExperiment) :
    componentCRawU32BlockValuesOrFirst raw.1 =
      componentCBlockValuesOrFirst
        (successfulComponentCRawU32DecompositionEquiv raw).1.1 := by
  unfold componentCRawU32BlockValuesOrFirst
  rw [← componentCRawU32DecompositionEquiv_fst]
  rfl

/-- The literal successful-`u32` law is exactly the already analysed
successful low31-candidate law.  The discarded high-bit factor vanishes by
uniform product projection; no independence or conditioning step is left
implicit. -/
theorem successfulComponentCRawU32BlockLaw_eq_candidateBlockLaw :
    successfulComponentCRawU32BlockLaw = successfulComponentCBlockLaw := by
  rw [successfulComponentCRawU32BlockLaw,
    uniform_filter_eq_uniform_subtype AllComponentCRawU32BlocksSucceed
      successfulComponentCRawU32BlockConditioningWitness,
    successfulComponentCBlockLaw,
    uniform_filter_eq_uniform_subtype AllComponentCBlocksSucceed
      successfulComponentCBlockConditioningWitness,
    PMF.map_comp, PMF.map_comp]
  have hfun : componentCRawU32BlockValuesOrFirst ∘
      (Subtype.val : SuccessfulComponentCRawU32BlockExperiment →
        ComponentCRawU32Blocks) =
      (componentCBlockValuesOrFirst ∘ Subtype.val ∘ Prod.fst) ∘
        successfulComponentCRawU32DecompositionEquiv := by
    funext raw
    exact componentCRawU32BlockValues_eq_decomposedValues raw
  rw [hfun, ← PMF.map_comp,
    AspisV5RankOneOpeningHiding.uniform_map_equiv
      successfulComponentCRawU32DecompositionEquiv]
  have hproj := congrArg
    (fun law : PMF SuccessfulComponentCBlockExperiment =>
      law.map (componentCBlockValuesOrFirst ∘ Subtype.val))
    (uniform_prod_map_fst
      (A := SuccessfulComponentCBlockExperiment)
      (B := ComponentCRawHighBitBlocks))
  simpa [PMF.map_comp, Function.comp_def] using hproj

/-- **Whole-success conditioning introduces no correlations.**  Under the
explicit preallocated iid block experiment, conditioning once on every call
succeeding leaves the full 4092-limb output exactly product-uniform. -/
theorem successfulComponentCBlockLaw_eq_joint_uniform :
    successfulComponentCBlockLaw =
      PMF.uniformOfFintype (ComponentCCallIndex → M31Value) := by
  rw [successfulComponentCBlockLaw,
    uniform_filter_eq_uniform_subtype AllComponentCBlocksSucceed
      successfulComponentCBlockConditioningWitness,
    PMF.map_comp]
  have hfun : componentCBlockValuesOrFirst ∘
      (Subtype.val : SuccessfulComponentCBlockExperiment → ComponentCRawBlocks) =
      successfulComponentCValues ∘ successfulComponentCBlockEquiv := by
    funext raw
    exact componentCBlockValues_eq_successfulValues raw
  rw [hfun, ← PMF.map_comp,
    AspisV5RankOneOpeningHiding.uniform_map_equiv successfulComponentCBlockEquiv]
  exact successfulComponentCCalls_joint_uniform

/-- Literal conditioned-`u32` capstone: conditioning once on success of all
4092 bounded samplers leaves the complete successful limb law exactly joint
uniform. -/
theorem successfulComponentCRawU32BlockLaw_eq_joint_uniform :
    successfulComponentCRawU32BlockLaw =
      PMF.uniformOfFintype (ComponentCCallIndex → M31Value) :=
  successfulComponentCRawU32BlockLaw_eq_candidateBlockLaw.trans
    successfulComponentCBlockLaw_eq_joint_uniform

/-- The same whole-success theorem in 1023×4 QM31-coordinate shape. -/
theorem successfulComponentCBlockCoordinates_eq_joint_uniform :
    successfulComponentCBlockLaw.map componentCFlatToCoordinates =
      PMF.uniformOfFintype
        (Fin componentCFreeCoordinateCount → QM31Limbs) := by
  rw [successfulComponentCBlockLaw_eq_joint_uniform]
  exact AspisV5RankOneOpeningHiding.uniform_map_equiv componentCFlatToCoordinates

/-! ### Exact abort accounting for the preallocated-block experiment -/

abbrev componentCCallCount : Nat :=
  componentCFreeCoordinateCount * qm31LimbCount

abbrev boundedCallRawCount : Nat := rawCandidateCount ^ retryLimit

theorem componentCCallIndex_card : Fintype.card ComponentCCallIndex = componentCCallCount := by
  simp [ComponentCCallIndex, componentCCallCount]

theorem componentCCallCount_eq : componentCCallCount = 4092 := by
  norm_num [componentCCallCount, componentCFreeCoordinateCount, qm31LimbCount]

theorem boundedCallRawCount_eq_pow_two : boundedCallRawCount = 2 ^ 496 := by
  change (2 ^ 31) ^ 16 = 2 ^ 496
  rw [← pow_mul]

theorem successfulRawAttempts_card :
    Fintype.card SuccessfulRawAttempts = boundedCallRawCount - 1 := by
  let e : SuccessfulRawAttempts ≃ {xs : RawAttempts // xs ≠ allRejected} :=
    Equiv.subtypeEquivRight fun xs =>
      not_congr (boundedSample_eq_none_iff_eq_allRejected xs)
  rw [Fintype.card_congr e, Fintype.card_subtype_compl (fun xs : RawAttempts => xs = allRejected)]
  simp [boundedCallRawCount]

theorem componentCRawBlocks_card :
    Fintype.card ComponentCRawBlocks = boundedCallRawCount ^ componentCCallCount := by
  simp [ComponentCRawBlocks, boundedCallRawCount, componentCCallCount,
    RawAttempts]

theorem successfulComponentCBlockExperiment_card :
    Fintype.card SuccessfulComponentCBlockExperiment =
      (boundedCallRawCount - 1) ^ componentCCallCount := by
  rw [Fintype.card_congr successfulComponentCBlockEquiv]
  simp [SuccessfulComponentCCalls, successfulRawAttempts_card, componentCCallCount]

/-- Abort of at least one preallocated bounded-call block. -/
def ComponentCBlockAborts (raw : ComponentCRawBlocks) : Prop :=
  ¬ AllComponentCBlocksSucceed raw

instance (raw : ComponentCRawBlocks) : Decidable (ComponentCBlockAborts raw) := by
  unfold ComponentCBlockAborts
  infer_instance

theorem componentCBlockAbortFibre_card :
    Fintype.card {raw : ComponentCRawBlocks // ComponentCBlockAborts raw} =
      boundedCallRawCount ^ componentCCallCount -
        (boundedCallRawCount - 1) ^ componentCCallCount := by
  let e : {raw : ComponentCRawBlocks // ComponentCBlockAborts raw} ≃
      {raw : ComponentCRawBlocks // ¬ AllComponentCBlocksSucceed raw} :=
    Equiv.subtypeEquivRight fun _ => Iff.rfl
  rw [Fintype.card_congr e, Fintype.card_subtype_compl AllComponentCBlocksSucceed,
    componentCRawBlocks_card, successfulComponentCBlockExperiment_card]

/-- Exact total abort mass for the ideal preallocated iid-block experiment. -/
noncomputable def componentCBlockAbortMass : ℝ≥0∞ :=
  (PMF.uniformOfFintype ComponentCRawBlocks).toOuterMeasure
    {raw : ComponentCRawBlocks | ComponentCBlockAborts raw}

/-- Exact finite-ratio formula.  This is stronger than a union bound and keeps
all 4092 calls and all 16 retries explicit. -/
theorem componentCBlockAbortMass_exact :
    componentCBlockAbortMass =
      ((boundedCallRawCount ^ componentCCallCount -
          (boundedCallRawCount - 1) ^ componentCCallCount : Nat) : ℝ≥0∞) /
        (boundedCallRawCount ^ componentCCallCount : Nat) := by
  have hcard : Fintype.card ↥{raw : ComponentCRawBlocks | ComponentCBlockAborts raw} =
      Fintype.card {raw : ComponentCRawBlocks // ComponentCBlockAborts raw} :=
    Fintype.card_congr (Equiv.refl _)
  rw [componentCBlockAbortMass, PMF.toOuterMeasure_uniformOfFintype_apply, hcard,
    componentCBlockAbortFibre_card, componentCRawBlocks_card]

/-- Fully numeric symbolic form:
`1 - (1 - 2^-496)^4092`, represented without lossy real arithmetic as the
exact ratio of two natural counts. -/
theorem componentCBlockAbortMass_exact_pow_two :
    componentCBlockAbortMass =
      (((2 ^ 496) ^ 4092 - ((2 ^ 496) - 1) ^ 4092 : Nat) : ℝ≥0∞) /
        (((2 ^ 496) ^ 4092 : Nat) : ℝ≥0∞) := by
  rw [componentCBlockAbortMass_exact, boundedCallRawCount_eq_pow_two,
    componentCCallCount_eq]

/-! ### Deployment-facing seams (not discharged here) -/

/-- Named code/model seam for Rust's `word & 0x7fff_ffff` operation.  The
finite theorem above uses reduction modulo `2^31`; identifying the executable
bit-mask with that map is deliberately explicit. -/
def RustLow31MaskMatches (rustLow31 : RawWord → RawCandidate) : Prop :=
  rustLow31 = low31Candidate

/-- Exact representation equivalence needed to reinterpret four canonical
M31 limbs as the deployed QM31 field value.  The theorem is generic because
the Rust tower-field representation is a correspondence obligation, not a
definition invented in Lean. -/
def componentCCoordinateRepresentationEquiv {K : Type*} (e : QM31Limbs ≃ K) :
    (Fin componentCFreeCoordinateCount → QM31Limbs) ≃
      (Fin componentCFreeCoordinateCount → K) :=
  Equiv.piCongrRight fun _ => e

theorem successfulComponentCCoordinates_uniform_under_representation
    {K : Type*} [Fintype K] [Nonempty K] (e : QM31Limbs ≃ K) :
    (successfulComponentCBlockLaw.map componentCFlatToCoordinates).map
        (componentCCoordinateRepresentationEquiv e) =
      PMF.uniformOfFintype (Fin componentCFreeCoordinateCount → K) := by
  rw [successfulComponentCBlockCoordinates_eq_joint_uniform]
  exact AspisV5RankOneOpeningHiding.uniform_map_equiv
    (componentCCoordinateRepresentationEquiv e)

/-- The proved-successful rejection-sampler law, packaged with the exact
four-limb↔field representation expected by the Component-C sampler kernel. -/
noncomputable def successfulComponentCFreeCoordinateLaw
    {K : Type*} [Fintype K] [Nonempty K] (e : QM31Limbs ≃ K) :
    PMF (AspisV5ComponentCSamplerKernel.FreeCoordinates K) :=
  (successfulComponentCRawU32BlockLaw.map componentCFlatToCoordinates).map
    (componentCCoordinateRepresentationEquiv e)

/-- Direct bridge into the sampler-kernel interface.  The exact rejection
calculation discharges the abstract successful-free-coordinate law without a
manual rewrite.  Rust entropy, stopping-time and codec correspondence remain
the separate seams below. -/
theorem successfulComponentCFreeCoordinateLaw_isIndependentUniform
    {K : Type*} [Field K] [Fintype K]
    (e : QM31Limbs ≃ K) :
    AspisV5ComponentCSamplerKernel.SuccessfulFreeCoordinatesAreIndependentUniform
      (successfulComponentCFreeCoordinateLaw e) := by
  classical
  rw [AspisV5ComponentCSamplerKernel.SuccessfulFreeCoordinatesAreIndependentUniform,
    successfulComponentCFreeCoordinateLaw,
    AspisV5ComponentCSamplerKernel.idealFreeCoordinateLaw]
  rw [successfulComponentCRawU32BlockLaw_eq_candidateBlockLaw]
  exact successfulComponentCCoordinates_uniform_under_representation e

/-- Block-experiment capstone: after an exact four-limb↔field representation
equivalence and the already checked derived-pivot encoder, whole-success
conditioning induces the exact uniform law on `ker ell`.  This remains an
ideal preallocated-block result until the deployment seams below are supplied. -/
theorem successfulComponentCKernelLaw_eq_uniform_under_representation
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (e : QM31Limbs ≃ K) (ell : (Fin 1024 → K) →ₗ[K] K) (pivot : Fin 1024)
    (hpivot : ell (Pi.single pivot 1) = 1) :
    (((successfulComponentCBlockLaw.map componentCFlatToCoordinates).map
        (componentCCoordinateRepresentationEquiv e)).map
          (AspisV5ComponentCSamplerKernel.componentCEncoderEquiv ell pivot hpivot)) =
      PMF.uniformOfFintype (LinearMap.ker ell) := by
  rw [successfulComponentCCoordinates_uniform_under_representation e]
  exact AspisV5RankOneOpeningHiding.uniform_map_linearEquiv
    (AspisV5ComponentCSamplerKernel.componentCEncoderEquiv ell pivot hpivot)

/-- Named code/model interface for the four-limb tower representation,
coordinate order, and deployed byte codec.  Nothing in this leaf proves it
for the Rust `QM31 { c0: (a,b), c1: (c,d) }` layout. -/
def DeployedQM31LimbOrderAndCodecMatch {K Bytes : Type*}
    (e : QM31Limbs ≃ K) (rustAssemble : QM31Limbs → K)
    (encode : K → Bytes) (decode : Bytes → Option K) : Prop :=
  rustAssemble = e ∧ ∀ k, decode (encode k) = some k

/-- Named honest interface for the variable-consumption Rust stream.  Rust
uses a stopping-time stream: a successful call consumes between 1 and 16
words, whereas the exact experiment above preallocates 16 candidates per
logical call.  Equality of the conditioned laws follows from an iid stream
and stopping-time argument, but is deliberately *not* asserted here. -/
def RustIidStreamStoppingTimeMatchesBlockExperiment
    (rustSuccessfulLaw : PMF
      (Fin componentCFreeCoordinateCount → QM31Limbs)) : Prop :=
  rustSuccessfulLaw = successfulComponentCBlockLaw.map componentCFlatToCoordinates

/-- Once the stopping-time/raw-stream interface is supplied, the Rust-facing
successful law is exactly product-uniform. -/
theorem rustSuccessfulLaw_eq_uniform_of_stoppingTime_interface
    (rustSuccessfulLaw : PMF
      (Fin componentCFreeCoordinateCount → QM31Limbs))
    (hstream : RustIidStreamStoppingTimeMatchesBlockExperiment rustSuccessfulLaw) :
    rustSuccessfulLaw = PMF.uniformOfFintype
      (Fin componentCFreeCoordinateCount → QM31Limbs) := by
  rw [RustIidStreamStoppingTimeMatchesBlockExperiment] at hstream
  exact hstream.trans successfulComponentCBlockCoordinates_eq_joint_uniform

/-- Separate computational seam for the production entropy expander.  A
finite 256-bit seed cannot produce the information-theoretically uniform law
on this enormous raw experiment.  The honest production claim is therefore a
computational hybrid supplied by an external CSPRNG/PRG assumption, represented
here by the caller's indistinguishability relation `Indist`. -/
def ProductionCSPRGRawU32Pseudorandomness
    (Indist : PMF ComponentCRawU32Blocks → PMF ComponentCRawU32Blocks → Prop)
    (productionRawU32Law : PMF ComponentCRawU32Blocks) : Prop :=
  Indist productionRawU32Law (PMF.uniformOfFintype ComponentCRawU32Blocks)

/-! ### Negative tooth -/

def secondM31Value : M31Value := ⟨1, by
  norm_num [m31Modulus, rawCandidateCount]⟩

theorem firstM31Value_ne_second : firstM31Value ≠ secondM31Value := by
  intro h
  have := congrArg Fin.val h
  norm_num [firstM31Value, secondM31Value] at this

/-- A deterministic successful source is not uniform.  Thus the iid/uniform
raw-source premise used above is load-bearing. -/
theorem deterministic_successful_source_not_uniform :
    (PMF.pure firstM31Value : PMF M31Value) ≠ PMF.uniformOfFintype M31Value := by
  intro h
  have hp := congrArg (fun law : PMF M31Value => law secondM31Value) h
  rw [PMF.pure_apply_of_ne firstM31Value secondM31Value firstM31Value_ne_second.symm,
    PMF.uniformOfFintype_apply] at hp
  have hcard : Fintype.card M31Value = m31Modulus := Fintype.card_fin _
  rw [hcard] at hp
  exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _) hp.symm

/-! ## Axiom audit -/

#print axioms boundedOutputLaw_abort_exact_pow_two
#print axioms uniformRawWord_low31_eq_uniform
#print axioms successfulM31Law_eq_uniform
#print axioms successfulQM31Limbs_joint_uniform
#print axioms successfulComponentCCoordinates_joint_uniform
#print axioms uniformComponentCRawU32Blocks_low31_eq_uniform
#print axioms successfulComponentCRawU32BlockLaw_eq_candidateBlockLaw
#print axioms successfulComponentCRawU32BlockLaw_eq_joint_uniform
#print axioms successfulComponentCBlockLaw_eq_joint_uniform
#print axioms componentCBlockAbortMass_exact_pow_two
#print axioms successfulComponentCFreeCoordinateLaw_isIndependentUniform
#print axioms successfulComponentCKernelLaw_eq_uniform_under_representation
#print axioms rustSuccessfulLaw_eq_uniform_of_stoppingTime_interface
#print axioms RustLow31MaskMatches
#print axioms DeployedQM31LimbOrderAndCodecMatch
#print axioms ProductionCSPRGRawU32Pseudorandomness
#print axioms deterministic_successful_source_not_uniform

end AspisV5ComponentCRejectionSampler

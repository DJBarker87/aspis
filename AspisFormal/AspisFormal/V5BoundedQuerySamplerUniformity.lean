import AspisFormal.V5WithoutReplacementQuerySoundness

/-!
# Uniformity of the ideal bounded query sampler

This file models the finite probabilistic experiment behind
`challenge_queries_without_replacement`: draw `maxDraws` independent uniform
elements of `Fin n`, keep first occurrences in their original order, and
return the first `q` distinct values when they exist.

The sample space is the finite type `Fin maxDraws → Fin n`. Giving every
draw tuple equal mass is exactly the independent uniform experiment. The main
result proves that, after conditioning on success, every ordered injection
`Fin q ↪ Fin n` has the same probability. It then identifies that probability
as the reciprocal of the number of ordered injections.

This is only the ideal finite experiment. It does not claim that SHA-256
blocks are independent uniform words or that the Rust transcript implements
this model. It also does not model the exact number of SHA-256 blocks consumed
or the resulting transcript state.
-/

namespace AspisV5BoundedQuerySamplerUniformity

/-- A complete bounded sequence of ideal draws. -/
abbrev Draws (n maxDraws : Nat) := Fin maxDraws → Fin n

/-- An ordered query result with no repeated position. -/
abbrev QuerySchedule (q n : Nat) := Fin q ↪ Fin n

/-- Keep the first occurrence of each value, in its original order.

`List.dedup` keeps rightmost occurrences, so reversing before and after it
gives the first-occurrence order used by the Rust loop. -/
def firstOccurrences {n : Nat} (xs : List (Fin n)) : List (Fin n) :=
  xs.reverse.dedup.reverse

/-- The bounded sampler's returned list before it is packaged as an
injection. -/
def outputList {n maxDraws : Nat} (q : Nat) (draws : Draws n maxDraws) :
    List (Fin n) :=
  (firstOccurrences (List.ofFn draws)).take q

/-- The bounded sampler succeeds exactly when the draw budget contains at
least `q` distinct values. -/
def Successful {n maxDraws : Nat} (q : Nat) (draws : Draws n maxDraws) : Prop :=
  q ≤ (firstOccurrences (List.ofFn draws)).length

/-- A draw tuple returns this exact ordered schedule. -/
def Produces {q n maxDraws : Nat} (schedule : QuerySchedule q n)
    (draws : Draws n maxDraws) : Prop :=
  outputList q draws = List.ofFn schedule

theorem firstOccurrences_nodup {n : Nat} (xs : List (Fin n)) :
    (firstOccurrences xs).Nodup := by
  simp [firstOccurrences, List.nodup_dedup]

theorem outputList_nodup {n maxDraws q : Nat} (draws : Draws n maxDraws) :
    (outputList q draws).Nodup := by
  unfold outputList
  exact List.Nodup.sublist (List.take_sublist q _)
    (firstOccurrences_nodup (List.ofFn draws))

theorem outputList_length_of_success {n maxDraws q : Nat}
    (draws : Draws n maxDraws) (h : Successful q draws) :
    (outputList q draws).length = q := by
  exact List.length_take_of_le h

/-- Turn a length-`q`, duplicate-free list into its ordered injection. -/
def scheduleOfList {q n : Nat} (xs : List (Fin n))
    (hlen : xs.length = q) (hnodup : xs.Nodup) : QuerySchedule q n where
  toFun i := xs.get (Fin.cast hlen.symm i)
  inj' := hnodup.injective_get.comp (Fin.cast_injective hlen.symm)

theorem ofFn_scheduleOfList {q n : Nat} (xs : List (Fin n))
    (hlen : xs.length = q) (hnodup : xs.Nodup) :
    List.ofFn (scheduleOfList xs hlen hnodup) = xs := by
  change List.ofFn (fun i : Fin q ↦ xs.get (Fin.cast hlen.symm i)) = xs
  rw [← List.ofFn_congr hlen xs.get]
  exact List.ofFn_get xs

/-- The ordered injection returned by a successful draw tuple. -/
def successfulSchedule {q n maxDraws : Nat} (draws : Draws n maxDraws)
    (h : Successful q draws) : QuerySchedule q n :=
  scheduleOfList (outputList q draws) (outputList_length_of_success draws h)
    (outputList_nodup draws)

theorem successfulSchedule_produced {q n maxDraws : Nat}
    (draws : Draws n maxDraws) (h : Successful q draws) :
    Produces (successfulSchedule draws h) draws := by
  exact (ofFn_scheduleOfList (outputList q draws)
    (outputList_length_of_success draws h) (outputList_nodup draws)).symm

theorem successful_of_produces {q n maxDraws : Nat}
    (schedule : QuerySchedule q n) (draws : Draws n maxDraws)
    (h : Produces schedule draws) : Successful q draws := by
  have hlen : (outputList q draws).length = q := by
    rw [h]
    simp
  simpa [outputList, Successful] using hlen

theorem successfulSchedule_eq_of_produces {q n maxDraws : Nat}
    (schedule : QuerySchedule q n) (draws : Draws n maxDraws)
    (h : Produces schedule draws) :
    successfulSchedule draws (successful_of_produces schedule draws h) = schedule := by
  have hlists :
      List.ofFn (successfulSchedule draws
        (successful_of_produces schedule draws h)) = List.ofFn schedule := by
    exact (successfulSchedule_produced draws
      (successful_of_produces schedule draws h)).symm.trans h
  have hfunctions := List.ofFn_injective hlists
  apply Function.Embedding.ext
  intro i
  exact congrFun hfunctions i

/-! ## Equivariance under relabelling the population -/

theorem firstOccurrences_map {n : Nat} (e : Equiv.Perm (Fin n))
    (xs : List (Fin n)) :
    firstOccurrences (xs.map e) = (firstOccurrences xs).map e := by
  unfold firstOccurrences
  rw [← List.map_reverse]
  rw [List.dedup_map_of_injective e.injective]
  rw [← List.map_reverse]

/-- Relabel every candidate draw by a permutation of the population. -/
def permuteDraws {n maxDraws : Nat} (e : Equiv.Perm (Fin n)) :
    Draws n maxDraws ≃ Draws n maxDraws where
  toFun draws i := e (draws i)
  invFun draws i := e.symm (draws i)
  left_inv draws := by
    funext i
    simp
  right_inv draws := by
    funext i
    simp

theorem outputList_permute {q n maxDraws : Nat} (e : Equiv.Perm (Fin n))
    (draws : Draws n maxDraws) :
    outputList q (permuteDraws e draws) = (outputList q draws).map e := by
  unfold outputList
  rw [show List.ofFn (permuteDraws e draws) =
      (List.ofFn draws).map e by
    exact List.ofFn_comp' draws e]
  rw [firstOccurrences_map]
  rw [← List.map_take]

theorem successful_permute_iff {q n maxDraws : Nat} (e : Equiv.Perm (Fin n))
    (draws : Draws n maxDraws) :
    Successful q (permuteDraws e draws) ↔ Successful q draws := by
  unfold Successful
  rw [show List.ofFn (permuteDraws e draws) =
      (List.ofFn draws).map e by
    exact List.ofFn_comp' draws e]
  rw [firstOccurrences_map, List.length_map]

theorem produces_permute_iff {q n maxDraws : Nat}
    (source target : QuerySchedule q n) (e : Equiv.Perm (Fin n))
    (he : ∀ i, e (source i) = target i) (draws : Draws n maxDraws) :
    Produces target (permuteDraws e draws) ↔ Produces source draws := by
  have hschedule : List.ofFn target = (List.ofFn source).map e := by
    rw [← List.ofFn_comp']
    exact congrArg List.ofFn (funext fun i ↦ (he i).symm)
  simp only [Produces, outputList_permute, hschedule]
  exact e.injective.list_map.eq_iff

/-! ## Equal fibres and exact conditional probability -/

noncomputable def producingDraws {q n maxDraws : Nat}
    (schedule : QuerySchedule q n) :=
  {draws : Draws n maxDraws // Produces schedule draws}

noncomputable instance producingDrawsFintype {q n maxDraws : Nat}
    (schedule : QuerySchedule q n) :
    Fintype (producingDraws (maxDraws := maxDraws) schedule) := by
  classical
  unfold producingDraws
  infer_instance

noncomputable def successfulDraws (q n maxDraws : Nat) :=
  {draws : Draws n maxDraws // Successful q draws}

noncomputable instance successfulDrawsFintype (q n maxDraws : Nat) :
    Fintype (successfulDraws q n maxDraws) := by
  classical
  unfold successfulDraws
  infer_instance

/-- Relabelling by a population permutation gives a bijection between any
two fixed output fibres. -/
noncomputable def producingDrawsEquiv {q n maxDraws : Nat}
    (source target : QuerySchedule q n) :
    producingDraws (maxDraws := maxDraws) source ≃
      producingDraws (maxDraws := maxDraws) target := by
  classical
  let witness := Equiv.Perm.exists_extending_pair source target
    source.injective target.injective
  let e := Classical.choose witness
  have he := Classical.choose_spec witness
  refine
    { toFun := fun draws ↦
        ⟨permuteDraws e draws.1,
          (produces_permute_iff source target e he draws.1).2 draws.2⟩
      invFun := fun draws ↦
        ⟨permuteDraws e.symm draws.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have he' : ∀ i, e.symm (target i) = source i := by
      intro i
      apply e.injective
      simpa using (he i).symm
    exact (produces_permute_iff target source e.symm he' draws.1).2 draws.2
  · intro draws
    apply Subtype.ext
    funext i
    simp [permuteDraws]
  · intro draws
    apply Subtype.ext
    funext i
    simp [permuteDraws]

theorem producingDraws_card_eq {q n maxDraws : Nat}
    (source target : QuerySchedule q n) :
    Fintype.card (producingDraws (maxDraws := maxDraws) source) =
      Fintype.card (producingDraws (maxDraws := maxDraws) target) := by
  classical
  exact Fintype.card_congr (producingDrawsEquiv source target)

/-- The deterministic schedule returned on the successful sample space. -/
def conditionedOutput {q n maxDraws : Nat} (draws : successfulDraws q n maxDraws) :
    QuerySchedule q n :=
  successfulSchedule draws.1 draws.2

/-- A fibre of `conditionedOutput` is the same data as a raw draw tuple that
produces the fibre's schedule. -/
noncomputable def outputFibreEquivProducing {q n maxDraws : Nat}
    (schedule : QuerySchedule q n) :
    {draws : successfulDraws q n maxDraws // conditionedOutput draws = schedule} ≃
      producingDraws (maxDraws := maxDraws) schedule where
  toFun draws := ⟨draws.1.1, by
    unfold Produces
    calc
      outputList q draws.1.1 = List.ofFn (conditionedOutput draws.1) :=
        successfulSchedule_produced draws.1.1 draws.1.2
      _ = List.ofFn schedule := congrArg
        (fun result : QuerySchedule q n ↦ List.ofFn fun i ↦ result i) draws.2⟩
  invFun draws :=
    ⟨⟨draws.1, successful_of_produces schedule draws.1 draws.2⟩,
      successfulSchedule_eq_of_produces schedule draws.1 draws.2⟩
  left_inv draws := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv draws := by
    apply Subtype.ext
    rfl

/-- Successful draw tuples are exactly a schedule paired with a draw tuple
that produces it. -/
noncomputable def successfulDrawsEquivSigma {q n maxDraws : Nat} :
    successfulDraws q n maxDraws ≃
      Σ schedule : QuerySchedule q n,
        producingDraws (maxDraws := maxDraws) schedule :=
  (Equiv.sigmaFiberEquiv (conditionedOutput (q := q) (n := n)
    (maxDraws := maxDraws))).symm.trans
    (Equiv.sigmaCongrRight outputFibreEquivProducing)

/-- The successful sample space is the number of schedules times the size of
any one schedule fibre. -/
theorem card_successfulDraws_eq_mul_fibre {q n maxDraws : Nat}
    (schedule : QuerySchedule q n) :
    Fintype.card (successfulDraws q n maxDraws) =
      Fintype.card (QuerySchedule q n) *
        Fintype.card (producingDraws (maxDraws := maxDraws) schedule) := by
  classical
  calc
    Fintype.card (successfulDraws q n maxDraws) =
        Fintype.card
          (Σ result : QuerySchedule q n,
            producingDraws (maxDraws := maxDraws) result) :=
      Fintype.card_congr successfulDrawsEquivSigma
    _ = ∑ result : QuerySchedule q n,
          Fintype.card (producingDraws (maxDraws := maxDraws) result) := by
      simp
    _ = ∑ _result : QuerySchedule q n,
          Fintype.card (producingDraws (maxDraws := maxDraws) schedule) := by
      apply Finset.sum_congr rfl
      intro result _
      exact producingDraws_card_eq result schedule
    _ = Fintype.card (QuerySchedule q n) *
          Fintype.card (producingDraws (maxDraws := maxDraws) schedule) := by
      simp

theorem firstOccurrences_eq_self_of_nodup {n : Nat} {xs : List (Fin n)}
    (h : xs.Nodup) : firstOccurrences xs = xs := by
  unfold firstOccurrences
  rw [List.dedup_eq_self.mpr (List.nodup_reverse.mpr h), List.reverse_reverse]

/-- If the budget fits inside the population, the tuple `0,1,...,maxDraws-1`
is a successful outcome. -/
theorem castLE_draws_successful {q n maxDraws : Nat}
    (hq : q ≤ maxDraws) (hbudget : maxDraws ≤ n) :
    Successful q (fun i : Fin maxDraws ↦ Fin.castLE hbudget i) := by
  have hinj : Function.Injective (fun i : Fin maxDraws ↦ Fin.castLE hbudget i) :=
    Fin.castLE_injective _
  have hnodup : (List.ofFn (fun i : Fin maxDraws ↦ Fin.castLE hbudget i)).Nodup :=
    List.nodup_ofFn.mpr hinj
  simp [Successful, firstOccurrences_eq_self_of_nodup hnodup, hq]

/-- Exact finite conditional probability of one schedule under uniformly
sampled bounded draw tuples. -/
noncomputable def conditionedScheduleProbability {q n maxDraws : Nat}
    (schedule : QuerySchedule q n) : ℝ :=
  Fintype.card (producingDraws (maxDraws := maxDraws) schedule) /
    Fintype.card (successfulDraws q n maxDraws)

/-- Conditioned on success, the ideal bounded rejection sampler is exactly
uniform over ordered injections. -/
theorem conditionedScheduleProbability_eq_uniform {q n maxDraws : Nat}
    (schedule : QuerySchedule q n) (hq : q ≤ maxDraws)
    (hbudget : maxDraws ≤ n) :
    conditionedScheduleProbability (maxDraws := maxDraws) schedule =
      (1 : ℝ) / Fintype.card (QuerySchedule q n) := by
  classical
  have hsuccess : 0 < Fintype.card (successfulDraws q n maxDraws) := by
    rw [Fintype.card_pos_iff]
    exact ⟨⟨(fun i : Fin maxDraws ↦ Fin.castLE hbudget i),
      castLE_draws_successful hq hbudget⟩⟩
  have hfactor := card_successfulDraws_eq_mul_fibre
    (maxDraws := maxDraws) schedule
  have hfibre : 0 < Fintype.card
      (producingDraws (maxDraws := maxDraws) schedule) := by
    rw [hfactor] at hsuccess
    exact pos_of_mul_pos_right hsuccess (Nat.zero_le _)
  have hschedule : 0 < Fintype.card (QuerySchedule q n) := by
    rw [Fintype.card_pos_iff]
    exact ⟨schedule⟩
  have hfibreReal :
      (Fintype.card (producingDraws (maxDraws := maxDraws) schedule) : ℝ) ≠ 0 := by
    exact_mod_cast hfibre.ne'
  have hscheduleReal : (Fintype.card (QuerySchedule q n) : ℝ) ≠ 0 := by
    exact_mod_cast hschedule.ne'
  unfold conditionedScheduleProbability
  rw [hfactor]
  rw [Nat.cast_mul]
  field_simp [hfibreReal, hscheduleReal]

/-- The deployed ideal sampler (`q = 18`, `n = 131072`, `maxDraws = 64`) is
uniform after conditioning on returning eighteen distinct values. -/
theorem deployed_q18_conditioned_uniform
    (schedule : QuerySchedule 18 131072) :
    conditionedScheduleProbability (maxDraws := 64) schedule =
      (1 : ℝ) / Fintype.card (QuerySchedule 18 131072) := by
  exact conditionedScheduleProbability_eq_uniform schedule (by norm_num) (by norm_num)

/-! ## Composition with the fixed-bad-set query bound -/

/-- Successful draw tuples whose returned schedule lies entirely in `bad`. -/
def AllOutputQueriesIn {q n maxDraws : Nat} (bad : Finset (Fin n))
    (draws : successfulDraws q n maxDraws) : Prop :=
  AspisV5WithoutReplacementQuerySoundness.AllQueriesIn bad
    (conditionedOutput draws)

noncomputable def successfulBadDraws {q n maxDraws : Nat}
    (bad : Finset (Fin n)) :=
  {draws : successfulDraws q n maxDraws // AllOutputQueriesIn bad draws}

noncomputable instance successfulBadDrawsFintype {q n maxDraws : Nat}
    (bad : Finset (Fin n)) :
    Fintype (successfulBadDraws (q := q) (maxDraws := maxDraws) bad) := by
  classical
  unfold successfulBadDraws
  infer_instance

/-- Exact conditional probability that all returned queries lie in `bad`. -/
noncomputable def conditionedAllQueriesInProbability {q n maxDraws : Nat}
    (bad : Finset (Fin n)) : ℝ :=
  Fintype.card (successfulBadDraws (q := q) (maxDraws := maxDraws) bad) /
    Fintype.card (successfulDraws q n maxDraws)

/-- Restricting the successful-output decomposition to schedules in `bad`
gives a sigma type over exactly those schedules. -/
noncomputable def successfulBadDrawsEquivSigma {q n maxDraws : Nat}
    (bad : Finset (Fin n)) :
    successfulBadDraws (q := q) (maxDraws := maxDraws) bad ≃
      Σ schedule :
          {schedule : QuerySchedule q n //
            AspisV5WithoutReplacementQuerySoundness.AllQueriesIn bad schedule},
        producingDraws (maxDraws := maxDraws) schedule.1 := by
  classical
  let split := successfulDrawsEquivSigma (q := q) (n := n)
    (maxDraws := maxDraws)
  let restricted := split.subtypeEquiv (p := AllOutputQueriesIn bad)
    (q := fun result ↦
      AspisV5WithoutReplacementQuerySoundness.AllQueriesIn bad result.1) (by
      intro draws
      rfl)
  exact restricted.trans (Equiv.subtypeSigmaEquiv
    (fun schedule : QuerySchedule q n ↦
      producingDraws (maxDraws := maxDraws) schedule)
    (AspisV5WithoutReplacementQuerySoundness.AllQueriesIn bad))

/-- The number of successful bad-set outcomes is the number of bad schedules
times the size of any one output fibre. -/
theorem card_successfulBadDraws_eq_mul_fibre {q n maxDraws : Nat}
    (bad : Finset (Fin n)) (reference : QuerySchedule q n) :
    Fintype.card
        (successfulBadDraws (q := q) (maxDraws := maxDraws) bad) =
      Fintype.card
          {schedule : QuerySchedule q n //
            AspisV5WithoutReplacementQuerySoundness.AllQueriesIn bad schedule} *
        Fintype.card (producingDraws (maxDraws := maxDraws) reference) := by
  classical
  calc
    Fintype.card
        (successfulBadDraws (q := q) (maxDraws := maxDraws) bad) =
        Fintype.card
          (Σ schedule :
              {schedule : QuerySchedule q n //
                AspisV5WithoutReplacementQuerySoundness.AllQueriesIn bad schedule},
            producingDraws (maxDraws := maxDraws) schedule.1) :=
      Fintype.card_congr (successfulBadDrawsEquivSigma bad)
    _ = ∑ schedule :
          {schedule : QuerySchedule q n //
            AspisV5WithoutReplacementQuerySoundness.AllQueriesIn bad schedule},
          Fintype.card (producingDraws (maxDraws := maxDraws) schedule.1) := by
      simp
    _ = ∑ _schedule :
          {schedule : QuerySchedule q n //
            AspisV5WithoutReplacementQuerySoundness.AllQueriesIn bad schedule},
          Fintype.card (producingDraws (maxDraws := maxDraws) reference) := by
      apply Finset.sum_congr rfl
      intro schedule _
      exact producingDraws_card_eq schedule.1 reference
    _ = Fintype.card
          {schedule : QuerySchedule q n //
            AspisV5WithoutReplacementQuerySoundness.AllQueriesIn bad schedule} *
        Fintype.card (producingDraws (maxDraws := maxDraws) reference) := by
      simp

/-- The increasing map from the draw-budget indices into the population. -/
def castLESchedule {q n : Nat} (h : q ≤ n) : QuerySchedule q n where
  toFun := Fin.castLE h
  inj' := Fin.castLE_injective h

/-- Conditioned on sampler success, the bounded independent-uniform draw
experiment has exactly the same fixed-bad-set probability as direct uniform
sampling from ordered injections. -/
theorem conditionedAllQueriesInProbability_eq_ideal {q n maxDraws : Nat}
    (bad : Finset (Fin n)) (hq : q ≤ maxDraws)
    (hbudget : maxDraws ≤ n) :
    conditionedAllQueriesInProbability (q := q) (maxDraws := maxDraws) bad =
      AspisV5WithoutReplacementQuerySoundness.idealMissProbability
        (q := q) bad := by
  classical
  let reference : QuerySchedule q n := castLESchedule (hq.trans hbudget)
  have hsuccess : 0 < Fintype.card (successfulDraws q n maxDraws) := by
    rw [Fintype.card_pos_iff]
    exact ⟨⟨(fun i : Fin maxDraws ↦ Fin.castLE hbudget i),
      castLE_draws_successful hq hbudget⟩⟩
  have hsuccessFactor := card_successfulDraws_eq_mul_fibre
    (maxDraws := maxDraws) reference
  have hfibre : 0 < Fintype.card
      (producingDraws (maxDraws := maxDraws) reference) := by
    rw [hsuccessFactor] at hsuccess
    exact pos_of_mul_pos_right hsuccess (Nat.zero_le _)
  have hfibreReal :
      (Fintype.card (producingDraws (maxDraws := maxDraws) reference) : ℝ) ≠ 0 := by
    exact_mod_cast hfibre.ne'
  rw [AspisV5WithoutReplacementQuerySoundness.ideal_miss_probability_eq_event_card_ratio]
  unfold conditionedAllQueriesInProbability
  rw [card_successfulBadDraws_eq_mul_fibre bad reference,
    hsuccessFactor, Nat.cast_mul, Nat.cast_mul]
  field_simp [hfibreReal]

/-- Probability, before conditioning, that the bounded sampler succeeds and
all returned queries lie in `bad`.  Draw-limit exhaustion is a rejecting
outcome in this experiment. -/
noncomputable def unconditionedSuccessfulBadProbability {q n maxDraws : Nat}
    (bad : Finset (Fin n)) : ℝ :=
  Fintype.card (successfulBadDraws (q := q) (maxDraws := maxDraws) bad) /
    Fintype.card (Draws n maxDraws)

/-- Counting draw-limit exhaustion as rejection cannot increase the bad-set
probability above the probability conditioned on sampler success. -/
theorem unconditionedSuccessfulBadProbability_le_conditioned
    {q n maxDraws : Nat} (bad : Finset (Fin n))
    (hq : q ≤ maxDraws) (hbudget : maxDraws ≤ n) :
    unconditionedSuccessfulBadProbability (q := q) (maxDraws := maxDraws) bad ≤
      conditionedAllQueriesInProbability (q := q) (maxDraws := maxDraws) bad := by
  classical
  have hsuccess : 0 < Fintype.card (successfulDraws q n maxDraws) := by
    rw [Fintype.card_pos_iff]
    exact ⟨⟨(fun i : Fin maxDraws ↦ Fin.castLE hbudget i),
      castLE_draws_successful hq hbudget⟩⟩
  have hsubset : Fintype.card (successfulDraws q n maxDraws) ≤
      Fintype.card (Draws n maxDraws) :=
    Fintype.card_subtype_le _
  unfold unconditionedSuccessfulBadProbability
    conditionedAllQueriesInProbability
  exact div_le_div_of_nonneg_left (by positivity)
    (by exact_mod_cast hsuccess) (by exact_mod_cast hsubset)

/-- In the full ideal bounded-draw experiment, success with every query in a
fixed bad set is bounded by the direct without-replacement probability. -/
theorem unconditionedSuccessfulBadProbability_le_ideal
    {q n maxDraws : Nat} (bad : Finset (Fin n))
    (hq : q ≤ maxDraws) (hbudget : maxDraws ≤ n) :
    unconditionedSuccessfulBadProbability (q := q) (maxDraws := maxDraws) bad ≤
      AspisV5WithoutReplacementQuerySoundness.idealMissProbability
        (q := q) bad := by
  rw [← conditionedAllQueriesInProbability_eq_ideal bad hq hbudget]
  exact unconditionedSuccessfulBadProbability_le_conditioned bad hq hbudget

/-- At the deployed parameters, composing the conditioned fixed-bad-set
probability with a separately justified work factor of at most `2^-32` gives
the existing `2^-111` numeric bound.

This theorem only multiplies two supplied experiment probabilities. It does
not establish independence, Fiat–Shamir random-oracle behaviour, or a link to
the Rust/SHA implementation. -/
theorem deployed_conditioned_bad_numeric_product_le
    (bad : Finset (Fin 131072)) (hcard : bad.card ≤ 6082)
    (workProbability : ℝ) (_hworkNonneg : 0 ≤ workProbability)
    (hwork : workProbability ≤ (1 : ℝ) / 2 ^ 32) :
    conditionedAllQueriesInProbability (q := 18) (maxDraws := 64) bad *
        workProbability ≤
      (1 : ℝ) / 2 ^ 111 := by
  rw [conditionedAllQueriesInProbability_eq_ideal bad (by norm_num) (by norm_num)]
  calc
    AspisV5WithoutReplacementQuerySoundness.idealMissProbability
          (q := 18) bad * workProbability ≤
        AspisV5WithoutReplacementQuerySoundness.idealMissProbability
          (q := 18) bad * ((1 : ℝ) / 2 ^ 32) :=
      mul_le_mul_of_nonneg_left hwork (by
        unfold AspisV5WithoutReplacementQuerySoundness.idealMissProbability
        exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    _ = AspisV5WithoutReplacementQuerySoundness.idealMissProbability
          (q := 18) bad / 2 ^ 32 := by ring
    _ ≤ (1 : ℝ) / 2 ^ 111 :=
      AspisV5WithoutReplacementQuerySoundness.deployed_q18_ideal_miss_ratio_div_2pow32_le
        bad hcard

/-- A valid overall failure bound follows from the numeric product theorem
once the caller separately proves that the actual joint failure probability
is at most that product. That premise may come from independence or from a
direct joint-event proof; neither is asserted here. -/
theorem deployed_conditioned_bad_overall_failure_le
    (bad : Finset (Fin 131072)) (hcard : bad.card ≤ 6082)
    (workProbability overallFailureProbability : ℝ)
    (_hworkNonneg : 0 ≤ workProbability)
    (hwork : workProbability ≤ (1 : ℝ) / 2 ^ 32)
    (hjoint : overallFailureProbability ≤
      conditionedAllQueriesInProbability (q := 18) (maxDraws := 64) bad *
        workProbability) :
    overallFailureProbability ≤ (1 : ℝ) / 2 ^ 111 :=
  hjoint.trans (deployed_conditioned_bad_numeric_product_le bad hcard
    workProbability _hworkNonneg hwork)

/-- The corresponding product bound for the full bounded-draw experiment.
Sampler exhaustion is included as rejection, so no conditioning factor is
needed.  The work probability and its product with the query event are still
supplied separately; this theorem does not assert independence. -/
theorem deployed_unconditioned_bad_numeric_product_le
    (bad : Finset (Fin 131072)) (hcard : bad.card ≤ 6082)
    (workProbability : ℝ) (hworkNonneg : 0 ≤ workProbability)
    (hwork : workProbability ≤ (1 : ℝ) / 2 ^ 32) :
    unconditionedSuccessfulBadProbability (q := 18) (maxDraws := 64) bad *
        workProbability ≤
      (1 : ℝ) / 2 ^ 111 := by
  calc
    unconditionedSuccessfulBadProbability (q := 18) (maxDraws := 64) bad *
          workProbability ≤
        conditionedAllQueriesInProbability (q := 18) (maxDraws := 64) bad *
          workProbability :=
      mul_le_mul_of_nonneg_right
        (unconditionedSuccessfulBadProbability_le_conditioned bad
          (by norm_num) (by norm_num)) hworkNonneg
    _ ≤ (1 : ℝ) / 2 ^ 111 :=
      deployed_conditioned_bad_numeric_product_le bad hcard workProbability
        hworkNonneg hwork

/-! ## Axiom audit -/

#print axioms firstOccurrences_map
#print axioms producingDraws_card_eq
#print axioms card_successfulDraws_eq_mul_fibre
#print axioms conditionedScheduleProbability_eq_uniform
#print axioms deployed_q18_conditioned_uniform
#print axioms conditionedAllQueriesInProbability_eq_ideal
#print axioms unconditionedSuccessfulBadProbability_le_conditioned
#print axioms unconditionedSuccessfulBadProbability_le_ideal
#print axioms deployed_conditioned_bad_numeric_product_le
#print axioms deployed_conditioned_bad_overall_failure_le
#print axioms deployed_unconditioned_bad_numeric_product_le

end AspisV5BoundedQuerySamplerUniformity

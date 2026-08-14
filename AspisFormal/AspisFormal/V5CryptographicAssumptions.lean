import AspisFormal.V5TranscriptConnection

/-!
# Explicit cryptographic assumptions for V5

The deterministic transcript schedule is proved in
`V5TranscriptConnection`.  This file names the computational events that a
deployed security statement must still bound.  It does not prove collision
resistance, preimage resistance, implementation correctness, or a
random-oracle theorem for SHA-256 or Poseidon2.

All concrete bounds are parameters.  A caller may instantiate them from a
separate cryptographic analysis, but known-answer tests alone do not provide
such an instantiation.
-/

namespace AspisV5CryptographicAssumptions

open MeasureTheory
open AspisFormal.V5ExactRuntimeWireRepair
open AspisV5TranscriptConnection

abbrev HashInput := HashVector
abbrev Digest32 := FixedBytes 32

/-! ## Concrete collision and preimage games -/

structure CollisionAttempt (Coins : Type*) where
  left : Coins → HashInput
  right : Coins → HashInput

def collisionFailure
    {Coins : Type*}
    (hash : HashInput → Digest32)
    (attempt : CollisionAttempt Coins) : Set Coins :=
  {coins |
    attempt.left coins ≠ attempt.right coins ∧
      hash (attempt.left coins) = hash (attempt.right coins)}

structure PreimageAttempt (Coins : Type*) where
  target : Coins → Digest32
  candidate : Coins → HashInput

def preimageFailure
    {Coins : Type*}
    (hash : HashInput → Digest32)
    (attempt : PreimageAttempt Coins) : Set Coins :=
  {coins | hash (attempt.candidate coins) = attempt.target coins}

/-- A byte-for-byte implementation disagreement on a hash input reached by
the experiment. -/
def implementationDivergence
    {Coins : Type*}
    (actual specification : HashInput → Digest32)
    (input : Coins → HashInput) : Set Coins :=
  {coins | actual (input coins) ≠ specification (input coins)}

/-! ## Failure-event ledger -/

inductive FailureKind where
  | rustToLean
  | sha256ImplementationDivergence
  | sha256Collision
  | sha256Preimage
  | sha256RandomOracle
  | poseidon2ImplementationDivergence
  | poseidon2Collision
  | poseidon2Preimage
  deriving DecidableEq, Fintype

theorem failure_kind_count_is_eight : Fintype.card FailureKind = 8 := by
  decide

structure SecurityFailureEvents (Coins : Type*) where
  event : FailureKind → Set Coins

def orderedFailureKinds : List FailureKind :=
  [.rustToLean,
    .sha256ImplementationDivergence,
    .sha256Collision,
    .sha256Preimage,
    .sha256RandomOracle,
    .poseidon2ImplementationDivergence,
    .poseidon2Collision,
    .poseidon2Preimage]

theorem ordered_failure_kinds_are_exactly_once :
    orderedFailureKinds.Nodup ∧
      ∀ kind : FailureKind, kind ∈ orderedFailureKinds := by
  decide

def totalFailure
    {Coins : Type*} (events : SecurityFailureEvents Coins) : Set Coins :=
  (orderedFailureKinds.map events.event).foldr (· ∪ ·) ∅

theorem member_subset_foldr_union
    {Coins : Type*} (sets : List (Set Coins)) (set : Set Coins)
    (hmember : set ∈ sets) :
    set ⊆ sets.foldr (· ∪ ·) ∅ := by
  induction sets with
  | nil => simp at hmember
  | cons head tail ih =>
      simp only [List.mem_cons] at hmember
      simp only [List.foldr_cons]
      rcases hmember with rfl | htail
      · exact Set.subset_union_left
      · exact Set.Subset.trans (ih htail) Set.subset_union_right

theorem one_failure_is_in_total
    {Coins : Type*} (events : SecurityFailureEvents Coins)
    (kind : FailureKind) :
    events.event kind ⊆ totalFailure events := by
  apply member_subset_foldr_union
  apply List.mem_map.mpr
  exact ⟨kind, ordered_failure_kinds_are_exactly_once.2 kind, rfl⟩

/-! ## Deterministic coupling to an ideal transcript -/

/-- Four views of the same accepted execution.  `production` is the Rust
result, `sourceModel` is the exact Lean driver, `sha256Specification` uses the
mathematical SHA-256 primitive, and `idealTranscript` uses the ideal oracle
required by a Fiat-Shamir argument. -/
structure TranscriptCoupling (Coins Outcome : Type*) where
  production : Coins → Outcome
  sourceModel : Coins → Outcome
  sha256Specification : Coins → Outcome
  idealTranscript : Coins → Outcome

def unequalOutputs
    {Coins Outcome : Type*} (left right : Coins → Outcome) : Set Coins :=
  {coins | left coins ≠ right coins}

/-- The complete accepted output differs between two transcript drivers.  The
output is intended to include the event trace, all decoded challenges, the
selector, and the query schedule. -/
def transcriptDivergence
    {Coins Outcome : Type*} (actual modeled : Coins → Outcome) : Set Coins :=
  unequalOutputs actual modeled

/-- Fill the complete event ledger.  Collision and preimage games are kept
separate from the three equality links used by the deterministic coupling. -/
def coupledFailureEvents
    {Coins Outcome : Type*}
    (coupling : TranscriptCoupling Coins Outcome)
    (sha256Collision sha256Preimage poseidon2ImplementationDivergence
      poseidon2Collision poseidon2Preimage : Set Coins) :
    SecurityFailureEvents Coins where
  event
    | .rustToLean =>
        transcriptDivergence coupling.production coupling.sourceModel
    | .sha256ImplementationDivergence =>
        transcriptDivergence coupling.sourceModel coupling.sha256Specification
    | .sha256Collision => sha256Collision
    | .sha256Preimage => sha256Preimage
    | .sha256RandomOracle =>
        transcriptDivergence coupling.sha256Specification coupling.idealTranscript
    | .poseidon2ImplementationDivergence => poseidon2ImplementationDivergence
    | .poseidon2Collision => poseidon2Collision
    | .poseidon2Preimage => poseidon2Preimage

/-- Outside the exact Rust/model, SHA implementation, and random-oracle
divergence events, the complete production outcome equals the ideal outcome.
Because the outcome contains both verifier-consumed challenges and the query
schedule, this equality includes gamma, kappa, all relation and fold
challenges, the selector, and all eighteen query positions. -/
theorem production_challenges_equal_ideal_outside_failures
    {Coins Outcome : Type*}
    (coupling : TranscriptCoupling Coins Outcome)
    (sha256Collision sha256Preimage poseidon2ImplementationDivergence
      poseidon2Collision poseidon2Preimage : Set Coins)
    (coins : Coins)
    (houtside : coins ∉ totalFailure
      (coupledFailureEvents coupling sha256Collision sha256Preimage
        poseidon2ImplementationDivergence poseidon2Collision
        poseidon2Preimage)) :
    coupling.production coins = coupling.idealTranscript coins := by
  let events := coupledFailureEvents coupling sha256Collision sha256Preimage
    poseidon2ImplementationDivergence poseidon2Collision poseidon2Preimage
  have hrust : coupling.production coins = coupling.sourceModel coins := by
    by_contra hne
    exact houtside (one_failure_is_in_total events .rustToLean hne)
  have hsha : coupling.sourceModel coins = coupling.sha256Specification coins := by
    by_contra hne
    exact houtside
      (one_failure_is_in_total events .sha256ImplementationDivergence hne)
  have hideal : coupling.sha256Specification coins = coupling.idealTranscript coins := by
    by_contra hne
    exact houtside (one_failure_is_in_total events .sha256RandomOracle hne)
  exact hrust.trans (hsha.trans hideal)

/-! ## Parameterized concrete bounds -/

/-- No numerical value is supplied here.  In particular, this definition does
not turn a digest width into a collision, preimage, or random-oracle bound. -/
structure ConcreteSecurityBudget where
  rustToLean : ℝ
  sha256ImplementationDivergence : ℝ
  sha256Collision : ℝ
  sha256Preimage : ℝ
  sha256RandomOracle : ℝ
  poseidon2ImplementationDivergence : ℝ
  poseidon2Collision : ℝ
  poseidon2Preimage : ℝ

def ConcreteSecurityBudget.bound
    (budget : ConcreteSecurityBudget) : FailureKind → ℝ
  | .rustToLean => budget.rustToLean
  | .sha256ImplementationDivergence => budget.sha256ImplementationDivergence
  | .sha256Collision => budget.sha256Collision
  | .sha256Preimage => budget.sha256Preimage
  | .sha256RandomOracle => budget.sha256RandomOracle
  | .poseidon2ImplementationDivergence => budget.poseidon2ImplementationDivergence
  | .poseidon2Collision => budget.poseidon2Collision
  | .poseidon2Preimage => budget.poseidon2Preimage

def ConcreteSecurityBudget.Valid (budget : ConcreteSecurityBudget) : Prop :=
  ∀ kind, 0 ≤ budget.bound kind

def ConcreteSecurityBudget.total (budget : ConcreteSecurityBudget) : ℝ :=
  (orderedFailureKinds.map budget.bound).sum

/-- These are assumptions, not theorems about either primitive.  Every field
is an externally justified upper bound for the correspondingly named event. -/
structure AssumedConcreteSecurityBounds
    {Coins : Type*} [MeasurableSpace Coins]
    (measure : Measure Coins)
    (events : SecurityFailureEvents Coins)
    (budget : ConcreteSecurityBudget) : Prop where
  nonnegative : budget.Valid
  eventBound : ∀ kind, measure.real (events.event kind) ≤ budget.bound kind

theorem measureReal_foldr_union_le_sum
    {Coins : Type*} [MeasurableSpace Coins]
    (measure : Measure Coins) (sets : List (Set Coins)) :
    measure.real (sets.foldr (· ∪ ·) ∅) ≤
      (sets.map measure.real).sum := by
  induction sets with
  | nil => simp
  | cons head tail ih =>
      simp only [List.foldr_cons, List.map_cons, List.sum_cons]
      exact (MeasureTheory.measureReal_union_le head
        (tail.foldr (· ∪ ·) ∅)).trans (add_le_add le_rfl ih)

theorem total_failure_probability_le_budget_sum
    {Coins : Type*} [MeasurableSpace Coins]
    (measure : Measure Coins)
    (events : SecurityFailureEvents Coins)
    (budget : ConcreteSecurityBudget)
    (hassumed : AssumedConcreteSecurityBounds measure events budget) :
    measure.real (totalFailure events) ≤
      budget.total := by
  calc
    measure.real (totalFailure events) ≤
        ((orderedFailureKinds.map events.event).map measure.real).sum := by
      exact measureReal_foldr_union_le_sum measure
        (orderedFailureKinds.map events.event)
    _ ≤ (orderedFailureKinds.map budget.bound).sum := by
      simp only [List.map_map]
      apply List.sum_le_sum
      intro kind _
      exact hassumed.eventBound kind
    _ = budget.total := rfl

theorem total_failure_probability_le_explicit_budget
    {Coins : Type*} [MeasurableSpace Coins]
    (measure : Measure Coins)
    (events : SecurityFailureEvents Coins)
    (budget : ConcreteSecurityBudget)
    (hassumed : AssumedConcreteSecurityBounds measure events budget) :
    measure.real (totalFailure events) ≤
      budget.rustToLean +
      budget.sha256ImplementationDivergence +
      budget.sha256Collision +
      budget.sha256Preimage +
      budget.sha256RandomOracle +
      budget.poseidon2ImplementationDivergence +
      budget.poseidon2Collision +
      budget.poseidon2Preimage := by
  simpa [ConcreteSecurityBudget.total, orderedFailureKinds,
    ConcreteSecurityBudget.bound, add_assoc] using
    total_failure_probability_le_budget_sum measure events budget hassumed

/-- The SHA-256 assumptions needed by this transcript argument, isolated from
the Rust correspondence and Poseidon2 assumptions. -/
def ExplicitSHA256Assumptions
    {Coins : Type*} [MeasurableSpace Coins]
    (measure : Measure Coins)
    (events : SecurityFailureEvents Coins)
    (implementationBound collisionBound preimageBound randomOracleBound : ℝ) : Prop :=
  measure.real (events.event .sha256ImplementationDivergence) ≤ implementationBound ∧
    measure.real (events.event .sha256Collision) ≤ collisionBound ∧
    measure.real (events.event .sha256Preimage) ≤ preimageBound ∧
    measure.real (events.event .sha256RandomOracle) ≤ randomOracleBound

/-- The Poseidon2 assumptions needed elsewhere in the spend argument.  The V5
SHA transcript does not derive these bounds. -/
def ExplicitPoseidon2Assumptions
    {Coins : Type*} [MeasurableSpace Coins]
    (measure : Measure Coins)
    (events : SecurityFailureEvents Coins)
    (implementationBound collisionBound preimageBound : ℝ) : Prop :=
  measure.real (events.event .poseidon2ImplementationDivergence) ≤ implementationBound ∧
    measure.real (events.event .poseidon2Collision) ≤ collisionBound ∧
    measure.real (events.event .poseidon2Preimage) ≤ preimageBound

theorem concrete_bounds_expose_sha256_assumptions
    {Coins : Type*} [MeasurableSpace Coins]
    (measure : Measure Coins)
    (events : SecurityFailureEvents Coins)
    (budget : ConcreteSecurityBudget)
    (hassumed : AssumedConcreteSecurityBounds measure events budget) :
    ExplicitSHA256Assumptions measure events
      budget.sha256ImplementationDivergence budget.sha256Collision
      budget.sha256Preimage budget.sha256RandomOracle := by
  exact ⟨hassumed.eventBound .sha256ImplementationDivergence,
    hassumed.eventBound .sha256Collision,
    hassumed.eventBound .sha256Preimage,
    hassumed.eventBound .sha256RandomOracle⟩

theorem concrete_bounds_expose_poseidon2_assumptions
    {Coins : Type*} [MeasurableSpace Coins]
    (measure : Measure Coins)
    (events : SecurityFailureEvents Coins)
    (budget : ConcreteSecurityBudget)
    (hassumed : AssumedConcreteSecurityBounds measure events budget) :
    ExplicitPoseidon2Assumptions measure events
      budget.poseidon2ImplementationDivergence budget.poseidon2Collision
      budget.poseidon2Preimage := by
  exact ⟨hassumed.eventBound .poseidon2ImplementationDivergence,
    hassumed.eventBound .poseidon2Collision,
    hassumed.eventBound .poseidon2Preimage⟩

#print axioms failure_kind_count_is_eight
#print axioms ordered_failure_kinds_are_exactly_once
#print axioms member_subset_foldr_union
#print axioms one_failure_is_in_total
#print axioms production_challenges_equal_ideal_outside_failures
#print axioms measureReal_foldr_union_le_sum
#print axioms total_failure_probability_le_budget_sum
#print axioms total_failure_probability_le_explicit_budget
#print axioms concrete_bounds_expose_sha256_assumptions
#print axioms concrete_bounds_expose_poseidon2_assumptions

end AspisV5CryptographicAssumptions

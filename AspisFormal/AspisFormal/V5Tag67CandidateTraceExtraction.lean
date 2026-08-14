import AspisFormal.V5AcceptedSpendRelation
import AspisFormal.V5FunctionalBatching
import AspisFormal.V5Tag67FalseAcceptanceDecomposition
import AspisFormal.V5ABToCResidualBridge

/-!
# From a fixed Tag-67 candidate to an extracted spend trace

`V5Tag67RelationListInclusion` starts with one 1,024-coordinate candidate for
the gamma-combined message.  That vector is not the original nineteen-lane
message and it is not an `ExtractedV5Trace`.  This file records the missing
direction without treating those objects as interchangeable.

The deterministic result proved here has two parts.

* The negation of `FalseForCandidate` is expanded into the exact initial and
  eight OOD scalar equalities.
* For a candidate accompanied by its full nineteen-lane metadata, a false
  public spend has a scalar mismatch unless one of six concrete earlier
  failures occurs: the four-claim batch equation is wrong, that batch
  collides, the nineteen lanes do not recombine to the FRI candidate, the
  public fields do not match, the arithmetic residuals do not vanish, or the
  hash/Merkle rows do not form the normalized extracted trace.

The last two predicates use the low-level residual structures from
`V5AcceptedSpendRelation`, not a premise saying that every candidate is
false.  Once they are excluded, `extracted_trace_implies_spend_relation`
constructs an actual spend witness and gives the required contradiction.

What this file cannot manufacture is the production instantiation of those
failure predicates.  In particular, a gamma-combined vector does not recover
the nineteen lanes.  The committed C1/C2 data, their code membership and
Merkle authentication, the Good-query argument, the compiled copy/LogUp
layout, and the Poseidon/Rust row correspondence must supply that metadata and
bound the named failures.
-/

namespace AspisV5Tag67CandidateTraceExtraction

open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisV5ABToCResidualBridge
open AspisV5AcceptedSpendRelation
open AspisV5FunctionalBatching
open AspisV5RelationSumcheckSoundness
open AspisV5Tag67FalseAcceptanceDecomposition
open AspisV5Tag67RelationListInclusion

variable {K : Type*} [Field K]

/-! ## Exact meaning of scalar agreement -/

/-- All nine scalar statements checked against one fixed FRI candidate agree:
the initial linear claim and the two OOD claims introduced in each of four
rounds.  The second OOD claim is evaluated after the first mix, exactly as in
the deployed transcript order. -/
structure CandidateScalarClaimsMatch
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K) : Prop where
  initial : (execution.discrepancyTrace challenges).before 0 = 0
  firstOOD : ∀ round : Fin 4,
    (execution.discrepancyTrace challenges).firstValueError round = 0
  secondOOD : ∀ round : Fin 4,
    (execution.discrepancyTrace challenges).secondValueError round
      ((execution.discrepancyTrace challenges).firstMix round) = 0

/-- If a candidate has no initial/OOD mismatch, all nine discrepancy scalars
are zero.  This is the forward form needed by trace extraction. -/
theorem scalarClaimsMatch_of_not_falseForCandidate
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K)
    (hnotFalse : ¬ execution.FalseForCandidate challenges) :
    CandidateScalarClaimsMatch execution challenges := by
  let trace := execution.discrepancyTrace challenges
  have hnoError : ¬ trace.HasInitialOrIntroducedError := hnotFalse
  refine {
    initial := ?_
    firstOOD := ?_
    secondOOD := ?_
  }
  · by_contra hne
    exact hnoError (Or.inl hne)
  · intro round
    by_contra hne
    exact hnoError (Or.inr ⟨round, Or.inl hne⟩)
  · intro round
    by_contra hne
    exact hnoError (Or.inr ⟨round, Or.inr hne⟩)

/-- Conversely, the nine scalar equalities rule out `FalseForCandidate`. -/
theorem not_falseForCandidate_of_scalarClaimsMatch
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K)
    (hmatch : CandidateScalarClaimsMatch execution challenges) :
    ¬ execution.FalseForCandidate challenges := by
  intro hfalse
  rcases hfalse with hinitial | ⟨round, hfirst | hsecond⟩
  · exact hinitial hmatch.initial
  · exact hfirst (hmatch.firstOOD round)
  · exact hsecond (hmatch.secondOOD round)

theorem not_falseForCandidate_iff_scalarClaimsMatch
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K) :
    ¬ execution.FalseForCandidate challenges ↔
      CandidateScalarClaimsMatch execution challenges :=
  ⟨scalarClaimsMatch_of_not_falseForCandidate execution challenges,
    not_falseForCandidate_of_scalarClaimsMatch execution challenges⟩

/-! ## The full nineteen-lane object hidden by gamma combination -/

/-- The data whose pointwise gamma combination is the layer-zero candidate:
sixteen semantic lanes, the copy lane, Component B, and Component C. -/
structure CandidateLaneEnsemble (K : Type*) where
  gamma : K
  semantic : Fin 16 → Fin 1024 → K
  hcopy : Fin 1024 → K
  componentB : Fin 1024 → K
  componentC : Fin 1024 → K

/-- Exact nineteen-lane gamma combination used by V5: powers zero through
fifteen for semantic lanes, then powers sixteen, seventeen, and eighteen. -/
def CandidateLaneEnsemble.combined
    (ensemble : CandidateLaneEnsemble K) : Fin 1024 → K :=
  preCWord ensemble.gamma ensemble.semantic ensemble.hcopy ensemble.componentB +
    ensemble.gamma ^ 18 • ensemble.componentC

theorem CandidateLaneEnsemble.combined_apply
    (ensemble : CandidateLaneEnsemble K) (row : Fin 1024) :
    ensemble.combined row =
      (∑ lane : Fin 16, ensemble.gamma ^ lane.val * ensemble.semantic lane row) +
        ensemble.gamma ^ 16 * ensemble.hcopy row +
        ensemble.gamma ^ 17 * ensemble.componentB row +
        ensemble.gamma ^ 18 * ensemble.componentC row := by
  simp [CandidateLaneEnsemble.combined, preCWord, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]

/-- Metadata carried with one FRI-list member.  `opened` is deliberately
separate from `lanes`: connecting the production trace layout to these fields
is one of the explicit failure conditions below. -/
structure CandidateSemanticRecord (K : Type*) where
  lanes : CandidateLaneEnsemble K
  opened : OpenedColumns
  /-- Four individual pre-kappa claim discrepancies. -/
  fourClaimDiscrepancy : Fin 4 → K
  /-- The pre-committed four-claim batching challenge. -/
  kappa : K

/-! ## Concrete earlier failures -/

/-- The aggregate initial discrepancy is not the scalar-power batch of the
four individual claim discrepancies.  This is the missing exact equation for
`prepare_relation_base_with_kappa_prepared`. -/
def FourClaimBatchEquationFailure
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K)
    (record : CandidateSemanticRecord K) : Prop :=
  CandidateScalarClaimsMatch execution challenges ∧
    (execution.discrepancyTrace challenges).before 0 ≠
      batchedDiscrepancy record.fourClaimDiscrepancy record.kappa

/-- A nonzero four-claim discrepancy is hidden by the sampled kappa.  The
existing cubic root theorem bounds exactly this event once transcript ordering
and uniformity are supplied. -/
def FourClaimBatchCollision (record : CandidateSemanticRecord K) : Prop :=
  record.fourClaimDiscrepancy ≠ 0 ∧
    batchedDiscrepancy record.fourClaimDiscrepancy record.kappa = 0

/-- The separately authenticated nineteen lanes do not recombine to the fixed
FRI candidate.  Excluding this requires C1/C2 binding and the exact gamma-lane
layout; it cannot be recovered from the combined vector alone. -/
def CombinedLaneBindingFailure
    (execution : AcceptedCandidateExecution K)
    (record : CandidateSemanticRecord K) : Prop :=
  record.lanes.combined ≠ execution.initialValues

/-- After the four individual claims and lane combination have been fixed,
the decoded spend fields differ from the statement accepted by the verifier. -/
def PublicStatementBindingFailure
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K)
    (statement : V5PublicStatement)
    (record : CandidateSemanticRecord K) : Prop :=
  CandidateScalarClaimsMatch execution challenges ∧
    record.fourClaimDiscrepancy = 0 ∧
    record.lanes.combined = execution.initialValues ∧
    ¬ OpenedColumnsMatchStatement statement record.opened

/-- The decoded arithmetic rows fail one of the exact range, balance, or
asset residual equations in `ExtractedArithmeticResiduals`. -/
def ArithmeticResidualFailure
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K)
    (statement : V5PublicStatement)
    (record : CandidateSemanticRecord K) : Prop :=
  CandidateScalarClaimsMatch execution challenges ∧
    record.fourClaimDiscrepancy = 0 ∧
    record.lanes.combined = execution.initialValues ∧
    OpenedColumnsMatchStatement statement record.opened ∧
    ¬ ExtractedArithmeticResiduals record.opened

/-- The decoded Poseidon and Merkle rows do not supply the normalized gate
and copy equations required by `ExtractedHashMerkleResiduals`. -/
def HashMerkleResidualFailure
    (rc : RoundConstants)
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K)
    (statement : V5PublicStatement)
    (record : CandidateSemanticRecord K) : Prop :=
  CandidateScalarClaimsMatch execution challenges ∧
    record.fourClaimDiscrepancy = 0 ∧
    record.lanes.combined = execution.initialValues ∧
    OpenedColumnsMatchStatement statement record.opened ∧
    ExtractedArithmeticResiduals record.opened ∧
    ¬ Nonempty (ExtractedHashMerkleResiduals rc record.opened)

/-- The exact disjunction that must be bounded before a semantic false spend
can be sent to the relation repair event.  None of its alternatives mentions
`FalseForCandidate` as a conclusion or assumes `AllCandidatesFalse`. -/
def CandidateEarlierFailure
    (rc : RoundConstants)
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K)
    (statement : V5PublicStatement)
    (record : CandidateSemanticRecord K) : Prop :=
  FourClaimBatchEquationFailure execution challenges record ∨
    FourClaimBatchCollision record ∨
    CombinedLaneBindingFailure execution record ∨
    PublicStatementBindingFailure execution challenges statement record ∨
    ArithmeticResidualFailure execution challenges statement record ∨
    HashMerkleResidualFailure rc execution challenges statement record

/-! ## Four-claim batch algebra -/

/-- Outside the batch-equation and cubic-collision failures, scalar agreement
forces all four individual pre-kappa claim discrepancies to be zero. -/
theorem fourClaimDiscrepancy_eq_zero_outside_failures
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K)
    (record : CandidateSemanticRecord K)
    (hmatch : CandidateScalarClaimsMatch execution challenges)
    (hEquation : ¬ FourClaimBatchEquationFailure execution challenges record)
    (hCollision : ¬ FourClaimBatchCollision record) :
    record.fourClaimDiscrepancy = 0 := by
  have hbatchEquation :
      (execution.discrepancyTrace challenges).before 0 =
        batchedDiscrepancy record.fourClaimDiscrepancy record.kappa := by
    by_contra hne
    exact hEquation ⟨hmatch, hne⟩
  have hbatchZero :
      batchedDiscrepancy record.fourClaimDiscrepancy record.kappa = 0 := by
    rw [← hbatchEquation]
    exact hmatch.initial
  by_contra hnonzero
  exact hCollision ⟨hnonzero, hbatchZero⟩

/-! ## Candidate-to-trace reconstruction and the desired contrapositive -/

/-- If none of the explicit earlier stages fails and the scalar claims match,
the candidate metadata constructs an actual normalized extracted trace for
the exact public statement. -/
theorem candidate_to_extracted_trace_outside_failures
    (rc : RoundConstants)
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K)
    (statement : V5PublicStatement)
    (record : CandidateSemanticRecord K)
    (hmatch : CandidateScalarClaimsMatch execution challenges)
    (houtside : ¬ CandidateEarlierFailure rc execution challenges
      statement record) :
    ∃ _trace : ExtractedV5Trace rc record.opened,
      OpenedColumnsMatchStatement statement record.opened := by
  have hEquation :
      ¬ FourClaimBatchEquationFailure execution challenges record := by
    intro h
    exact houtside (Or.inl h)
  have hCollision : ¬ FourClaimBatchCollision record := by
    intro h
    exact houtside (Or.inr (Or.inl h))
  have hfourClaims : record.fourClaimDiscrepancy = 0 :=
    fourClaimDiscrepancy_eq_zero_outside_failures execution challenges record
      hmatch hEquation hCollision
  have hlanes : record.lanes.combined = execution.initialValues := by
    by_contra hne
    exact houtside (Or.inr (Or.inr (Or.inl hne)))
  have hpublic : OpenedColumnsMatchStatement statement record.opened := by
    by_contra hne
    exact houtside (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hmatch, hfourClaims, hlanes, hne⟩))))
  have harithmetic : ExtractedArithmeticResiduals record.opened := by
    by_contra hne
    exact houtside (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hmatch, hfourClaims, hlanes, hpublic, hne⟩)))))
  have hhash : Nonempty (ExtractedHashMerkleResiduals rc record.opened) := by
    by_contra hne
    exact houtside (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨hmatch, hfourClaims, hlanes, hpublic, harithmetic, hne⟩)))))
  rcases hhash with ⟨hashAndMerkle⟩
  exact ⟨⟨harithmetic, hashAndMerkle⟩, hpublic⟩

/-- The sought fixed-candidate implication.  For a statement with no spend
witness, every candidate outside the explicit earlier failures must disagree
with the initial claim or one of the eight OOD claims. -/
theorem false_statement_outside_failures_implies_candidate_scalar_mismatch
    (rc : RoundConstants)
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode)
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K)
    (statement : V5PublicStatement)
    (record : CandidateSemanticRecord K)
    (noWitness : ¬ StatementHasSpendWitness statement deployedOwner
      deployedNote deployedNullifier deployedNode)
    (houtside : ¬ CandidateEarlierFailure rc execution challenges
      statement record) :
    execution.FalseForCandidate challenges := by
  by_contra hnotFalse
  have hmatch := scalarClaimsMatch_of_not_falseForCandidate execution
    challenges hnotFalse
  obtain ⟨trace, hpublic⟩ :=
    candidate_to_extracted_trace_outside_failures rc execution challenges
      statement record hmatch houtside
  obtain ⟨inputValue, outputValue, relation⟩ :=
    extracted_trace_implies_spend_relation rc record.opened poseidon trace
  exact noWitness ⟨record.opened, inputValue, outputValue, hpublic, relation⟩

/-- Equivalent decomposition form: a false statement gives either an actual
candidate scalar mismatch or one of the named earlier failures. -/
theorem false_statement_implies_scalar_mismatch_or_earlier_failure
    (rc : RoundConstants)
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode)
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K)
    (statement : V5PublicStatement)
    (record : CandidateSemanticRecord K)
    (noWitness : ¬ StatementHasSpendWitness statement deployedOwner
      deployedNote deployedNullifier deployedNode) :
    execution.FalseForCandidate challenges ∨
      CandidateEarlierFailure rc execution challenges statement record := by
  by_cases hfailure : CandidateEarlierFailure rc execution challenges
      statement record
  · exact Or.inr hfailure
  · exact Or.inl
      (false_statement_outside_failures_implies_candidate_scalar_mismatch
        rc poseidon execution challenges statement record noWitness hfailure)

/-! ## Every member of a fixed FRI family -/

/-- Candidate-specific nineteen-lane metadata for every member of a coherent
FRI list.  It is intentionally additional data: `family.initialValues` alone
does not determine these records. -/
abbrev CandidateRecords (Candidate : Type*) (K : Type*) :=
  Candidate → CandidateSemanticRecord K

/-- If every list member is outside the concrete earlier failures, a false
statement makes every fixed candidate false for the relation execution. -/
theorem false_statement_outside_all_candidate_failures
    (rc : RoundConstants)
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode)
    {Candidate : Type*}
    (family : CoherentCandidateFamily K Candidate)
    (records : CandidateRecords Candidate K)
    (challenges : TwelveRelationChallenges K)
    (statement : V5PublicStatement)
    (noWitness : ¬ StatementHasSpendWitness statement deployedOwner
      deployedNote deployedNullifier deployedNode)
    (houtside : ∀ candidate,
      ¬ CandidateEarlierFailure rc (family.execution candidate) challenges
        statement (records candidate)) :
    AllCandidatesFalse family challenges := by
  intro candidate
  exact false_statement_outside_failures_implies_candidate_scalar_mismatch
    rc poseidon (family.execution candidate) challenges statement
      (records candidate) noWitness (houtside candidate)

/-! ## A gamma-combined vector does not determine its lanes -/

private def zeroVector : Fin 1024 → Rat := fun _ => 0
private def oneVector : Fin 1024 → Rat := fun _ => 1

private def zeroEnsemble : CandidateLaneEnsemble Rat where
  gamma := 1
  semantic := fun _ => zeroVector
  hcopy := zeroVector
  componentB := zeroVector
  componentC := zeroVector

private def cancellingEnsemble : CandidateLaneEnsemble Rat where
  gamma := 1
  semantic := fun lane => if lane = 0 then oneVector else zeroVector
  hcopy := zeroVector
  componentB := zeroVector
  componentC := fun _ => -1

/-- Concrete non-injectivity example: changing semantic lane zero by the all-
one vector and Component C by its negative leaves the gamma-combined vector
unchanged at gamma one.  Thus a theorem that accepts only `Fin 1024 → K`
cannot reconstruct the original nineteen lanes. -/
theorem gamma_combination_does_not_determine_lane_ensemble :
    zeroEnsemble ≠ cancellingEnsemble ∧
      zeroEnsemble.combined = cancellingEnsemble.combined := by
  constructor
  · intro heq
    have hsemantic := congrArg
      (fun ensemble : CandidateLaneEnsemble Rat => ensemble.semantic 0 0) heq
    norm_num [zeroEnsemble, cancellingEnsemble, zeroVector, oneVector] at hsemantic
  · funext row
    rw [CandidateLaneEnsemble.combined_apply,
      CandidateLaneEnsemble.combined_apply]
    have hsum :
        (∑ lane : Fin 16,
          (if lane = 0 then oneVector else zeroVector) row) = (1 : Rat) := by
      classical
      calc
        (∑ lane : Fin 16,
            (if lane = 0 then oneVector else zeroVector) row) =
            ∑ lane : Fin 16, if lane = 0 then (1 : Rat) else 0 := by
          apply Finset.sum_congr rfl
          intro lane _
          by_cases hlane : lane = 0 <;>
            simp [hlane, zeroVector, oneVector]
        _ = 1 := Fintype.sum_ite_eq' (0 : Fin 16) (fun _ => (1 : Rat))
    simp [zeroEnsemble, cancellingEnsemble, zeroVector, hsum]

#print axioms scalarClaimsMatch_of_not_falseForCandidate
#print axioms not_falseForCandidate_of_scalarClaimsMatch
#print axioms gamma_combination_does_not_determine_lane_ensemble
#print axioms fourClaimDiscrepancy_eq_zero_outside_failures
#print axioms candidate_to_extracted_trace_outside_failures
#print axioms false_statement_outside_failures_implies_candidate_scalar_mismatch
#print axioms false_statement_implies_scalar_mismatch_or_earlier_failure
#print axioms false_statement_outside_all_candidate_failures

end AspisV5Tag67CandidateTraceExtraction

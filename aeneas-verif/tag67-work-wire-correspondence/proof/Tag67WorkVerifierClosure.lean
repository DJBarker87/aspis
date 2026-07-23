import Tag67DigestPredicateProof
import Tag67SixActualStepsExtractedProof
import Tag67WorkWireLE64Bridge

open Aeneas Aeneas.Std Result

namespace AspisTag67WorkVerifierClosure

open AspisFormal.V5ExactRuntimeWireRepair
open AspisV5NonceWorkAuthentication
open AspisTag67DigestPredicate
open AspisTag67SixActualSteps
open AspisTag67SixActualStepsExtracted
open tag67_six_actual_steps

abbrev GrindingDigest := Array Std.U8 32#usize

/-- The maintained `Nat`-indexed predicate is exactly the extracted `u8`
predicate when the difficulty has a Rust `u8` representative. -/
def digestHasLeadingZeroBitsNat (digest : GrindingDigest) (bits : Nat) : Prop :=
  ∃ rustBits : Std.U8,
    rustBits.val = bits ∧ digestHasLeadingZeroBits digest rustBits

def grindingOKFromComputedDigest {State : Type*}
    (actualTranscriptGrindingDigest : State → Nonce64 → GrindingDigest) :
    State → Nat → Nonce64 → Prop :=
  fun state bits nonce =>
    digestHasLeadingZeroBitsNat
      (actualTranscriptGrindingDigest state nonce) bits

def deployedRustBits : WorkKind → Std.U8
  | .batch => 37#u8
  | .fold ⟨0, _⟩ => 34#u8
  | .fold ⟨1, _⟩ => 33#u8
  | .fold ⟨2, _⟩ => 30#u8
  | .fold ⟨3, _⟩ => 25#u8
  | .finalQuery => 32#u8

theorem deployedRustBits_val (kind : WorkKind) :
    (deployedRustBits kind).val = kind.difficulty := by
  cases kind with
  | batch => decide
  | fold round => fin_cases round <;> decide
  | finalQuery => decide

theorem digestHasLeadingZeroBitsNat_deployed
    (digest : GrindingDigest) (kind : WorkKind) :
    digestHasLeadingZeroBitsNat digest kind.difficulty ↔
      digestHasLeadingZeroBits digest (deployedRustBits kind) := by
  constructor
  · rintro ⟨rustBits, hval, hpredicate⟩
    have heq : rustBits = deployedRustBits kind := by
      apply UScalar.eq_of_val_eq
      rw [hval, deployedRustBits_val]
    simpa [heq] using hpredicate
  · intro hpredicate
    exact ⟨deployedRustBits kind, deployedRustBits_val kind, hpredicate⟩

/-- Boolean returned by the extracted pure Rust digest predicate. -/
def extractedDigestCheck (digest : GrindingDigest) (bits : Std.U8) : Bool :=
  match aspis_core.transcript.digest_has_leading_zero_bits digest bits with
  | ok true => true
  | _ => false

theorem extractedDigestCheck_iff
    (digest : GrindingDigest) (bits : Std.U8) :
    extractedDigestCheck digest bits = true ↔
      digestHasLeadingZeroBits digest bits := by
  rw [← extracted_digest_predicate_iff_maintained]
  unfold extractedDigestCheck
  generalize hresult :
    aspis_core.transcript.digest_has_leading_zero_bits digest bits = result
  cases result with
  | ok value => cases value <;> simp
  | fail error => simp
  | div => simp

def actualComputedChecks {State : Type*}
    (actualTranscriptGrindingDigest : State → Nonce64 → GrindingDigest)
    (stateBefore : WorkKind → State) (view : WorkWireView) :
    SixComputedWorkChecks where
  batch := extractedDigestCheck
    (actualTranscriptGrindingDigest (stateBefore .batch) (view.nonces .batch))
    (deployedRustBits .batch)
  fold0 := extractedDigestCheck
    (actualTranscriptGrindingDigest (stateBefore (.fold 0))
      (view.nonces (.fold 0))) (deployedRustBits (.fold 0))
  fold1 := extractedDigestCheck
    (actualTranscriptGrindingDigest (stateBefore (.fold 1))
      (view.nonces (.fold 1))) (deployedRustBits (.fold 1))
  fold2 := extractedDigestCheck
    (actualTranscriptGrindingDigest (stateBefore (.fold 2))
      (view.nonces (.fold 2))) (deployedRustBits (.fold 2))
  fold3 := extractedDigestCheck
    (actualTranscriptGrindingDigest (stateBefore (.fold 3))
      (view.nonces (.fold 3))) (deployedRustBits (.fold 3))
  finalQuery := extractedDigestCheck
    (actualTranscriptGrindingDigest (stateBefore .finalQuery)
      (view.nonces .finalQuery)) (deployedRustBits .finalQuery)

def actualWorkFunctions {State Challenge : Type*}
    (actualTranscriptGrindingDigest : State → Nonce64 → GrindingDigest)
    (absorb : State → Nat →
      List AspisFormal.V5ExactRuntimeWireRepair.Byte → State)
    (executeNext : State → NextWorkAction → Challenge) :
    ExecutableWorkFunctions State Challenge where
  grindingOK := grindingOKFromComputedDigest actualTranscriptGrindingDigest
  absorb := absorb
  executeNext := executeNext

theorem actualComputedChecks_are_exact_predicates
    {State Challenge : Type*}
    (actualTranscriptGrindingDigest : State → Nonce64 → GrindingDigest)
    (absorb : State → Nat →
      List AspisFormal.V5ExactRuntimeWireRepair.Byte → State)
    (executeNext : State → NextWorkAction → Challenge)
    (stateBefore : WorkKind → State) (view : WorkWireView) :
    ComputedChecksAreActualPredicates
      (actualComputedChecks actualTranscriptGrindingDigest stateBefore view)
      (actualWorkFunctions actualTranscriptGrindingDigest absorb executeNext)
      stateBefore view := by
  intro kind
  change
    (actualComputedChecks actualTranscriptGrindingDigest stateBefore view).at
        kind = true ↔
      digestHasLeadingZeroBitsNat
        (actualTranscriptGrindingDigest (stateBefore kind) (view.nonces kind))
        kind.difficulty
  rw [digestHasLeadingZeroBitsNat_deployed
    (actualTranscriptGrindingDigest (stateBefore kind) (view.nonces kind)) kind]
  cases kind with
  | batch =>
      exact extractedDigestCheck_iff _ _
  | fold round =>
      fin_cases round <;> exact extractedDigestCheck_iff _ _
  | finalQuery =>
      exact extractedDigestCheck_iff _ _

/-- Source-extracted six-deep acceptance, after the six actual digest calls
have been evaluated once each. -/
def extractedSixStepAcceptance {State : Type*}
    (actualTranscriptGrindingDigest : State → Nonce64 → GrindingDigest)
    (stateBefore : WorkKind → State) (view : WorkWireView) : Prop :=
  let checks := actualComputedChecks
    actualTranscriptGrindingDigest stateBefore view
  tag67_proof_six_actual_steps
      checks.batch checks.fold0 checks.fold1 checks.fold2 checks.fold3
      checks.finalQuery
      (nonceToU64 (view.nonces .batch))
      (nonceToU64 (view.nonces (.fold 0)))
      (nonceToU64 (view.nonces (.fold 1)))
      (nonceToU64 (view.nonces (.fold 2)))
      (nonceToU64 (view.nonces (.fold 3)))
      (nonceToU64 (view.nonces .finalQuery)) =
    ok (some (extractedMaintainedTrace view))

/-- The generated Result/Option chain accepts exactly when all six positioned
check/absorb/next steps execute.  No correspondence premise remains. -/
theorem acceptanceIffExactSixSteps
    {State Challenge : Type*}
    (actualTranscriptGrindingDigest : State → Nonce64 → GrindingDigest)
    (absorb : State → Nat →
      List AspisFormal.V5ExactRuntimeWireRepair.Byte → State)
    (executeNext : State → NextWorkAction → Challenge)
    (stateBefore : WorkKind → State) (view : WorkWireView) :
    extractedSixStepAcceptance actualTranscriptGrindingDigest stateBefore view ↔
      ExecutableWorkAcceptance
        (actualWorkFunctions actualTranscriptGrindingDigest absorb executeNext)
        (positionedInputsFromActualOperations
          (actualWorkFunctions actualTranscriptGrindingDigest absorb executeNext)
          stateBefore view.nonces) := by
  unfold extractedSixStepAcceptance
  rw [extracted_success_iff_maintained_success]
  exact proofFacingSuccess_iff_exactSixActualSteps
    (actualComputedChecks actualTranscriptGrindingDigest stateBefore view)
    (actualWorkFunctions actualTranscriptGrindingDigest absorb executeNext)
    stateBefore view
    (actualComputedChecks_are_exact_predicates
      actualTranscriptGrindingDigest absorb executeNext stateBefore view)

/-- The only irreducible HashFn boundary: identify the digest returned by the
actual Transcript hash application with the maintained hash on the exact
state/domain/LE64 payload. -/
theorem exactGrindingHashInput
    {State : Type*}
    (actualTranscriptGrindingDigest : State → Nonce64 → GrindingDigest)
    (rustHash : State →
      List AspisFormal.V5ExactRuntimeWireRepair.Byte → GrindingDigest)
    (hHashApplication : ∀ state nonce,
      actualTranscriptGrindingDigest state nonce =
        rustHash state (grindingHashPayload nonce)) :
    HashRandomOracleWorkInterface rustHash digestHasLeadingZeroBitsNat
      (grindingOKFromComputedDigest actualTranscriptGrindingDigest) := by
  intro state bits nonce
  change digestHasLeadingZeroBitsNat
      (actualTranscriptGrindingDigest state nonce) bits ↔
    digestHasLeadingZeroBitsNat
      (rustHash state (grindingHashPayload nonce)) bits
  rw [hHashApplication]

/-- `ExactRustWorkVerifierCorrespondence` is reduced to the single concrete
HashFn-application equation above; its acceptance field is discharged by the
source-extracted six-step theorem. -/
theorem exactRustWorkVerifierCorrespondence_of_hash_application
    {State Challenge : Type*}
    (actualTranscriptGrindingDigest : State → Nonce64 → GrindingDigest)
    (rustHash : State →
      List AspisFormal.V5ExactRuntimeWireRepair.Byte → GrindingDigest)
    (absorb : State → Nat →
      List AspisFormal.V5ExactRuntimeWireRepair.Byte → State)
    (executeNext : State → NextWorkAction → Challenge)
    (stateBefore : WorkKind → State) (view : WorkWireView)
    (hHashApplication : ∀ state nonce,
      actualTranscriptGrindingDigest state nonce =
        rustHash state (grindingHashPayload nonce)) :
    ExactRustWorkVerifierCorrespondence
      (extractedSixStepAcceptance actualTranscriptGrindingDigest stateBefore view)
      rustHash digestHasLeadingZeroBitsNat
      (actualWorkFunctions actualTranscriptGrindingDigest absorb executeNext)
      (positionedInputsFromActualOperations
        (actualWorkFunctions actualTranscriptGrindingDigest absorb executeNext)
        stateBefore view.nonces) := by
  constructor
  · exact exactGrindingHashInput
      actualTranscriptGrindingDigest rustHash hHashApplication
  · exact acceptanceIffExactSixSteps
      actualTranscriptGrindingDigest absorb executeNext stateBefore view

/-- Final composition: generated wire guards/reads existentially construct
the maintained view, and that same view feeds the extracted six-step verifier.
There is no arbitrary-view/projection premise and only one HashFn application
equation. -/
theorem tag67AcceptedWireAndVerifierClosure
    {State Challenge : Type*}
    (shape : RuntimeShape) (wire : RuntimeExactWire shape)
    (hfit : runtimeRepairedProofBytes shape ≤ Std.Usize.max)
    (fold0 fold1 fold2 fold3 batch final : Std.U64) (selected : Std.U8)
    (hmagic : aspis_verifier.v5_cu_probe.v5_work_wire_magic_is_valid
      (AspisTag67WorkWireMaintained.serializedRuntimeSlice shape wire hfit) =
        ok true)
    (hfold0 : aspis_verifier.v5_cu_probe.v5_work_wire_u64
      (AspisTag67WorkWireMaintained.serializedRuntimeSlice shape wire hfit)
        11048#usize = ok fold0)
    (hfold1 : aspis_verifier.v5_cu_probe.v5_work_wire_u64
      (AspisTag67WorkWireMaintained.serializedRuntimeSlice shape wire hfit)
        11056#usize = ok fold1)
    (hfold2 : aspis_verifier.v5_cu_probe.v5_work_wire_u64
      (AspisTag67WorkWireMaintained.serializedRuntimeSlice shape wire hfit)
        11064#usize = ok fold2)
    (hfold3 : aspis_verifier.v5_cu_probe.v5_work_wire_u64
      (AspisTag67WorkWireMaintained.serializedRuntimeSlice shape wire hfit)
        11072#usize = ok fold3)
    (hbatch : aspis_verifier.v5_cu_probe.v5_work_wire_u64
      (AspisTag67WorkWireMaintained.serializedRuntimeSlice shape wire hfit)
        11080#usize = ok batch)
    (hfinal : aspis_verifier.v5_cu_probe.v5_work_wire_u64
      (AspisTag67WorkWireMaintained.serializedRuntimeSlice shape wire hfit)
        19127#usize = ok final)
    (hselector : Slice.index_usize
      (AspisTag67WorkWireMaintained.serializedRuntimeSlice shape wire hfit)
        19135#usize = ok selected)
    (hzero : aspis_verifier.v5_cu_probe.v5_relation_final_zero_tail_is_valid
      (AspisTag67WorkWireMaintained.serializedRelationFinalSlice
        shape wire hfit) = ok true)
    (actualTranscriptGrindingDigest : State → Nonce64 → GrindingDigest)
    (rustHash : State →
      List AspisFormal.V5ExactRuntimeWireRepair.Byte → GrindingDigest)
    (absorb : State → Nat →
      List AspisFormal.V5ExactRuntimeWireRepair.Byte → State)
    (executeNext : State → NextWorkAction → Challenge)
    (stateBefore : WorkKind → State)
    (hHashApplication : ∀ state nonce,
      actualTranscriptGrindingDigest state nonce =
        rustHash state (grindingHashPayload nonce)) :
    ∃ view : WorkWireView,
      view = AspisTag67WorkWireMaintained.decodedWorkWireView
        fold0 fold1 fold2 fold3 batch final ∧
      projectWorkWire shape wire = canonicalWorkWire view ∧
      aspis_verifier.v5_cu_probe.project_v5_work_wire
        (AspisTag67WorkWireMaintained.serializedRuntimeSlice shape wire hfit) =
          ok {
            fold_nonces := Array.make 4#usize [fold0, fold1, fold2, fold3]
            batch_nonce := batch
            final_nonce := final
            query_selector := selected
          } ∧
      ExactRustWorkVerifierCorrespondence
        (extractedSixStepAcceptance
          actualTranscriptGrindingDigest stateBefore view)
        rustHash digestHasLeadingZeroBitsNat
        (actualWorkFunctions
          actualTranscriptGrindingDigest absorb executeNext)
        (positionedInputsFromActualOperations
          (actualWorkFunctions
            actualTranscriptGrindingDigest absorb executeNext)
          stateBefore view.nonces) := by
  rcases AspisTag67WorkWireMaintained.generated_acceptance_constructs_exact_work_wire_view
      shape wire hfit fold0 fold1 fold2 fold3 batch final selected
      hmagic hfold0 hfold1 hfold2 hfold3 hbatch hfinal hselector hzero with
    ⟨view, hview, hprojection, hprojector⟩
  refine ⟨view, hview, hprojection, hprojector, ?_⟩
  exact exactRustWorkVerifierCorrespondence_of_hash_application
    actualTranscriptGrindingDigest rustHash absorb executeNext
    stateBefore view hHashApplication

#print axioms deployedRustBits_val
#print axioms digestHasLeadingZeroBitsNat_deployed
#print axioms extractedDigestCheck_iff
#print axioms actualComputedChecks_are_exact_predicates
#print axioms acceptanceIffExactSixSteps
#print axioms exactGrindingHashInput
#print axioms exactRustWorkVerifierCorrespondence_of_hash_application
#print axioms tag67AcceptedWireAndVerifierClosure

end AspisTag67WorkVerifierClosure

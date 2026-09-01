import AspisFormal.K1.V7Tag73ExactFoldWorkExposureTrial

/-!
# Literal source separation for the outer fold-work coordinate

The fold-work query has the deployed 41-byte grinding grammar.  Therefore no
33-byte squeeze/advance answer used by alpha or q16 can occupy the same root
exposure.  The remaining 41-byte final-work case is deliberately not decided
here; it must be discharged by the clean transcript-collision accounting.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73FoldOuterSourceSeparation

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFoldWorkExposureTrial
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

theorem selected_record_eq_of_equal_prefix_length
    {records priorLeft laterLeft priorRight laterRight :
      List UnifiedExposureRecord}
    {left right : UnifiedExposureRecord}
    (leftExact : records = priorLeft ++ left :: laterLeft)
    (rightExact : records = priorRight ++ right :: laterRight)
    (sameIndex : priorLeft.length = priorRight.length) :
    left = right := by
  have leftAt : records[priorLeft.length]? = some left := by
    rw [leftExact]
    simp
  have rightAt : records[priorRight.length]? = some right := by
    rw [rightExact]
    simp
  rw [sameIndex, rightAt] at leftAt
  exact Option.some.inj leftAt.symm

theorem machine_fresh_prefix_lengths_ne_of_input_lengths_ne
    {records priorLeft laterLeft priorRight laterRight :
      List UnifiedExposureRecord}
    {leftActor rightActor : QueryActor}
    {leftInput rightInput : ShaInput}
    {leftAnswer rightAnswer : Digest256}
    (leftExact : records = priorLeft ++
      (.machineFresh leftActor leftInput leftAnswer : UnifiedExposureRecord) ::
        laterLeft)
    (rightExact : records = priorRight ++
      (.machineFresh rightActor rightInput rightAnswer : UnifiedExposureRecord) ::
        laterRight)
    (differentLengths : leftInput.length ≠ rightInput.length) :
    priorLeft.length ≠ priorRight.length := by
  intro sameIndex
  have recordExact := selected_record_eq_of_equal_prefix_length leftExact
    rightExact sameIndex
  have inputExact : leftInput = rightInput := by
    injection recordExact
  exact differentLengths (congrArg List.length inputExact)

@[simp] theorem literal_fold_work_input_length
    (digest : Digest256) (nonce : NonceBytes) :
    (bytes digest ++ [domGrind] ++ bytes nonce).length = 41 := by
  simp [bytes_length]

/-- Any literal 33-byte root coordinate is at a different compiler exposure
from the accepted fold-work coordinate. -/
theorem exact_33_byte_root_prefix_ne_fold_trial
    {HiddenTape TapeIdentity Observation Statement Payload Result : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Result parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (foldTrial : ExactCompilerExposureTrial parameters)
    (foldDigest foldAnswer : Digest256)
    (foldActor : QueryActor) (foldPrior foldLater : List UnifiedExposureRecord)
    (foldExact : exactFixedRootRecords input.package.root =
      foldPrior ++
        (.machineFresh foldActor
          (bytes foldDigest ++ [domGrind] ++
            bytes (exactOperationalTape input).messages.foldGrinding.selected)
          foldAnswer : UnifiedExposureRecord) :: foldLater)
    (trialExact : foldTrial.val = foldPrior.length)
    (actor : QueryActor) (queryInput : ShaInput) (answer : Digest256)
    (prior later : List UnifiedExposureRecord)
    (decomposition : exactFixedRootRecords input.package.root =
      prior ++ (.machineFresh actor queryInput answer : UnifiedExposureRecord) ::
        later)
    (inputLength : queryInput.length = 33) :
    prior.length ≠ foldTrial.val := by
  rw [trialExact]
  apply machine_fresh_prefix_lengths_ne_of_input_lengths_ne decomposition
    foldExact
  rw [inputLength, literal_fold_work_input_length]
  decide

#print axioms selected_record_eq_of_equal_prefix_length
#print axioms machine_fresh_prefix_lengths_ne_of_input_lengths_ne
#print axioms literal_fold_work_input_length
#print axioms exact_33_byte_root_prefix_ne_fold_trial

end

end AspisK1.V7Tag73FoldOuterSourceSeparation

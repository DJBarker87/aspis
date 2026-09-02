import AspisFormal.K1.V7Tag73ExactRootLookupCausalOrder
import AspisFormal.K1.V7Tag73SqueezeInputStateInjectivity

/-!
# Generic reverse closure for retained causal digest chains

This module factors the common argument used when two accepted Tag-73 fork
fibres retain the same first-creation record prefix.  Starting at a typed
absorption boundary, every later state-changing oracle input literally begins
with the preceding transcript digest.  If the terminal answers agree and the
retained answers are unique, the chains can be walked backwards without any
SHA-256 injectivity assumption.

The only grammar premise is cross-chain boundary separation.  It rules out
one chain reaching its typed boundary while the other still points at a later
state-changing input.  For the K1.3 application the boundary is the C2-root
absorption, whose label/length is disjoint from every later transition.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73ExactRootCausalChain

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactRootLookupCausalOrder
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73SqueezeInputStateInjectivity
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-- A retained causal chain of transcript-state answers.  The boundary record
produces the initial state.  Every later record has an input whose first 32
bytes are exactly the preceding state digest. -/
inductive ExactRetainedDigestChain
    (prior : List UnifiedExposureRecord) (boundaryInput : ShaInput)
    (allowedInput : ShaInput → Prop) :
    Digest256 → Digest256 → Prop
  | boundary (initial : Digest256) (actor : QueryActor)
      (member : (.machineFresh actor boundaryInput initial :
        UnifiedExposureRecord) ∈ prior) :
      ExactRetainedDigestChain prior boundaryInput allowedInput initial initial
  | step (initial current next : Digest256) (input : ShaInput)
      (actor : QueryActor)
      (chain : ExactRetainedDigestChain prior boundaryInput allowedInput initial
        current)
      (causalPrefix : HasLiteralStatePrefix current input)
      (allowed : allowedInput input)
      (member : (.machineFresh actor input next : UnifiedExposureRecord) ∈
        prior) :
      ExactRetainedDigestChain prior boundaryInput allowedInput initial next

private theorem equal_answer_records_fix_input
    {prior : List UnifiedExposureRecord}
    (answersNodup : (prior.map UnifiedExposureRecord.answer).Nodup)
    {leftActor rightActor : QueryActor}
    {leftInput rightInput : ShaInput} {answer : Digest256}
    (leftMember :
      (.machineFresh leftActor leftInput answer : UnifiedExposureRecord) ∈
        prior)
    (rightMember :
      (.machineFresh rightActor rightInput answer : UnifiedExposureRecord) ∈
        prior) :
    leftInput = rightInput := by
  have recordExact :
      (.machineFresh leftActor leftInput answer : UnifiedExposureRecord) =
        .machineFresh rightActor rightInput answer := by
    apply List.inj_on_of_nodup_map answersNodup leftMember rightMember
    rfl
  injection recordExact

private theorem literal_prefix_input_eq_fixes_digest
    {leftDigest rightDigest : Digest256} {leftInput rightInput : ShaInput}
    (leftPrefix : HasLiteralStatePrefix leftDigest leftInput)
    (rightPrefix : HasLiteralStatePrefix rightDigest rightInput)
    (inputExact : leftInput = rightInput) :
    leftDigest = rightDigest := by
  apply digest_bytes_injective
  calc
    bytes leftDigest = leftInput.take 32 := leftPrefix
    _ = rightInput.take 32 := by rw [inputExact]
    _ = bytes rightDigest := rightPrefix.symm

/-- Reverse two retained causal chains from a common terminal answer to their
typed boundary inputs.  This is a random-oracle first-creation argument, not
hash injectivity: equal answers select one retained record, and literal state
prefixes expose the predecessor digest.

The cross-chain allowed-input separation premises rule out unequal chain
lengths.  They are intentionally stated in both directions because the two
boundary payloads may contain different prover-supplied bytes before equality
is proved. -/
theorem exact_retained_digest_chains_boundary_input_eq
    {prior : List UnifiedExposureRecord}
    (answersNodup : (prior.map UnifiedExposureRecord.answer).Nodup)
    {leftBoundary rightBoundary : ShaInput}
    {leftAllowed rightAllowed : ShaInput → Prop}
    {leftInitial rightInitial terminal : Digest256}
    (leftChain : ExactRetainedDigestChain prior leftBoundary leftAllowed
      leftInitial terminal)
    (rightChain : ExactRetainedDigestChain prior rightBoundary rightAllowed
      rightInitial terminal)
    (leftBoundaryAvoidsRight : ∀ input, rightAllowed input →
      leftBoundary ≠ input)
    (rightBoundaryAvoidsLeft : ∀ input, leftAllowed input →
      rightBoundary ≠ input) :
    leftBoundary = rightBoundary := by
  revert rightInitial rightChain leftBoundaryAvoidsRight
    rightBoundaryAvoidsLeft
  induction leftChain with
  | boundary leftActor leftMember =>
      intro rightInitial rightChain leftBoundaryAvoidsRight
        rightBoundaryAvoidsLeft
      cases rightChain with
      | boundary rightActor rightMember =>
          exact equal_answer_records_fix_input answersNodup leftMember
            rightMember
      | step rightCurrent terminal rightInput rightActor
          rightPrevious rightPrefix rightAllowedInput rightMember =>
          have inputExact : leftBoundary = rightInput :=
            equal_answer_records_fix_input answersNodup leftMember rightMember
          have inputNe : leftBoundary ≠ rightInput :=
            leftBoundaryAvoidsRight rightInput rightAllowedInput
          exact (inputNe inputExact).elim
  | step leftCurrent terminal leftInput leftActor leftPrevious
      leftPrefix leftAllowedInput leftMember ih =>
      intro rightInitial rightChain leftBoundaryAvoidsRight
        rightBoundaryAvoidsLeft
      cases rightChain with
      | boundary rightActor rightMember =>
          have inputExact : leftInput = rightBoundary :=
            equal_answer_records_fix_input answersNodup leftMember rightMember
          have inputNe : rightBoundary ≠ leftInput :=
            rightBoundaryAvoidsLeft leftInput leftAllowedInput
          exact (inputNe inputExact.symm).elim
      | step rightCurrent terminal rightInput rightActor
          rightPrevious rightPrefix rightAllowedInput rightMember =>
          have inputExact : leftInput = rightInput :=
            equal_answer_records_fix_input answersNodup leftMember rightMember
          have currentExact : leftCurrent = rightCurrent :=
            literal_prefix_input_eq_fixes_digest leftPrefix rightPrefix
              inputExact
          subst rightCurrent
          exact ih rightPrevious leftBoundaryAvoidsRight
            rightBoundaryAvoidsLeft

#print axioms exact_retained_digest_chains_boundary_input_eq

end

end AspisK1.V7Tag73ExactRootCausalChain

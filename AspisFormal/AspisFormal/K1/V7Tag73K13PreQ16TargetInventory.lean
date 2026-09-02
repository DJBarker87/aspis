import AspisFormal.K1.V7Tag73K13PreQ16MerkleWordSource
import AspisFormal.K1.V7Tag73ExactPairRootAbsorbChainClosure
import AspisFormal.K1.V7Tag73RootAbsorbInputInjectivity
import AspisFormal.K1.V7Tag73K12Merkle208PrefixProjection

/-!
# Prefix-measurable Merkle target inventory before q16

The first unresolved target of a binary Merkle path is either its public root
or one of the two child digests contained in an already-resolved node input.
For the adversary-first q16 case we need a target inventory that is available
from the chronological SHA inputs alone, without inspecting a future opening.

Four fixed 26-byte slices suffice as a conservative inventory for each input:

* offsets 1 and 27 cover the children of `0x11 || left || right`;
* offsets 34 and 35 cover the deployed C2 and C1 transcript-root positions.

Short or unrelated inputs merely contribute deterministic padded candidates.
That over-approximation is harmless and keeps the cardinality bounded by four
per already-visible SHA input.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73K13PreQ16TargetInventory

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73AdaptiveQ16TrialAccounting
open AspisK1.V7Tag73AtomicForkUniformScheduler
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedFullRunFactorization
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedQ16JointEventHandoff
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactPairRootAbsorbChainClosure
open AspisK1.V7Tag73ExactRootCausalChain
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73FutureFreeCheckedRefinementBisimulation
open AspisK1.V7Tag73IndexedAlignedRecordReplay
open AspisK1.V7Tag73K13PreQ16MerkleWordSource
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73RawProverMessages
open AspisK1.V7Tag73K12Merkle208PrefixProjection
open AspisPool.V7MerkleQueryGrammar
open AspisPool.V7MerkleQueryExtractor
open AspisPool.V7MerklePartialPathExtractor

noncomputable section

abbrev MerkleDigest208 := AspisPool.V7MerkleQueryGrammar.Digest208

/-- The four fixed digest locations relevant to Tag-73 Merkle nodes and root
absorptions.  The use of `fixedOfListD` makes this total on arbitrary SHA
inputs while preserving exact values on the deployed fixed-width encodings. -/
def rawInputMerkleCandidates (input : RawHashInput) : Finset MerkleDigest208 :=
  [ fixedOfListD ((input.drop 1).take 26),
    fixedOfListD ((input.drop 27).take 26),
    fixedOfListD ((input.drop 34).take 26),
    fixedOfListD ((input.drop 35).take 26) ].toFinset

theorem rawInputMerkleCandidates_card_le_four (input : RawHashInput) :
    (rawInputMerkleCandidates input).card ≤ 4 := by
  unfold rawInputMerkleCandidates
  exact (List.toFinset_card_le _).trans (by simp)

theorem node_left_mem_rawInputMerkleCandidates
    (left right : MerkleDigest208) :
    left ∈ rawInputMerkleCandidates (serialize (.node left right)) := by
  have slice : ((serialize (.node left right)).drop 1).take 26 =
      fixedBytes left := by
    simp [serialize, fixedBytes_length]
  rw [rawInputMerkleCandidates, List.mem_toFinset]
  simp only [List.mem_cons]
  exact Or.inl (by rw [slice, fixedOfListD_fixedBytes])

theorem node_right_mem_rawInputMerkleCandidates
    (left right : MerkleDigest208) :
    right ∈ rawInputMerkleCandidates (serialize (.node left right)) := by
  have slice : ((serialize (.node left right)).drop 27).take 26 =
      fixedBytes right := by
    simp [serialize, fixedBytes_length]
  rw [rawInputMerkleCandidates, List.mem_toFinset]
  simp only [List.mem_cons]
  exact Or.inr (Or.inl (by rw [slice, fixedOfListD_fixedBytes]))

theorem c1_root_mem_rawInputMerkleCandidates
    (before : Digest256)
    (root : AspisK1.V7Tag73TranscriptSchedule.Digest208)
    (salt : Digest256) :
    runtimeDigest208ToMerkleDigest root ∈ rawInputMerkleCandidates
      (runtimeInputToRawHashInput
        (bytes before ++ [domAbsorb, c1RootLabel] ++
          (Payload.c1Root root salt).data)) := by
  let input := bytes before ++ [domAbsorb, c1RootLabel] ++
    (Payload.c1Root root salt).data
  let inputPrefix := bytes before ++ [domAbsorb, c1RootLabel, 0]
  have prefixLength : inputPrefix.length = 35 := by
    simp [inputPrefix, bytes_length]
  have normalized : input = inputPrefix ++ bytes root ++ bytes salt := by
    simp [input, inputPrefix, Payload.data, List.append_assoc]
  have runtimeSlice : (input.drop 35).take 26 = bytes root := by
    rw [normalized]
    simp [prefixLength, bytes_length, List.append_assoc]
  have rawSlice :
      ((runtimeInputToRawHashInput input).drop 35).take 26 =
        fixedBytes (runtimeDigest208ToMerkleDigest root) := by
    unfold runtimeInputToRawHashInput
    rw [← List.map_drop, ← List.map_take, runtimeSlice]
    apply List.ext_get
    · simp [fixedBytes, bytes_length]
    · intro index leftBound rightBound
      simp [fixedBytes, bytes, runtimeDigest208ToMerkleDigest]
  rw [rawInputMerkleCandidates, List.mem_toFinset]
  simp only [List.mem_cons]
  exact Or.inr (Or.inr (Or.inr (Or.inl (by
    rw [rawSlice, fixedOfListD_fixedBytes]))))

theorem c2_root_mem_rawInputMerkleCandidates
    (before : Digest256)
    (root : AspisK1.V7Tag73TranscriptSchedule.Digest208)
    (salt : Digest256) :
    runtimeDigest208ToMerkleDigest root ∈ rawInputMerkleCandidates
      (runtimeInputToRawHashInput
        (bytes before ++ [domAbsorb, c2RootLabel] ++
          (Payload.c2Root root salt).data)) := by
  let input := bytes before ++ [domAbsorb, c2RootLabel] ++
    (Payload.c2Root root salt).data
  let inputPrefix := bytes before ++ [domAbsorb, c2RootLabel]
  have prefixLength : inputPrefix.length = 34 := by
    simp [inputPrefix, bytes_length]
  have normalized : input = inputPrefix ++ bytes root ++ bytes salt := by
    simp [input, inputPrefix, Payload.data, List.append_assoc]
  have runtimeSlice : (input.drop 34).take 26 = bytes root := by
    rw [normalized]
    simp [prefixLength, bytes_length, List.append_assoc]
  have rawSlice :
      ((runtimeInputToRawHashInput input).drop 34).take 26 =
        fixedBytes (runtimeDigest208ToMerkleDigest root) := by
    unfold runtimeInputToRawHashInput
    rw [← List.map_drop, ← List.map_take, runtimeSlice]
    apply List.ext_get
    · simp [fixedBytes, bytes_length]
    · intro index leftBound rightBound
      simp [fixedBytes, bytes, runtimeDigest208ToMerkleDigest]
  rw [rawInputMerkleCandidates, List.mem_toFinset]
  simp only [List.mem_cons]
  exact Or.inr (Or.inr (Or.inl (by
    rw [rawSlice, fixedOfListD_fixedBytes])))

/-- Conservative Merkle target inventory exposed by a chronological raw-query
prefix.  It is a function only of inputs known before the next oracle answer. -/
def prefixMerkleCandidateSet (log : OrderedRawQueryLog) :
    Finset MerkleDigest208 :=
  log.toFinset.biUnion rawInputMerkleCandidates

theorem rawInput_candidate_mem_prefixMerkleCandidateSet
    (log : OrderedRawQueryLog) (input : RawHashInput)
    (inputMem : input ∈ log) (target : MerkleDigest208)
    (targetMem : target ∈ rawInputMerkleCandidates input) :
    target ∈ prefixMerkleCandidateSet log := by
  exact Finset.mem_biUnion.mpr
    ⟨input, List.mem_toFinset.mpr inputMem, targetMem⟩

theorem retainedDigestChain_boundary_member
    (records : List UnifiedExposureRecord) (boundaryInput : ShaInput)
    (allowedInput : ShaInput → Prop) (initial terminal : Digest256)
    (chain : ExactRetainedDigestChain records boundaryInput allowedInput
      initial terminal) :
    ∃ actor,
      (.machineFresh actor boundaryInput initial : UnifiedExposureRecord) ∈
        records := by
  induction chain with
  | boundary actor member => exact ⟨actor, member⟩
  | step current next input actor chain causalPrefix allowed member ih =>
      exact ih

theorem machineFresh_input_mem_exposurePrefixRawQueries
    (records : List UnifiedExposureRecord) (actor : QueryActor)
    (input : ShaInput) (answer : Digest256)
    (member : (.machineFresh actor input answer : UnifiedExposureRecord) ∈
      records) :
    runtimeInputToRawHashInput input ∈ exposurePrefixRawQueries records := by
  unfold exposurePrefixRawQueries
  apply List.mem_map.mpr
  refine ⟨input, ?_, rfl⟩
  apply List.mem_filterMap.mpr
  exact ⟨.machineFresh actor input answer, member, rfl⟩

theorem c1_root_mem_prefixMerkleCandidateSet_of_retained
    (records : List UnifiedExposureRecord)
    (before : Digest256)
    (root : AspisK1.V7Tag73TranscriptSchedule.Digest208)
    (salt answer terminal : Digest256)
    (allowedInput : ShaInput → Prop)
    (chain : ExactRetainedDigestChain records
      (bytes before ++ [domAbsorb, c1RootLabel] ++
        (Payload.c1Root root salt).data)
      allowedInput answer terminal) :
    runtimeDigest208ToMerkleDigest root ∈
      prefixMerkleCandidateSet (exposurePrefixRawQueries records) := by
  obtain ⟨actor, member⟩ := retainedDigestChain_boundary_member _ _ _ _ _ chain
  apply rawInput_candidate_mem_prefixMerkleCandidateSet
      (exposurePrefixRawQueries records)
      (runtimeInputToRawHashInput
        (bytes before ++ [domAbsorb, c1RootLabel] ++
          (Payload.c1Root root salt).data))
  · exact machineFresh_input_mem_exposurePrefixRawQueries _ actor _ answer member
  · exact c1_root_mem_rawInputMerkleCandidates before root salt

theorem c2_root_mem_prefixMerkleCandidateSet_of_retained
    (records : List UnifiedExposureRecord)
    (before : Digest256)
    (root : AspisK1.V7Tag73TranscriptSchedule.Digest208)
    (salt answer terminal : Digest256)
    (allowedInput : ShaInput → Prop)
    (chain : ExactRetainedDigestChain records
      (bytes before ++ [domAbsorb, c2RootLabel] ++
        (Payload.c2Root root salt).data)
      allowedInput answer terminal) :
    runtimeDigest208ToMerkleDigest root ∈
      prefixMerkleCandidateSet (exposurePrefixRawQueries records) := by
  obtain ⟨actor, member⟩ := retainedDigestChain_boundary_member _ _ _ _ _ chain
  apply rawInput_candidate_mem_prefixMerkleCandidateSet
      (exposurePrefixRawQueries records)
      (runtimeInputToRawHashInput
        (bytes before ++ [domAbsorb, c2RootLabel] ++
          (Payload.c2Root root salt).data))
  · exact machineFresh_input_mem_exposurePrefixRawQueries _ actor _ answer member
  · exact c2_root_mem_rawInputMerkleCandidates before root salt

/-- At most four candidate 208-bit targets are retained per prior SHA input. -/
theorem prefixMerkleCandidateSet_card_le (log : OrderedRawQueryLog) :
    (prefixMerkleCandidateSet log).card ≤ log.length * 4 := by
  calc
    (prefixMerkleCandidateSet log).card ≤ log.toFinset.card * 4 := by
      apply Finset.card_biUnion_le_card_mul
      intro input inputMem
      exact rawInputMerkleCandidates_card_le_four input
    _ ≤ log.length * 4 := Nat.mul_le_mul_right 4 (List.toFinset_card_le log)

/-- Lifting the conservative inventory back to complete SHA-256 outputs costs
exactly the expected `2^48` factor and no independence assumption. -/
theorem prefixMerkleCandidatePreimage_card_le (log : OrderedRawQueryLog) :
    (deployedPrefixTargetPreimage (prefixMerkleCandidateSet log)).card ≤
      (log.length * 4) * 2 ^ 48 := by
  exact deployed_prefix_target_preimage_card_le
    (prefixMerkleCandidateSet log) (prefixMerkleCandidateSet_card_le log)

/-- Once the current root/child target is in the byte-derived inventory, the
entire first-unresolved traversal stays inside that same prefix-measurable
inventory. -/
theorem firstUnresolvedTarget_mem_prefixMerkleCandidateSet
    {Leaf : Type} (parseLeaf : RawHashInput → Option Leaf)
    (truncateSha256 : RawHashInput → MerkleDigest208)
    (log : OrderedRawQueryLog) :
    ∀ (height : Nat) (current : MerkleDigest208) (position : Nat)
      (target : MerkleDigest208),
      current ∈ prefixMerkleCandidateSet log →
      firstUnresolvedTarget parseLeaf truncateSha256 log height current
          position = some target →
      target ∈ prefixMerkleCandidateSet log := by
  intro height
  induction height with
  | zero =>
      intro current position target currentMem targetExact
      cases resolvedExact : resolveInput truncateSha256 current log with
      | none =>
          simp [firstUnresolvedTarget, resolvedExact] at targetExact
          simpa [targetExact] using currentMem
      | some input =>
          cases leafExact : parseLeaf input with
          | none =>
              simp [firstUnresolvedTarget, resolvedExact, leafExact] at targetExact
              simpa [targetExact] using currentMem
          | some leaf =>
              simp [firstUnresolvedTarget, resolvedExact, leafExact] at targetExact
  | succ height ih =>
      intro current position target currentMem targetExact
      cases resolvedExact : resolveInput truncateSha256 current log with
      | none =>
          simp [firstUnresolvedTarget, resolvedExact] at targetExact
          simpa [targetExact] using currentMem
      | some input =>
          have inputMem : input ∈ log :=
            resolveInput_success_mem truncateSha256 current log input
              resolvedExact
          cases typedExact : parseTypedPreimage input with
          | none =>
              simp [firstUnresolvedTarget, resolvedExact, typedExact] at targetExact
              simpa [targetExact] using currentMem
          | some typed =>
              cases typed with
              | c1Leaf value salt =>
                  simp [firstUnresolvedTarget, resolvedExact, typedExact] at targetExact
                  simpa [targetExact] using currentMem
              | c2Leaf value salt =>
                  simp [firstUnresolvedTarget, resolvedExact, typedExact] at targetExact
                  simpa [targetExact] using currentMem
              | node left right =>
                  have inputSerialized : input = serialize (.node left right) :=
                    (parseTypedPreimage_success_reserializes input
                      (.node left right) typedExact).symm
                  by_cases direction : position.testBit height
                  · apply ih right position target
                    · apply rawInput_candidate_mem_prefixMerkleCandidateSet
                        log input inputMem
                      rw [inputSerialized]
                      exact node_right_mem_rawInputMerkleCandidates left right
                    · simpa [firstUnresolvedTarget, resolvedExact, typedExact,
                        direction] using targetExact
                  · have directionFalse : position.testBit height = false :=
                      Bool.eq_false_iff.mpr direction
                    apply ih left position target
                    · apply rawInput_candidate_mem_prefixMerkleCandidateSet
                        log input inputMem
                      rw [inputSerialized]
                      exact node_left_mem_rawInputMerkleCandidates left right
                    · simpa [firstUnresolvedTarget, resolvedExact, typedExact,
                        directionFalse] using targetExact

/-- Every first-unresolved target selected by the two-tree opening inventory is
already present in the proof-independent byte inventory, provided the two
public roots have appeared in their canonical pre-q16 absorb inputs. -/
theorem prefixResolutionTargetSet_subset_prefixMerkleCandidateSet
    (truncateSha256 : RawHashInput → MerkleDigest208)
    (log : OrderedRawQueryLog) (roots : Roots)
    (proof : TwoTreeOpeningProof)
    (c1RootMem : roots.c1 ∈ prefixMerkleCandidateSet log)
    (c2RootMem : roots.c2 ∈ prefixMerkleCandidateSet log) :
    prefixResolutionTargetSet truncateSha256 log roots proof ⊆
      prefixMerkleCandidateSet log := by
  intro target targetMem
  have targetListMem :
      target ∈ prefixResolutionTargetList truncateSha256 log roots proof :=
    List.mem_toFinset.mp targetMem
  rw [prefixResolutionTargetList, List.mem_append] at targetListMem
  rcases targetListMem with c1TargetMem | c2TargetMem
  · obtain ⟨candidate, candidateMem, candidateExact⟩ :=
      List.mem_filterMap.mp c1TargetMem
    have candidateExact' : candidate = some target := by
      simpa using candidateExact
    subst candidate
    obtain ⟨ordinal, targetExact⟩ := List.mem_ofFn.mp candidateMem
    exact firstUnresolvedTarget_mem_prefixMerkleCandidateSet parseC1Leaf
      truncateSha256 log treeDepth roots.c1 (proof ordinal).position.val target
      c1RootMem (by simpa [firstUnresolvedC1Target] using targetExact)
  · obtain ⟨candidate, candidateMem, candidateExact⟩ :=
      List.mem_filterMap.mp c2TargetMem
    have candidateExact' : candidate = some target := by
      simpa using candidateExact
    subst candidate
    obtain ⟨ordinal, targetExact⟩ := List.mem_ofFn.mp candidateMem
    exact firstUnresolvedTarget_mem_prefixMerkleCandidateSet parseC2Leaf
      truncateSha256 log treeDepth roots.c2 (proof ordinal).position.val target
      c2RootMem (by simpa [firstUnresolvedC2Target] using targetExact)

/-- For an actual accepted K1.3 trial, both transcript roots and therefore all
first-unresolved opening targets are already determined by the chronological
record prefix before the selected final-work/q16 coordinate. -/
theorem exact_actual_trial_prefixResolutionTargetSet_subset
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {sample : ExactCompilerSample HiddenTape parameters}
    (transitionRoom : 2 ≤ transitionFuel)
    (input : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance sample)
    (trial : ExactCompilerExposureTrial parameters)
    (actual : ExactFixedK13ActualJointTrial input trial)
    (prior later : List UnifiedExposureRecord)
    (pivotActor : QueryActor) (pivotInput : ShaInput)
    (pivotAnswer : Digest256)
    (rootExact : exactFixedRootRecords input.package.root =
      prior ++ (.machineFresh pivotActor pivotInput pivotAnswer :
        UnifiedExposureRecord) :: later)
    (trialExact : trial.val = prior.length) :
    prefixResolutionTargetSet (exactK12Truncate input)
        (exposurePrefixRawQueries prior) (exactK12Roots input)
        (exactK12Openings input) ⊆
      prefixMerkleCandidateSet (exposurePrefixRawQueries prior) := by
  obtain ⟨c1Before, c2Before, c1Salt, c2Salt, c1Answer, c2Answer,
      terminal, c1Chain, c2Chain, terminalPrefix⟩ :=
    exact_actual_trial_retains_root_chains transitionRoom input trial actual
      prior later pivotActor pivotInput pivotAnswer rootExact trialExact
  apply prefixResolutionTargetSet_subset_prefixMerkleCandidateSet
  · change runtimeDigest208ToMerkleDigest
      (exactK12Runtime input).adversaryValue.rawMessages.c1Root ∈
        prefixMerkleCandidateSet (exposurePrefixRawQueries prior)
    have messagesExact :
        fixedTapeRawMessages (exactOperationalTape input) =
          (exactK12Runtime input).adversaryValue.rawMessages :=
      input.package.root.fixedRoot.base.rawMessagesExact
    have c1Exact :
        (exactOperationalTape input).messages.c1Root =
          (exactK12Runtime input).adversaryValue.rawMessages.c1Root := by
      simpa [fixedTapeRawMessages, rawOfMessages] using
        congrArg (fun raw => raw.c1Root) messagesExact
    rw [← c1Exact]
    exact c1_root_mem_prefixMerkleCandidateSet_of_retained prior c1Before
      (exactOperationalTape input).messages.c1Root c1Salt c1Answer terminal
      IsPostC1StateInput c1Chain
  · change runtimeDigest208ToMerkleDigest
      (exactK12Runtime input).adversaryValue.rawMessages.c2Root ∈
        prefixMerkleCandidateSet (exposurePrefixRawQueries prior)
    have messagesExact :
        fixedTapeRawMessages (exactOperationalTape input) =
          (exactK12Runtime input).adversaryValue.rawMessages :=
      input.package.root.fixedRoot.base.rawMessagesExact
    have c2Exact :
        (exactOperationalTape input).messages.c2.root =
          (exactK12Runtime input).adversaryValue.rawMessages.c2Root := by
      simpa [fixedTapeRawMessages, rawOfMessages] using
        congrArg (fun raw => raw.c2Root) messagesExact
    rw [← c2Exact]
    exact c2_root_mem_prefixMerkleCandidateSet_of_retained prior c2Before
      (exactOperationalTape input).messages.c2.root c2Salt c2Answer terminal
      IsPostC2StateInput c2Chain

#print axioms rawInputMerkleCandidates_card_le_four
#print axioms node_left_mem_rawInputMerkleCandidates
#print axioms node_right_mem_rawInputMerkleCandidates
#print axioms c1_root_mem_rawInputMerkleCandidates
#print axioms c2_root_mem_rawInputMerkleCandidates
#print axioms rawInput_candidate_mem_prefixMerkleCandidateSet
#print axioms retainedDigestChain_boundary_member
#print axioms machineFresh_input_mem_exposurePrefixRawQueries
#print axioms c1_root_mem_prefixMerkleCandidateSet_of_retained
#print axioms c2_root_mem_prefixMerkleCandidateSet_of_retained
#print axioms prefixMerkleCandidateSet_card_le
#print axioms prefixMerkleCandidatePreimage_card_le
#print axioms firstUnresolvedTarget_mem_prefixMerkleCandidateSet
#print axioms prefixResolutionTargetSet_subset_prefixMerkleCandidateSet
#print axioms exact_actual_trial_prefixResolutionTargetSet_subset

end

end AspisK1.V7Tag73K13PreQ16TargetInventory

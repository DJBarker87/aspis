import AspisFormal.K1.V7Tag73ConcreteQueryDag
import AspisFormal.K1.V7Tag73InteractiveAncestor

/-!
# Alignment of the Tag-73 query DAG with the ROM-free ancestor plan

Every forkable query-DAG prefix is aligned here with one literal
`VerifierAction.squeezePair` in `fullPlan`.  The construction is list-only: it
does not execute an oracle, posit a restore operation, or assume a trace-cover
predicate.  In particular, the q16 alignment distinguishes the accumulated
action history (completed discarded branches included) from the current
branch path beginning at the one saved base.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73DagActionAlignment

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ConcreteQueryDag
open AspisK1.V7Tag73InteractiveAncestor

/-! ## Generic finite-list decompositions -/

theorem list_decompose_at {α : Type*} (values : List α)
    (index : Fin values.length) :
    values = values.take index.val ++ [values.get index] ++
      values.drop (index.val + 1) := by
  calc
    values = values.take (index.val + 1) ++
        values.drop (index.val + 1) :=
      (List.take_append_drop (index.val + 1) values).symm
    _ = (values.take index.val ++ [values[index.val]]) ++
        values.drop (index.val + 1) := by
      rw [List.take_succ_eq_append_getElem index.isLt]
    _ = values.take index.val ++ [values.get index] ++
        values.drop (index.val + 1) := by
      simp [List.append_assoc]

theorem flatMap_decompose_at {α β : Type*} (values : List α)
    (mapValue : α → List β) (index : Fin values.length) :
    values.flatMap mapValue =
      (values.take index.val).flatMap mapValue ++
      mapValue (values.get index) ++
      (values.drop (index.val + 1)).flatMap mapValue := by
  calc
    values.flatMap mapValue =
        (values.take index.val ++ [values.get index] ++
          values.drop (index.val + 1)).flatMap mapValue :=
      congrArg (List.flatMap mapValue) (list_decompose_at values index)
    _ = (values.take index.val).flatMap mapValue ++
        mapValue (values.get index) ++
        (values.drop (index.val + 1)).flatMap mapValue := by
      simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.nil_append, List.append_assoc]

def squeezeActions (owner : SqueezeOwner) (count : Nat) :
    List VerifierAction :=
  (List.range count).map fun block => .squeezePair owner block

@[simp] theorem squeeze_actions_length (owner : SqueezeOwner) (count : Nat) :
    (squeezeActions owner count).length = count := by
  simp [squeezeActions]

theorem squeeze_actions_get (owner : SqueezeOwner) (count : Nat)
    (block : Fin count) :
    (squeezeActions owner count).get
      (Fin.cast (squeeze_actions_length owner count).symm block) =
      .squeezePair owner block.val := by
  simp [squeezeActions]

theorem squeeze_actions_decompose (owner : SqueezeOwner) (count : Nat)
    (block : Fin count) :
    squeezeActions owner count =
      (squeezeActions owner count).take block.val ++
      [.squeezePair owner block.val] ++
      (squeezeActions owner count).drop (block.val + 1) := by
  let lifted : Fin (squeezeActions owner count).length :=
    Fin.cast (squeeze_actions_length owner count).symm block
  have getValue :
      (squeezeActions owner count).get lifted =
        .squeezePair owner block.val := by
    simpa [lifted] using squeeze_actions_get owner count block
  have liftedValue : lifted.val = block.val := by
    rfl
  calc
    squeezeActions owner count =
        (squeezeActions owner count).take lifted.val ++
        [(squeezeActions owner count).get lifted] ++
        (squeezeActions owner count).drop (lifted.val + 1) :=
      list_decompose_at (squeezeActions owner count) lifted
    _ = (squeezeActions owner count).take block.val ++
        [.squeezePair owner block.val] ++
        (squeezeActions owner count).drop (block.val + 1) := by
      rw [getValue, liftedValue]

@[simp] theorem challenge_actions_eq_squeeze_actions
    (id : ChallengeId) (use : SamplerUse id) :
    challengeActions id use =
      squeezeActions (.challenge id) use.blocksUsed := by
  rfl

theorem events_to_actions_decompose_at_challenge
    (events : List MachineEvent) (index : Fin events.length)
    (id : ChallengeId) (use : SamplerUse id)
    (atEvent : events.get index = .challenge id use) :
    eventsToActions events =
      eventsToActions (events.take index.val) ++
      challengeActions id use ++
      eventsToActions (events.drop (index.val + 1)) := by
  unfold eventsToActions
  rw [flatMap_decompose_at events eventActions index, atEvent]
  rfl

/-! ## Four exact linear segments -/

def c1BridgeActions (tape : DeployedFixedTape) : List VerifierAction :=
  [.requestRootSalt .initialC1, .absorbC1 (c1TypedRoot tape.messages)]

def c2BridgeActions (tape : DeployedFixedTape) : List VerifierAction :=
  [.requestRootSalt .foldedC2,
   .absorbC2 (tape.messages.challengeValue .lambda)
     (tape.messages.challengeValue .chi) tape.messages.c2]

def lambdaChiActions (tape : DeployedFixedTape) : List VerifierAction :=
  challengeActions .lambda (tape.messages.challengeUse .lambda) ++
    challengeActions .chi (tape.messages.challengeUse .chi)

theorem adaptive_prefix_plan_expanded (tape : DeployedFixedTape) :
    adaptivePrefixPlan tape =
      eventsToActions (prefixBeforeC1 tape.messages) ++
      c1BridgeActions tape ++ lambdaChiActions tape ++
      c2BridgeActions tape ++
      eventsToActions (prefixAfterC2 tape.messages) := by
  simp [adaptivePrefixPlan, adaptiveRounds, expandAdaptiveRound,
    c1BridgeActions, c2BridgeActions, lambdaChiActions, List.append_assoc]

def actionsBeforeSegment (tape : DeployedFixedTape) :
    LinearSegment → List VerifierAction
  | .beforeC1 => []
  | .lambdaChi =>
      eventsToActions (prefixBeforeC1 tape.messages) ++ c1BridgeActions tape
  | .afterC2 =>
      eventsToActions (prefixBeforeC1 tape.messages) ++ c1BridgeActions tape ++
        lambdaChiActions tape ++ c2BridgeActions tape
  | .afterQ16 => adaptivePrefixPlan tape ++ q16Plan tape

def actionsAfterSegment (tape : DeployedFixedTape) :
    LinearSegment → List VerifierAction
  | .beforeC1 =>
      c1BridgeActions tape ++ lambdaChiActions tape ++ c2BridgeActions tape ++
        eventsToActions (prefixAfterC2 tape.messages) ++ q16Plan tape ++
        eventsToActions (afterAcceptedQueryScan tape.messages) ++ [.terminal]
  | .lambdaChi =>
      c2BridgeActions tape ++
        eventsToActions (prefixAfterC2 tape.messages) ++ q16Plan tape ++
        eventsToActions (afterAcceptedQueryScan tape.messages) ++ [.terminal]
  | .afterC2 =>
      q16Plan tape ++ eventsToActions (afterAcceptedQueryScan tape.messages) ++
        [.terminal]
  | .afterQ16 => [.terminal]

theorem full_plan_decomposes_around_each_linear_segment
    (tape : DeployedFixedTape) (segment : LinearSegment) :
    fullPlan tape =
      actionsBeforeSegment tape segment ++
      eventsToActions (eventsInSegment tape.messages segment) ++
      actionsAfterSegment tape segment := by
  cases segment <;>
    simp [fullPlan, adaptive_prefix_plan_expanded, actionsBeforeSegment,
      actionsAfterSegment, eventsInSegment, lambdaChiActions,
      eventsToActions, eventActions, challengeEvent, List.append_assoc]

def actionsBeforeLinearFork {dag : ConcreteDagInstance}
    (fork : LinearChallengeFork dag) : List VerifierAction :=
  actionsBeforeSegment dag.tape fork.segment ++
    eventsToActions
      ((eventsInSegment dag.messages fork.segment).take fork.eventIndex.val) ++
    (challengeActions fork.id fork.use).take fork.block.val

def actionsAfterLinearFork {dag : ConcreteDagInstance}
    (fork : LinearChallengeFork dag) : List VerifierAction :=
  (challengeActions fork.id fork.use).drop (fork.block.val + 1) ++
    eventsToActions
      ((eventsInSegment dag.messages fork.segment).drop
        (fork.eventIndex.val + 1)) ++
    actionsAfterSegment dag.tape fork.segment

theorem full_plan_decomposes_at_linear_fork
    {dag : ConcreteDagInstance} (fork : LinearChallengeFork dag) :
    fullPlan dag.tape =
      actionsBeforeLinearFork fork ++
      [.squeezePair (.challenge fork.id) fork.block.val] ++
      actionsAfterLinearFork fork := by
  have segmentDecomposition :=
    full_plan_decomposes_around_each_linear_segment dag.tape fork.segment
  have eventDecomposition := events_to_actions_decompose_at_challenge
    (eventsInSegment dag.messages fork.segment) fork.eventIndex
    fork.id fork.use fork.atEvent
  have squeezeDecomposition := squeeze_actions_decompose
    (.challenge fork.id) fork.use.blocksUsed fork.block
  calc
    fullPlan dag.tape =
        actionsBeforeSegment dag.tape fork.segment ++
        eventsToActions (eventsInSegment dag.messages fork.segment) ++
        actionsAfterSegment dag.tape fork.segment := segmentDecomposition
    _ = actionsBeforeLinearFork fork ++
        [.squeezePair (.challenge fork.id) fork.block.val] ++
        actionsAfterLinearFork fork := by
      rw [eventDecomposition, challenge_actions_eq_squeeze_actions,
        squeezeDecomposition]
      simp [actionsBeforeLinearFork, actionsAfterLinearFork,
        List.append_assoc]

/-! ## q16 earlier and selected branches -/

@[simp] theorem earlier_specs_length
    {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes) :
    (earlierSpecs search).length = search.selectedCounter.val := by
  simp [earlierSpecs]

theorem earlier_specs_get
    {frontierNodes : QuerySchedule → Nat}
    (search : FirstCap203Search frontierNodes) (counter : Fin 64)
    (earlier : counter.val < search.selectedCounter.val) :
    (earlierSpecs search).get
      ⟨counter.val, by simpa using earlier⟩ =
      { counter := counter, outcome := search.outcome counter } := by
  simp [earlierSpecs]

def q16SqueezeActions (counter : Fin 64) (outcome : CandidateOutcome) :
    List VerifierAction :=
  squeezeActions (.queryCandidate counter) outcome.blocksUsed

theorem candidate_actions_expanded (spec : CandidateSpec) (selected : Bool) :
    candidateActions spec selected =
      [.q16CandidateAbsorb spec.counter spec.outcome selected] ++
      q16SqueezeActions spec.counter spec.outcome := by
  rfl

theorem candidate_actions_decompose_at_block (spec : CandidateSpec)
    (selected : Bool) (block : Fin spec.outcome.blocksUsed) :
    candidateActions spec selected =
      [.q16CandidateAbsorb spec.counter spec.outcome selected] ++
      (q16SqueezeActions spec.counter spec.outcome).take block.val ++
      [.squeezePair (.queryCandidate spec.counter) block.val] ++
      (q16SqueezeActions spec.counter spec.outcome).drop (block.val + 1) := by
  have squeezeDecomposition :
      q16SqueezeActions spec.counter spec.outcome =
        (q16SqueezeActions spec.counter spec.outcome).take block.val ++
        [.squeezePair (.queryCandidate spec.counter) block.val] ++
        (q16SqueezeActions spec.counter spec.outcome).drop
          (block.val + 1) := by
    exact squeeze_actions_decompose
      (.queryCandidate spec.counter) spec.outcome.blocksUsed block
  calc
    candidateActions spec selected =
        [.q16CandidateAbsorb spec.counter spec.outcome selected] ++
        q16SqueezeActions spec.counter spec.outcome :=
      candidate_actions_expanded spec selected
    _ = [.q16CandidateAbsorb spec.counter spec.outcome selected] ++
        ((q16SqueezeActions spec.counter spec.outcome).take block.val ++
          [.squeezePair (.queryCandidate spec.counter) block.val] ++
          (q16SqueezeActions spec.counter spec.outcome).drop
            (block.val + 1)) :=
      congrArg
        (List.append
          [.q16CandidateAbsorb spec.counter spec.outcome selected])
        squeezeDecomposition
    _ = [.q16CandidateAbsorb spec.counter spec.outcome selected] ++
        (q16SqueezeActions spec.counter spec.outcome).take block.val ++
        [.squeezePair (.queryCandidate spec.counter) block.val] ++
        (q16SqueezeActions spec.counter spec.outcome).drop
          (block.val + 1) := by
      simp [List.append_assoc]

def priorDiscardedActions (dag : ConcreteDagInstance) (counter : Fin 64) :
    List VerifierAction :=
  ((q16TapeOfSearch dag.tape.search).earlier.take counter.val).flatMap
    discardedCandidateActions

def q16CommonPlanPrefix (dag : ConcreteDagInstance) : List VerifierAction :=
  adaptivePrefixPlan dag.tape ++ [.markQ16Base]

def earlierQ16Spec (dag : ConcreteDagInstance)
    (fork : Q16ChallengeFork dag) : CandidateSpec :=
  { counter := fork.branch.counter,
    outcome := dag.tape.search.outcome fork.branch.counter }

def actionsBeforeEarlierQ16Fork (dag : ConcreteDagInstance)
    (fork : Q16ChallengeFork dag) : List VerifierAction :=
  q16CommonPlanPrefix dag ++
    priorDiscardedActions dag fork.branch.counter ++
    [.q16CandidateAbsorb fork.branch.counter
      (dag.tape.search.outcome fork.branch.counter) false] ++
    (q16SqueezeActions fork.branch.counter
      (dag.tape.search.outcome fork.branch.counter)).take fork.block.val

/-! An earlier-branch suffix is constructed only under an explicit strict
counter inequality; no total definition fabricates that inequality. -/

def actionsAfterEarlierQ16Fork (dag : ConcreteDagInstance)
    (fork : Q16ChallengeFork dag) : List VerifierAction :=
  (q16SqueezeActions fork.branch.counter
      (dag.tape.search.outcome fork.branch.counter)).drop
        (fork.block.val + 1) ++
    [.q16Restore fork.branch.counter] ++
    ((q16TapeOfSearch dag.tape.search).earlier.drop
      (fork.branch.counter.val + 1)).flatMap discardedCandidateActions ++
    candidateActions (q16TapeOfSearch dag.tape.search).selected true ++
    [.q16Selected (q16TapeOfSearch dag.tape.search).selected.counter] ++
    eventsToActions (afterAcceptedQueryScan dag.messages) ++ [.terminal]

theorem full_plan_decomposes_at_earlier_q16_fork
    {dag : ConcreteDagInstance} (fork : Q16ChallengeFork dag)
    (earlier : fork.branch.counter.val <
      dag.tape.search.selectedCounter.val) :
    fullPlan dag.tape =
      actionsBeforeEarlierQ16Fork dag fork ++
      [.squeezePair (.queryCandidate fork.branch.counter) fork.block.val] ++
      actionsAfterEarlierQ16Fork dag fork := by
  let allEarlier := (q16TapeOfSearch dag.tape.search).earlier
  let currentIndex : Fin allEarlier.length :=
    ⟨fork.branch.counter.val, by simpa [allEarlier, q16TapeOfSearch] using earlier⟩
  let currentSpec : CandidateSpec :=
    { counter := fork.branch.counter,
      outcome := dag.tape.search.outcome fork.branch.counter }
  have currentGet : allEarlier.get currentIndex = currentSpec := by
    simpa [allEarlier, currentIndex, currentSpec, q16TapeOfSearch] using
      earlier_specs_get dag.tape.search fork.branch.counter earlier
  have branches := flatMap_decompose_at allEarlier
    discardedCandidateActions currentIndex
  rw [currentGet] at branches
  have currentCandidate := candidate_actions_decompose_at_block
    currentSpec false fork.block
  rw [fullPlan, q16Plan]
  rw [branches]
  rw [discardedCandidateActions, currentCandidate]
  simp [actionsBeforeEarlierQ16Fork, priorDiscardedActions,
    actionsAfterEarlierQ16Fork, q16CommonPlanPrefix, allEarlier, currentIndex,
    currentSpec, q16TapeOfSearch, ConcreteDagInstance.messages,
    List.append_assoc]

def selectedQ16Spec (dag : ConcreteDagInstance) : CandidateSpec :=
  { counter := dag.tape.search.selectedCounter,
    outcome := .schedule dag.tape.search.selectedSchedule }

def actionsBeforeSelectedQ16Fork (dag : ConcreteDagInstance)
    (block : Nat) : List VerifierAction :=
  q16CommonPlanPrefix dag ++
    (q16TapeOfSearch dag.tape.search).earlier.flatMap
      discardedCandidateActions ++
    [.q16CandidateAbsorb dag.tape.search.selectedCounter
      (.schedule dag.tape.search.selectedSchedule) true] ++
    (q16SqueezeActions dag.tape.search.selectedCounter
      (.schedule dag.tape.search.selectedSchedule)).take block

def actionsAfterSelectedQ16Fork (dag : ConcreteDagInstance)
    (block : Nat) : List VerifierAction :=
  (q16SqueezeActions dag.tape.search.selectedCounter
      (.schedule dag.tape.search.selectedSchedule)).drop (block + 1) ++
    [.q16Selected dag.tape.search.selectedCounter] ++
    eventsToActions (afterAcceptedQueryScan dag.messages) ++ [.terminal]

theorem full_plan_decomposes_at_selected_q16_fork
    {dag : ConcreteDagInstance} (fork : Q16ChallengeFork dag)
    (selected : fork.branch.counter = dag.tape.search.selectedCounter) :
    fullPlan dag.tape =
      actionsBeforeSelectedQ16Fork dag fork.block.val ++
      [.squeezePair (.queryCandidate fork.branch.counter) fork.block.val] ++
      actionsAfterSelectedQ16Fork dag fork.block.val := by
  have outcomeAtBranch :
      dag.tape.search.outcome fork.branch.counter =
        .schedule dag.tape.search.selectedSchedule := by
    rw [selected]
    exact dag.tape.search.selectedOutcome
  let selectedBlock : Fin dag.tape.search.selectedSchedule.blocksUsed :=
    Fin.cast (congrArg CandidateOutcome.blocksUsed outcomeAtBranch) fork.block
  have selectedCandidate :
      candidateActions (q16TapeOfSearch dag.tape.search).selected true =
        [.q16CandidateAbsorb dag.tape.search.selectedCounter
          (.schedule dag.tape.search.selectedSchedule) true] ++
        (q16SqueezeActions dag.tape.search.selectedCounter
          (.schedule dag.tape.search.selectedSchedule)).take selectedBlock.val ++
        [.squeezePair (.queryCandidate dag.tape.search.selectedCounter)
          selectedBlock.val] ++
        (q16SqueezeActions dag.tape.search.selectedCounter
          (.schedule dag.tape.search.selectedSchedule)).drop
            (selectedBlock.val + 1) := by
    simpa [selectedQ16Spec, q16TapeOfSearch] using
      candidate_actions_decompose_at_block
        (selectedQ16Spec dag) true selectedBlock
  rw [fullPlan, q16Plan]
  rw [selectedCandidate]
  simp [actionsBeforeSelectedQ16Fork, q16CommonPlanPrefix,
    actionsAfterSelectedQ16Fork, selectedQ16Spec, selectedBlock,
    q16TapeOfSearch, selected, ConcreteDagInstance.messages,
    List.append_assoc]

/-! ## One concrete checkpoint for every generated replay prefix -/

structure SqueezeActionCheckpoint (tape : DeployedFixedTape) where
  owner : SqueezeOwner
  block : Nat
  actionsBefore : List VerifierAction
  suffix : List VerifierAction
  decomposition : fullPlan tape =
    actionsBefore ++ [.squeezePair owner block] ++ suffix

def linearCheckpoint {dag : ConcreteDagInstance}
    (fork : LinearChallengeFork dag) : SqueezeActionCheckpoint dag.tape where
  owner := .challenge fork.id
  block := fork.block.val
  actionsBefore := actionsBeforeLinearFork fork
  suffix := actionsAfterLinearFork fork
  decomposition := full_plan_decomposes_at_linear_fork fork

noncomputable def q16Checkpoint {dag : ConcreteDagInstance}
    (fork : Q16ChallengeFork dag) : SqueezeActionCheckpoint dag.tape := by
  classical
  if selected : fork.branch.counter = dag.tape.search.selectedCounter then
    exact
      { owner := .queryCandidate fork.branch.counter
        block := fork.block.val
        actionsBefore := actionsBeforeSelectedQ16Fork dag fork.block.val
        suffix := actionsAfterSelectedQ16Fork dag fork.block.val
        decomposition :=
          full_plan_decomposes_at_selected_q16_fork fork selected }
  else
    have earlier : fork.branch.counter.val <
        dag.tape.search.selectedCounter.val := by
      have notEqualValue : fork.branch.counter.val ≠
          dag.tape.search.selectedCounter.val := by
        intro equal
        apply selected
        exact Fin.ext equal
      exact Nat.lt_of_le_of_ne fork.branch.noLaterThanSelected notEqualValue
    exact
      { owner := .queryCandidate fork.branch.counter
        block := fork.block.val
        actionsBefore := actionsBeforeEarlierQ16Fork dag fork
        suffix := actionsAfterEarlierQ16Fork dag fork
        decomposition :=
          full_plan_decomposes_at_earlier_q16_fork fork earlier }

noncomputable def checkpointForGenerated {dag : ConcreteDagInstance} :
    GeneratedReplayPrefix dag → SqueezeActionCheckpoint dag.tape
  | .linear fork => linearCheckpoint fork
  | .q16 fork => q16Checkpoint fork

def SqueezeActionCheckpoint.cursor {tape : DeployedFixedTape}
    (checkpoint : SqueezeActionCheckpoint tape) : Nat :=
  checkpoint.actionsBefore.length

theorem checkpoint_cursor_is_strictly_inside_full_plan
    {tape : DeployedFixedTape} (checkpoint : SqueezeActionCheckpoint tape) :
    checkpoint.cursor < (fullPlan tape).length := by
  rw [checkpoint.decomposition]
  simp [SqueezeActionCheckpoint.cursor]

theorem checkpoint_next_action_is_exact_squeeze_pair
    {tape : DeployedFixedTape} (checkpoint : SqueezeActionCheckpoint tape) :
    (fullPlan tape)[checkpoint.cursor]'(
      checkpoint_cursor_is_strictly_inside_full_plan checkpoint) =
      .squeezePair checkpoint.owner checkpoint.block := by
  simpa [checkpoint.decomposition, SqueezeActionCheckpoint.cursor]

theorem generated_cursor_phase_mapping_is_unique
    {dag : ConcreteDagInstance} (generated : GeneratedReplayPrefix dag) :
    ∃! location : Nat × SqueezeOwner × Nat,
      location =
        ((checkpointForGenerated generated).cursor,
         (checkpointForGenerated generated).owner,
         (checkpointForGenerated generated).block) := by
  exact ⟨_, rfl, by intro other equal; exact equal⟩

theorem q16_checkpoint_history_contains_completed_discarded_branches
    {dag : ConcreteDagInstance} (fork : Q16ChallengeFork dag)
    (earlier : fork.branch.counter.val <
      dag.tape.search.selectedCounter.val) :
    q16CommonPlanPrefix dag ++ priorDiscardedActions dag fork.branch.counter <+:
      actionsBeforeEarlierQ16Fork dag fork := by
  simp [actionsBeforeEarlierQ16Fork]

theorem q16_current_core_path_starts_at_saved_base
    {dag : ConcreteDagInstance} (fork : Q16ChallengeFork dag) :
    [.markQ16Base,
      .q16CandidateAbsorb fork.branch.counter
        (dag.tape.search.outcome fork.branch.counter)
        (decide (fork.branch.counter = dag.tape.search.selectedCounter))] <+:
      [.markQ16Base] ++
        [.q16CandidateAbsorb fork.branch.counter
          (dag.tape.search.outcome fork.branch.counter)
          (decide (fork.branch.counter = dag.tape.search.selectedCounter))] ++
        (q16SqueezeActions fork.branch.counter
          (dag.tape.search.outcome fork.branch.counter)).take fork.block.val := by
  simp

#print axioms list_decompose_at
#print axioms flatMap_decompose_at
#print axioms squeeze_actions_decompose
#print axioms events_to_actions_decompose_at_challenge
#print axioms adaptive_prefix_plan_expanded
#print axioms full_plan_decomposes_around_each_linear_segment
#print axioms full_plan_decomposes_at_linear_fork
#print axioms earlier_specs_get
#print axioms candidate_actions_decompose_at_block
#print axioms full_plan_decomposes_at_earlier_q16_fork
#print axioms full_plan_decomposes_at_selected_q16_fork
#print axioms checkpoint_cursor_is_strictly_inside_full_plan
#print axioms checkpoint_next_action_is_exact_squeeze_pair
#print axioms generated_cursor_phase_mapping_is_unique
#print axioms q16_checkpoint_history_contains_completed_discarded_branches
#print axioms q16_current_core_path_starts_at_saved_base

end AspisK1.V7Tag73DagActionAlignment

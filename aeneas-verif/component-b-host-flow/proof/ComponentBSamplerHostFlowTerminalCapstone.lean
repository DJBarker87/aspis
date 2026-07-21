import BoundMaskFlowCorrespondence
import ComponentBSamplerTerminalCapstone

open Aeneas Aeneas.Std Result ControlFlow Error

namespace ComponentBSamplerHostFlowTerminalCapstone

abbrev SamplerQM31 := ComponentBSamplerMaintainedPredicatesBridge.SamplerQM31
abbrev SamplerMask := ComponentBSamplerMaintainedPredicatesBridge.SamplerMask
abbrev HostQM31 := AspisComponentBHostFlow.Extracted.QM31
abbrev HostMask := AspisComponentBHostFlow.Extracted.Mask
abbrev MaintainedQM31 :=
  ComponentBSamplerMaintainedPredicatesBridge.MaintainedQM31
abbrev MaintainedMask :=
  ComponentBSamplerMaintainedPredicatesBridge.MaintainedMask

abbrev hostBind := AspisComponentBHostFlow.Extracted.bind
abbrev hostForCommitment := AspisComponentBHostFlow.Extracted.forCommitment
abbrev hostForInitialClaim := AspisComponentBHostFlow.Extracted.forInitialClaim
abbrev hostForSumcheck := AspisComponentBHostFlow.Extracted.forSumcheck
abbrev hostForTerminal := AspisComponentBHostFlow.Extracted.forTerminal

noncomputable local instance :
    Field ComponentBRealEvaluatorProof.ExactQM31 := by
  change Field AspisV5ComponentCQM31TowerExact.QM31Exact
  infer_instance

def samplerQM31ToHost (value : SamplerQM31) : HostQM31 :=
  { c0 := { a := value.c0.a, b := value.c0.b }
    c1 := { a := value.c1.a, b := value.c1.b } }

def samplerArrayToHost {n : Std.Usize}
    (values : Array SamplerQM31 n) : Array HostQM31 n :=
  ⟨values.val.map samplerQM31ToHost, by
    rw [List.length_map]
    exact values.property⟩

def samplerRoundsToHost
    (rounds : Array (Array SamplerQM31 28#usize) 10#usize) :
    Array (Array HostQM31 28#usize) 10#usize :=
  ⟨rounds.val.map samplerArrayToHost, by
    rw [List.length_map]
    exact rounds.property⟩

/-- Coordinatewise representation bridge from the authentic sampler's Aeneas
copy to the real-host handle's independently extracted Aeneas copy.  It changes
no limb, coefficient, round, or ordering. -/
def samplerMaskToHost (mask : SamplerMask) : HostMask :=
  { initial_claim := samplerQM31ToHost mask.initial_claim
    zero_boundary_rounds := samplerRoundsToHost mask.zero_boundary_rounds }

def hostQM31ToMaintained (value : HostQM31) : MaintainedQM31 :=
  { c0 := { a := value.c0.a, b := value.c0.b }
    c1 := { a := value.c1.a, b := value.c1.b } }

def hostArrayToMaintained {n : Std.Usize}
    (values : Array HostQM31 n) : Array MaintainedQM31 n :=
  ⟨values.val.map hostQM31ToMaintained, by
    rw [List.length_map]
    exact values.property⟩

def hostRoundsToMaintained
    (rounds : Array (Array HostQM31 28#usize) 10#usize) :
    Array (Array MaintainedQM31 28#usize) 10#usize :=
  ⟨rounds.val.map hostArrayToMaintained, by
    rw [List.length_map]
    exact rounds.property⟩

def hostMaskToMaintained (mask : HostMask) : MaintainedMask :=
  { initial_claim := hostQM31ToMaintained mask.initial_claim
    zero_boundary_rounds := hostRoundsToMaintained mask.zero_boundary_rounds }

private theorem hostArrayToMaintained_samplerArrayToHost {n : Std.Usize}
    (values : Array SamplerQM31 n) :
    hostArrayToMaintained (samplerArrayToHost values) =
      ComponentBSamplerMaintainedPredicatesBridge.toMaintainedArray values := by
  apply Subtype.ext
  simp [hostArrayToMaintained, samplerArrayToHost,
    hostQM31ToMaintained, samplerQM31ToHost,
    ComponentBSamplerMaintainedPredicatesBridge.toMaintainedArray,
    ComponentBSamplerMaintainedPredicatesBridge.toMaintainedQM31,
    List.map_map, Function.comp_def]

theorem samplerMaskToHost_initial_claim (mask : SamplerMask) :
    (samplerMaskToHost mask).initial_claim =
      samplerQM31ToHost mask.initial_claim := by
  rfl

theorem samplerMaskToHost_rounds (mask : SamplerMask) :
    (samplerMaskToHost mask).zero_boundary_rounds =
      samplerRoundsToHost mask.zero_boundary_rounds := by
  rfl

/-- The caller-installed host mask and the evaluator mask are two nominal
Aeneas copies of exactly the same Rust value. -/
theorem hostMaskToMaintained_samplerMaskToHost (mask : SamplerMask) :
    hostMaskToMaintained (samplerMaskToHost mask) =
      ComponentBSamplerMaintainedPredicatesBridge.toMaintainedMask mask := by
  cases mask with
  | mk initial rounds =>
    simp [hostMaskToMaintained, samplerMaskToHost,
      hostRoundsToMaintained, samplerRoundsToHost,
      hostQM31ToMaintained, samplerQM31ToHost,
      ComponentBSamplerMaintainedPredicatesBridge.toMaintainedMask,
      ComponentBSamplerMaintainedPredicatesBridge.toMaintainedRounds,
      ComponentBSamplerMaintainedPredicatesBridge.toMaintainedQM31,
      hostArrayToMaintained_samplerArrayToHost,
      List.map_map, Function.comp_def]

/-- End-to-end deterministic Component-B capstone.

An authentic successful sample is explicitly installed by the caller as the
real-host mask.  The source-authentic host handle then returns that exact one
mask for commitment, initial-claim, sumcheck, and terminal roles, while the
source-authentic evaluator returns the maintained `terminalCovector` value.

The only executable assumptions beyond the successful run itself are word
source totality, the extracted 64-bit target fact, canonical point limbs, and
the explicit caller installation equality.  This theorem makes no entropy or
uniformity claim. -/
theorem authentic_sample_flows_through_host_and_evaluates_to_terminal
    {S : Type} (sourceInst : aspis_prover.v5_mask.Qm31WordSource S)
    (nextWordTotal : ∀ source : S,
      ∃ word source', sourceInst.next_word source = .ok (word, source'))
    (source finalSource : S) (mask : SamplerMask)
    (run : aspis_prover.v5_sumcheck_mask.V5SumcheckMask.sample
      sourceInst source = .ok (.Ok mask, finalSource))
    (targetWidth : System.Platform.numBits = 64)
    (point : Array ComponentBMaintainedTerminalBridge.QM31 10#usize)
    (hpoint : ∀ i : Fin 10,
      ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 point.val[i.val])
    (callerMask : HostMask)
    (callerInstalledExactSample : callerMask = samplerMaskToHost mask) :
    ∃ bound out,
      hostBind callerMask = ok bound ∧
      hostForCommitment bound = ok callerMask ∧
      hostForInitialClaim bound = ok callerMask ∧
      hostForSumcheck bound = ok callerMask ∧
      hostForTerminal bound = ok callerMask ∧
      hostMaskToMaintained callerMask =
        ComponentBSamplerMaintainedPredicatesBridge.toMaintainedMask mask ∧
      ComponentBGenerated.v5_sumcheck_mask.V5SumcheckMask.evaluate
          (ComponentBSamplerMaintainedPredicatesBridge.toMaintainedMask mask)
          point = .ok out ∧
      ComponentBRealEvaluatorProof.GeneratedCanonicalQM31 out ∧
      ComponentBRealEvaluatorProof.generatedQm31ToExact out =
        AspisV5SumcheckCommitment.terminalCovector
          (fun i : Fin 10 ↦
            ComponentBRealEvaluatorProof.generatedQm31ToExact point.val[i.val])
          (ComponentBRealEvaluatorProof.generatedQm31ToExact
            (ComponentBSamplerMaintainedPredicatesBridge.toMaintainedMask mask).initial_claim)
          (fun i ↦ ComponentBMaintainedTerminalBridge.exactTail
            (ComponentBMaintainedTerminalBridge.storedRound
              (ComponentBSamplerMaintainedPredicatesBridge.toMaintainedMask mask)
              i)) := by
  subst callerMask
  have hostFlow :=
    AspisComponentBHostFlow.Extracted.V5RealHostInputsSumcheckMaskProvenanceAndFlow
      (samplerMaskToHost mask)
  obtain ⟨bound, hBind, hCommitment, hInitial, hSumcheck, hTerminal⟩ := hostFlow
  obtain ⟨out, hEvaluate, hCanonical, hTerminalCovector⟩ :=
    ComponentBSamplerTerminalCapstone.sample_success_evaluates_to_terminal sourceInst
      nextWordTotal source finalSource mask run targetWidth point hpoint
  refine ⟨bound, out, hBind, hCommitment, hInitial, hSumcheck, hTerminal,
    hostMaskToMaintained_samplerMaskToHost mask,
    hEvaluate, hCanonical, hTerminalCovector⟩

/-- The explicit caller-equality premise is satisfiable for every authentic
sample: the caller installs the coordinatewise representation of that sample. -/
theorem authentic_sample_caller_installation_nonvacuous
    (mask : SamplerMask) :
    ∃ callerMask : HostMask, callerMask = samplerMaskToHost mask :=
  ⟨samplerMaskToHost mask, rfl⟩

#print axioms samplerMaskToHost_initial_claim
#print axioms samplerMaskToHost_rounds
#print axioms hostMaskToMaintained_samplerMaskToHost
#print axioms authentic_sample_flows_through_host_and_evaluates_to_terminal
#print axioms authentic_sample_caller_installation_nonvacuous

end ComponentBSamplerHostFlowTerminalCapstone

import AspisFormal.K1.V7Tag73TranscriptSchedule

/-!
# Literal verifier transcript prefix before Tag-73 gamma

The zero-check evaluation point and the three width-29 point-claim rows are
already present before the first gamma squeeze.  This is a structural fact
about the deployed transcript schedule.  It distinguishes the protocol's
causal order from the separate source-model problem of projecting those
values out of a paused monolithic oracle machine.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73PreGammaTranscriptPrefix

open AspisK1.V7Tag73TranscriptSchedule

/-- The exact deployed verifier event prefix ending immediately before the
gamma challenge event. -/
def beforeGammaVerifierEvents (oracle : HashOracle) (messages : Messages) :
    List MachineEvent :=
  let context := messages.context
  let c1Salt := publicRootSalt oracle context c1TreeTag
  let c2Salt := publicRootSalt oracle context c2TreeTag
  [.check .canonicalWire,
   .absorb .profile,
   .absorb .circleBasis,
   .absorb (.deployment context),
   .absorb (.statement context.statementDigest),
   .absorb (.hidingPrecommit context),
   .absorb (.c1Root messages.c1Root c1Salt),
   challengeEvent messages .lambda,
   challengeEvent messages .chi,
   .absorb (.c2Root messages.c2.root c2Salt),
   .absorb .constraintRegistry,
   .absorb .helperSum,
   challengeEvent messages .theta] ++
  (List.ofFn fun coordinate : Fin 10 =>
    challengeEvent messages (.zerocheckPoint coordinate)) ++
  [challengeEvent messages .mu,
   .absorb (.initialMaskClaim messages.initialClaim),
   challengeEvent messages .eta] ++
  semanticEvents messages ++
  [.absorb (.pointClaims messages.pointClaims),
   .check .semanticTerminal,
   .grind .batch messages.batchGrinding,
   .check .batchWork,
   .absorb (.batchNonce messages.batchGrinding.selected)]

/-- The remainder of the deployed pre-query-scan schedule after gamma. -/
def afterGammaVerifierEvents (messages : Messages) : List MachineEvent :=
  [.absorb (.inactiveClaim messages.inactiveClaim),
   challengeEvent messages .kappa] ++
  oodEvents messages ++
  [.absorb (.relationRound 0 (messages.relationSent 0)),
   .grind .fold messages.foldGrinding,
   .check .foldWork,
   .absorb (.foldNonce messages.foldGrinding.selected),
   challengeEvent messages (.alpha 0),
   .absorb (.final256 messages.finalValues),
   .grind .final messages.finalGrinding,
   .check .finalWork,
   .absorb (.finalNonce messages.finalGrinding.selected)]

/-- Exact stopping-coordinate decomposition of the deployed verifier
schedule. -/
theorem beforeQueryScan_gamma_split (oracle : HashOracle)
    (messages : Messages) :
    beforeQueryScan oracle messages =
      beforeGammaVerifierEvents oracle messages ++
        challengeEvent messages .gamma :: afterGammaVerifierEvents messages :=
  by
    simp [beforeQueryScan, beforeGammaVerifierEvents,
      afterGammaVerifierEvents]

/-- Every zero-check point coordinate has already been sampled in the
pre-gamma verifier prefix. -/
theorem zerocheck_point_challenge_mem_before_gamma
    (oracle : HashOracle) (messages : Messages) (coordinate : Fin 10) :
    challengeEvent messages (.zerocheckPoint coordinate) ∈
      beforeGammaVerifierEvents oracle messages := by
  have member : challengeEvent messages (.zerocheckPoint coordinate) ∈
      List.ofFn (fun coordinate : Fin 10 =>
        challengeEvent messages (.zerocheckPoint coordinate)) := by
    rw [List.mem_ofFn']
    exact ⟨coordinate, rfl⟩
  unfold beforeGammaVerifierEvents
  exact List.mem_append_left _
    (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_right _ member)))

/-- The complete three-by-twenty-nine point-claim matrix has already been
absorbed in the pre-gamma verifier prefix. -/
theorem point_claims_mem_before_gamma
    (oracle : HashOracle) (messages : Messages) :
    .absorb (.pointClaims messages.pointClaims) ∈
      beforeGammaVerifierEvents oracle messages := by
  simp [beforeGammaVerifierEvents]

#print axioms beforeQueryScan_gamma_split
#print axioms zerocheck_point_challenge_mem_before_gamma
#print axioms point_claims_mem_before_gamma

end AspisK1.V7Tag73PreGammaTranscriptPrefix

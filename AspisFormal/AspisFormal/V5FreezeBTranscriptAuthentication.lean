import AspisFormal.SumcheckMasking
import AspisFormal.V5SumcheckTranscriptBinding
import AspisFormal.V5CompactTerminalOptimized
import AspisFormal.V5ComponentBTriangularHiding
import AspisFormal.V5DeployedCarriedInvariant

/-!
# Component-B freeze audit: transcript and terminal authentication

This file deliberately separates three layers.

* `authenticated_bound_terminal_and_same_pass_relation` is kernel-closed
  algebra once its hypotheses are supplied.  It binds the complete
  271-coordinate state, derives the ten challenges from the accepted
  transcript model, authenticates the terminal at that derived point and
  identifies the compact relation-lane check with the same terminal value.
* `OpeningUniquenessAt`, `AuthenticatedTerminalMaskEvaluation` and the
  relation-carried equation remain explicit hypotheses.  For the candidate
  wire they respectively stand for computational C2/PCS binding, the exact
  root-and-point opening path, and the existing relation/FRI opening path.
* The executable claims that the Rust bytes instantiate those hypotheses,
  and the exact residual-pad coverage needed for hiding, are not conclusions
  of this file.  In particular, no injective hash is postulated and no KAT is
  promoted to a rank theorem.

The negative models give the audit teeth.  Boolean boundary values do not
bind a degree-27 round polynomial; committing after `eta` permits adaptive
state choice; omitting the terminal authentication or authenticating it at
the wrong root/point does not bind the intended value; and the carried
invariant can succeed even when the older pivot-freshness premise is false.
-/

namespace AspisV5FreezeBTranscriptAuthentication

open AspisSumcheckMasking
open AspisV5CompleteView
open AspisV5SumcheckCommitment
open AspisV5SumcheckTranscriptBinding
open AspisV5CompactTerminal
open AspisV5CompactTerminalOptimized

/-! ## Kernel-closed conditional gate -/

/-- The strongest kernel-closed Component-B authentication statement in this
audit.

The state opened at the pre-`eta` C2 root is the full
`BoundComponentBState`: one initial coordinate plus ten blocks of 27 tail
coefficients.  Opening uniqueness fixes that state.  The accepted-run
equations fix `eta` and the ten-round point from the committed prefix and
authenticated round messages.  Terminal authentication then fixes the mask
terminal at exactly that point.  Finally, the already-existing compact
relation-lane identity carries the same value through the four final
openings; it is not a second dense opening.

Every hypothesis is used.  None asserts that the current Rust encoder,
transcript, relation lane or PCS actually instantiates the corresponding
mathematical interface. -/
theorem authenticated_bound_terminal_and_same_pass_relation
    {Public Root K : Type*} [Field K]
    {scheme : FiatShamirSchedule Public Root K}
    (h2 : (2 : K) ≠ 0)
    (Opens : Root → BoundComponentBState K → Prop)
    (AuthenticatedTerminal : Root → (Fin roundCount → K) → K → Prop)
    (run : AcceptedRun scheme)
    (hbinding : OpeningUniquenessAt Opens run.preEta.maskRoot)
    (hauthenticated : AuthenticatedTerminalMaskEvaluation
      Opens AuthenticatedTerminal boundTerminal)
    (state alternate : BoundComponentBState K)
    (hstate : Opens run.preEta.maskRoot state)
    (halternate : Opens run.preEta.maskRoot alternate)
    (value : K)
    (hvalue : AuthenticatedTerminal run.preEta.maskRoot run.point value)
    (scale : K) (alphas : Fin 4 → K) (finalValues : Fin 4 → K)
    (relation_carried :
      compactComponentBFinalDot
          (derivedPoint scheme run.preEta (scheme.eta run.preEta) run.messages)
          scale alphas finalValues =
        dot
          (terminalWeights
            (derivedPoint scheme run.preEta (scheme.eta run.preEta) run.messages)
            scale)
          (rowMessage state.initial state.tails)) :
    alternate = state ∧
      value = tenRoundTerminal state.initial state.tails
        (derivedPoint scheme run.preEta (scheme.eta run.preEta) run.messages) ∧
      optimizedCompactFinalDot
          (derivedPoint scheme run.preEta (scheme.eta run.preEta) run.messages)
          scale alphas finalValues =
        scale * value := by
  obtain ⟨halt, hterminal⟩ := acceptedRun_tenRoundTerminal_determined
    Opens AuthenticatedTerminal run hbinding hauthenticated state alternate
      hstate halternate value hvalue
  refine ⟨halt, hterminal, ?_⟩
  have hcompact := optimizedCompactFinalDot_eq_tenRoundTerminal_of_relation
    h2
    (derivedPoint scheme run.preEta (scheme.eta run.preEta) run.messages)
    scale state.initial state.tails alphas finalValues relation_carried
  simpa only [hterminal] using hcompact

/-! ## Boundary-only authentication is insufficient -/

/-- The literal pair `0` and `X^27 - X^26`, specialised to M31, has identical
values at `0` and `1` but a different value at `2`.  The polynomial identity
and nonzero leading coefficient are part of the conclusion, so this is the
concrete boundary-only counterexample rather than an existential wrapper. -/
theorem exact_degree27_boundary_only_authentication_fails :
    letI : Fact (Nat.Prime 2147483647) := ⟨by norm_num⟩
    coeffEval (0 : RoundCoeff (ZMod 2147483647) 27) 0 =
        coeffEval (endpointKernelDegree27 (K := ZMod 2147483647)) 0 ∧
      coeffEval (0 : RoundCoeff (ZMod 2147483647) 27) 1 =
        coeffEval (endpointKernelDegree27 (K := ZMod 2147483647)) 1 ∧
      coeffEval (0 : RoundCoeff (ZMod 2147483647) 27) 2 ≠
        coeffEval (endpointKernelDegree27 (K := ZMod 2147483647)) 2 ∧
      endpointKernelDegree27 (K := ZMod 2147483647) ⟨27, by omega⟩ ≠ 0 ∧
      ∀ x : ZMod 2147483647,
        coeffEval (endpointKernelDegree27 (K := ZMod 2147483647)) x =
          x ^ 27 - x ^ 26 := by
  letI : Fact (Nat.Prime 2147483647) := ⟨by norm_num⟩
  refine ⟨?_, ?_, ?_, ?_, coeffEval_endpointKernelDegree27⟩
  · rw [coeffEval_endpointKernelDegree27]
    simp [coeffEval]
  · rw [coeffEval_endpointKernelDegree27]
    simp [coeffEval]
  · rw [coeffEval_endpointKernelDegree27]
    simp only [coeffEval, Pi.zero_apply, zero_mul, Finset.sum_const_zero]
    apply Ne.symm
    rw [show (2 : ZMod 2147483647) ^ 27 - 2 ^ 26 =
      2 ^ 26 * (2 - 1) by ring]
    apply mul_ne_zero (pow_ne_zero 26 ?_) (by norm_num)
    have htwo : ((2 : ℕ) : ZMod 2147483647) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      decide
    exact htwo
  · intro hzero
    have hleading :=
      endpointKernelDegree27_leadingCoefficient (K := ZMod 2147483647)
    exact one_ne_zero (hleading.symm.trans hzero)

/-! ## Transcript-order countermodel -/

/-- A challenge-indexed state choice is fixed before the challenge precisely
when it is constant.  This tiny semantic predicate is enough to expose why
commitment injectivity alone says nothing about chronology. -/
def StateFixedBeforeChallenge {Challenge State : Type*}
    (stateAfterChallenge : Challenge → State) : Prop :=
  ∀ challenge₁ challenge₂,
    stateAfterChallenge challenge₁ = stateAfterChallenge challenge₂

/-- Even an injective commitment made after the challenge can bind each
adaptively selected state while failing to fix any state before the
challenge.  The accepted transcript therefore needs the pre-`eta` prefix
equation; injectivity by itself cannot replace it. -/
theorem commitment_after_eta_allows_adaptive_state :
    ∃ (commit : Bool → Bool) (stateAfterEta : Bool → Bool),
      Function.Injective commit ∧
      (∀ eta, commit (stateAfterEta eta) = eta) ∧
      ¬ StateFixedBeforeChallenge stateAfterEta := by
  refine ⟨id, id, fun _ _ h => h, fun _ => rfl, ?_⟩
  intro hfixed
  have hfalse : false = true := hfixed false true
  simp at hfalse

/-! ## Omitted and mismatched terminal authentication -/

/-- Authentication binds a value at a root and point only if accepted values
there are unique. -/
def TerminalValueUniqueAt {Root Point Value : Type*}
    (Authenticated : Root → Point → Value → Prop)
    (root : Root) (point : Point) : Prop :=
  ∀ value₁ value₂,
    Authenticated root point value₁ →
      Authenticated root point value₂ → value₁ = value₂

/-- Omitting the terminal opening accepts every value. -/
def omittedTerminalAuthentication
    (_root : Unit) (_point : Unit) (_value : Bool) : Prop :=
  True

/-- If the terminal opening is omitted, two different terminal values are
accepted at the same root and point. -/
theorem omitted_terminal_opening_is_not_binding :
    ¬ TerminalValueUniqueAt omittedTerminalAuthentication () () := by
  intro hunique
  have hfalse : false = true := hunique false true trivial trivial
  simp at hfalse

/-- A minimal authentication relation that binds a value to the supplied
root. -/
def rootEchoAuthentication
    (root : Bool) (_point : Unit) (value : Bool) : Prop :=
  value = root

/-- Authentication may be perfectly unique at each individual root and yet
say nothing about the pre-`eta` root when checked against a different root. -/
theorem wrong_root_authentication_does_not_bind_preEta_root :
    TerminalValueUniqueAt rootEchoAuthentication false () ∧
      TerminalValueUniqueAt rootEchoAuthentication true () ∧
      rootEchoAuthentication true () true ∧
      ¬ rootEchoAuthentication false () true := by
  refine ⟨?_, ?_, rfl, by simp [rootEchoAuthentication]⟩
  · intro value₁ value₂ h₁ h₂
    exact h₁.trans h₂.symm
  · intro value₁ value₂ h₁ h₂
    exact h₁.trans h₂.symm

/-- A minimal authentication relation that binds a value to the supplied
evaluation point. -/
def pointEchoAuthentication
    (_root : Unit) (point value : Bool) : Prop :=
  value = point

/-- Point-local uniqueness likewise does not authenticate the terminal at
the transcript-derived point when the opening is checked at another point. -/
theorem wrong_point_authentication_does_not_bind_derived_point :
    TerminalValueUniqueAt pointEchoAuthentication () false ∧
      TerminalValueUniqueAt pointEchoAuthentication () true ∧
      pointEchoAuthentication () true true ∧
      ¬ pointEchoAuthentication () false true := by
  refine ⟨?_, ?_, rfl, by simp [pointEchoAuthentication]⟩
  · intro value₁ value₂ h₁ h₂
    exact h₁.trans h₂.symm
  · intro value₁ value₂ h₁ h₂
    exact h₁.trans h₂.symm

/-! ## Freshness is not the live correlated premise -/

/-- The finite carried-invariant model closes its exact generator
certificate even though the residual released map reads the pivot.  This is
the required counterexample to treating pivot freshness as a necessary
premise. -/
theorem correlated_certificate_succeeds_when_pivot_freshness_fails :
    AspisV5DeployedCarriedInvariant.egReleased
        AspisV5DeployedCarriedInvariant.egPivot ≠ 0 ∧
      AspisV5DeployedCarriedInvariant.CarriedCertificate
        AspisV5DeployedCarriedInvariant.egInactive
        AspisV5DeployedCarriedInvariant.egReleased
        AspisV5DeployedCarriedInvariant.egPivot
        AspisV5DeployedCarriedInvariant.egGens
        AspisV5DeployedCarriedInvariant.egΔB ∧
      AspisV5DeployedCarriedInvariant.egReleased
          (0 : AspisV5DeployedCarriedInvariant.egM) -
            ((AspisV5DeployedCarriedInvariant.egInactive
                AspisV5DeployedCarriedInvariant.egPivot)⁻¹ *
              AspisV5DeployedCarriedInvariant.egInactive
                (0 : AspisV5DeployedCarriedInvariant.egM)) •
              AspisV5DeployedCarriedInvariant.egReleased
                AspisV5DeployedCarriedInvariant.egPivot =
        AspisV5DeployedCarriedInvariant.egReleased
            (AspisV5DeployedCarriedInvariant.egGens 1) -
          ((AspisV5DeployedCarriedInvariant.egInactive
              AspisV5DeployedCarriedInvariant.egPivot)⁻¹ *
            AspisV5DeployedCarriedInvariant.egInactive
              (AspisV5DeployedCarriedInvariant.egGens 1)) •
            AspisV5DeployedCarriedInvariant.egReleased
              AspisV5DeployedCarriedInvariant.egPivot :=
  ⟨AspisV5DeployedCarriedInvariant.egBeyondFresh.1,
    AspisV5DeployedCarriedInvariant.egCertificate,
    AspisV5DeployedCarriedInvariant.egPair_carried⟩

/-! ## Residual coverage remains load-bearing -/

/-- Terminal determinism does not hide an independently released residual
coordinate when the pad map is not surjective.  Therefore the candidate
Rust pad-plus-pivot map still needs an exact coverage theorem; a measured
rank is not enough. -/
theorem missing_residual_pad_coverage_leaks :
    ¬ Function.Surjective
        AspisV5ComponentBTriangularHiding.Model.zeroPadMap ∧
      (PMF.uniformOfFintype
          (AspisV5ComponentBTriangularHiding.Model.F ×
            AspisV5ComponentBTriangularHiding.Model.F)).map
          (AspisV5ComponentBTriangularHiding.triangularView
            AspisV5ComponentBTriangularHiding.Model.terminal
            (0 : AspisV5ComponentBTriangularHiding.Model.F →ₗ[
              AspisV5ComponentBTriangularHiding.Model.F]
              AspisV5ComponentBTriangularHiding.Model.F)
            AspisV5ComponentBTriangularHiding.Model.zeroPadMap 0 0) ≠
        (PMF.uniformOfFintype
          (AspisV5ComponentBTriangularHiding.Model.F ×
            AspisV5ComponentBTriangularHiding.Model.F)).map
          (AspisV5ComponentBTriangularHiding.triangularView
            AspisV5ComponentBTriangularHiding.Model.terminal
            (0 : AspisV5ComponentBTriangularHiding.Model.F →ₗ[
              AspisV5ComponentBTriangularHiding.Model.F]
              AspisV5ComponentBTriangularHiding.Model.F)
            AspisV5ComponentBTriangularHiding.Model.zeroPadMap 0 1) :=
  ⟨AspisV5ComponentBTriangularHiding.Model.zeroPadMap_not_surjective,
    AspisV5ComponentBTriangularHiding.Model.no_pad_coverage_leaks⟩

end AspisV5FreezeBTranscriptAuthentication

#print axioms AspisV5FreezeBTranscriptAuthentication.authenticated_bound_terminal_and_same_pass_relation
#print axioms AspisV5FreezeBTranscriptAuthentication.exact_degree27_boundary_only_authentication_fails
#print axioms AspisV5FreezeBTranscriptAuthentication.commitment_after_eta_allows_adaptive_state
#print axioms AspisV5FreezeBTranscriptAuthentication.omitted_terminal_opening_is_not_binding
#print axioms AspisV5FreezeBTranscriptAuthentication.wrong_root_authentication_does_not_bind_preEta_root
#print axioms AspisV5FreezeBTranscriptAuthentication.wrong_point_authentication_does_not_bind_derived_point
#print axioms AspisV5FreezeBTranscriptAuthentication.correlated_certificate_succeeds_when_pivot_freshness_fails
#print axioms AspisV5FreezeBTranscriptAuthentication.missing_residual_pad_coverage_leaks

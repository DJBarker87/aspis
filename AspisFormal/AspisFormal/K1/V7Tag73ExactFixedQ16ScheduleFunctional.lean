import AspisFormal.K1.V7Tag73ExactParsedProofSourceBinding
import AspisFormal.K1.V7Tag73ExactClientKnowledgeComposition

/-!
# Source schedule functionality for fixed Tag-73 K1.3 q16

The fixed q16 residual package needs the total one-fold schedule to be a
function of the verifier's round-zero alpha.  This is not an additional
cryptographic hypothesis: the parsed-source binding already carries the two
checked inverse-table equations, and a small local uniqueness argument turns
those equations into the required functionality.

The module deliberately leaves the actual four-field residual-fibre
noninterference theorem open.  It closes only the independent
alpha-to-schedule seam used by that theorem.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace AspisK1.V7Tag73ExactFixedQ16ScheduleFunctional

open AspisK1.V7FsAokExperiment
open AspisK1.V7Tag73ExactClientKnowledgeComposition
open AspisK1.V7Tag73ExactCompilerResources
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73ExactFixedK13K14Classifier
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisK1.V7Tag73ExactParsedProofSourceBinding
open AspisK1.V7Tag73ExactPlainRomRun
open AspisK1.V7Tag73ExactSourceAcceptanceModel
open AspisK1.V7Tag73OperationalSemanticReplay
open AspisK1.V7Tag73TranscriptSchedule
open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7CoherentTraceExtraction
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-- Two base-field entries satisfying the same nonzero extension-field
inverse equation are equal.  This is the one coordinate-level fact required
to avoid importing the aggregate canonical-schedule construction. -/
private theorem inverse_entry_unique
    (multiplier : QM31Exact) (left right : M31Exact)
    (leftExact : multiplier * algebraMap M31Exact QM31Exact left = 1)
    (rightExact : multiplier * algebraMap M31Exact QM31Exact right = 1) :
    left = right := by
  apply FaithfulSMul.algebraMap_injective M31Exact QM31Exact
  have multiplierNonzero : multiplier ≠ 0 := by
    intro zero
    rw [zero] at leftExact
    norm_num at leftExact
  apply (mul_left_cancel₀ multiplierNonzero)
  calc
    multiplier * algebraMap M31Exact QM31Exact left = 1 := leftExact
    _ = multiplier * algebraMap M31Exact QM31Exact right := rightExact.symm

/-- Alpha and the two source-checked inverse arrays uniquely determine the
full total schedule.  It is intentionally a local, low-memory form of the
canonical schedule uniqueness result. -/
private theorem exact_one_fold_schedule_unique_from_tables
    (left right : ExactSchedule)
    (alphaExact : left.alpha = right.alpha)
    (leftTables : ExactOneFoldInverseTables left)
    (rightTables : ExactOneFoldInverseTables right) :
    left = right := by
  cases left with
  | mk leftAlpha leftX leftY =>
      cases right with
      | mk rightAlpha rightX rightY =>
          dsimp only at alphaExact leftTables rightTables ⊢
          have xExact : leftX = rightX := by
            funext index
            exact inverse_entry_unique (2 * exactCircleX index)
              (leftX index) (rightX index) (leftTables.1 index)
              (rightTables.1 index)
          have yExact : leftY = rightY := by
            funext index
            exact inverse_entry_unique (2 * exactCircleY index)
              (leftY index) (rightY index) (leftTables.2 index)
              (rightTables.2 index)
          cases alphaExact
          cases xExact
          cases yExact
          rfl

/-- Equal operational alpha-zero challenges and two parsed-source bindings
give equal total one-fold schedules.  This is the pointwise form consumed by
the derived q16 profile argument; keeping it pointwise avoids unfolding that
large dependent predicate while preserving the exact mathematical content. -/
theorem exact_fixed_k13_schedule_eq_of_source_bindings
    {HiddenTape TapeIdentity Observation Statement Payload Witness : Type}
    {parameters : ExactCompilerResourceParameters}
    {transitionFuel : Nat}
    {configuration : ExactPlainRomWitnessConfiguration HiddenTape TapeIdentity
      Observation Statement Tag73K12ParsedProof Payload Witness parameters}
    {projection : AcceptedTapeProjection Statement Tag73K12ParsedProof Payload}
    {fixedInstance : PublicInstance Statement}
    {leftSample rightSample : ExactCompilerSample HiddenTape parameters}
    (left : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance leftSample)
    (leftDecoded : Fin 641 → QM31Exact)
    (leftBinding : ExactParsedProofSourceBinding left leftDecoded)
    (right : ExactK12OperationalInput transitionFuel configuration projection
      fixedInstance rightSample)
    (rightDecoded : Fin 641 → QM31Exact)
    (rightBinding : ExactParsedProofSourceBinding right rightDecoded)
    (alphaExact : exactOperationalChallenge left (.alpha 0) =
      exactOperationalChallenge right (.alpha 0)) :
    (exactK13ParsedProof left).schedule =
      (exactK13ParsedProof right).schedule := by
  refine exact_one_fold_schedule_unique_from_tables
    (exactK13ParsedProof left).schedule (exactK13ParsedProof right).schedule
    ?_ leftBinding.inverseTablesExact rightBinding.inverseTablesExact
  calc
    (exactK13ParsedProof left).schedule.alpha =
        exactOperationalChallenge left (.alpha 0) :=
      leftBinding.alphaZeroExact
    _ = exactOperationalChallenge right (.alpha 0) := alphaExact
    _ = (exactK13ParsedProof right).schedule.alpha :=
      rightBinding.alphaZeroExact.symm

#print axioms exact_fixed_k13_schedule_eq_of_source_bindings

end

end AspisK1.V7Tag73ExactFixedQ16ScheduleFunctional

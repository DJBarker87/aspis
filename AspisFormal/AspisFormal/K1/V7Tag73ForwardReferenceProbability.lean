import AspisFormal.K1.V7Tag73NoPairOccurrenceTrichotomy
import AspisFormal.K1.V7Tag73ResourceLazyOracle

/-!
# Uniform bounds for literal Tag-73 forward-reference targets

`V7Tag73NoPairOccurrenceTrichotomy` proves that a raw SHA input beginning
with a missing advance state's 32 bytes determines at most one possible
advance state.  This module transports that deterministic singleton fact to
the concrete uniform `Digest256` law.

The finite coefficient below is exactly the number of explicitly supplied
raw query inputs.  It is not the verifier-call count, the q16 forest size, a
work-grinding budget, or the total adversary query bound unless a later
operational theorem proves that the relevant causal target list has that
length.  No such protocol failure inclusion is asserted here.

These results cover literal byte-prefix references only.  A transformed use
of an advance answer is outside this module because `QueryRecord.input` does
not retain semantic dependency provenance.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73ForwardReferenceProbability

open MeasureTheory
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement
open AspisK1.V7Tag73ConcreteQueryDag
open AspisK1.V7Tag73InteractiveExecution
open AspisK1.V7Tag73AtomicPairFork
open AspisK1.V7Tag73NoPairOccurrenceTrichotomy
open AspisK1.V7Tag73ResourceLazyOracle
open AspisK1.V7FsAokExperiment
open AspisK1.V7FsStateRestorationCoupling

noncomputable section

/-! ## A subsingleton set under the exact deployed uniform law -/

/-- First-principles finite-cardinality bound for any subsingleton set of
deployed 32-byte digests. -/
theorem uniform_digest_hits_subsingleton_set_le
    (target : Set Digest256) (small : target.Subsingleton) :
    uniformDigest256.toOuterMeasure target ≤
      (1 : ENNReal) / ((2 : ENNReal) ^ 256) := by
  classical
  unfold uniformDigest256
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  have targetCardLe : Fintype.card ↑target ≤ 1 := by
    apply Fintype.card_le_one_iff_subsingleton.mpr
    exact (Set.subsingleton_coe target).mpr small
  have digestCard :
      (Fintype.card Digest256 : ENNReal) = (2 : ENNReal) ^ 256 := by
    rw [deployed_digest_256_cardinality]
    norm_num
  rw [digestCard]
  apply ENNReal.div_le_div_right
  exact_mod_cast targetCardLe

/-- For any fixed raw query input, a uniform 256-bit advance state matches
its literal 32-byte prefix target with probability at most `2^-256`. -/
theorem uniform_digest_hits_literal_state_prefix_target_le
    (input : ShaInput) :
    uniformDigest256.toOuterMeasure (literalStatePrefixTarget input) ≤
      (1 : ENNReal) / ((2 : ENNReal) ^ 256) := by
  exact uniform_digest_hits_subsingleton_set_le
    (literalStatePrefixTarget input)
    (literal_state_prefix_target_subsingleton input)

/-- Once a concrete state is known to inhabit a literal-prefix target, the
target is exactly that singleton. -/
theorem literal_state_prefix_target_eq_singleton_of_mem
    (input : ShaInput) (state : Digest256)
    (member : state ∈ literalStatePrefixTarget input) :
    literalStatePrefixTarget input = {state} := by
  ext candidate
  constructor
  · intro candidateMember
    exact Set.mem_singleton_iff.mpr
      (literal_state_prefix_target_subsingleton input
        candidateMember member)
  · intro singletonMember
    have equal : candidate = state := Set.mem_singleton_iff.mp singletonMember
    simpa [equal] using member

/-- A nonempty literal target has exactly singleton mass, rather than merely
the upper bound. -/
theorem uniform_digest_hits_nonempty_literal_target_exact
    (input : ShaInput) (state : Digest256)
    (member : state ∈ literalStatePrefixTarget input) :
    uniformDigest256.toOuterMeasure (literalStatePrefixTarget input) =
      (1 : ENNReal) / ((2 : ENNReal) ^ 256) := by
  rw [literal_state_prefix_target_eq_singleton_of_mem input state member]
  exact uniform_digest_guess_probability state

/-! ## Exact specialization of the generated forward-reference branch -/

/-- Fix a generated squeeze, a frozen Q1 history, and the first literal
forward-reference occurrence certified by the deterministic trichotomy.  If
the resulting raw target is then tested against a fresh uniform digest, its
mass is exactly `2^-256`.

This is deliberately a fixed-target statement.  It does not say that an input
chosen after observing the same sampled digest is causal; that ordering must
come from the eventual operational replay theorem. -/
theorem generated_literal_forward_reference_fixed_target_probability_exact
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (stateAtAdversaryHalt : OracleState)
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (advanceAnswer : Digest256)
    (occurrence : StatePrefixOccurrence)
    (noPair : firstGeneratedPairOccurrenceInFrozenQ1 stateAtAdversaryHalt
      execution generated = none)
    (found : firstStatePrefixOccurrence advanceAnswer
      (freezeAdversaryQ1 stateAtAdversaryHalt) = some occurrence) :
    uniformDigest256.toOuterMeasure
        (literalStatePrefixTarget occurrence.chosen.input) =
      (1 : ENNReal) / ((2 : ENNReal) ^ 256) := by
  obtain ⟨_decomposition, _priorFresh, _chosenPrefix,
      _notOutput, _notAdvance, _actor, targetMember, _targetSmall⟩ :=
    generated_first_literal_forward_reference_is_exact
      stateAtAdversaryHalt execution generated advanceAnswer occurrence
      noPair found
  exact uniform_digest_hits_nonempty_literal_target_exact
    occurrence.chosen.input advanceAnswer targetMember

theorem generated_literal_forward_reference_fixed_target_probability_le
    {table : FixedOracleTable} {dag : ConcreteDagInstance}
    (stateAtAdversaryHalt : OracleState)
    (execution : ConcreteFirstExecution table dag.tape)
    (generated : GeneratedReplayPrefix dag)
    (advanceAnswer : Digest256)
    (occurrence : StatePrefixOccurrence)
    (noPair : firstGeneratedPairOccurrenceInFrozenQ1 stateAtAdversaryHalt
      execution generated = none)
    (found : firstStatePrefixOccurrence advanceAnswer
      (freezeAdversaryQ1 stateAtAdversaryHalt) = some occurrence) :
    uniformDigest256.toOuterMeasure
        (literalStatePrefixTarget occurrence.chosen.input) ≤
      (1 : ENNReal) / ((2 : ENNReal) ^ 256) := by
  rw [generated_literal_forward_reference_fixed_target_probability_exact
    stateAtAdversaryHalt execution generated advanceAnswer occurrence
    noPair found]

/-! ## Finite fixed-input unions -/

/-- Union of the literal state-prefix targets named by exactly `count` raw
query inputs.  The index type, rather than an unrelated protocol budget, is
the target count. -/
def literalStatePrefixTargetUnion {count : Nat}
    (inputs : Fin count → ShaInput) : Set Digest256 :=
  ⋃ index, literalStatePrefixTarget (inputs index)

theorem uniform_digest_hits_literal_prefix_target_union_le
    {count : Nat} (inputs : Fin count → ShaInput) :
    uniformDigest256.toOuterMeasure
        (literalStatePrefixTargetUnion inputs) ≤
      (count : ENNReal) / ((2 : ENNReal) ^ 256) := by
  calc
    uniformDigest256.toOuterMeasure
        (literalStatePrefixTargetUnion inputs) ≤
        ∑ index : Fin count,
          uniformDigest256.toOuterMeasure
            (literalStatePrefixTarget (inputs index)) := by
      exact measure_iUnion_fintype_le uniformDigest256.toOuterMeasure
        (fun index => literalStatePrefixTarget (inputs index))
    _ ≤ ∑ _index : Fin count,
          (1 : ENNReal) / ((2 : ENNReal) ^ 256) := by
      exact Finset.sum_le_sum fun index _ =>
        uniform_digest_hits_literal_state_prefix_target_le (inputs index)
    _ = (count : ENNReal) / ((2 : ENNReal) ^ 256) := by
      simp [div_eq_mul_inv]

/-- The zero-target case is literally empty and has probability zero. -/
theorem uniform_digest_hits_zero_literal_prefix_targets
    (inputs : Fin 0 → ShaInput) :
    uniformDigest256.toOuterMeasure
        (literalStatePrefixTargetUnion inputs) = 0 := by
  simp [literalStatePrefixTargetUnion]

/-- List wrapper whose coefficient is exactly the number of supplied raw
query inputs. -/
def literalStatePrefixTargetUnionForList
    (inputs : List ShaInput) : Set Digest256 :=
  literalStatePrefixTargetUnion (fun index => inputs.get index)

theorem uniform_digest_hits_literal_prefix_target_list_union_le
    (inputs : List ShaInput) :
    uniformDigest256.toOuterMeasure
        (literalStatePrefixTargetUnionForList inputs) ≤
      (inputs.length : ENNReal) / ((2 : ENNReal) ^ 256) := by
  exact uniform_digest_hits_literal_prefix_target_union_le
    (fun index => inputs.get index)

#print axioms uniform_digest_hits_subsingleton_set_le
#print axioms uniform_digest_hits_literal_state_prefix_target_le
#print axioms literal_state_prefix_target_eq_singleton_of_mem
#print axioms uniform_digest_hits_nonempty_literal_target_exact
#print axioms generated_literal_forward_reference_fixed_target_probability_exact
#print axioms generated_literal_forward_reference_fixed_target_probability_le
#print axioms uniform_digest_hits_literal_prefix_target_union_le
#print axioms uniform_digest_hits_zero_literal_prefix_targets
#print axioms uniform_digest_hits_literal_prefix_target_list_union_le

end

end AspisK1.V7Tag73ForwardReferenceProbability

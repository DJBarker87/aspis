import AspisFormal.Pool.V7Width29ComponentExtraction
import AspisFormal.Pool.V7ExtractedLaneWords

/-!
# Recovering the M31 C1 messages from the uniform QM31 decoder

The width-29 correlated theorem and its algorithmic decoder are stated over
one field, QM31.  The first 26 committed lanes, however, are literal M31
values embedded in QM31.  A selected QM31 message must therefore be shown to
lie in that embedded subfield before its first sixteen lanes can be used as
the production trace.

This file proves the generic recovery argument.  Projection to the base
coordinate commutes with the exact circle encoder because every released
domain coordinate is in M31.  If a candidate differed from its projection,
the two codewords could agree on at most 1024 positions.  The common accepted
support has more than 38229 positions, so they must be the same message.

`InitialProjectionBinding` isolates the two concrete encoder facts still to
be instantiated: projection commutation and the already-proved 1024 overlap
cap.  It is not a cryptographic or list-decoding assumption.
-/

set_option autoImplicit false

namespace AspisPool.V7C1SubfieldRecovery

open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7ExtractedLaneWords
open AspisPool.V7Width29ComponentExtraction
open AspisV5ComponentCQM31TowerExact
open AspisV6Width29CorrelatedAgreement

/-- Keep the literal `(c0.a)` coordinate and zero the other three tower
coordinates. -/
def projectBase (value : QM31Exact) : QM31Exact :=
  embedM31Exact value.re.re

@[simp] theorem projectBase_embedM31Exact (value : M31Exact) :
    projectBase (embedM31Exact value) = embedM31Exact value := by
  rfl

@[simp] theorem projectBase_zero : projectBase (0 : QM31Exact) = 0 := by
  rfl

def projectMessage (message : InitialMessage QM31Exact) :
    InitialMessage QM31Exact :=
  fun row => projectBase (message row)

/-- Exact non-cryptographic properties of the concrete initial encoder used
by the subfield-recovery argument. -/
structure InitialProjectionBinding
    (decoder : ExactDecoderInstantiation QM31Exact) : Prop where
  commutes : ∀ message,
    decoder.initialEncoder (projectMessage message) =
      fun index => projectBase (decoder.initialEncoder message index)
  overlapCap : ∀ left right,
    left ≠ right →
      agreementCount (decoder.initialEncoder left)
        (decoder.initialEncoder right) ≤ 1024

/-- A message agreeing with base-valued received symbols on more than 1024
common positions is fixed by base projection. -/
theorem message_fixed_by_base_projection_of_large_shared_support
    (decoder : ExactDecoderInstantiation QM31Exact)
    (binding : InitialProjectionBinding decoder)
    (lanes : Width29InitialWords QM31Exact)
    (components : Width29InitialMessages QM31Exact)
    (support : Finset (Fin 1048576))
    (column : Fin 26)
    (shared : support ⊆
      width29JointAgreementSet decoder.initialEncoder lanes components)
    (receivedFixed : ∀ index,
      projectBase (lanes (c1LaneIndex column) index) =
        lanes (c1LaneIndex column) index)
    (supportLarge : 1024 < support.card) :
    projectMessage (components (c1LaneIndex column)) =
      components (c1LaneIndex column) := by
  classical
  let message := components (c1LaneIndex column)
  by_contra differs
  have messageNe : message ≠ projectMessage message := by
    exact fun equal => differs equal.symm
  have supportSubsetAgreement : support ⊆
      Finset.univ.filter fun index =>
        decoder.initialEncoder message index =
          decoder.initialEncoder (projectMessage message) index := by
    intro index indexInSupport
    have jointAll : ∀ lane,
        lanes lane index = decoder.initialEncoder (components lane) index := by
      simpa only [width29JointAgreementSet, Finset.mem_filter,
        Finset.mem_univ, true_and] using (shared indexInSupport)
    have commuteAt := congrFun (binding.commutes message) index
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    calc
      decoder.initialEncoder message index =
          lanes (c1LaneIndex column) index :=
        (jointAll (c1LaneIndex column)).symm
      _ = projectBase (lanes (c1LaneIndex column) index) :=
        (receivedFixed index).symm
      _ = projectBase (decoder.initialEncoder message index) :=
        congrArg projectBase (jointAll (c1LaneIndex column))
      _ = decoder.initialEncoder (projectMessage message) index :=
        commuteAt.symm
  have supportCardLe : support.card ≤
      agreementCount (decoder.initialEncoder message)
        (decoder.initialEncoder (projectMessage message)) := by
    simpa only [agreementCount] using
      Finset.card_le_card supportSubsetAgreement
  have overlap := binding.overlapCap message (projectMessage message) messageNe
  omega

/-- Every value in a reconstructed C1 lane is base-valued, including the
canonical zero used to totalize an unavailable/noncanonical raw symbol. -/
theorem projectBase_c1Received
    (words : V7MerkleQueryExtractor.ExtractedWords)
    (column : Fin 26) (index : Fin 1048576) :
    projectBase (c1Received words column index) =
      c1Received words column index := by
  unfold c1Received
  cases decoded : V7PackedFibreTowerBridge.decodeC1EntryExact
      (extractedC1Leaf words (fibreIndex index)).value
      (fibreSlot index) column with
  | none => simp [decoded]
  | some value => simp [decoded]

/-- The common support returned by the width-29 extraction makes all 26 C1
component messages literal embedded-M31 messages. -/
theorem extracted_c1_components_are_base
    (decoder : ExactDecoderInstantiation QM31Exact)
    (binding : InitialProjectionBinding decoder)
    (words : V7MerkleQueryExtractor.ExtractedWords)
    (strategy : Width29ProximateStrategy QM31Exact
      (Fin 1048576) (InitialMessage QM31Exact))
    (gamma : QM31Exact)
    (selected : Width29InitialMessages QM31Exact)
    (valid : Width29ValidResponse decoder.initialEncoder
      AspisV6PublishedTheoremInterfaces.initialAgreementThreshold
        (extractedWidth29InitialWords words) strategy gamma)
    (shared : strategy.support gamma ⊆
      width29JointAgreementSet decoder.initialEncoder
        (extractedWidth29InitialWords words) selected) :
    ∀ column : Fin 26,
      projectMessage (selected (c1LaneIndex column)) =
        selected (c1LaneIndex column) := by
  intro column
  apply message_fixed_by_base_projection_of_large_shared_support
    decoder binding (extractedWidth29InitialWords words) selected
      (strategy.support gamma) column shared
  · intro index
    rw [extractedWidth29_c1_lane]
    exact projectBase_c1Received words column index
  · have large : 38229 < (strategy.support gamma).card := by
      simpa [AspisV6PublishedTheoremInterfaces.initialAgreementThreshold] using
        valid.1
    omega

def semanticColumnIndex (lane : Fin 16) : Fin 26 :=
  ⟨lane.val, by omega⟩

/-- The first sixteen recovered messages, now as the exact M31 trace shape
consumed by the accepted-terminal extraction theorems. -/
def semanticTrace (selected : Width29InitialMessages QM31Exact) :
    Fin 1024 → Fin 16 → M31Exact :=
  fun row lane =>
    (selected (c1LaneIndex (semanticColumnIndex lane)) row).re.re

theorem semanticTrace_embeds_to_selected
    (selected : Width29InitialMessages QM31Exact)
    (base : ∀ column : Fin 26,
      projectMessage (selected (c1LaneIndex column)) =
        selected (c1LaneIndex column))
    (row : Fin 1024) (lane : Fin 16) :
    embedM31Exact (semanticTrace selected row lane) =
      selected (c1LaneIndex (semanticColumnIndex lane)) row := by
  have fixed := congrFun (base (semanticColumnIndex lane)) row
  simpa [projectMessage, projectBase, semanticTrace] using fixed

#print axioms message_fixed_by_base_projection_of_large_shared_support
#print axioms projectBase_c1Received
#print axioms extracted_c1_components_are_base
#print axioms semanticTrace_embeds_to_selected

end AspisPool.V7C1SubfieldRecovery

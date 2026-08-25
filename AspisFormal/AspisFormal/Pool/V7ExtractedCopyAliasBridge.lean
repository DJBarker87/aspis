import AspisFormal.Pool.V7AcceptedSemanticRelationComposition

/-!
# Exact copy-source bridge for the extracted Tag-73 trace

`RequiredTraceAliases` names five alias conclusions, but the accepted semantic
composition currently exposes the compiled copy lane only as an independent
row function.  A zero value of that opaque function does not by itself say
which C1 cells are equal.

This leaf therefore records only the concrete source equations used by the
deployed atomic copy registry:

* tag 21 links input range `(864,11)` to input note `(795,0)`;
* tag 22 links output range `(866,11)` to output note `(799,0)`;
* tag 23 links output note `(799,0)` to balance `(864,12)`; and
* at each of the twenty path levels, the two source links run
  `input bit -> output bit -> sibling bit` through the frozen auxiliary rows.

The equations are stated directly on the selected width-29 C1 messages.  The
proofs project them to the literal extracted M31 table and derive every field
of `RequiredTraceAliases`, plus the separately named `BalanceOutputCellAlias`.
No generic copy-lane-zero premise, LogUp faithfulness predicate, or Poseidon
semantic is introduced here.
-/

set_option autoImplicit false

namespace AspisPool.V7ExtractedCopyAliasBridge

open AspisPool.AlgorithmicCircleDecoderV7
open AspisPool.V7AcceptedSemanticRelationComposition
open AspisPool.V7AtomicSemanticRowsFromTrace
open AspisPool.V7C1SubfieldRecovery
open AspisPool.V7CoherentTraceExtraction
open AspisPool.V7ExtractedLaneWords
open AspisPool.V7OpenedColumnsFromTrace
open AspisPool.V7Width29ComponentExtraction
open AspisV5ComponentCQM31TowerExact
open AspisV6OneFoldCandidateExtraction

/-! ## The selected C1 table at an exact physical coordinate -/

/-- One of the first sixteen selected C1 component values, before taking its
literal M31 base coordinate. -/
def selectedC1Cell
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (row : Fin 1024) (column : Fin 16) : QM31Exact :=
  extraction.components
    (c1LaneIndex (semanticColumnIndex column)) row

/-- `extractedPhysicalTrace` is definitionally the base coordinate of the
same selected C1 table. -/
@[simp] theorem selectedC1Cell_base
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (row : Fin 1024) (column : Fin 16) :
    (selectedC1Cell extraction row column).re.re =
      extractedPhysicalTrace extraction row column := by
  rfl

/-- Equality at two selected QM31 C1 coordinates projects to equality at the
corresponding concrete M31 trace coordinates. -/
theorem extractedPhysicalTrace_eq_of_selectedC1Cell_eq
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    {leftRow rightRow : Fin 1024} {leftColumn rightColumn : Fin 16}
    (equation : selectedC1Cell extraction leftRow leftColumn =
      selectedC1Cell extraction rightRow rightColumn) :
    extractedPhysicalTrace extraction leftRow leftColumn =
      extractedPhysicalTrace extraction rightRow rightColumn := by
  have baseEquation := congrArg (fun value : QM31Exact => value.re.re) equation
  simpa only [selectedC1Cell_base] using baseEquation

/-! ## Exact deployed source equations -/

/-- The five concrete source-link families sufficient for
`RequiredTraceAliases`.  The first three fields are the literal scalar links
21--23.  The final two fields are the two literal path-bit hops at each of the
twenty frozen auxiliary-row triples. -/
structure RequiredCopySourceEquations
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule) : Prop where
  inputRangeToNote :
    selectedC1Cell extraction 864 11 = selectedC1Cell extraction 795 0
  outputRangeToNote :
    selectedC1Cell extraction 866 11 = selectedC1Cell extraction 799 0
  outputNoteToBalance :
    selectedC1Cell extraction 799 0 = selectedC1Cell extraction 864 12
  inputPathToOutput : ∀ level : Fin 20,
    selectedC1Cell extraction (inputPathRow level) 0 =
      selectedC1Cell extraction (outputPathRow level) 0
  outputPathToSibling : ∀ level : Fin 20,
    selectedC1Cell extraction (outputPathRow level) 0 =
      selectedC1Cell extraction (siblingPathRow level) 0

/-! ## Every required raw alias -/

theorem input_value_alias_of_copy_sources
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (source : RequiredCopySourceEquations extraction) :
    (rawOpenedColumnsFromTrace (extractedPhysicalTrace extraction)).inputNoteValue =
      (rawOpenedColumnsFromTrace (extractedPhysicalTrace extraction)).rin.value := by
  change extractedPhysicalTrace extraction 795 0 =
    extractedPhysicalTrace extraction 864 11
  exact extractedPhysicalTrace_eq_of_selectedC1Cell_eq extraction
    source.inputRangeToNote.symm

theorem output_value_alias_of_copy_sources
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (source : RequiredCopySourceEquations extraction) :
    (rawOpenedColumnsFromTrace (extractedPhysicalTrace extraction)).outputNoteValue =
      (rawOpenedColumnsFromTrace (extractedPhysicalTrace extraction)).rout.value := by
  change extractedPhysicalTrace extraction 799 0 =
    extractedPhysicalTrace extraction 866 11
  exact extractedPhysicalTrace_eq_of_selectedC1Cell_eq extraction
    source.outputRangeToNote.symm

theorem balance_output_value_alias_of_copy_sources
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (source : RequiredCopySourceEquations extraction) :
    (rawOpenedColumnsFromTrace
        (extractedPhysicalTrace extraction)).balanceOutputValue =
      (rawOpenedColumnsFromTrace (extractedPhysicalTrace extraction)).rout.value := by
  change extractedPhysicalTrace extraction 864 12 =
    extractedPhysicalTrace extraction 866 11
  have noteToBalance := extractedPhysicalTrace_eq_of_selectedC1Cell_eq extraction
    source.outputNoteToBalance
  have rangeToNote := extractedPhysicalTrace_eq_of_selectedC1Cell_eq extraction
    source.outputRangeToNote
  exact noteToBalance.symm.trans rangeToNote.symm

theorem output_path_bit_alias_of_copy_sources
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (source : RequiredCopySourceEquations extraction) (level : Fin 20) :
    (rawOpenedColumnsFromTrace
        (extractedPhysicalTrace extraction)).outputPathBits level =
      (rawOpenedColumnsFromTrace
        (extractedPhysicalTrace extraction)).inputPathBits level := by
  change extractedPhysicalTrace extraction (outputPathRow level) 0 =
    extractedPhysicalTrace extraction (inputPathRow level) 0
  exact (extractedPhysicalTrace_eq_of_selectedC1Cell_eq extraction
    (source.inputPathToOutput level)).symm

theorem sibling_path_bit_alias_of_copy_sources
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (source : RequiredCopySourceEquations extraction) (level : Fin 20) :
    (rawOpenedColumnsFromTrace
        (extractedPhysicalTrace extraction)).siblingPathBits level =
      (rawOpenedColumnsFromTrace
        (extractedPhysicalTrace extraction)).inputPathBits level := by
  change extractedPhysicalTrace extraction (siblingPathRow level) 0 =
    extractedPhysicalTrace extraction (inputPathRow level) 0
  have inputToOutput := extractedPhysicalTrace_eq_of_selectedC1Cell_eq extraction
    (source.inputPathToOutput level)
  have outputToSibling := extractedPhysicalTrace_eq_of_selectedC1Cell_eq extraction
    (source.outputPathToSibling level)
  exact outputToSibling.symm.trans inputToOutput.symm

/-- All five fields of `RequiredTraceAliases` follow from exactly the three
scalar source links and two twenty-level path-link families above. -/
theorem requiredTraceAliases_of_copy_sources
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (source : RequiredCopySourceEquations extraction) :
    RequiredTraceAliases
      (rawOpenedColumnsFromTrace (extractedPhysicalTrace extraction)) where
  inputValue := input_value_alias_of_copy_sources extraction source
  outputValue := output_value_alias_of_copy_sources extraction source
  balanceOutputValue := balance_output_value_alias_of_copy_sources extraction source
  outputPathBit := output_path_bit_alias_of_copy_sources extraction source
  siblingPathBit := sibling_path_bit_alias_of_copy_sources extraction source

/-- The arithmetic bridge's standalone balance alias is the same concrete
tag-22/tag-23 consequence already present in `RequiredTraceAliases`. -/
theorem balanceOutputCellAlias_of_copy_sources
    {decoder : ExactDecoderInstantiation QM31Exact}
    {binding : InitialProjectionBinding decoder}
    {words : V7MerkleQueryExtractor.ExtractedWords}
    {gamma : QM31Exact} {disclosedFinal : FinalMessage QM31Exact}
    {schedule : ExactSchedule}
    (extraction : CoherentTraceExtraction decoder binding words gamma
      disclosedFinal schedule)
    (source : RequiredCopySourceEquations extraction) :
    BalanceOutputCellAlias (extractedPhysicalTrace extraction) := by
  exact (balanceOutputCellAlias_iff_raw_alias
    (extractedPhysicalTrace extraction)).2
      (balance_output_value_alias_of_copy_sources extraction source)

/-! ## Audit -/

#print axioms selectedC1Cell_base
#print axioms extractedPhysicalTrace_eq_of_selectedC1Cell_eq
#print axioms input_value_alias_of_copy_sources
#print axioms output_value_alias_of_copy_sources
#print axioms balance_output_value_alias_of_copy_sources
#print axioms output_path_bit_alias_of_copy_sources
#print axioms sibling_path_bit_alias_of_copy_sources
#print axioms requiredTraceAliases_of_copy_sources
#print axioms balanceOutputCellAlias_of_copy_sources

end AspisPool.V7ExtractedCopyAliasBridge

import AspisFormal.V5Tag67CandidateTraceExtraction

/-!
# Exact decomposition of the V5 hash and Merkle residual obligation

The accepted-false accounting previously exposed one remaining
`HashMerkleResidualFailure`.  That name still grouped six independent pieces
of the application trace: four typed hashes and two Merkle paths.  This file
splits the group without weakening it.

The structures below are projections of `ExtractedHashMerkleResiduals`.
Their conjunction is equivalent to the original record, so the resulting
six-way failure disjunction neither adds an assumption nor loses a case.
-/

namespace AspisV5HashMerkleResidualDecomposition

open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel
open AspisV5AcceptedSpendRelation
open AspisV5RelationSumcheckSoundness
open AspisV5Tag67CandidateTraceExtraction
open AspisV5Tag67RelationListInclusion

variable {K : Type*} [Field K]

/-! ## Six independently checkable residual groups -/

structure ExtractedOwnerHashResiduals
    (rc : RoundConstants) (O : OpenedColumns) where
  state : State
  gate : TwoRoundPermutationRows rc
    (absorb (initState DOM_OWNER 8) O.k_nu) state
  digestResidual : O.pk_in - truncate8 state = 0

structure ExtractedNullifierHashResiduals
    (rc : RoundConstants) (O : OpenedColumns) where
  state1 : State
  state2 : State
  gate1 : TwoRoundPermutationRows rc
    (absorb (initState DOM_NULLIFIER 16) O.k_nu) state1
  gate2 : TwoRoundPermutationRows rc (absorb state1 O.r_in) state2
  digestResidual : O.nu - truncate8 state2 = 0

structure ExtractedInputNoteHashResiduals
    (rc : RoundConstants) (O : OpenedColumns) where
  state1 : State
  state2 : State
  state3 : State
  gate1 : TwoRoundPermutationRows rc
    (absorb (initState DOM_NOTE 18) O.pk_in) state1
  gate2 : TwoRoundPermutationRows rc
    (absorb state1 (noteChunk1 O.rin.value O.a_in O.r_in)) state2
  gate3 : TwoRoundPermutationRows rc
    (absorb state2 (noteChunk2 O.r_in)) state3
  digestResidual : O.L_in - truncate8 state3 = 0

structure ExtractedOutputNoteHashResiduals
    (rc : RoundConstants) (O : OpenedColumns) where
  state1 : State
  state2 : State
  state3 : State
  gate1 : TwoRoundPermutationRows rc
    (absorb (initState DOM_NOTE 18) O.pk_out) state1
  gate2 : TwoRoundPermutationRows rc
    (absorb state1 (noteChunk1 O.rout.value O.a O.r_out)) state2
  gate3 : TwoRoundPermutationRows rc
    (absorb state2 (noteChunk2 O.r_out)) state3
  digestResidual : O.C_out - truncate8 state3 = 0

def ownerComponent
    {rc : RoundConstants} {O : OpenedColumns}
    (raw : ExtractedHashMerkleResiduals rc O) :
    ExtractedOwnerHashResiduals rc O where
  state := raw.ownerState
  gate := raw.ownerGate
  digestResidual := raw.ownerDigestResidual

def nullifierComponent
    {rc : RoundConstants} {O : OpenedColumns}
    (raw : ExtractedHashMerkleResiduals rc O) :
    ExtractedNullifierHashResiduals rc O where
  state1 := raw.nullState1
  state2 := raw.nullState2
  gate1 := raw.nullGate1
  gate2 := raw.nullGate2
  digestResidual := raw.nullDigestResidual

def inputNoteComponent
    {rc : RoundConstants} {O : OpenedColumns}
    (raw : ExtractedHashMerkleResiduals rc O) :
    ExtractedInputNoteHashResiduals rc O where
  state1 := raw.inputNoteState1
  state2 := raw.inputNoteState2
  state3 := raw.inputNoteState3
  gate1 := raw.inputNoteGate1
  gate2 := raw.inputNoteGate2
  gate3 := raw.inputNoteGate3
  digestResidual := raw.inputNoteDigestResidual

def outputNoteComponent
    {rc : RoundConstants} {O : OpenedColumns}
    (raw : ExtractedHashMerkleResiduals rc O) :
    ExtractedOutputNoteHashResiduals rc O where
  state1 := raw.outputNoteState1
  state2 := raw.outputNoteState2
  state3 := raw.outputNoteState3
  gate1 := raw.outputNoteGate1
  gate2 := raw.outputNoteGate2
  gate3 := raw.outputNoteGate3
  digestResidual := raw.outputNoteDigestResidual

def ofHashMerkleComponents
    {rc : RoundConstants} {O : OpenedColumns}
    (owner : ExtractedOwnerHashResiduals rc O)
    (nullifier : ExtractedNullifierHashResiduals rc O)
    (inputNote : ExtractedInputNoteHashResiduals rc O)
    (outputNote : ExtractedOutputNoteHashResiduals rc O)
    (inputPath : ExtractedMerklePath rc O.L_in O.A O.bits O.sib)
    (outputPath : ExtractedMerklePath rc O.C_out O.A' O.bits O.sib) :
    ExtractedHashMerkleResiduals rc O where
  ownerState := owner.state
  ownerGate := owner.gate
  ownerDigestResidual := owner.digestResidual
  nullState1 := nullifier.state1
  nullState2 := nullifier.state2
  nullGate1 := nullifier.gate1
  nullGate2 := nullifier.gate2
  nullDigestResidual := nullifier.digestResidual
  inputNoteState1 := inputNote.state1
  inputNoteState2 := inputNote.state2
  inputNoteState3 := inputNote.state3
  inputNoteGate1 := inputNote.gate1
  inputNoteGate2 := inputNote.gate2
  inputNoteGate3 := inputNote.gate3
  inputNoteDigestResidual := inputNote.digestResidual
  outputNoteState1 := outputNote.state1
  outputNoteState2 := outputNote.state2
  outputNoteState3 := outputNote.state3
  outputNoteGate1 := outputNote.gate1
  outputNoteGate2 := outputNote.gate2
  outputNoteGate3 := outputNote.gate3
  outputNoteDigestResidual := outputNote.digestResidual
  inputPath := inputPath
  outputPath := outputPath

/-- The original hash/Merkle trace exists exactly when each of its six
independent residual groups exists. -/
theorem extracted_hash_merkle_nonempty_iff_components
    (rc : RoundConstants) (O : OpenedColumns) :
    Nonempty (ExtractedHashMerkleResiduals rc O) ↔
      Nonempty (ExtractedOwnerHashResiduals rc O) ∧
      Nonempty (ExtractedNullifierHashResiduals rc O) ∧
      Nonempty (ExtractedInputNoteHashResiduals rc O) ∧
      Nonempty (ExtractedOutputNoteHashResiduals rc O) ∧
      Nonempty (ExtractedMerklePath rc O.L_in O.A O.bits O.sib) ∧
      Nonempty (ExtractedMerklePath rc O.C_out O.A' O.bits O.sib) := by
  constructor
  · rintro ⟨raw⟩
    exact ⟨⟨ownerComponent raw⟩, ⟨nullifierComponent raw⟩,
      ⟨inputNoteComponent raw⟩, ⟨outputNoteComponent raw⟩,
      ⟨raw.inputPath⟩, ⟨raw.outputPath⟩⟩
  · rintro ⟨⟨owner⟩, ⟨nullifier⟩, ⟨inputNote⟩, ⟨outputNote⟩,
      ⟨inputPath⟩, ⟨outputPath⟩⟩
    exact ⟨ofHashMerkleComponents owner nullifier
      inputNote outputNote inputPath outputPath⟩

/-! ## Exact six-way accepted-candidate failure split -/

def HashMerkleResidualPrefix
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K)
    (statement : V5PublicStatement)
    (record : CandidateSemanticRecord K) : Prop :=
  CandidateScalarClaimsMatch execution challenges ∧
    record.fourClaimDiscrepancy = 0 ∧
    record.lanes.combined = execution.initialValues ∧
    OpenedColumnsMatchStatement statement record.opened ∧
    ExtractedArithmeticResiduals record.opened

def OwnerHashResidualFailure
    (rc : RoundConstants)
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K)
    (statement : V5PublicStatement)
    (record : CandidateSemanticRecord K) : Prop :=
  HashMerkleResidualPrefix execution challenges statement record ∧
    ¬ Nonempty (ExtractedOwnerHashResiduals rc record.opened)

def NullifierHashResidualFailure
    (rc : RoundConstants)
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K)
    (statement : V5PublicStatement)
    (record : CandidateSemanticRecord K) : Prop :=
  HashMerkleResidualPrefix execution challenges statement record ∧
    ¬ Nonempty (ExtractedNullifierHashResiduals rc record.opened)

def InputNoteHashResidualFailure
    (rc : RoundConstants)
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K)
    (statement : V5PublicStatement)
    (record : CandidateSemanticRecord K) : Prop :=
  HashMerkleResidualPrefix execution challenges statement record ∧
    ¬ Nonempty (ExtractedInputNoteHashResiduals rc record.opened)

def OutputNoteHashResidualFailure
    (rc : RoundConstants)
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K)
    (statement : V5PublicStatement)
    (record : CandidateSemanticRecord K) : Prop :=
  HashMerkleResidualPrefix execution challenges statement record ∧
    ¬ Nonempty (ExtractedOutputNoteHashResiduals rc record.opened)

def InputPathResidualFailure
    (rc : RoundConstants)
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K)
    (statement : V5PublicStatement)
    (record : CandidateSemanticRecord K) : Prop :=
  HashMerkleResidualPrefix execution challenges statement record ∧
    ¬ Nonempty (ExtractedMerklePath rc record.opened.L_in record.opened.A
      record.opened.bits record.opened.sib)

def OutputPathResidualFailure
    (rc : RoundConstants)
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K)
    (statement : V5PublicStatement)
    (record : CandidateSemanticRecord K) : Prop :=
  HashMerkleResidualPrefix execution challenges statement record ∧
    ¬ Nonempty (ExtractedMerklePath rc record.opened.C_out record.opened.A'
      record.opened.bits record.opened.sib)

/-- No residual group is hidden by the old aggregate name: its failure is
exactly the disjunction of the six component failures. -/
theorem hashMerkleResidualFailure_iff_six_components
    (rc : RoundConstants)
    (execution : AcceptedCandidateExecution K)
    (challenges : TwelveRelationChallenges K)
    (statement : V5PublicStatement)
    (record : CandidateSemanticRecord K) :
    HashMerkleResidualFailure rc execution challenges statement record ↔
      OwnerHashResidualFailure rc execution challenges statement record ∨
      NullifierHashResidualFailure rc execution challenges statement record ∨
      InputNoteHashResidualFailure rc execution challenges statement record ∨
      OutputNoteHashResidualFailure rc execution challenges statement record ∨
      InputPathResidualFailure rc execution challenges statement record ∨
      OutputPathResidualFailure rc execution challenges statement record := by
  rw [HashMerkleResidualFailure]
  constructor
  · rintro ⟨hmatch, hfour, hlanes, hstatement, harithmetic, missing⟩
    have hpfx :
        HashMerkleResidualPrefix execution challenges statement record :=
      ⟨hmatch, hfour, hlanes, hstatement, harithmetic⟩
    classical
    by_cases owner : Nonempty (ExtractedOwnerHashResiduals rc record.opened)
    · by_cases nullifier :
          Nonempty (ExtractedNullifierHashResiduals rc record.opened)
      · by_cases inputNote :
            Nonempty (ExtractedInputNoteHashResiduals rc record.opened)
        · by_cases outputNote :
              Nonempty (ExtractedOutputNoteHashResiduals rc record.opened)
          · by_cases inputPath : Nonempty (ExtractedMerklePath rc
                record.opened.L_in record.opened.A record.opened.bits
                record.opened.sib)
            · by_cases outputPath : Nonempty (ExtractedMerklePath rc
                  record.opened.C_out record.opened.A' record.opened.bits
                  record.opened.sib)
              · exact False.elim (missing
                  ((extracted_hash_merkle_nonempty_iff_components rc
                    record.opened).mpr
                    ⟨owner, nullifier, inputNote, outputNote, inputPath,
                      outputPath⟩))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                  ⟨hpfx, outputPath⟩))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                ⟨hpfx, inputPath⟩))))
          · exact Or.inr (Or.inr (Or.inr (Or.inl
              ⟨hpfx, outputNote⟩)))
        · exact Or.inr (Or.inr (Or.inl ⟨hpfx, inputNote⟩))
      · exact Or.inr (Or.inl ⟨hpfx, nullifier⟩)
    · exact Or.inl ⟨hpfx, owner⟩
  · intro failure
    rcases failure with owner | nullifier | inputNote | outputNote |
        inputPath | outputPath
    · rcases owner.1 with ⟨hmatch, hfour, hlanes, hstatement, harithmetic⟩
      exact ⟨hmatch, hfour, hlanes, hstatement, harithmetic,
        fun ⟨full⟩ => owner.2 ⟨ownerComponent full⟩⟩
    · rcases nullifier.1 with
        ⟨hmatch, hfour, hlanes, hstatement, harithmetic⟩
      exact ⟨hmatch, hfour, hlanes, hstatement, harithmetic,
        fun ⟨full⟩ => nullifier.2 ⟨nullifierComponent full⟩⟩
    · rcases inputNote.1 with
        ⟨hmatch, hfour, hlanes, hstatement, harithmetic⟩
      exact ⟨hmatch, hfour, hlanes, hstatement, harithmetic,
        fun ⟨full⟩ => inputNote.2 ⟨inputNoteComponent full⟩⟩
    · rcases outputNote.1 with
        ⟨hmatch, hfour, hlanes, hstatement, harithmetic⟩
      exact ⟨hmatch, hfour, hlanes, hstatement, harithmetic,
        fun ⟨full⟩ => outputNote.2 ⟨outputNoteComponent full⟩⟩
    · rcases inputPath.1 with
        ⟨hmatch, hfour, hlanes, hstatement, harithmetic⟩
      exact ⟨hmatch, hfour, hlanes, hstatement, harithmetic,
        fun ⟨full⟩ => inputPath.2 ⟨full.inputPath⟩⟩
    · rcases outputPath.1 with
        ⟨hmatch, hfour, hlanes, hstatement, harithmetic⟩
      exact ⟨hmatch, hfour, hlanes, hstatement, harithmetic,
        fun ⟨full⟩ => outputPath.2 ⟨full.outputPath⟩⟩

#print axioms extracted_hash_merkle_nonempty_iff_components
#print axioms hashMerkleResidualFailure_iff_six_components

end AspisV5HashMerkleResidualDecomposition

import AspisFormal.HashMerkleModel
import AspisFormal.V5SelectedGoodVerifierRelation

/-!
# From an extracted V5 trace to the spend relation

An accepted non-interactive proof cannot imply a witness as a matter of pure
logic.  The implication is probabilistic and depends on the soundness of the
interactive-oracle proof, Fiat--Shamir transform, and polynomial commitment.
On the event where
that soundness argument succeeds, it must produce a trace whose checked
residuals vanish.  This file states that boundary directly and proves the
deterministic part after it.

The input below is deliberately lower-level than `HashMerkleWitness`.  It is
a normalized trace reconstructed from the committed openings and the zero
residuals checked by the arithmetic, Poseidon, Merkle, and copy constraints.
It is not a literal transcription of every committed row.  In particular,
the extraction step must justify the copy substitutions, the compiled LogUp
registry, and the transition from the deployed absorption rows to the typed
hash inputs used here.  The proofs in this file:

1. turn those zero residuals into `ConstraintsSatisfied`;
2. turn the extracted Poseidon and Merkle rows into `HashMerkleWitness`;
3. use `HashMerkleModel.spend_relation_of_faithful` to obtain the complete
   spend relation.

The final accepted-run theorem has explicit premises that this file does not
manufacture:

* outside a concrete soundness-failure event that must be defined and bounded,
  accepted V5
  verification extracts the trace below with the exact spend statement; and
* the deployed Poseidon2 constants and framing equal the Lean model
  (`Poseidon2Faithful`).

That first premise must cover the polynomial commitment and FRI extraction,
Fiat--Shamir transcript argument, every zero-denominator and challenge
collision event, compiled copy/LogUp topology, byte decoding and live-state
bindings, and the Rust-to-trace correspondence.  The public pool, sequence,
and deployment-domain values bind the transcript but are outside the
mathematical `SpendRelation`; the eventual Rust theorem must carry them as
part of the run statement as well.  It must also bind the runtime program id
and account identities, including the pool and nullifier account, and prove
how the deployment domain is derived from that program id.  It would be
incorrect to replace this premise by acceptance alone.
-/

namespace AspisV5AcceptedSpendRelation

open AspisFormal.ArithmetizationCore
open AspisFormal.HashMerkleModel

/-! ## Extracted arithmetic residuals -/

/-- The arithmetic residual equations for the opened V5 trace.  These are
written as `left - right = 0`, matching the form evaluated by the constraint
code, instead of assuming `ConstraintsSatisfied`. -/
structure ExtractedArithmeticResiduals (O : OpenedColumns) : Prop where
  rangeInBit : ∀ j k, O.rin.bit j k * (O.rin.bit j k - 1) = 0
  rangeInLimb : ∀ j,
    O.rin.limb j - (∑ k : Fin 10, O.rin.bit j k * (2 : F) ^ (k : Nat)) = 0
  rangeInValue :
    O.rin.value - (∑ j : Fin 3, O.rin.limb j * (2 : F) ^ (10 * (j : Nat))) = 0
  rangeOutBit : ∀ j k, O.rout.bit j k * (O.rout.bit j k - 1) = 0
  rangeOutLimb : ∀ j,
    O.rout.limb j - (∑ k : Fin 10, O.rout.bit j k * (2 : F) ^ (k : Nat)) = 0
  rangeOutValue :
    O.rout.value - (∑ j : Fin 3, O.rout.limb j * (2 : F) ^ (10 * (j : Nat))) = 0
  balance : O.rin.value - (O.rout.value + (O.f : F)) = 0
  asset : O.a_in - O.a = 0

/-- Vanishing extracted arithmetic residuals give the maintained arithmetic
constraint record. -/
theorem ExtractedArithmeticResiduals.toConstraintsSatisfied
    {O : OpenedColumns} (h : ExtractedArithmeticResiduals O) :
    ConstraintsSatisfied O where
  rangeIn := {
    bitness := h.rangeInBit
    limbRecon := fun j => sub_eq_zero.mp (h.rangeInLimb j)
    valueRecon := sub_eq_zero.mp h.rangeInValue
  }
  rangeOut := {
    bitness := h.rangeOutBit
    limbRecon := fun j => sub_eq_zero.mp (h.rangeOutLimb j)
    valueRecon := sub_eq_zero.mp h.rangeOutValue
  }
  balance := sub_eq_zero.mp h.balance
  assetIn := sub_eq_zero.mp h.asset

/-! ## Poseidon rows -/

/-- The twelve states committed for one deployed permutation block.  Each of
the eleven checked transitions applies two rounds; the intermediate state is
not committed. -/
structure TwoRoundPermutationRows
    (rc : RoundConstants) (input output : State) where
  row : Nat → State
  startResidual : row 0 - input = 0
  pairResidual : ∀ pair, pair < 11 →
    row (pair + 1) -
      gateStep rc (2 * pair + 1) (gateStep rc (2 * pair) (row pair)) = 0
  finishResidual : row 11 - output = 0

/-! The deployed two-round rows imply the twenty-two single-round chain used
by the mathematical Poseidon model.  The missing intermediate states are
synthesized by `runUpto`; they are not extra witness assumptions. -/
def TwoRoundPermutationRows.toRoundChain
    {rc : RoundConstants} {input output : State}
    (gate : TwoRoundPermutationRows rc input output) :
    RoundChain rc input output := by
  have rowsAgree : ∀ pair, pair ≤ 11 →
      gate.row pair = runUpto (gateStep rc) (2 * pair) input := by
    intro pair hpair
    induction pair with
    | zero =>
        simpa [runUpto] using sub_eq_zero.mp gate.startResidual
    | succ previous inductionHypothesis =>
        have hprevious : previous < 11 := by omega
        have hinduction := inductionHypothesis (by omega)
        have hpairStep := sub_eq_zero.mp (gate.pairResidual previous hprevious)
        rw [hpairStep, hinduction]
        have hindex : 2 * (previous + 1) = 2 * previous + 2 := by omega
        rw [hindex, runUpto, runUpto]
  refine {
    y := fun round => runUpto (gateStep rc) round input
    start := by simp [runUpto]
    chain := ?_
    finish := ?_
  }
  · intro round _
    rw [runUpto]
  · have hrow := rowsAgree 11 (by omega)
    have hfinish := sub_eq_zero.mp gate.finishResidual
    norm_num at hrow
    exact hrow.symm.trans hfinish

/-! ## Extracted Merkle data -/

/-- One normalized Merkle level: the path bit copy, both child-selection
residuals, the node permutation rows, and the copy into the next running
digest.  The deployed evaluator reaches the node input through a committed
row-zero value and its absorption lane; the missing extraction theorem must
prove that those rows equal the `nodeState` expression used here. -/
structure ExtractedMerkleLevel
    (rc : RoundConstants) (direction : Bool)
    (current sibling next : Digest) where
  bit : F
  bitCopyResidual : bit - (if direction then 1 else 0) = 0
  left : Digest
  right : Digest
  leftResidual : ∀ lane,
    left lane - (current lane + bit * (sibling lane - current lane)) = 0
  rightResidual : ∀ lane,
    right lane - (sibling lane + bit * (current lane - sibling lane)) = 0
  parentState : State
  nodeGate : TwoRoundPermutationRows rc
    (nodeState NODE_TWEAK left right) parentState
  nextResidual : next - truncate8 parentState = 0

def ExtractedMerkleLevel.toMerkleLevelData
    {rc : RoundConstants} {direction : Bool}
    {current sibling next : Digest}
    (level : ExtractedMerkleLevel rc direction current sibling next) :
    MerkleLevelData rc direction current sibling next where
  b := level.bit
  hbit := sub_eq_zero.mp level.bitCopyResidual
  left := level.left
  right := level.right
  hsel_l := fun lane => sub_eq_zero.mp (level.leftResidual lane)
  hsel_r := fun lane => sub_eq_zero.mp (level.rightResidual lane)
  parentState := level.parentState
  hnode := level.nodeGate.toRoundChain
  hnext := sub_eq_zero.mp level.nextResidual

/-- Twenty extracted Merkle levels sharing the path bits and siblings already
held in `OpenedColumns`.  Establishing that sharing from the deployed trace is
part of the compiled copy/LogUp extraction obligation. -/
structure ExtractedMerklePath
    (rc : RoundConstants) (leaf root : Digest)
    (bits : Fin 20 → Bool) (siblings : Fin 20 → Digest) where
  current : Nat → Digest
  startResidual : current 0 - leaf = 0
  finishResidual : current 20 - root = 0
  level : ∀ index : Fin 20,
    ExtractedMerkleLevel rc (bits index) (current index) (siblings index)
      (current (index + 1))

def ExtractedMerklePath.toMerklePathWitness
    {rc : RoundConstants} {leaf root : Digest}
    {bits : Fin 20 → Bool} {siblings : Fin 20 → Digest}
    (path : ExtractedMerklePath rc leaf root bits siblings) :
    MerklePathWitness rc leaf root bits siblings where
  current := path.current
  h0 := sub_eq_zero.mp path.startResidual
  hlast := sub_eq_zero.mp path.finishResidual
  level := fun index => (path.level index).toMerkleLevelData

/-! ## All extracted hash and Merkle residuals -/

/-- A normalized view of the gate rows for the four typed hashes and both
Merkle paths used by the spend relation.  Digest equalities are represented as
zero copy residuals.  The deployed output-note trace has a separate asset cell
before checking it against the public asset, and each deployed node gate has a
row-zero plus absorption step before the permutation pairs.  The missing
extraction theorem must prove those substitutions; they are not assumed away
by calling this structure a trace. -/
structure ExtractedHashMerkleResiduals (rc : RoundConstants) (O : OpenedColumns) where
  ownerState : State
  ownerGate : TwoRoundPermutationRows rc
    (absorb (initState DOM_OWNER 8) O.k_nu) ownerState
  ownerDigestResidual : O.pk_in - truncate8 ownerState = 0

  nullState1 : State
  nullState2 : State
  nullGate1 : TwoRoundPermutationRows rc
    (absorb (initState DOM_NULLIFIER 16) O.k_nu) nullState1
  nullGate2 : TwoRoundPermutationRows rc (absorb nullState1 O.r_in) nullState2
  nullDigestResidual : O.nu - truncate8 nullState2 = 0

  inputNoteState1 : State
  inputNoteState2 : State
  inputNoteState3 : State
  inputNoteGate1 : TwoRoundPermutationRows rc
    (absorb (initState DOM_NOTE 18) O.pk_in) inputNoteState1
  inputNoteGate2 : TwoRoundPermutationRows rc
    (absorb inputNoteState1 (noteChunk1 O.rin.value O.a_in O.r_in))
    inputNoteState2
  inputNoteGate3 : TwoRoundPermutationRows rc
    (absorb inputNoteState2 (noteChunk2 O.r_in)) inputNoteState3
  inputNoteDigestResidual : O.L_in - truncate8 inputNoteState3 = 0

  outputNoteState1 : State
  outputNoteState2 : State
  outputNoteState3 : State
  outputNoteGate1 : TwoRoundPermutationRows rc
    (absorb (initState DOM_NOTE 18) O.pk_out) outputNoteState1
  outputNoteGate2 : TwoRoundPermutationRows rc
    (absorb outputNoteState1 (noteChunk1 O.rout.value O.a O.r_out))
    outputNoteState2
  outputNoteGate3 : TwoRoundPermutationRows rc
    (absorb outputNoteState2 (noteChunk2 O.r_out)) outputNoteState3
  outputNoteDigestResidual : O.C_out - truncate8 outputNoteState3 = 0

  inputPath : ExtractedMerklePath rc O.L_in O.A O.bits O.sib
  outputPath : ExtractedMerklePath rc O.C_out O.A' O.bits O.sib

/-- Extracted gate rows construct the higher-level hash/Merkle witness used by
the existing relation proof. -/
def ExtractedHashMerkleResiduals.toHashMerkleWitness
    {rc : RoundConstants} {O : OpenedColumns}
    (raw : ExtractedHashMerkleResiduals rc O) : HashMerkleWitness rc O where
  ownerState := raw.ownerState
  ownerChain := raw.ownerGate.toRoundChain
  ownerDigest := sub_eq_zero.mp raw.ownerDigestResidual
  nullState1 := raw.nullState1
  nullState2 := raw.nullState2
  nullChain1 := raw.nullGate1.toRoundChain
  nullChain2 := raw.nullGate2.toRoundChain
  nullDigest := sub_eq_zero.mp raw.nullDigestResidual
  inNote1 := raw.inputNoteState1
  inNote2 := raw.inputNoteState2
  inNote3 := raw.inputNoteState3
  inNoteChain1 := raw.inputNoteGate1.toRoundChain
  inNoteChain2 := raw.inputNoteGate2.toRoundChain
  inNoteChain3 := raw.inputNoteGate3.toRoundChain
  inNoteDigest := sub_eq_zero.mp raw.inputNoteDigestResidual
  outNote1 := raw.outputNoteState1
  outNote2 := raw.outputNoteState2
  outNote3 := raw.outputNoteState3
  outNoteChain1 := raw.outputNoteGate1.toRoundChain
  outNoteChain2 := raw.outputNoteGate2.toRoundChain
  outNoteChain3 := raw.outputNoteGate3.toRoundChain
  outNoteDigest := sub_eq_zero.mp raw.outputNoteDigestResidual
  inputPath := raw.inputPath.toMerklePathWitness
  outputPath := raw.outputPath.toMerklePathWitness

/-! ## Deterministic relation theorem -/

/-- The complete residual trace obtained on the successful soundness/extraction
event. -/
structure ExtractedV5Trace (rc : RoundConstants) (O : OpenedColumns) where
  arithmetic : ExtractedArithmeticResiduals O
  hashAndMerkle : ExtractedHashMerkleResiduals rc O

/-- Once an accepted proof has been extracted to normalized gate data, the complete
spend relation follows.  This theorem does not assume `HashMerkleWitness` or
`ConstraintsSatisfied`; both are constructed above. -/
theorem extracted_trace_implies_spend_relation
    (rc : RoundConstants) (O : OpenedColumns)
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode)
    (trace : ExtractedV5Trace rc O) :
    ∃ inputValue outputValue : Nat,
      SpendRelation deployedOwner deployedNote deployedNullifier deployedNode
        O inputValue outputValue := by
  exact spend_relation_of_faithful rc O poseidon
    trace.hashAndMerkle.toHashMerkleWitness
    trace.arithmetic.toConstraintsSatisfied

/-! ## Accepted verifier executions -/

/-- The public statement passed to the V5 verifier after Rust has decoded the
wire bytes and checked that digest and asset encodings are field elements.
`feeBound` is the check performed before statement hashing.  Pool, sequence,
and deployment domain are included because they are bound into that hash even
though the mathematical `SpendRelation` concerns the six spend fields. -/
structure V5PublicStatement where
  pool : Fin 32 → UInt8
  sequence : Nat
  sequenceBound : sequence < 2 ^ 64
  currentAnchor : Digest
  nullifier : Digest
  outputCommitment : Digest
  outputAnchor : Digest
  asset : F
  fee : Nat
  feeBound : fee < 2 ^ 30
  deploymentDomain : Fin 32 → UInt8

/-- The relation openings use exactly the six public spend fields accepted by
the Rust verifier.  This concrete predicate prevents the theorem from being
instantiated with an uninformative matching predicate such as `True`. -/
structure OpenedColumnsMatchStatement
    (statement : V5PublicStatement) (opened : OpenedColumns) : Prop where
  currentAnchor : opened.A = statement.currentAnchor
  nullifier : opened.nu = statement.nullifier
  outputCommitment : opened.C_out = statement.outputCommitment
  outputAnchor : opened.A' = statement.outputAnchor
  asset : opened.a = statement.asset
  fee : opened.f = statement.fee

/-- The exact statement has a witness for the complete private-spend
relation.  The run itself is not needed in the conclusion: it supplies the
proof from which these existential values are extracted. -/
def StatementHasSpendWitness
    (statement : V5PublicStatement)
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (deployedNullifier : Digest → Digest → Digest)
    (deployedNode : Digest → Digest → Digest) : Prop :=
  ∃ opened inputValue outputValue,
    OpenedColumnsMatchStatement statement opened ∧
      SpendRelation deployedOwner deployedNote deployedNullifier deployedNode
        opened inputValue outputValue

/-- The missing extraction theorem, stated without hiding its failure event.
For an exact public statement and accepted run, it must reconstruct the
normalized trace whenever the soundness-failure event did not occur.

This remains a parameterized proof obligation, not a theorem about the Rust
verifier.  Its concrete instantiation must prove the deterministic parts:
copy/LogUp sharing and registry layout, transcript restoration, and the
byte/parser/live-account mapping to `V5PublicStatement`.  It must also define
`badEvent` as the concrete union of polynomial-commitment and FRI failures,
Fiat--Shamir failures, tuple-compression collisions, and zero-denominator
events, then bound that union separately.  Choosing `badEvent := True` would
make the schema vacuous and would establish no security claim. -/
def AcceptedRunExtractsTrace
    {Run : Type*}
    (accepts : V5PublicStatement → Run → Prop)
    (badEvent : V5PublicStatement → Run → Prop)
    (rc : RoundConstants) : Prop :=
  ∀ statement run, accepts statement run → ¬ badEvent statement run →
    ∃ opened,
      OpenedColumnsMatchStatement statement opened ∧
        Nonempty (ExtractedV5Trace rc opened)

/-- Honest acceptance-to-relation composition currently available.  An
accepted run either has a complete spend witness for the exact statement or
lies in the caller's soundness-failure event.  This is a proof schema until
`accepts`, `badEvent`, and `extraction` are instantiated for the deployed Rust
and the event receives a probability bound. -/
theorem accepted_run_implies_spend_relation_or_bad_event
    {Run : Type*}
    (accepts : V5PublicStatement → Run → Prop)
    (badEvent : V5PublicStatement → Run → Prop)
    (rc : RoundConstants)
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode)
    (extraction : AcceptedRunExtractsTrace accepts badEvent rc)
    (statement : V5PublicStatement) (run : Run)
    (accepted : accepts statement run) :
    StatementHasSpendWitness statement deployedOwner deployedNote
        deployedNullifier deployedNode ∨
      badEvent statement run := by
  by_cases hbad : badEvent statement run
  · exact Or.inr hbad
  · obtain ⟨opened, hpublic, ⟨trace⟩⟩ :=
      extraction statement run accepted hbad
    obtain ⟨inputValue, outputValue, relation⟩ :=
      extracted_trace_implies_spend_relation rc opened poseidon trace
    exact Or.inl ⟨opened, inputValue, outputValue, hpublic, relation⟩

/-- On a run for which the soundness-failure event did not occur, acceptance
gives the complete spend relation.  A separate probability theorem must bound
how often `badEvent` can occur. -/
theorem accepted_run_outside_bad_event_implies_spend_relation
    {Run : Type*}
    (accepts : V5PublicStatement → Run → Prop)
    (badEvent : V5PublicStatement → Run → Prop)
    (rc : RoundConstants)
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode)
    (extraction : AcceptedRunExtractsTrace accepts badEvent rc)
    (statement : V5PublicStatement) (run : Run)
    (accepted : accepts statement run)
    (notBad : ¬ badEvent statement run) :
    StatementHasSpendWitness statement deployedOwner deployedNote
      deployedNullifier deployedNode := by
  obtain ⟨opened, hpublic, ⟨trace⟩⟩ :=
    extraction statement run accepted notBad
  obtain ⟨inputValue, outputValue, relation⟩ :=
    extracted_trace_implies_spend_relation rc opened poseidon trace
  exact ⟨opened, inputValue, outputValue, hpublic, relation⟩

/-- False acceptance is contained in the same event that a later probability
proof must bound.  This is the direct glue shape needed for a soundness bound;
no probability theory is hidden in this deterministic file. -/
theorem false_accept_implies_bad_event
    {Run : Type*}
    (accepts : V5PublicStatement → Run → Prop)
    (badEvent : V5PublicStatement → Run → Prop)
    (rc : RoundConstants)
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode)
    (extraction : AcceptedRunExtractsTrace accepts badEvent rc)
    (statement : V5PublicStatement) (run : Run)
    (accepted : accepts statement run)
    (noWitness : ¬ StatementHasSpendWitness statement deployedOwner
      deployedNote deployedNullifier deployedNode) :
    badEvent statement run := by
  rcases accepted_run_implies_spend_relation_or_bad_event accepts badEvent rc
      poseidon extraction statement run accepted with witness | bad
  · exact False.elim (noWitness witness)
  · exact bad

/-- For a fixed public statement, the set of verifier runs that accept even
though the statement has no spend witness is contained in `badEvent`. -/
theorem false_accept_event_subset_bad_event
    {Run : Type*}
    (accepts : V5PublicStatement → Run → Prop)
    (badEvent : V5PublicStatement → Run → Prop)
    (rc : RoundConstants)
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode)
    (extraction : AcceptedRunExtractsTrace accepts badEvent rc)
    (statement : V5PublicStatement) :
    {run | accepts statement run ∧
      ¬ StatementHasSpendWitness statement deployedOwner deployedNote
        deployedNullifier deployedNode} ⊆
      {run | badEvent statement run} := by
  intro run falseAccept
  exact false_accept_implies_bad_event accepts badEvent rc poseidon extraction
    statement run falseAccept.1 falseAccept.2

/-- Measure form of `false_accept_event_subset_bad_event`.  If `μ` is a
probability distribution over verifier runs, the false-acceptance probability
is at most the probability assigned to the caller's concrete `badEvent`.
This theorem supplies no numerical bound on that event. -/
theorem false_accept_measure_le_bad_event
    {Run : Type*} [MeasurableSpace Run]
    (measure : MeasureTheory.Measure Run)
    (accepts : V5PublicStatement → Run → Prop)
    (badEvent : V5PublicStatement → Run → Prop)
    (rc : RoundConstants)
    {deployedOwner : Digest → Digest}
    {deployedNote : Digest → F → F → Digest → Digest}
    {deployedNullifier : Digest → Digest → Digest}
    {deployedNode : Digest → Digest → Digest}
    (poseidon : Poseidon2Faithful rc deployedOwner deployedNote
      deployedNullifier deployedNode)
    (extraction : AcceptedRunExtractsTrace accepts badEvent rc)
    (statement : V5PublicStatement) :
    measure {run | accepts statement run ∧
      ¬ StatementHasSpendWitness statement deployedOwner deployedNote
        deployedNullifier deployedNode} ≤
      measure {run | badEvent statement run} :=
  MeasureTheory.measure_mono
    (false_accept_event_subset_bad_event accepts badEvent rc poseidon extraction
      statement)

/-! ## Regression: the selected-schedule check is not full proof acceptance -/

private def invalidRange : RangeWitness where
  bit := fun _ _ => 2
  limb := fun _ => 0
  value := 0

private def zeroDigest : Digest := fun _ => 0

private def invalidOpenedColumns : OpenedColumns where
  rin := invalidRange
  rout := invalidRange
  k_nu := zeroDigest
  r_in := zeroDigest
  r_out := zeroDigest
  pk_out := zeroDigest
  pk_in := zeroDigest
  L_in := zeroDigest
  nu := zeroDigest
  C_out := zeroDigest
  A := zeroDigest
  A' := zeroDigest
  a_in := 0
  a := 0
  bits := fun _ => false
  sib := fun _ => zeroDigest
  f := 0
  hf := by norm_num

theorem invalid_opened_columns_do_not_satisfy_constraints :
    ¬ ConstraintsSatisfied invalidOpenedColumns := by
  intro constraints
  have bad := constraints.rangeIn.bitness (0 : Fin 3) (0 : Fin 10)
  have badProduct : (2 : F) * ((2 : F) - 1) = 0 := by
    simpa [invalidOpenedColumns, invalidRange] using bad
  have twoNeZero : (2 : F) ≠ 0 := by
    have h : ((2 : Nat) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      decide
    simpa using h
  have oneNeZero : (2 : F) - 1 ≠ 0 := by
    have twoMinusOne : (2 : F) - 1 = 1 := by ring
    rw [twoMinusOne]
    exact one_ne_zero
  exact (mul_ne_zero twoNeZero oneNeZero) badProduct

/-- `verifierAccepts` in `V5SelectedGoodVerifierRelation` checks only the
selected public schedule.  This concrete example prevents that local helper
from ever being cited as acceptance of the complete proof. -/
theorem selected_schedule_acceptance_does_not_imply_trace_constraints :
    ∃ (good : Unit → Bool) (schedules : Fin 3 → Unit) (selected : Fin 3),
      AspisV5SelectedGoodVerifierRelation.verifierAccepts
          good schedules selected ∧
        ¬ ConstraintsSatisfied invalidOpenedColumns := by
  exact ⟨fun _ => true, fun _ => (), 0, rfl,
    invalid_opened_columns_do_not_satisfy_constraints⟩

#print axioms ExtractedArithmeticResiduals.toConstraintsSatisfied
#print axioms TwoRoundPermutationRows.toRoundChain
#print axioms ExtractedMerkleLevel.toMerkleLevelData
#print axioms ExtractedMerklePath.toMerklePathWitness
#print axioms ExtractedHashMerkleResiduals.toHashMerkleWitness
#print axioms extracted_trace_implies_spend_relation
#print axioms accepted_run_implies_spend_relation_or_bad_event
#print axioms accepted_run_outside_bad_event_implies_spend_relation
#print axioms false_accept_implies_bad_event
#print axioms false_accept_event_subset_bad_event
#print axioms false_accept_measure_le_bad_event
#print axioms invalid_opened_columns_do_not_satisfy_constraints
#print axioms selected_schedule_acceptance_does_not_imply_trace_constraints

end AspisV5AcceptedSpendRelation

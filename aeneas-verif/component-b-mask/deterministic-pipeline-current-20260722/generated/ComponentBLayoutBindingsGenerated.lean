-- MECHANICALLY NORMALIZED FROM LayoutFullV3.lean (source-authentic Aeneas output).
-- Duplicate field/type declarations are supplied by ComponentBMaintainedTerminalBridge.
import ComponentBMaintainedTerminalBridge
import InactiveTableU32
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
noncomputable section

namespace ComponentBGenerated
/-- [aspis_core::circle::CirclePointError]
    Source: 'crates/aspis-core/src/circle.rs', lines 18:0-18:25
    Name pattern: [aspis_core::circle::CirclePointError]
    Visibility: public -/
@[discriminant isize, rust_type "aspis_core::circle::CirclePointError"]
inductive aspis_core.circle.CirclePointError where
| SingularParameter : aspis_core.circle.CirclePointError
| ParameterInCm31Subfield : aspis_core.circle.CirclePointError

/-- [aspis_core::circle_fri::FoldDenominator]
    Source: 'crates/aspis-core/src/circle_fri.rs', lines 185:0-185:24
    Name pattern: [aspis_core::circle_fri::FoldDenominator]
    Visibility: public -/
@[discriminant isize, rust_type "aspis_core::circle_fri::FoldDenominator"]
inductive aspis_core.circle_fri.FoldDenominator where
| CircleY : aspis_core.circle_fri.FoldDenominator
| CircleX : aspis_core.circle_fri.FoldDenominator
| LineFirstPairX : aspis_core.circle_fri.FoldDenominator
| LineSecondPairX : aspis_core.circle_fri.FoldDenominator
| LineSecondFoldX : aspis_core.circle_fri.FoldDenominator

/-- [aspis_core::circle_fri::CircleFriError]
    Source: 'crates/aspis-core/src/circle_fri.rs', lines 194:0-194:23
    Name pattern: [aspis_core::circle_fri::CircleFriError]
    Visibility: public -/
@[discriminant isize, rust_type "aspis_core::circle_fri::CircleFriError"]
inductive aspis_core.circle_fri.CircleFriError where
| CircleIndexOutOfRange : aspis_core.circle_fri.CircleFriError
| CircleFiberOutOfRange : aspis_core.circle_fri.CircleFriError
| InvalidLineLayer : aspis_core.circle_fri.CircleFriError
| InvalidLineFoldLayer : aspis_core.circle_fri.CircleFriError
| LineIndexOutOfRange : aspis_core.circle_fri.CircleFriError
| LineFiberOutOfRange : aspis_core.circle_fri.CircleFriError
| QueryOutOfRange : aspis_core.circle_fri.CircleFriError
| InvalidBitReverseLength : aspis_core.circle_fri.CircleFriError
| BitReverseIndexOutOfRange : aspis_core.circle_fri.CircleFriError
| ZeroDenominator :
  aspis_core.circle_fri.FoldDenominator →
  aspis_core.circle_fri.CircleFriError
| InvalidInverseBackend : aspis_core.circle_fri.CircleFriError

/-- [aspis_core::circle_line_merkle::CircleLineMerkleError]
    Source: 'crates/aspis-core/src/circle_line_merkle.rs', lines 58:0-58:30
    Name pattern: [aspis_core::circle_line_merkle::CircleLineMerkleError]
    Visibility: public -/
@[discriminant isize, rust_type
  "aspis_core::circle_line_merkle::CircleLineMerkleError"]
inductive aspis_core.circle_line_merkle.CircleLineMerkleError where
| EmptyQueries : aspis_core.circle_line_merkle.CircleLineMerkleError
| QueryOutOfRange :
  Std.U32 →
  aspis_core.circle_line_merkle.CircleLineMerkleError
| CountMismatch :
  Std.U8 →
  Std.Usize →
  Std.Usize →
  aspis_core.circle_line_merkle.CircleLineMerkleError
| UnexpectedEnd :
  Std.U8 →
  Std.Usize →
  Std.Usize →
  aspis_core.circle_line_merkle.CircleLineMerkleError
| TrailingBytes :
  Std.Usize →
  Std.Usize →
  aspis_core.circle_line_merkle.CircleLineMerkleError
| LengthOverflow : aspis_core.circle_line_merkle.CircleLineMerkleError
| NonCanonicalLeaf :
  Std.U8 →
  Std.Usize →
  Std.Usize →
  aspis_core.circle_line_merkle.CircleLineMerkleError
| MerkleMismatch :
  Std.U8 →
  aspis_core.circle_line_merkle.CircleLineMerkleError
| PrefixRootMissing :
  Std.U8 →
  aspis_core.circle_line_merkle.CircleLineMerkleError
| InvalidLayer : Std.U8 → aspis_core.circle_line_merkle.CircleLineMerkleError
| QueryNotOpened :
  Std.U32 →
  aspis_core.circle_line_merkle.CircleLineMerkleError
| LeafIndexNotFound :
  Std.U8 →
  Std.U32 →
  aspis_core.circle_line_merkle.CircleLineMerkleError
/-- [aspis_core::field::{impl core::clone::Clone for aspis_core::field::QM31}::clone]:
    Source: 'crates/aspis-core/src/field.rs', lines 351:9-351:14
    Name pattern: [aspis_core::field::{core::clone::Clone<aspis_core::field::QM31>}::clone]
    Visibility: public -/
@[rust_fun
  "aspis_core::field::{core::clone::Clone<aspis_core::field::QM31>}::clone"]
def aspis_core.field.QM31.Insts.CoreCloneClone.clone
  (self : aspis_core.field.QM31) : Result aspis_core.field.QM31 := do
  ok self

/-- Trait implementation: [aspis_core::field::{impl core::clone::Clone for aspis_core::field::QM31}]
    Source: 'crates/aspis-core/src/field.rs', lines 351:9-351:14
    Name pattern: [core::clone::Clone<aspis_core::field::QM31>] -/
@[reducible, rust_trait_impl "core::clone::Clone<aspis_core::field::QM31>"]
def aspis_core.field.QM31.Insts.CoreCloneClone : core.clone.Clone
  aspis_core.field.QM31 := {
  clone := aspis_core.field.QM31.Insts.CoreCloneClone.clone
}

/-- [aspis_core::field::{aspis_core::field::QM31}::ONE]
    Source: 'crates/aspis-core/src/field.rs', lines 725:4-725:23
    Name pattern: [aspis_core::field::{aspis_core::field::QM31}::ONE]
    Visibility: public -/
@[global_simps, irreducible, rust_const
  "aspis_core::field::{aspis_core::field::QM31}::ONE"]
def aspis_core.field.QM31.ONE : aspis_core.field.QM31 :=
  { c0 := { a := 1#u32, b := 0#u32 }, c1 := { a := 0#u32, b := 0#u32 } }
/-- [aspis_core::state_only_private_openings::StateOnlyPrivateOpeningError]
    Source: 'crates/aspis-core/src/state_only_private_openings.rs', lines 21:0-21:37
    Name pattern: [aspis_core::state_only_private_openings::StateOnlyPrivateOpeningError]
    Visibility: public -/
@[discriminant isize, rust_type
  "aspis_core::state_only_private_openings::StateOnlyPrivateOpeningError"]
inductive aspis_core.state_only_private_openings.StateOnlyPrivateOpeningError
  where
| EmptyOpening :
  aspis_core.state_only_private_openings.StateOnlyPrivateOpeningError
| InvalidDepth :
  Std.U32 →
  aspis_core.state_only_private_openings.StateOnlyPrivateOpeningError
| InvalidValueWidth :
  Std.Usize →
  aspis_core.state_only_private_openings.StateOnlyPrivateOpeningError
| CountOutOfRange :
  Std.Usize →
  aspis_core.state_only_private_openings.StateOnlyPrivateOpeningError
| CountMismatch :
  Std.Usize →
  Std.Usize →
  aspis_core.state_only_private_openings.StateOnlyPrivateOpeningError
| IndicesNotStrictlyIncreasing :
  aspis_core.state_only_private_openings.StateOnlyPrivateOpeningError
| LeafIndexOutOfRange :
  Std.U32 →
  aspis_core.state_only_private_openings.StateOnlyPrivateOpeningError
| UnexpectedEnd :
  Std.Usize →
  Std.Usize →
  aspis_core.state_only_private_openings.StateOnlyPrivateOpeningError
| LengthOverflow :
  aspis_core.state_only_private_openings.StateOnlyPrivateOpeningError
| MerkleMismatch :
  aspis_core.state_only_private_openings.StateOnlyPrivateOpeningError
| TrailingBytes :
  Std.Usize →
  Std.Usize →
  aspis_core.state_only_private_openings.StateOnlyPrivateOpeningError

/-- [aspis_statement::atomic_state_only_registry::AtomicStateOnlyRegistryErrorV3]
    Source: 'crates/aspis-statement/src/atomic_state_only_registry.rs', lines 148:0-148:39
    Name pattern: [aspis_statement::atomic_state_only_registry::AtomicStateOnlyRegistryErrorV3]
    Visibility: public -/
@[discriminant isize, rust_type
  "aspis_statement::atomic_state_only_registry::AtomicStateOnlyRegistryErrorV3"]
inductive aspis_statement.atomic_state_only_registry.AtomicStateOnlyRegistryErrorV3
  where
| Layout :
  aspis_statement.atomic_state_only_registry.AtomicStateOnlyRegistryErrorV3
| AuxRowMismatch :
  Std.U8 →
  aspis_statement.atomic_state_only_registry.AtomicStateOnlyRegistryErrorV3
| NonRowLocalTuple :
  Std.U16 →
  aspis_statement.atomic_state_only_registry.AtomicStateOnlyRegistryErrorV3
| EndpointCapacity :
  Std.U16 →
  aspis_statement.atomic_state_only_registry.AtomicStateOnlyRegistryErrorV3
| CopyImbalance :
  aspis_statement.atomic_state_only_registry.AtomicStateOnlyRegistryErrorV3
| PublicRootMismatch :
  aspis_statement.atomic_state_only_registry.AtomicStateOnlyRegistryErrorV3

/-- [aspis_statement::atomic_state_only_terminal::constants::COMPILED_ATOMIC_COPY_ACTIVE_ROWS]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal_constants.rs', lines 6:0-6:61
    Name pattern: [aspis_statement::atomic_state_only_terminal::constants::COMPILED_ATOMIC_COPY_ACTIVE_ROWS] -/
@[rust_const
  "aspis_statement::atomic_state_only_terminal::constants::COMPILED_ATOMIC_COPY_ACTIVE_ROWS"]
def
  aspis_statement.atomic_state_only_terminal.constants.COMPILED_ATOMIC_COPY_ACTIVE_ROWS
  : Result (Array Std.U16 210#usize) :=
  ok
    _root_.aspis_statement.atomic_state_only_terminal.constants.COMPILED_ATOMIC_COPY_ACTIVE_ROWS

/-- [aspis_statement::atomic_state_only_terminal::atomic_state_only_copy_inactive_row_masks_v3]: loop body 0:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 133:4-138:5
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_state_only_copy_inactive_row_masks_v3]
    Visibility: public -/
@[rust_loop_body, rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_state_only_copy_inactive_row_masks_v3"]
def
  aspis_statement.atomic_state_only_terminal.atomic_state_only_copy_inactive_row_masks_v3_loop.body
  (iter : core.slice.iter.Iter Std.U16) (masks : Array Std.U16 64#usize) :
  Result (ControlFlow ((core.slice.iter.Iter Std.U16) × (Array Std.U16
    64#usize)) (Array Std.U16 64#usize))
  := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none => ok (done masks)
  | some row =>
    let row1 ← lift (core.convert.num.FromUsizeU16.from row)
    let i ← lift (row1 &&& 15#usize)
    let low ← lift (UScalar.cast .U32 i)
    let word ← lift (Std.Usize.wrapping_shr row1 4#u32)
    let i1 ← lift (Std.U16.wrapping_shl 1#u16 low)
    let i2 ← lift (~~~ i1)
    let i3 ← Array.index_usize masks word
    let i4 ← lift (i3 &&& i2)
    let a ← Array.update masks word i4
    ok (cont (iter1, a))

/-- [aspis_statement::atomic_state_only_terminal::atomic_state_only_copy_inactive_row_masks_v3]: loop 0:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 133:4-138:5
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_state_only_copy_inactive_row_masks_v3]
    Visibility: public -/
@[rust_loop, rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_state_only_copy_inactive_row_masks_v3"]
def
  aspis_statement.atomic_state_only_terminal.atomic_state_only_copy_inactive_row_masks_v3_loop
  (iter : core.slice.iter.Iter Std.U16) (masks : Array Std.U16 64#usize) :
  Result (Array Std.U16 64#usize)
  := do
  loop
    (fun (iter1, masks1) =>
      aspis_statement.atomic_state_only_terminal.atomic_state_only_copy_inactive_row_masks_v3_loop.body
      iter1 masks1)
    (iter, masks)

/-- [aspis_statement::atomic_state_only_terminal::atomic_state_only_copy_inactive_row_masks_v3]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 131:0-131:66
    Name pattern: [aspis_statement::atomic_state_only_terminal::atomic_state_only_copy_inactive_row_masks_v3]
    Visibility: public -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::atomic_state_only_copy_inactive_row_masks_v3"]
def
  aspis_statement.atomic_state_only_terminal.atomic_state_only_copy_inactive_row_masks_v3
  : Result (Array Std.U16 64#usize) := do
  let a ←
    aspis_statement.atomic_state_only_terminal.constants.COMPILED_ATOMIC_COPY_ACTIVE_ROWS
  let masks := Array.repeat 64#usize core.num.U16.MAX
  let iter ←
    SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter a
  aspis_statement.atomic_state_only_terminal.atomic_state_only_copy_inactive_row_masks_v3_loop
    iter masks

/-- [aspis_statement::atomic_state_only_trace::AtomicStateOnlyTraceV3Error]
    Source: 'crates/aspis-statement/src/atomic_state_only_trace.rs', lines 126:0-126:36
    Name pattern: [aspis_statement::atomic_state_only_trace::AtomicStateOnlyTraceV3Error]
    Visibility: public -/
@[discriminant isize, rust_type
  "aspis_statement::atomic_state_only_trace::AtomicStateOnlyTraceV3Error"]
inductive aspis_statement.atomic_state_only_trace.AtomicStateOnlyTraceV3Error
  where
| PathDepth :
  aspis_statement.atomic_state_only_trace.AtomicStateOnlyTraceV3Error
| PathIndexOutOfRange :
  aspis_statement.atomic_state_only_trace.AtomicStateOnlyTraceV3Error
| CurrentAnchorMismatch :
  aspis_statement.atomic_state_only_trace.AtomicStateOnlyTraceV3Error
| OutputAnchorMismatch :
  aspis_statement.atomic_state_only_trace.AtomicStateOnlyTraceV3Error
| SpendBinding :
  aspis_statement.atomic_state_only_trace.AtomicStateOnlyTraceV3Error
| SurrogateTrace :
  aspis_statement.atomic_state_only_trace.AtomicStateOnlyTraceV3Error
| Projection :
  aspis_statement.atomic_state_only_trace.AtomicStateOnlyTraceV3Error
| Layout : aspis_statement.atomic_state_only_trace.AtomicStateOnlyTraceV3Error
| TraceMismatch :
  Std.U16 →
  Std.U8 →
  aspis_statement.atomic_state_only_trace.AtomicStateOnlyTraceV3Error
| PathMetadataMismatch :
  Std.U8 →
  aspis_statement.atomic_state_only_trace.AtomicStateOnlyTraceV3Error

/-- [aspis_prover::circle_candidate::CircleCandidateError]
    Source: 'crates/aspis-prover/src/circle_candidate.rs', lines 53:0-88:1
    Visibility: public -/
@[discriminant isize]
inductive circle_candidate.CircleCandidateError where
| MessageLength :
  Std.Usize →
  Std.Usize →
  circle_candidate.CircleCandidateError
| ColumnCount :
  Std.Usize →
  Std.Usize →
  circle_candidate.CircleCandidateError
| CodewordLength :
  Std.Usize →
  Std.Usize →
  Std.Usize →
  circle_candidate.CircleCandidateError
| FiberIndex : Std.Usize → circle_candidate.CircleCandidateError
| LeafLength :
  Std.Usize →
  Std.Usize →
  circle_candidate.CircleCandidateError
| NonCanonicalM31 : Std.Usize → circle_candidate.CircleCandidateError
| NonCanonicalQm31 : Std.Usize → circle_candidate.CircleCandidateError
| CombinedLength :
  Std.Usize →
  Std.Usize →
  circle_candidate.CircleCandidateError
| TerminalEvaluationMismatch :
  Std.Usize →
  circle_candidate.CircleCandidateError
| Fold :
  aspis_core.circle_fri.CircleFriError →
  circle_candidate.CircleCandidateError

/-- [aspis_prover::state_only_hiding::StateOnlyMaskBuildError]
    Source: 'crates/aspis-prover/src/state_only_hiding.rs', lines 41:0-47:1
    Visibility: public -/
@[discriminant isize]
inductive state_only_hiding.StateOnlyMaskBuildError where
| ZeroPrivateEntropy : state_only_hiding.StateOnlyMaskBuildError
| ReusedMaskNonce : state_only_hiding.StateOnlyMaskBuildError
| MaskSampleExhausted : state_only_hiding.StateOnlyMaskBuildError
| TraceShape : state_only_hiding.StateOnlyMaskBuildError
| Layout : state_only_hiding.StateOnlyMaskBuildError

/-- [aspis_prover::state_only_private_openings::StateOnlyPrivateOpeningBuildError]
    Source: 'crates/aspis-prover/src/state_only_private_openings.rs', lines 10:0-21:1
    Visibility: public -/
@[discriminant isize]
inductive state_only_private_openings.StateOnlyPrivateOpeningBuildError where
| InvalidDepth :
  Std.U32 →
  state_only_private_openings.StateOnlyPrivateOpeningBuildError
| InvalidValueWidth :
  Std.Usize →
  state_only_private_openings.StateOnlyPrivateOpeningBuildError
| ValuesLengthMismatch :
  Std.Usize →
  Std.Usize →
  state_only_private_openings.StateOnlyPrivateOpeningBuildError
| SaltCountMismatch :
  Std.Usize →
  Std.Usize →
  state_only_private_openings.StateOnlyPrivateOpeningBuildError
| EmptyOpening : state_only_private_openings.StateOnlyPrivateOpeningBuildError
| CountOutOfRange :
  Std.Usize →
  state_only_private_openings.StateOnlyPrivateOpeningBuildError
| IndicesNotStrictlyIncreasing :
  state_only_private_openings.StateOnlyPrivateOpeningBuildError
| LeafIndexOutOfRange :
  Std.U32 →
  state_only_private_openings.StateOnlyPrivateOpeningBuildError
| LengthOverflow :
  state_only_private_openings.StateOnlyPrivateOpeningBuildError
| OpenedLeafDoesNotMatchTree :
  Std.U32 →
  state_only_private_openings.StateOnlyPrivateOpeningBuildError

/-- [aspis_prover::v5_mask::V5_TRACE_ROWS]
    Source: 'crates/aspis-prover/src/v5_mask.rs', lines 146:0-146:38
    Visibility: public -/
@[global_simps, irreducible]
def v5_mask.V5_TRACE_ROWS : Std.Usize := 1024#usize

/-- [aspis_prover::v5_mask::V5MaskError]
    Source: 'crates/aspis-prover/src/v5_mask.rs', lines 781:0-790:1
    Visibility: public -/
@[discriminant isize]
inductive v5_mask.V5MaskError where
| ColumnLength : Std.Usize → Std.Usize → v5_mask.V5MaskError
| ScheduleLength : Std.Usize → Std.Usize → v5_mask.V5MaskError
| CirclePoint : aspis_core.circle.CirclePointError → v5_mask.V5MaskError
| Encoder : circle_candidate.CircleCandidateError → v5_mask.V5MaskError

/-- [aspis_prover::v5_mask::spend_messages::V5_B_ROUND_BLOCKS]
    Source: 'crates/aspis-prover/src/v5_spend_messages.rs', lines 92:0-92:77
    Visibility: public -/
@[global_simps, irreducible]
def v5_mask.spend_messages.V5_B_ROUND_BLOCKS : Array Std.Usize 10#usize :=
  Array.make 10#usize [
    0#usize, 1#usize, 2#usize, 3#usize, 4#usize, 5#usize, 6#usize, 28#usize,
    29#usize, 30#usize
    ]

/-- [aspis_prover::v5_mask::spend_messages::V5_B_ROUND_BLOCK_ROWS]
    Source: 'crates/aspis-prover/src/v5_spend_messages.rs', lines 93:0-93:44
    Visibility: public -/
@[global_simps, irreducible]
def v5_mask.spend_messages.V5_B_ROUND_BLOCK_ROWS : Std.Usize := 32#usize

/-- [aspis_prover::v5_mask::spend_messages::V5_B_ROUND_COEFFICIENTS]
    Source: 'crates/aspis-prover/src/v5_spend_messages.rs', lines 94:0-94:46
    Visibility: public -/
@[global_simps, irreducible]
def v5_mask.spend_messages.V5_B_ROUND_COEFFICIENTS : Std.Usize := 28#usize

/-- [aspis_prover::v5_mask::spend_messages::V5_B_INITIAL_CLAIM_ROW]
    Source: 'crates/aspis-prover/src/v5_spend_messages.rs', lines 96:0-96:46
    Visibility: public -/
@[global_simps, irreducible]
def v5_mask.spend_messages.V5_B_INITIAL_CLAIM_ROW : Std.Usize := 992#usize

/-- [aspis_prover::v5_mask::spend_messages::V5_B_INACTIVE_PIVOT_ROW]
    Source: 'crates/aspis-prover/src/v5_spend_messages.rs', lines 97:0-97:47
    Visibility: public -/
@[global_simps, irreducible]
def v5_mask.spend_messages.V5_B_INACTIVE_PIVOT_ROW : Std.Usize := 993#usize

/-- [aspis_prover::v5_mask::spend_messages::V5_B_PAD_START]
    Source: 'crates/aspis-prover/src/v5_spend_messages.rs', lines 98:0-98:38
    Visibility: public -/
@[global_simps, irreducible]
def v5_mask.spend_messages.V5_B_PAD_START : Std.Usize := 224#usize

/-- [aspis_prover::v5_mask::spend_messages::V5_B_PAD_COORDINATES]
    Source: 'crates/aspis-prover/src/v5_spend_messages.rs', lines 99:0-99:44
    Visibility: public -/
@[global_simps, irreducible]
def v5_mask.spend_messages.V5_B_PAD_COORDINATES : Std.Usize := 255#usize

/-- [aspis_prover::v5_mask::spend_messages::V5SpendMessageError]
    Source: 'crates/aspis-prover/src/v5_spend_messages.rs', lines 122:0-146:1
    Visibility: public -/
@[discriminant isize]
inductive v5_mask.spend_messages.V5SpendMessageError where
| AtomicTrace :
  aspis_statement.atomic_state_only_trace.AtomicStateOnlyTraceV3Error →
  v5_mask.spend_messages.V5SpendMessageError
| AtomicCopy :
  aspis_statement.atomic_state_only_registry.AtomicStateOnlyRegistryErrorV3 →
  v5_mask.spend_messages.V5SpendMessageError
| ComponentA :
  v5_mask.V5MaskError →
  v5_mask.spend_messages.V5SpendMessageError
| HcopyPadding :
  state_only_hiding.StateOnlyMaskBuildError →
  v5_mask.spend_messages.V5SpendMessageError
| Circle :
  circle_candidate.CircleCandidateError →
  v5_mask.spend_messages.V5SpendMessageError
| PrivateMerkle :
  state_only_private_openings.StateOnlyPrivateOpeningBuildError →
  v5_mask.spend_messages.V5SpendMessageError
| Query :
  aspis_core.circle_line_merkle.CircleLineMerkleError →
  v5_mask.spend_messages.V5SpendMessageError
| OpeningVerify :
  Std.U8 →
  aspis_core.state_only_private_openings.StateOnlyPrivateOpeningError →
  v5_mask.spend_messages.V5SpendMessageError
| OpeningTrailingBytes :
  Std.Usize →
  Std.Usize →
  v5_mask.spend_messages.V5SpendMessageError
| LayerZeroRootMismatch : v5_mask.spend_messages.V5SpendMessageError
| ComponentARelation : Std.Usize → v5_mask.spend_messages.V5SpendMessageError
| HcopyRelation : v5_mask.spend_messages.V5SpendMessageError
| ComponentBRelation : v5_mask.spend_messages.V5SpendMessageError
| ComponentCRelation : v5_mask.spend_messages.V5SpendMessageError
| MessageShape : v5_mask.spend_messages.V5SpendMessageError

/-- [aspis_prover::v5_mask::spend_messages::atomic_inactive]:
    Source: 'crates/aspis-prover/src/v5_spend_messages.rs', lines 230:0-235:1 -/
def v5_mask.spend_messages.atomic_inactive
  (row : Std.Usize) : Result Bool := do
  let masks ←
    aspis_statement.atomic_state_only_terminal.atomic_state_only_copy_inactive_row_masks_v3
  let high ← lift (Std.Usize.wrapping_shr row 4#u32)
  let i ← lift (row &&& 15#usize)
  let low ← lift (UScalar.cast .U32 i)
  let i1 ← Array.index_usize masks high
  let i2 ← lift (Std.U16.wrapping_shl 1#u16 low)
  let i3 ← lift (i1 &&& i2)
  ok (i3 != 0#u16)

/-- [aspis_prover::v5_mask::spend_messages::atomic_inactive_sum_qm31]: loop body 0:
    Source: 'crates/aspis-prover/src/v5_spend_messages.rs', lines 254:4-259:5 -/
@[rust_loop_body]
def v5_mask.spend_messages.atomic_inactive_sum_qm31_loop.body
  (values : Slice aspis_core.field.QM31) (sum : aspis_core.field.QM31)
  (row : Std.Usize) :
  Result (ControlFlow (aspis_core.field.QM31 × Std.Usize)
    aspis_core.field.QM31)
  := do
  let i := Slice.len values
  if row < i
  then
    let b ← v5_mask.spend_messages.atomic_inactive row
    let sum1 ←
      if b
      then
        do
        let q ← Slice.index_usize values row
        aspis_core.field.QM31.add sum q
      else ok sum
    let row1 ← lift (Std.Usize.wrapping_add row 1#usize)
    ok (cont (sum1, row1))
  else ok (done sum)

/-- [aspis_prover::v5_mask::spend_messages::atomic_inactive_sum_qm31]: loop 0:
    Source: 'crates/aspis-prover/src/v5_spend_messages.rs', lines 254:4-259:5 -/
@[rust_loop]
def v5_mask.spend_messages.atomic_inactive_sum_qm31_loop
  (values : Slice aspis_core.field.QM31) (sum : aspis_core.field.QM31)
  (row : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  loop
    (fun (sum1, row1) =>
      v5_mask.spend_messages.atomic_inactive_sum_qm31_loop.body values sum1
      row1)
    (sum, row)

/-- [aspis_prover::v5_mask::spend_messages::atomic_inactive_sum_qm31]:
    Source: 'crates/aspis-prover/src/v5_spend_messages.rs', lines 248:0-261:1 -/
def v5_mask.spend_messages.atomic_inactive_sum_qm31
  (values : Slice aspis_core.field.QM31) :
  Result (Option aspis_core.field.QM31)
  := do
  let i := Slice.len values
  if i != v5_mask.V5_TRACE_ROWS
  then ok none
  else
    let sum ←
      v5_mask.spend_messages.atomic_inactive_sum_qm31_loop values
        aspis_core.field.QM31.ZERO 0#usize
    ok (some sum)

/-- [aspis_prover::v5_mask::spend_messages::b_block_row]:
    Source: 'crates/aspis-prover/src/v5_spend_messages.rs', lines 263:0-265:1 -/
def v5_mask.spend_messages.b_block_row
  (round : Std.Usize) (offset : Std.Usize) : Result Std.Usize := do
  let i ← Array.index_usize v5_mask.spend_messages.V5_B_ROUND_BLOCKS round
  let i1 ←
    lift (Std.Usize.wrapping_mul i
      v5_mask.spend_messages.V5_B_ROUND_BLOCK_ROWS)
  ok (Std.Usize.wrapping_add i1 offset)

/-- [aspis_prover::v5_mask::spend_messages::V5StructuredBLane]
    Source: 'crates/aspis-prover/src/v5_spend_messages.rs', lines 276:0-279:1
    Visibility: public -/
structure v5_mask.spend_messages.V5StructuredBLane where
  values : Array aspis_core.field.QM31 1024#usize
  pivot_pad : aspis_core.field.QM31

/-- [aspis_prover::v5_sumcheck_mask::{aspis_prover::v5_sumcheck_mask::V5SumcheckMask}::commitment_coefficient]: loop body 0:
    Source: 'crates/aspis-prover/src/v5_sumcheck_mask.rs', lines 128:12-131:13 -/
@[rust_loop_body]
def v5_sumcheck_mask.V5SumcheckMask.commitment_coefficient_loop.body
  (self : v5_sumcheck_mask.V5SumcheckMask) (round : Std.Usize)
  (tail_sum : aspis_core.field.QM31) (offset : Std.Usize) :
  Result (ControlFlow (aspis_core.field.QM31 × Std.Usize)
    aspis_core.field.QM31)
  := do
  if offset < 28#usize
  then
    let a ← Array.index_usize self.zero_boundary_rounds round
    let q ← Array.index_usize a offset
    let tail_sum1 ← aspis_core.field.QM31.add tail_sum q
    let offset1 ← lift (Std.Usize.wrapping_add offset 1#usize)
    ok (cont (tail_sum1, offset1))
  else ok (done tail_sum)

/-- [aspis_prover::v5_sumcheck_mask::{aspis_prover::v5_sumcheck_mask::V5SumcheckMask}::commitment_coefficient]: loop 0:
    Source: 'crates/aspis-prover/src/v5_sumcheck_mask.rs', lines 128:12-131:13 -/
@[rust_loop]
def v5_sumcheck_mask.V5SumcheckMask.commitment_coefficient_loop
  (self : v5_sumcheck_mask.V5SumcheckMask) (round : Std.Usize)
  (tail_sum : aspis_core.field.QM31) (offset : Std.Usize) :
  Result aspis_core.field.QM31
  := do
  loop
    (fun (tail_sum1, offset1) =>
      v5_sumcheck_mask.V5SumcheckMask.commitment_coefficient_loop.body self
      round tail_sum1 offset1)
    (tail_sum, offset)

/-- [aspis_prover::v5_sumcheck_mask::{aspis_prover::v5_sumcheck_mask::V5SumcheckMask}::commitment_coefficient]:
    Source: 'crates/aspis-prover/src/v5_sumcheck_mask.rs', lines 124:4-136:5 -/
def v5_sumcheck_mask.V5SumcheckMask.commitment_coefficient
  (self : v5_sumcheck_mask.V5SumcheckMask) (round : Std.Usize)
  (coefficient : Std.Usize) : Result aspis_core.field.QM31 := do
  if coefficient = 0#usize
  then
    let tail_sum1 ←
      v5_sumcheck_mask.V5SumcheckMask.commitment_coefficient_loop self round
        aspis_core.field.QM31.ZERO 1#usize
    let q ← aspis_core.field.QM31.neg tail_sum1
    let q2 ← aspis_core.field.QM31.half aspis_core.field.QM31.ONE
    aspis_core.field.QM31.mul q q2
  else
    let a ← Array.index_usize self.zero_boundary_rounds round
    Array.index_usize a coefficient

/-- [aspis_prover::v5_sumcheck_mask::{aspis_prover::v5_sumcheck_mask::V5SumcheckMask}::initial_claim]:
    Source: 'crates/aspis-prover/src/v5_sumcheck_mask.rs', lines 104:4-106:5
    Visibility: public -/
def v5_sumcheck_mask.V5SumcheckMask.impl.initial_claim
  (self : v5_sumcheck_mask.V5SumcheckMask) : Result aspis_core.field.QM31 := do
  ok self.initial_claim

/-- [aspis_prover::v5_mask::spend_messages::{aspis_prover::v5_mask::spend_messages::V5StructuredBLane}::encode]: loop body 1:
    Source: 'crates/aspis-prover/src/v5_spend_messages.rs', lines 296:12-300:13
    Visibility: public -/
@[rust_loop_body]
def v5_mask.spend_messages.V5StructuredBLane.encode_loop0_loop0.body
  (mask : v5_sumcheck_mask.V5SumcheckMask) (round : Std.Usize)
  (values : Array aspis_core.field.QM31 1024#usize) (offset : Std.Usize) :
  Result (ControlFlow ((Array aspis_core.field.QM31 1024#usize) × Std.Usize)
    (Array aspis_core.field.QM31 1024#usize))
  := do
  if offset < v5_mask.spend_messages.V5_B_ROUND_COEFFICIENTS
  then
    let value ←
      v5_sumcheck_mask.V5SumcheckMask.commitment_coefficient mask round offset
    let i ← v5_mask.spend_messages.b_block_row round offset
    let a ← Array.update values i value
    let offset1 ← lift (Std.Usize.wrapping_add offset 1#usize)
    ok (cont (a, offset1))
  else ok (done values)

/-- [aspis_prover::v5_mask::spend_messages::{aspis_prover::v5_mask::spend_messages::V5StructuredBLane}::encode]: loop 1:
    Source: 'crates/aspis-prover/src/v5_spend_messages.rs', lines 296:12-300:13
    Visibility: public -/
@[rust_loop]
def v5_mask.spend_messages.V5StructuredBLane.encode_loop0_loop0
  (mask : v5_sumcheck_mask.V5SumcheckMask)
  (values : Array aspis_core.field.QM31 1024#usize) (round : Std.Usize)
  (offset : Std.Usize) : Result (Array aspis_core.field.QM31 1024#usize) := do
  loop
    (fun (values1, offset1) =>
      v5_mask.spend_messages.V5StructuredBLane.encode_loop0_loop0.body mask
      round values1 offset1)
    (values, offset)

/-- [aspis_prover::v5_mask::spend_messages::{aspis_prover::v5_mask::spend_messages::V5StructuredBLane}::encode]: loop body 0:
    Source: 'crates/aspis-prover/src/v5_spend_messages.rs', lines 294:8-302:9
    Visibility: public -/
@[rust_loop_body]
def v5_mask.spend_messages.V5StructuredBLane.encode_loop0.body
  (mask : v5_sumcheck_mask.V5SumcheckMask)
  (values : Array aspis_core.field.QM31 1024#usize) (round : Std.Usize) :
  Result (ControlFlow ((Array aspis_core.field.QM31 1024#usize) × Std.Usize)
    (Array aspis_core.field.QM31 1024#usize))
  := do
  if round < 10#usize
  then
    let values1 ←
      v5_mask.spend_messages.V5StructuredBLane.encode_loop0_loop0 mask values
        round 0#usize
    let round1 ← lift (Std.Usize.wrapping_add round 1#usize)
    ok (cont (values1, round1))
  else ok (done values)

/-- [aspis_prover::v5_mask::spend_messages::{aspis_prover::v5_mask::spend_messages::V5StructuredBLane}::encode]: loop 0:
    Source: 'crates/aspis-prover/src/v5_spend_messages.rs', lines 294:8-302:9
    Visibility: public -/
@[rust_loop]
def v5_mask.spend_messages.V5StructuredBLane.encode_loop0
  (mask : v5_sumcheck_mask.V5SumcheckMask)
  (values : Array aspis_core.field.QM31 1024#usize) (round : Std.Usize) :
  Result (Array aspis_core.field.QM31 1024#usize)
  := do
  loop
    (fun (values1, round1) =>
      v5_mask.spend_messages.V5StructuredBLane.encode_loop0.body mask values1
      round1)
    (values, round)

/-- [aspis_prover::v5_mask::spend_messages::{aspis_prover::v5_mask::spend_messages::V5StructuredBLane}::encode]: loop body 2:
    Source: 'crates/aspis-prover/src/v5_spend_messages.rs', lines 308:8-311:9
    Visibility: public -/
@[rust_loop_body]
def v5_mask.spend_messages.V5StructuredBLane.encode_loop1.body
  (pads : Array aspis_core.field.QM31 255#usize)
  (values : Array aspis_core.field.QM31 1024#usize) (offset : Std.Usize) :
  Result (ControlFlow ((Array aspis_core.field.QM31 1024#usize) × Std.Usize)
    (Array aspis_core.field.QM31 1024#usize))
  := do
  if offset < v5_mask.spend_messages.V5_B_PAD_COORDINATES
  then
    let q ← Array.index_usize pads offset
    let i ←
      lift (Std.Usize.wrapping_add v5_mask.spend_messages.V5_B_PAD_START
        offset)
    let a ← Array.update values i q
    let offset1 ← lift (Std.Usize.wrapping_add offset 1#usize)
    ok (cont (a, offset1))
  else ok (done values)

/-- [aspis_prover::v5_mask::spend_messages::{aspis_prover::v5_mask::spend_messages::V5StructuredBLane}::encode]: loop 2:
    Source: 'crates/aspis-prover/src/v5_spend_messages.rs', lines 308:8-311:9
    Visibility: public -/
@[rust_loop]
def v5_mask.spend_messages.V5StructuredBLane.encode_loop1
  (pads : Array aspis_core.field.QM31 255#usize)
  (values : Array aspis_core.field.QM31 1024#usize) (offset : Std.Usize) :
  Result (Array aspis_core.field.QM31 1024#usize)
  := do
  loop
    (fun (values1, offset1) =>
      v5_mask.spend_messages.V5StructuredBLane.encode_loop1.body pads values1
      offset1)
    (values, offset)

/-- [aspis_prover::v5_mask::spend_messages::{aspis_prover::v5_mask::spend_messages::V5StructuredBLane}::encode]:
    Source: 'crates/aspis-prover/src/v5_spend_messages.rs', lines 282:4-320:5
    Visibility: public -/
def v5_mask.spend_messages.V5StructuredBLane.encode
  (mask : v5_sumcheck_mask.V5SumcheckMask)
  (pads : Array aspis_core.field.QM31 255#usize)
  (pivot_pad : aspis_core.field.QM31) :
  Result (core.result.Result v5_mask.spend_messages.V5StructuredBLane
    v5_mask.spend_messages.V5SpendMessageError)
  := do
  let b ←
    v5_mask.spend_messages.atomic_inactive
      v5_mask.spend_messages.V5_B_INACTIVE_PIVOT_ROW
  if b
  then
    let values := Array.repeat 1024#usize aspis_core.field.QM31.ZERO
    let q ← v5_sumcheck_mask.V5SumcheckMask.impl.initial_claim mask
    let a ←
      Array.update values v5_mask.spend_messages.V5_B_INITIAL_CLAIM_ROW q
    let values1 ←
      v5_mask.spend_messages.V5StructuredBLane.encode_loop0 mask a 0#usize
    let values2 ←
      v5_mask.spend_messages.V5StructuredBLane.encode_loop1 pads values1
        0#usize
    let s ← lift (Array.to_slice values2)
    let o ← v5_mask.spend_messages.atomic_inactive_sum_qm31 s
    match o with
    | none =>
      ok (core.result.Result.Err
        v5_mask.spend_messages.V5SpendMessageError.ComponentBRelation)
    | some value =>
      let q1 ← aspis_core.field.QM31.neg value
      let q2 ← aspis_core.field.QM31.add pivot_pad q1
      let values3 ←
        Array.update values2 v5_mask.spend_messages.V5_B_INACTIVE_PIVOT_ROW q2
      let s1 ← lift (Array.to_slice values3)
      let o1 ← v5_mask.spend_messages.atomic_inactive_sum_qm31 s1
      match o1 with
      | none =>
        ok (core.result.Result.Err
          v5_mask.spend_messages.V5SpendMessageError.ComponentBRelation)
      | some value1 =>
        let b1 ←
          aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq value1 pivot_pad
        if b1
        then ok (core.result.Result.Ok { values := values3, pivot_pad })
        else
          ok (core.result.Result.Err
            v5_mask.spend_messages.V5SpendMessageError.ComponentBRelation)
  else
    ok (core.result.Result.Err
      v5_mask.spend_messages.V5SpendMessageError.ComponentBRelation)

/-- [aspis_prover::v5_mask::split_layer_zero::v5_structured_terminal_covector]: loop body 0:
    Source: 'crates/aspis-prover/src/v5_split_layer_zero.rs', lines 161:4-164:5
    Visibility: public -/
@[rust_loop_body]
def v5_mask.split_layer_zero.v5_structured_terminal_covector_loop0.body
  (half : aspis_core.field.QM31)
  (half_powers : Array aspis_core.field.QM31 11#usize) (exponent : Std.Usize) :
  Result (ControlFlow ((Array aspis_core.field.QM31 11#usize) × Std.Usize)
    (Array aspis_core.field.QM31 11#usize))
  := do
  let s ← lift (Array.to_slice half_powers)
  let i := Slice.len s
  if exponent < i
  then
    let i1 ← lift (Std.Usize.wrapping_sub exponent 1#usize)
    let q ← Array.index_usize half_powers i1
    let q1 ← aspis_core.field.QM31.mul q half
    let a ← Array.update half_powers exponent q1
    let exponent1 ← lift (Std.Usize.wrapping_add exponent 1#usize)
    ok (cont (a, exponent1))
  else ok (done half_powers)

/-- [aspis_prover::v5_mask::split_layer_zero::v5_structured_terminal_covector]: loop 0:
    Source: 'crates/aspis-prover/src/v5_split_layer_zero.rs', lines 161:4-164:5
    Visibility: public -/
@[rust_loop]
def v5_mask.split_layer_zero.v5_structured_terminal_covector_loop0
  (half : aspis_core.field.QM31)
  (half_powers : Array aspis_core.field.QM31 11#usize) (exponent : Std.Usize) :
  Result (Array aspis_core.field.QM31 11#usize)
  := do
  loop
    (fun (half_powers1, exponent1) =>
      v5_mask.split_layer_zero.v5_structured_terminal_covector_loop0.body half
      half_powers1 exponent1)
    (half_powers, exponent)

/-- [aspis_prover::v5_mask::split_layer_zero::v5_structured_terminal_covector]: loop body 2:
    Source: 'crates/aspis-prover/src/v5_split_layer_zero.rs', lines 174:8-178:9
    Visibility: public -/
@[rust_loop_body]
def v5_mask.split_layer_zero.v5_structured_terminal_covector_loop1_loop0.body
  (challenge : aspis_core.field.QM31) (scale : aspis_core.field.QM31)
  (start : Std.Usize) (covector : alloc.vec.Vec aspis_core.field.QM31)
  (power : aspis_core.field.QM31) (offset : Std.Usize) :
  Result (ControlFlow ((alloc.vec.Vec aspis_core.field.QM31) ×
    aspis_core.field.QM31 × Std.Usize) (alloc.vec.Vec aspis_core.field.QM31))
  := do
  if offset < v5_mask.spend_messages.V5_B_ROUND_COEFFICIENTS
  then
    let q ← aspis_core.field.QM31.mul scale power
    let i ← lift (Std.Usize.wrapping_add start offset)
    let (_, index_mut_back) ←
      alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
        aspis_core.field.QM31) covector i
    let power1 ← aspis_core.field.QM31.mul power challenge
    let offset1 ← lift (Std.Usize.wrapping_add offset 1#usize)
    let covector1 := index_mut_back q
    ok (cont (covector1, power1, offset1))
  else ok (done covector)

/-- [aspis_prover::v5_mask::split_layer_zero::v5_structured_terminal_covector]: loop 2:
    Source: 'crates/aspis-prover/src/v5_split_layer_zero.rs', lines 174:8-178:9
    Visibility: public -/
@[rust_loop]
def v5_mask.split_layer_zero.v5_structured_terminal_covector_loop1_loop0
  (covector : alloc.vec.Vec aspis_core.field.QM31)
  (challenge : aspis_core.field.QM31) (scale : aspis_core.field.QM31)
  (start : Std.Usize) (power : aspis_core.field.QM31) (offset : Std.Usize) :
  Result (alloc.vec.Vec aspis_core.field.QM31)
  := do
  loop
    (fun (covector1, power1, offset1) =>
      v5_mask.split_layer_zero.v5_structured_terminal_covector_loop1_loop0.body
      challenge scale start covector1 power1 offset1)
    (covector, power, offset)

/-- [aspis_prover::v5_mask::split_layer_zero::v5_structured_terminal_covector]: loop body 1:
    Source: 'crates/aspis-prover/src/v5_split_layer_zero.rs', lines 168:4-180:5
    Visibility: public -/
@[rust_loop_body]
def v5_mask.split_layer_zero.v5_structured_terminal_covector_loop1.body
  (point : Array aspis_core.field.QM31 10#usize)
  (half_powers : Array aspis_core.field.QM31 11#usize)
  (covector : alloc.vec.Vec aspis_core.field.QM31) (round : Std.Usize) :
  Result (ControlFlow ((alloc.vec.Vec aspis_core.field.QM31) × Std.Usize)
    (alloc.vec.Vec aspis_core.field.QM31))
  := do
  let s ← lift (Array.to_slice point)
  let i := Slice.len s
  if round < i
  then
    let challenge ← Array.index_usize point round
    let i1 ← lift (Std.Usize.wrapping_sub 9#usize round)
    let scale ← Array.index_usize half_powers i1
    let i2 ← Array.index_usize v5_mask.spend_messages.V5_B_ROUND_BLOCKS round
    let start ←
      lift (Std.Usize.wrapping_mul i2
        v5_mask.spend_messages.V5_B_ROUND_BLOCK_ROWS)
    let covector1 ←
      v5_mask.split_layer_zero.v5_structured_terminal_covector_loop1_loop0
        covector challenge scale start aspis_core.field.QM31.ONE 0#usize
    let round1 ← lift (Std.Usize.wrapping_add round 1#usize)
    ok (cont (covector1, round1))
  else ok (done covector)

/-- [aspis_prover::v5_mask::split_layer_zero::v5_structured_terminal_covector]: loop 1:
    Source: 'crates/aspis-prover/src/v5_split_layer_zero.rs', lines 168:4-180:5
    Visibility: public -/
@[rust_loop]
def v5_mask.split_layer_zero.v5_structured_terminal_covector_loop1
  (point : Array aspis_core.field.QM31 10#usize)
  (half_powers : Array aspis_core.field.QM31 11#usize)
  (covector : alloc.vec.Vec aspis_core.field.QM31) (round : Std.Usize) :
  Result (alloc.vec.Vec aspis_core.field.QM31)
  := do
  loop
    (fun (covector1, round1) =>
      v5_mask.split_layer_zero.v5_structured_terminal_covector_loop1.body point
      half_powers covector1 round1)
    (covector, round)

/-- [aspis_prover::v5_mask::split_layer_zero::v5_structured_terminal_covector]:
    Source: 'crates/aspis-prover/src/v5_split_layer_zero.rs', lines 153:0-182:1
    Visibility: public -/
def v5_mask.split_layer_zero.v5_structured_terminal_covector
  (point : Array aspis_core.field.QM31 10#usize) :
  Result (alloc.vec.Vec aspis_core.field.QM31)
  := do
  let half ← aspis_core.field.QM31.half aspis_core.field.QM31.ONE
  let half_powers := Array.repeat 11#usize aspis_core.field.QM31.ONE
  let half_powers1 ←
    v5_mask.split_layer_zero.v5_structured_terminal_covector_loop0 half
      half_powers 1#usize
  let covector ←
    alloc.vec.from_elem aspis_core.field.QM31.Insts.CoreCloneClone
      aspis_core.field.QM31.ZERO v5_mask.V5_TRACE_ROWS
  let q ← Array.index_usize half_powers1 10#usize
  let (_, index_mut_back) ←
    alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice
      aspis_core.field.QM31) covector
      v5_mask.spend_messages.V5_B_INITIAL_CLAIM_ROW
  let covector1 := index_mut_back q
  v5_mask.split_layer_zero.v5_structured_terminal_covector_loop1 point
    half_powers1 covector1 0#usize

end ComponentBGenerated

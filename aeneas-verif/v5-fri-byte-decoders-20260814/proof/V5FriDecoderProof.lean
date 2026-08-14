import V5FriDecoderGenerated.Funs
import AspisFormal.V5MerkleConsumedValueBridge

open Aeneas Aeneas.Std Result ControlFlow Error
set_option maxRecDepth 3000

namespace AspisV5FriDecoderSourceProof

open AspisV5ComponentCQM31Representation
open AspisV5ComponentCRejectionSampler
open AspisV5MerkleConsumedValueBridge

def toU8 (byte : AspisV5ComponentCQM31Representation.Byte) : Std.U8 :=
  Std.U8.ofNatCore byte.val (by simpa using byte.isLt)

@[simp] theorem toU8_val
    (byte : AspisV5ComponentCQM31Representation.Byte) :
    (toU8 byte).val = byte.val := by
  simp [toU8]

def wordArray (bytes : WordBytes) : Array Std.U8 4#usize :=
  ⟨[toU8 (bytes 0), toU8 (bytes 1), toU8 (bytes 2), toU8 (bytes 3)],
    by scalar_tac⟩

def qm31Array (bytes : QM31Bytes) : Array Std.U8 16#usize :=
  Array.make 16#usize [
    toU8 (bytes 0), toU8 (bytes 1), toU8 (bytes 2), toU8 (bytes 3),
    toU8 (bytes 4), toU8 (bytes 5), toU8 (bytes 6), toU8 (bytes 7),
    toU8 (bytes 8), toU8 (bytes 9), toU8 (bytes 10), toU8 (bytes 11),
    toU8 (bytes 12), toU8 (bytes 13), toU8 (bytes 14), toU8 (bytes 15)]

def generatedM31Raw (bytes : WordBytes) : Option Nat :=
  match aspis_core.field.M31.from_le_bytes (wordArray bytes) with
  | .ok none => none
  | .ok (some value) => some value.val
  | .fail _ => none
  | .div => none

def modelM31Raw (bytes : WordBytes) : Option Nat :=
  (decodeM31LE bytes).map Fin.val

def m31ValueToU32 (value : M31Value) : Std.U32 :=
  Std.U32.ofNatCore value.val (by
    have := value.isLt
    norm_num [m31Modulus, rawCandidateCount] at *
    omega)

def modelM31U32 (bytes : WordBytes) : Option Std.U32 :=
  (decodeM31LE bytes).map m31ValueToU32

/-- Semantic transport from Aeneas's extracted `u32` representation to the
maintained finite subtype.  The guard is data, not an assumption. -/
def generatedM31ToModel (value : aspis_core.field.M31) : Option M31Value :=
  if h : value.val < m31Modulus then some ⟨value.val, h⟩ else none

/-- The extracted production M31 decoder, transported into the maintained
model's result type. -/
def extractedM31Decode (bytes : WordBytes) : Option M31Value :=
  match aspis_core.field.M31.from_le_bytes (wordArray bytes) with
  | .ok value => value.bind generatedM31ToModel
  | .fail _ => none
  | .div => none

theorem fromLEBytes_four_toNat (b0 b1 b2 b3 : BitVec 8) :
    (BitVec.fromLEBytes [b0, b1, b2, b3]).toNat =
      b0.toNat + 256 * b1.toNat + 65536 * b2.toNat +
        16777216 * b3.toNat := by
  have hb0 : b0.toNat < 256 := by simpa using b0.isLt
  have hb1 : b1.toNat < 256 := by simpa using b1.isLt
  have hb2 : b2.toNat < 256 := by simpa using b2.isLt
  have hb3 : b3.toNat < 256 := by simpa using b3.isLt
  have hb3s : b3.toNat * 256 < 65536 := by omega
  have h23 : b2.toNat + 256 * b3.toNat < 65536 := by omega
  have h23s : (b2.toNat + 256 * b3.toNat) * 256 < 16777216 := by omega
  have h123 : b1.toNat + 256 * (b2.toNat + 256 * b3.toNat) < 16777216 := by
    omega
  have h123s :
      (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat)) * 256 < 4294967296 := by
    omega
  simp only [BitVec.fromLEBytes, BitVec.toNat_or, BitVec.toNat_setWidth,
    BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, List.length_cons,
    List.length_nil, Nat.mul_zero, Nat.mul_one, Nat.reducePow,
    BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_mul, Nat.or_zero]
  norm_num at ⊢
  rw [Nat.mod_eq_of_lt (by omega : b0.toNat < 4294967296),
    Nat.mod_eq_of_lt (by omega : b1.toNat < 16777216),
    Nat.mod_eq_of_lt (by omega : b2.toNat < 65536), Nat.mod_eq_of_lt hb3]
  rw [Nat.mod_eq_of_lt hb3s]
  rw [show b2.toNat ||| b3.toNat * 256 =
      b2.toNat + 256 * b3.toNat by
    rw [Nat.or_comm, Nat.mul_comm]
    simpa [Nat.add_comm] using
      (Nat.two_pow_add_eq_or_of_lt (i := 8) hb2 b3.toNat).symm]
  rw [Nat.mod_eq_of_lt h23s]
  rw [show b1.toNat ||| (b2.toNat + 256 * b3.toNat) * 256 =
      b1.toNat + 256 * (b2.toNat + 256 * b3.toNat) by
    rw [Nat.or_comm, Nat.mul_comm]
    simpa [Nat.add_comm] using
      (Nat.two_pow_add_eq_or_of_lt (i := 8) hb1
        (b2.toNat + 256 * b3.toNat)).symm]
  rw [Nat.mod_eq_of_lt h123s]
  rw [show b0.toNat |||
        (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat)) * 256 =
      b0.toNat + 256 *
        (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat)) by
    rw [Nat.or_comm, Nat.mul_comm]
    simpa [Nat.add_comm] using
      (Nat.two_pow_add_eq_or_of_lt (i := 8) hb0
        (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat))).symm]
  omega

theorem generated_u32_from_le_bytes_val (bytes : WordBytes) :
    (core.num.U32.from_le_bytes (wordArray bytes)).val =
      (decodeWordLE bytes : Nat) := by
  have hlist :
      List.map Std.U8.bv (wordArray bytes).val =
        [(toU8 (bytes 0)).bv, (toU8 (bytes 1)).bv,
          (toU8 (bytes 2)).bv, (toU8 (bytes 3)).bv] := by
    rfl
  unfold core.num.U32.from_le_bytes UScalar.val
  rw [BitVec.toNat_cast, hlist, fromLEBytes_four_toNat]
  change (toU8 (bytes 0)).val + 256 * (toU8 (bytes 1)).val +
      65536 * (toU8 (bytes 2)).val + 16777216 * (toU8 (bytes 3)).val =
    (decodeWordLE bytes : Nat)
  simp only [toU8_val, decodeWordLE]

theorem generatedM31Raw_eq_modelM31Raw (bytes : WordBytes) :
    generatedM31Raw bytes = modelM31Raw bytes := by
  unfold generatedM31Raw modelM31Raw aspis_core.field.M31.from_le_bytes
  rw [show core.num.U32.from_le_bytes (wordArray bytes) =
      core.num.U32.from_le_bytes (wordArray bytes) by rfl]
  have hvalue := generated_u32_from_le_bytes_val bytes
  by_cases hcanonical : (decodeWordLE bytes : Nat) < m31Modulus
  · have hnotge : ¬(aspis_core.field.P.val ≤
        (core.num.U32.from_le_bytes (wordArray bytes)).val) := by
      rw [hvalue]
      simpa [aspis_core.field.P, m31Modulus, rawCandidateCount] using
        (Nat.not_le_of_lt hcanonical)
    have hnotgeModel : ¬(aspis_core.field.P.val ≤
        (decodeWordLE bytes : Nat)) := by
      simpa [aspis_core.field.P, m31Modulus, rawCandidateCount] using
        (Nat.not_le_of_lt hcanonical)
    simp [lift, hnotge, hnotgeModel, decodeM31LE, hcanonical, hvalue]
  · have hge : aspis_core.field.P.val ≤
        (core.num.U32.from_le_bytes (wordArray bytes)).val := by
      rw [hvalue]
      simpa [aspis_core.field.P, m31Modulus, rawCandidateCount] using
        (Nat.le_of_not_gt hcanonical)
    have hgeModel : aspis_core.field.P.val ≤ (decodeWordLE bytes : Nat) := by
      simpa [aspis_core.field.P, m31Modulus, rawCandidateCount] using
        (Nat.le_of_not_gt hcanonical)
    simp [lift, hge, hgeModel, decodeM31LE, hcanonical, hvalue]

theorem generatedM31Result_eq_modelM31U32 (bytes : WordBytes) :
    aspis_core.field.M31.from_le_bytes (wordArray bytes) =
      .ok (modelM31U32 bytes) := by
  unfold aspis_core.field.M31.from_le_bytes modelM31U32
  have hvalue := generated_u32_from_le_bytes_val bytes
  by_cases hcanonical : (decodeWordLE bytes : Nat) < m31Modulus
  · have hnotgeModel : ¬(aspis_core.field.P.val ≤
        (decodeWordLE bytes : Nat)) := by
      simpa [aspis_core.field.P, m31Modulus, rawCandidateCount] using
        (Nat.not_le_of_lt hcanonical)
    simp [lift, hnotgeModel, decodeM31LE, hcanonical, hvalue]
    apply UScalar.eq_of_val_eq
    simp [m31ValueToU32, hvalue]
  · have hgeModel : aspis_core.field.P.val ≤ (decodeWordLE bytes : Nat) := by
      simpa [aspis_core.field.P, m31Modulus, rawCandidateCount] using
        (Nat.le_of_not_gt hcanonical)
    simp [lift, hgeModel, decodeM31LE, hcanonical, hvalue]

theorem generatedM31Result_eq_modelM31U32_of_val
    {array : Array Std.U8 4#usize} (bytes : WordBytes)
    (hval : array.val = (wordArray bytes).val) :
    aspis_core.field.M31.from_le_bytes array = .ok (modelM31U32 bytes) := by
  have harray : array = wordArray bytes := Subtype.ext hval
  subst array
  exact generatedM31Result_eq_modelM31U32 bytes

theorem extractedM31Decode_eq_model (bytes : WordBytes) :
    extractedM31Decode bytes = decodeM31LE bytes := by
  unfold extractedM31Decode
  rw [generatedM31Result_eq_modelM31U32]
  cases hdecode : decodeM31LE bytes with
  | none => simp [modelM31U32, hdecode]
  | some value =>
      simp [modelM31U32, hdecode, generatedM31ToModel, m31ValueToU32,
        value.isLt]

def qm31Limb0 (bytes : QM31Bytes) : WordBytes := qm31LimbBytes bytes 0
def qm31Limb1 (bytes : QM31Bytes) : WordBytes := qm31LimbBytes bytes 1
def qm31Limb2 (bytes : QM31Bytes) : WordBytes := qm31LimbBytes bytes 2
def qm31Limb3 (bytes : QM31Bytes) : WordBytes := qm31LimbBytes bytes 3

theorem first_qm31_word_slice_is_exact (bytes : QM31Bytes) :
    (do
      let slice ← core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)
        (Array.to_slice (qm31Array bytes))
        { start := 0#usize, «end» := 4#usize }
      core.array.TryFromArrayCopySlice.try_from 4#usize
        core.marker.CopyU8 slice) =
      .ok (core.result.Result.Ok (wordArray (qm31Limb0 bytes))) := by
  simp [core.slice.index.Slice.index,
    core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index,
    core.array.TryFromArrayCopySlice.try_from,
    Array.to_slice, qm31Array, wordArray, qm31Limb0, qm31LimbBytes,
    limbByteIndex, toU8]
  apply Subtype.ext
  rfl

def pairSlice (low high : WordBytes) : Slice Std.U8 :=
  ⟨[toU8 (low 0), toU8 (low 1), toU8 (low 2), toU8 (low 3),
    toU8 (high 0), toU8 (high 1), toU8 (high 2), toU8 (high 3)],
    by scalar_tac⟩

def modelCM31U32 (low high : WordBytes) : Option aspis_core.field.CM31 := do
  let a ← modelM31U32 low
  let b ← modelM31U32 high
  some { a, b }

theorem generatedCM31Pair_eq_model (low high : WordBytes) :
    aspis_core.field.CM31.from_le_bytes (pairSlice low high) =
      .ok (modelCM31U32 low high) := by
  unfold aspis_core.field.CM31.from_le_bytes
  simp [core.slice.index.Slice.index,
    core.slice.index.SliceIndexRangeUsizeSlice.index,
    pairSlice, wordArray, Slice.length, UScalar.le_equiv,
    core.array.TryFromArrayCopySlice.try_from,
    core.result.Result.ok,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]
  rw [generatedM31Result_eq_modelM31U32_of_val low (by rfl),
    generatedM31Result_eq_modelM31U32_of_val high (by rfl)]
  cases hlow : modelM31U32 low <;> cases hhigh : modelM31U32 high <;>
    simp [modelCM31U32, hlow, hhigh,
      core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]

theorem generatedCM31Pair_eq_model_of_val
    {slice : Slice Std.U8} (low high : WordBytes)
    (hval : slice.val = (pairSlice low high).val) :
    aspis_core.field.CM31.from_le_bytes slice =
      .ok (modelCM31U32 low high) := by
  have hslice : slice = pairSlice low high := Subtype.ext hval
  subst slice
  exact generatedCM31Pair_eq_model low high

def quadSlice (w0 w1 w2 w3 : WordBytes) : Slice Std.U8 :=
  ⟨[toU8 (w0 0), toU8 (w0 1), toU8 (w0 2), toU8 (w0 3),
    toU8 (w1 0), toU8 (w1 1), toU8 (w1 2), toU8 (w1 3),
    toU8 (w2 0), toU8 (w2 1), toU8 (w2 2), toU8 (w2 3),
    toU8 (w3 0), toU8 (w3 1), toU8 (w3 2), toU8 (w3 3)],
    by scalar_tac⟩

def modelQM31U32FromWords (w0 w1 w2 w3 : WordBytes) :
    Option aspis_core.field.QM31 := do
  let c0 ← modelCM31U32 w0 w1
  let c1 ← modelCM31U32 w2 w3
  some { c0, c1 }

theorem generatedQM31Quad_eq_model (w0 w1 w2 w3 : WordBytes) :
    aspis_core.field.QM31.from_le_bytes (quadSlice w0 w1 w2 w3) =
      .ok (modelQM31U32FromWords w0 w1 w2 w3) := by
  unfold aspis_core.field.QM31.from_le_bytes
  simp [core.slice.index.Slice.index,
    core.slice.index.SliceIndexRangeUsizeSlice.index,
    quadSlice, pairSlice, Slice.length, UScalar.le_equiv,
    core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual]
  rw [generatedCM31Pair_eq_model_of_val w0 w1 (by rfl),
    generatedCM31Pair_eq_model_of_val w2 w3 (by rfl)]
  cases hc0 : modelCM31U32 w0 w1 <;> cases hc1 : modelCM31U32 w2 w3 <;>
    simp [modelQM31U32FromWords, hc0, hc1]

theorem generatedQM31Quad_eq_model_of_val
    {slice : Slice Std.U8} (w0 w1 w2 w3 : WordBytes)
    (hval : slice.val = (quadSlice w0 w1 w2 w3).val) :
    aspis_core.field.QM31.from_le_bytes slice =
      .ok (modelQM31U32FromWords w0 w1 w2 w3) := by
  have hslice : slice = quadSlice w0 w1 w2 w3 := Subtype.ext hval
  subst slice
  exact generatedQM31Quad_eq_model w0 w1 w2 w3

theorem generatedQM31Bytes_eq_model (bytes : QM31Bytes) :
    aspis_core.field.QM31.from_le_bytes
        (Array.to_slice (qm31Array bytes)) =
      .ok (modelQM31U32FromWords
        (qm31Limb0 bytes) (qm31Limb1 bytes)
        (qm31Limb2 bytes) (qm31Limb3 bytes)) := by
  apply generatedQM31Quad_eq_model_of_val
  apply List.ext_getElem
  · rfl
  · intro index hindexLeft hindexRight
    have hindex : index < 16 := by simpa using hindexLeft
    interval_cases index <;>
      simp [Array.to_slice, Array.make, qm31Array, quadSlice, qm31Limb0, qm31Limb1,
        qm31Limb2, qm31Limb3, qm31LimbBytes, limbByteIndex,
        finProdFinEquiv, toU8]

def decodeQM31ViaM31 (bytes : QM31Bytes) : Option QM31Limbs := do
  let limb0 ← decodeM31LE (qm31Limb0 bytes)
  let limb1 ← decodeM31LE (qm31Limb1 bytes)
  let limb2 ← decodeM31LE (qm31Limb2 bytes)
  let limb3 ← decodeM31LE (qm31Limb3 bytes)
  some ![limb0, limb1, limb2, limb3]

theorem decodeQM31ViaM31_eq_decodeQM31LE (bytes : QM31Bytes) :
    decodeQM31ViaM31 bytes = decodeQM31LE bytes := by
  let raw (limb : Fin 4) : Nat :=
    (decodeWordLE (qm31LimbBytes bytes limb) : Nat)
  by_cases h0 : raw 0 < m31Modulus
  · by_cases h1 : raw 1 < m31Modulus
    · by_cases h2 : raw 2 < m31Modulus
      · by_cases h3 : raw 3 < m31Modulus
        · have hall : ∀ limb : Fin 4, raw limb < m31Modulus := by
            intro limb
            fin_cases limb <;> assumption
          have hd0 : decodeM31LE (qm31Limb0 bytes) = some
              ⟨decodeWordLE (qm31Limb0 bytes), by
                simpa [raw, qm31Limb0] using h0⟩ := by
            unfold decodeM31LE
            rw [dif_pos]
          have hd1 : decodeM31LE (qm31Limb1 bytes) = some
              ⟨decodeWordLE (qm31Limb1 bytes), by
                simpa [raw, qm31Limb1] using h1⟩ := by
            unfold decodeM31LE
            rw [dif_pos]
          have hd2 : decodeM31LE (qm31Limb2 bytes) = some
              ⟨decodeWordLE (qm31Limb2 bytes), by
                simpa [raw, qm31Limb2] using h2⟩ := by
            unfold decodeM31LE
            rw [dif_pos]
          have hd3 : decodeM31LE (qm31Limb3 bytes) = some
              ⟨decodeWordLE (qm31Limb3 bytes), by
                simpa [raw, qm31Limb3] using h3⟩ := by
            unfold decodeM31LE
            rw [dif_pos]
          rw [show decodeQM31LE bytes = some (fun limb =>
              ⟨decodeWordLE (qm31LimbBytes bytes limb), hall limb⟩) by
            simp [decodeQM31LE, hall, raw]]
          simp only [decodeQM31ViaM31, hd0, hd1, hd2, hd3,
            Option.bind_some]
          apply congrArg some
          funext limb
          apply Fin.ext
          fin_cases limb <;> rfl
        · have hnotall : ¬ ∀ limb : Fin 4, raw limb < m31Modulus := by
            intro hall
            exact h3 (hall 3)
          simp [decodeQM31ViaM31, decodeM31LE, decodeQM31LE,
            qm31Limb0, qm31Limb1, qm31Limb2, qm31Limb3,
            raw, h0, h1, h2, h3, hnotall]
      · have hnotall : ¬ ∀ limb : Fin 4, raw limb < m31Modulus := by
          intro hall
          exact h2 (hall 2)
        simp [decodeQM31ViaM31, decodeM31LE, decodeQM31LE,
          qm31Limb0, qm31Limb1, qm31Limb2, qm31Limb3,
          raw, h0, h1, h2, hnotall]
    · have hnotall : ¬ ∀ limb : Fin 4, raw limb < m31Modulus := by
        intro hall
        exact h1 (hall 1)
      simp [decodeQM31ViaM31, decodeM31LE, decodeQM31LE,
        qm31Limb0, qm31Limb1, qm31Limb2, qm31Limb3,
        raw, h0, h1, hnotall]
  · have hnotall : ¬ ∀ limb : Fin 4, raw limb < m31Modulus := by
      intro hall
      exact h0 (hall 0)
    simp [decodeQM31ViaM31, decodeM31LE, decodeQM31LE,
      qm31Limb0, qm31Limb1, qm31Limb2, qm31Limb3,
      raw, h0, hnotall]

/-- Semantic transport from the extracted Rust tower representation into the
maintained four-limb representation.  Each generated limb is checked before
constructing its finite-subtype value. -/
def generatedQM31ToModel (value : aspis_core.field.QM31) : Option QM31Limbs := do
  let limb0 ← generatedM31ToModel value.c0.a
  let limb1 ← generatedM31ToModel value.c0.b
  let limb2 ← generatedM31ToModel value.c1.a
  let limb3 ← generatedM31ToModel value.c1.b
  some ![limb0, limb1, limb2, limb3]

/-- The extracted production QM31 decoder, transported into the maintained
model's result type. -/
def extractedQM31Decode (bytes : QM31Bytes) : Option QM31Limbs :=
  match aspis_core.field.QM31.from_le_bytes
      (Array.to_slice (qm31Array bytes)) with
  | .ok value => value.bind generatedQM31ToModel
  | .fail _ => none
  | .div => none

theorem modelQM31U32_bind_generatedQM31ToModel (bytes : QM31Bytes) :
    (modelQM31U32FromWords
      (qm31Limb0 bytes) (qm31Limb1 bytes)
      (qm31Limb2 bytes) (qm31Limb3 bytes)).bind generatedQM31ToModel =
      decodeQM31ViaM31 bytes := by
  unfold modelQM31U32FromWords modelCM31U32 decodeQM31ViaM31
  cases h0 : decodeM31LE (qm31Limb0 bytes) <;>
    cases h1 : decodeM31LE (qm31Limb1 bytes) <;>
    cases h2 : decodeM31LE (qm31Limb2 bytes) <;>
    cases h3 : decodeM31LE (qm31Limb3 bytes) <;>
    simp [modelM31U32, h0, h1, h2, h3, generatedQM31ToModel,
      generatedM31ToModel, m31ValueToU32]

theorem extractedQM31Decode_eq_model (bytes : QM31Bytes) :
    extractedQM31Decode bytes = decodeQM31LE bytes := by
  unfold extractedQM31Decode
  rw [generatedQM31Bytes_eq_model]
  change (modelQM31U32FromWords
      (qm31Limb0 bytes) (qm31Limb1 bytes)
      (qm31Limb2 bytes) (qm31Limb3 bytes)).bind generatedQM31ToModel =
    decodeQM31LE bytes
  rw [modelQM31U32_bind_generatedQM31ToModel,
    decodeQM31ViaM31_eq_decodeQM31LE]

/-- Charon/Aeneas extraction of the production decoders discharges the exact
decoder boundary used by all four modeled FRI read schedules. -/
theorem exact_extracted_fri_byte_decoders :
    ExactRustFriByteDecoderEquality extractedM31Decode extractedQM31Decode := by
  constructor
  · funext bytes
    exact extractedM31Decode_eq_model bytes
  · funext bytes
    exact extractedQM31Decode_eq_model bytes

#print axioms extractedM31Decode_eq_model
#print axioms extractedQM31Decode_eq_model
#print axioms exact_extracted_fri_byte_decoders

end AspisV5FriDecoderSourceProof

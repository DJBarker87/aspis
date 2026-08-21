import V5PrefixNonceEncodingProof

/-!
# Exact byte conversions used by the concrete V5 prefix helper join

This small module is deliberately independent of the generated prefix helper
environment.  In particular, the `u64::to_le_bytes` proof is checked against
the Aeneas scalar model before the larger generated modules introduce their
own rewrite rules.
-/

namespace AspisV5PrefixByteEncodingProof

open Aeneas Aeneas.Std
open AspisFormal.V5ExactRuntimeWireRepair
open AspisV5NonceWorkAuthentication
open AspisV5PrefixNonceEncodingProof

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def byteToGenerated (value : ModelByte) : Std.U8 :=
  Std.U8.ofNatCore value.val (by simpa using value.isLt)

@[simp] theorem generatedToByte_byteToGenerated (value : ModelByte) :
    generatedToByte (byteToGenerated value) = value := by
  apply Fin.ext
  simp [generatedToByte, byteToGenerated]

@[simp] theorem generatedToByte_0 : generatedToByte 0#u8 = (0 : ModelByte) := by decide
@[simp] theorem generatedToByte_10 : generatedToByte 10#u8 = (10 : ModelByte) := by decide
@[simp] theorem generatedToByte_12 : generatedToByte 12#u8 = (12 : ModelByte) := by decide
@[simp] theorem generatedToByte_13 : generatedToByte 13#u8 = (13 : ModelByte) := by decide
@[simp] theorem generatedToByte_27 : generatedToByte 27#u8 = (27 : ModelByte) := by decide
@[simp] theorem generatedToByte_28 : generatedToByte 28#u8 = (28 : ModelByte) := by decide
@[simp] theorem generatedToByte_29 : generatedToByte 29#u8 = (29 : ModelByte) := by decide
@[simp] theorem generatedToByte_31 : generatedToByte 31#u8 = (31 : ModelByte) := by decide
@[simp] theorem generatedToByte_32 : generatedToByte 32#u8 = (32 : ModelByte) := by decide
@[simp] theorem generatedToByte_33 : generatedToByte 33#u8 = (33 : ModelByte) := by decide

@[simp] theorem generated_byte_list_roundtrip (values : List ModelByte) :
    (values.map byteToGenerated).map generatedToByte = values := by
  induction values with
  | nil => rfl
  | cons head tail ih => simp [ih]

end AspisV5PrefixByteEncodingProof

import AspisFormal.K1.V7Tag73TranscriptSchedule

/-!
# Root recovery from exact Tag-73 absorb inputs

The C1 and C2 roots occupy fixed byte slices of their transcript absorb
inputs.  Equality of two literal inputs therefore implies equality of the
encoded roots without assuming SHA-256 injectivity or equality of the prior
digest and salts.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73RootAbsorbInputInjectivity

open AspisK1.V7Tag73TranscriptSchedule

/-- C1 root bytes start after the 32-byte digest, two domain bytes, and the
one-byte C1 payload discriminator. -/
theorem c1_root_eq_of_absorb_input_eq
    (leftBefore rightBefore : Digest256)
    (leftRoot rightRoot : Digest208)
    (leftSalt rightSalt : Digest256)
    (inputExact :
      bytes leftBefore ++ [domAbsorb, c1RootLabel] ++
          (Payload.c1Root leftRoot leftSalt).data =
        bytes rightBefore ++ [domAbsorb, c1RootLabel] ++
          (Payload.c1Root rightRoot rightSalt).data) :
    leftRoot = rightRoot := by
  let leftPrefix := bytes leftBefore ++ [domAbsorb, c1RootLabel, 0]
  let rightPrefix := bytes rightBefore ++ [domAbsorb, c1RootLabel, 0]
  have leftPrefixLength : leftPrefix.length = 35 := by
    simp [leftPrefix, bytes_length]
  have rightPrefixLength : rightPrefix.length = 35 := by
    simp [rightPrefix, bytes_length]
  have normalized :
      leftPrefix ++ bytes leftRoot ++ bytes leftSalt =
        rightPrefix ++ bytes rightRoot ++ bytes rightSalt := by
    simpa [leftPrefix, rightPrefix, Payload.data, List.append_assoc] using
      inputExact
  have bytesExact : bytes leftRoot = bytes rightRoot := by
    have sliceNormalized := congrArg
      (fun input => (input.drop 35).take 26) normalized
    simpa [leftPrefixLength, rightPrefixLength, bytes_length,
      List.append_assoc] using sliceNormalized
  exact List.ofFn_injective bytesExact

/-- C2 root bytes begin immediately after the 32-byte digest and two domain
bytes. -/
theorem c2_root_eq_of_absorb_input_eq
    (leftBefore rightBefore : Digest256)
    (leftRoot rightRoot : Digest208)
    (leftSalt rightSalt : Digest256)
    (inputExact :
      bytes leftBefore ++ [domAbsorb, c2RootLabel] ++
          (Payload.c2Root leftRoot leftSalt).data =
        bytes rightBefore ++ [domAbsorb, c2RootLabel] ++
          (Payload.c2Root rightRoot rightSalt).data) :
    leftRoot = rightRoot := by
  let leftPrefix := bytes leftBefore ++ [domAbsorb, c2RootLabel]
  let rightPrefix := bytes rightBefore ++ [domAbsorb, c2RootLabel]
  have leftPrefixLength : leftPrefix.length = 34 := by
    simp [leftPrefix, bytes_length]
  have rightPrefixLength : rightPrefix.length = 34 := by
    simp [rightPrefix, bytes_length]
  have normalized :
      leftPrefix ++ bytes leftRoot ++ bytes leftSalt =
        rightPrefix ++ bytes rightRoot ++ bytes rightSalt := by
    simpa [leftPrefix, rightPrefix, Payload.data, List.append_assoc] using
      inputExact
  have bytesExact : bytes leftRoot = bytes rightRoot := by
    have sliceNormalized := congrArg
      (fun input => (input.drop 34).take 26) normalized
    simpa [leftPrefixLength, rightPrefixLength, bytes_length,
      List.append_assoc] using sliceNormalized
  exact List.ofFn_injective bytesExact

#print axioms c1_root_eq_of_absorb_input_eq
#print axioms c2_root_eq_of_absorb_input_eq

end AspisK1.V7Tag73RootAbsorbInputInjectivity

import AspisFormal.V5ComponentCBlockSamplerDirectHiding
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# v5 Component C: exact low31 and four-limb representation model

This leaf closes the *finite representation* part of the Component-C sampler
without pretending that Lean can inspect Rust object code.

* `rustLow31BitAnd` is the literal mathematical semantics of
  `word & 0x7fff_ffff`, and is proved equal to the modulo-`2^31` map used by
  `V5ComponentCRejectionSampler`.
* `encodeQM31LE` and `decodeQM31LE` pin the deployed limb/byte order
  `(c0.a, c0.b, c1.a, c1.b)`, with every limb encoded as one canonical
  little-endian `u32`; their round trip is kernel checked.
* four canonical M31 limbs have exactly the cardinality of the canonical
  finite field `GF((2^31-1)^4)`.  Hence an exact equivalence exists and the
  successful Component-C sampler capstone can be instantiated without a
  caller-supplied representation equivalence.

The last point is deliberately representation-invariant: uniformity survives
every bijection.  It does **not** prove that Rust's Karatsuba operations are the
operations of the noncomputably chosen Galois-field equivalence.  The remaining
executable seam is therefore only equality of Rust's pure assembly/arithmetic/
codec functions with the explicit model below; it is named at the end.
-/

namespace AspisV5ComponentCQM31Representation

open AspisV5ComponentCRejectionSampler

/-! ## Literal low-31-bit masking -/

/-- Mathematical semantics of Rust's `word & 0x7fff_ffff`. -/
def rustLow31BitAnd (word : RawWord) : RawCandidate :=
  ⟨(word : Nat) &&& 0x7fff_ffff, by
    rw [show (0x7fff_ffff : Nat) = 2 ^ 31 - 1 by norm_num,
      Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by norm_num)⟩

/-- Bit masking by `0x7fff_ffff` is exactly reduction modulo `2^31`. -/
theorem rustLow31BitAnd_eq_low31Candidate :
    rustLow31BitAnd = low31Candidate := by
  funext word
  apply Fin.ext
  simp only [rustLow31BitAnd, low31Candidate, Fin.val_mk]
  rw [show (0x7fff_ffff : Nat) = 2 ^ 31 - 1 by norm_num,
    Nat.and_two_pow_sub_one_eq_mod]

/-- The old deployment-facing low31 interface is discharged for the exact
mathematical bit-and function.  Relating a Rust expression to this function is
now the sole code-semantics edge. -/
theorem rustLow31BitAnd_matches : RustLow31MaskMatches rustLow31BitAnd :=
  rustLow31BitAnd_eq_low31Candidate

/-! ## Exact little-endian codec and limb order -/

abbrev Byte := Fin 256
abbrev WordBytes := Fin 4 → Byte
abbrev QM31Bytes := Fin 16 → Byte

private def byteMod (n : Nat) : Byte :=
  ⟨n % 256, Nat.mod_lt _ (by norm_num)⟩

/-- Four little-endian bytes of one mathematical `u32`. -/
def encodeWordLE (word : RawWord) : WordBytes :=
  ![byteMod word,
    byteMod ((word : Nat) / 256),
    byteMod ((word : Nat) / 65536),
    byteMod ((word : Nat) / 16777216)]

/-- Reassemble four little-endian bytes into one mathematical `u32`. -/
def decodeWordLE (bytes : WordBytes) : RawWord :=
  ⟨(bytes 0 : Nat) + 256 * (bytes 1 : Nat) +
      65536 * (bytes 2 : Nat) + 16777216 * (bytes 3 : Nat), by
    have h0 := (bytes 0).isLt
    have h1 := (bytes 1).isLt
    have h2 := (bytes 2).isLt
    have h3 := (bytes 3).isLt
    norm_num [rawWordCount] at *
    omega⟩

/-- The mathematical `u32` little-endian codec round trips exactly. -/
theorem decodeWordLE_encodeWordLE (word : RawWord) :
    decodeWordLE (encodeWordLE word) = word := by
  apply Fin.ext
  simp only [decodeWordLE, encodeWordLE, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Fin.val_mk, byteMod]
  have hword := word.isLt
  norm_num [rawWordCount] at hword ⊢
  omega

/-- Canonically embed one accepted M31 residue in a mathematical `u32`. -/
def m31AsRawWord (value : M31Value) : RawWord :=
  ⟨value, lt_trans value.isLt (by
    norm_num [m31Modulus, rawCandidateCount, rawWordCount])⟩

def encodeM31LE (value : M31Value) : WordBytes :=
  encodeWordLE (m31AsRawWord value)

/-- Canonical Rust-style M31 decoder: reject a `u32` at or above `P`. -/
def decodeM31LE (bytes : WordBytes) : Option M31Value :=
  let word := decodeWordLE bytes
  if h : (word : Nat) < m31Modulus then some ⟨word, h⟩ else none

theorem decodeM31LE_encodeM31LE (value : M31Value) :
    decodeM31LE (encodeM31LE value) = some value := by
  have hround : decodeWordLE (encodeM31LE value) = m31AsRawWord value :=
    decodeWordLE_encodeWordLE _
  have hlt : ((decodeWordLE (encodeM31LE value) : RawWord) : Nat) < m31Modulus := by
    rw [hround]
    exact value.isLt
  unfold decodeM31LE
  rw [dif_pos hlt]
  apply congrArg some
  apply Fin.ext
  calc
    ((decodeWordLE (encodeM31LE value) : RawWord) : Nat) =
        (m31AsRawWord value : Nat) := congrArg Fin.val hround
    _ = (value : Nat) := rfl

/-- Byte offset `byte + 4*limb`.  Thus limbs `0,1,2,3` occupy byte ranges
`0..4`, `4..8`, `8..12`, `12..16`, exactly Rust's
`(c0.a,c0.b,c1.a,c1.b)` order. -/
def limbByteIndex (limb byte : Fin 4) : Fin 16 :=
  finProdFinEquiv (limb, byte)

@[simp] theorem limbByteIndex_val (limb byte : Fin 4) :
    (limbByteIndex limb byte : Nat) = (byte : Nat) + 4 * (limb : Nat) := rfl

/-- Encode four limbs consecutively in the pinned tower order. -/
def encodeQM31LE (limbs : QM31Limbs) : QM31Bytes :=
  fun offset =>
    let position : Fin 4 × Fin 4 := finProdFinEquiv.symm offset
    encodeM31LE (limbs position.1) position.2

/-- Extract the four bytes belonging to one pinned limb. -/
def qm31LimbBytes (bytes : QM31Bytes) (limb : Fin 4) : WordBytes :=
  fun byte => bytes (limbByteIndex limb byte)

@[simp] theorem qm31LimbBytes_encodeQM31LE (limbs : QM31Limbs) (limb : Fin 4) :
    qm31LimbBytes (encodeQM31LE limbs) limb = encodeM31LE (limbs limb) := by
  funext byte
  simp [qm31LimbBytes, encodeQM31LE, limbByteIndex]

/-- Decode four consecutive canonical M31 words.  Any noncanonical limb is
rejected, just as `QM31::from_le_bytes` rejects through its nested M31
decoders. -/
def decodeQM31LE (bytes : QM31Bytes) : Option QM31Limbs :=
  if h : ∀ limb, ((decodeWordLE (qm31LimbBytes bytes limb) : RawWord) : Nat) <
      m31Modulus then
    some (fun limb => ⟨decodeWordLE (qm31LimbBytes bytes limb), h limb⟩)
  else none

/-- The exact `(c0.a,c0.b,c1.a,c1.b)` 16-byte codec round trip. -/
theorem decodeQM31LE_encodeQM31LE (limbs : QM31Limbs) :
    decodeQM31LE (encodeQM31LE limbs) = some limbs := by
  have hword (limb : Fin 4) :
      decodeWordLE (qm31LimbBytes (encodeQM31LE limbs) limb) =
        m31AsRawWord (limbs limb) := by
    rw [qm31LimbBytes_encodeQM31LE]
    exact decodeWordLE_encodeWordLE _
  have hlt : ∀ limb,
      ((decodeWordLE (qm31LimbBytes (encodeQM31LE limbs) limb) : RawWord) : Nat) <
        m31Modulus := by
    intro limb
    rw [hword]
    exact (limbs limb).isLt
  unfold decodeQM31LE
  rw [dif_pos hlt]
  apply congrArg some
  funext limb
  apply Fin.ext
  calc
    ((decodeWordLE (qm31LimbBytes (encodeQM31LE limbs) limb) : RawWord) : Nat) =
        (m31AsRawWord (limbs limb) : Nat) := congrArg Fin.val (hword limb)
    _ = (limbs limb : Nat) := rfl

/-! ## Four limbs versus the canonical field of order `P^4` -/

abbrev DeployedPrime : Nat := m31Modulus

instance deployedPrimeFact : Fact DeployedPrime.Prime := ⟨by
  norm_num [DeployedPrime, m31Modulus, rawCandidateCount]⟩

/-- Canonical mathematical finite field with the deployed QM31 cardinality.
This is a field model, not an assertion about Rust's chosen tower basis. -/
abbrev CardinalityQM31 := GaloisField DeployedPrime 4

noncomputable instance cardinalityQM31Fintype : Fintype CardinalityQM31 :=
  Fintype.ofFinite CardinalityQM31

noncomputable instance cardinalityQM31DecidableEq : DecidableEq CardinalityQM31 :=
  Classical.decEq CardinalityQM31

theorem qm31Limbs_card : Fintype.card QM31Limbs = DeployedPrime ^ 4 := by
  simp [QM31Limbs, qm31LimbCount, M31Value, DeployedPrime]

theorem cardinalityQM31_card : Fintype.card CardinalityQM31 = DeployedPrime ^ 4 := by
  rw [← Nat.card_eq_fintype_card]
  exact GaloisField.card DeployedPrime (n := 4) (by norm_num)

/-- A kernel-justified representation equivalence.  It is intentionally
noncomputable and basis-agnostic, because the sampler's uniformity claim uses
only bijectivity. -/
noncomputable def cardinalityQM31LimbEquiv : QM31Limbs ≃ CardinalityQM31 :=
  Fintype.equivOfCardEq (qm31Limbs_card.trans cardinalityQM31_card.symm)

/-- Uniform successful Component-C free coordinates in the canonical
`P^4`-element field, with no caller-supplied `QM31Limbs ≃ K`. -/
theorem successfulCardinalityQM31FreeCoordinates_areIndependentUniform :
    AspisV5ComponentCSamplerKernel.SuccessfulFreeCoordinatesAreIndependentUniform
      (successfulComponentCFreeCoordinateLaw cardinalityQM31LimbEquiv) :=
  successfulComponentCFreeCoordinateLaw_isIndependentUniform
    cardinalityQM31LimbEquiv

/-- The committed sampler-kernel capstone instantiated at the canonical
field of deployed cardinality. -/
theorem successfulCardinalityQM31KernelLaw_eq_uniform
    (ell : (Fin 1024 → CardinalityQM31) →ₗ[CardinalityQM31] CardinalityQM31)
    (pivot : Fin 1024) (hpivot : ell (Pi.single pivot 1) = 1) :
    (((successfulComponentCBlockLaw.map componentCFlatToCoordinates).map
        (componentCCoordinateRepresentationEquiv cardinalityQM31LimbEquiv)).map
          (AspisV5ComponentCSamplerKernel.componentCEncoderEquiv ell pivot hpivot)) =
      PMF.uniformOfFintype (LinearMap.ker ell) :=
  successfulComponentCKernelLaw_eq_uniform_under_representation
    cardinalityQM31LimbEquiv ell pivot hpivot

/-- Literal-`u32` form of the kernel capstone.  Its left-hand side starts at
the single whole-block conditioning law on all 4092 families of sixteen
uniform `u32` words; the previously proved equality to the low31-candidate
experiment is used inside the proof, not left as a caller obligation. -/
theorem successfulCardinalityQM31RawU32KernelLaw_eq_uniform
    (ell : (Fin 1024 → CardinalityQM31) →ₗ[CardinalityQM31] CardinalityQM31)
    (pivot : Fin 1024) (hpivot : ell (Pi.single pivot 1) = 1) :
    (((successfulComponentCRawU32BlockLaw.map componentCFlatToCoordinates).map
        (componentCCoordinateRepresentationEquiv cardinalityQM31LimbEquiv)).map
          (AspisV5ComponentCSamplerKernel.componentCEncoderEquiv ell pivot hpivot)) =
      PMF.uniformOfFintype (LinearMap.ker ell) := by
  rw [successfulComponentCRawU32BlockLaw_eq_candidateBlockLaw]
  exact successfulCardinalityQM31KernelLaw_eq_uniform ell pivot hpivot

/-! ## Honest executable boundary -/

noncomputable def cardinalityQM31Encode (value : CardinalityQM31) : QM31Bytes :=
  encodeQM31LE (cardinalityQM31LimbEquiv.symm value)

noncomputable def cardinalityQM31Decode (bytes : QM31Bytes) : Option CardinalityQM31 :=
  (decodeQM31LE bytes).map cardinalityQM31LimbEquiv

theorem cardinalityQM31Codec_roundTrip (value : CardinalityQM31) :
    cardinalityQM31Decode (cardinalityQM31Encode value) = some value := by
  simp [cardinalityQM31Decode, cardinalityQM31Encode,
    decodeQM31LE_encodeQM31LE]

/-- The old combined representation/codec interface is genuinely
instantiable for the explicit mathematical functions in this leaf.  This is
not a claim that the Rust functions equal them; that remaining equality is
stated immediately below. -/
theorem cardinalityQM31LimbOrderAndCodecMatch :
    DeployedQM31LimbOrderAndCodecMatch cardinalityQM31LimbEquiv
      cardinalityQM31LimbEquiv cardinalityQM31Encode cardinalityQM31Decode := by
  exact ⟨rfl, cardinalityQM31Codec_roundTrip⟩

/-- Exact residual code/model edge for the Rust byte codec after identifying
`QM31 { c0 : (a,b), c1 : (c,d) }` with four limbs.  There is no abstract
"codec is faithful" slogan here: the executable functions must equal the
two explicit functions proved above. -/
def RustQM31CodecMatchesPinnedLimbOrder
    (rustEncode : QM31Limbs → QM31Bytes)
    (rustDecode : QM31Bytes → Option QM31Limbs) : Prop :=
  rustEncode = encodeQM31LE ∧ rustDecode = decodeQM31LE

/-- Exact residual arithmetic edge.  `e` is the *same* limb-to-field
equivalence used by the sampler.  Every primitive used by the deployed tower
is required to commute with field arithmetic; in particular an arbitrary
cardinality bijection is not silently treated as a field isomorphism. -/
def RustQM31TowerArithmeticMatches {K : Type*} [Field K] [DecidableEq K]
    (e : QM31Limbs ≃ K)
    (rustZero rustOne : QM31Limbs)
    (rustAdd rustMul : QM31Limbs → QM31Limbs → QM31Limbs)
    (rustNeg : QM31Limbs → QM31Limbs)
    (rustTryInv : QM31Limbs → Option QM31Limbs) : Prop :=
  e rustZero = 0 ∧ e rustOne = 1 ∧
  (∀ a b, e (rustAdd a b) = e a + e b) ∧
  (∀ a b, e (rustMul a b) = e a * e b) ∧
  (∀ a, e (rustNeg a) = -e a) ∧
  (∀ a, (rustTryInv a).map e = if e a = 0 then none else some (e a)⁻¹)

/-- Exact residual assembly edge for `sample_qm31`: after the four accepted
M31 calls have been obtained in order, Rust's constructor must be the same
equivalence `e` used in the field model. -/
def RustQM31SamplerAssemblyMatches {K : Type*}
    (e : QM31Limbs ≃ K) (rustAssemble : QM31Limbs → K) : Prop :=
  rustAssemble = e

/-! ## Axiom audit -/

#print axioms rustLow31BitAnd_eq_low31Candidate
#print axioms decodeWordLE_encodeWordLE
#print axioms decodeQM31LE_encodeQM31LE
#print axioms successfulCardinalityQM31FreeCoordinates_areIndependentUniform
#print axioms successfulCardinalityQM31KernelLaw_eq_uniform
#print axioms successfulCardinalityQM31RawU32KernelLaw_eq_uniform
#print axioms cardinalityQM31Codec_roundTrip
#print axioms cardinalityQM31LimbOrderAndCodecMatch

end AspisV5ComponentCQM31Representation

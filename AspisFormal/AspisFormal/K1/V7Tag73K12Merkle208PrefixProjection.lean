import AspisFormal.K1.V7Tag73ExactFixedK12MerkleClassifier
import AspisFormal.K1.V7Tag73K12Merkle208CollisionProbability

/-!
# Uniform 256-to-208 prefix projection for Tag-73 K1.2

The deployed SHA oracle returns 32 runtime bytes, while K1.2 consumes its
first 26 bytes through the exact runtime-byte equivalence.  This module proves
that projection is uniform by splitting every 32-byte digest bijectively into
its 26-byte Merkle prefix and six-byte tail.  It is the distribution bridge
between the existing full-output lazy oracle and the shared-208-bit collision
counting theorem; no SHA security or extraction-failure inclusion is assumed.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73K12Merkle208PrefixProjection

open MeasureTheory
open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7FsStateRestorationCoupling
open AspisK1.V7Tag73ResourceLazyOracle
open AspisK1.V7Tag73ExactFixedK12MerkleClassifier
open AspisK1.V7Tag73K12Merkle208CollisionProbability
open AspisPool.V7MerkleQueryGrammar

noncomputable section

abbrev RuntimeDigest256 := AspisK1.V7Tag73TranscriptSchedule.Digest256
abbrev MerkleDigest208 := AspisPool.V7MerkleQueryGrammar.Digest208
abbrev RuntimeDigestTail48 := Fin 6 → UInt8

def digestIndexSplitEquiv : Fin 26 ⊕ Fin 6 ≃ Fin 32 :=
  finSumFinEquiv.trans (finCongr (by norm_num))

def runtimePrefixEquivMerkle : (Fin 26 → UInt8) ≃ MerkleDigest208 :=
  { toFun := fun pfx index => runtimeByteEquivMerkleByte (pfx index)
    invFun := fun pfx index => runtimeByteEquivMerkleByte.symm (pfx index)
    left_inv := by intro pfx; ext index; simp
    right_inv := by intro pfx; ext index; simp }

def runtimeDigestSplitEquiv :
    RuntimeDigest256 ≃ (MerkleDigest208 × RuntimeDigestTail48) :=
  ((Equiv.piCongrLeft (fun _ : Fin 32 ↦ UInt8)
      digestIndexSplitEquiv).symm.trans
    (Equiv.sumPiEquivProdPi (fun _ : Fin 26 ⊕ Fin 6 ↦ UInt8))).trans
      (Equiv.prodCongr runtimePrefixEquivMerkle (Equiv.refl _))

theorem runtime_digest_split_prefix_is_deployed_projection
    (digest : RuntimeDigest256) :
    (runtimeDigestSplitEquiv digest).1 =
      runtimeDigest256PrefixToMerkleDigest digest := by
  apply funext
  intro index
  change runtimeByteEquivMerkleByte
      (digest (digestIndexSplitEquiv (Sum.inl index))) =
    runtimeByteEquivMerkleByte (digest ⟨index.val, by omega⟩)
  apply congrArg runtimeByteEquivMerkleByte
  apply congrArg digest
  apply Fin.ext
  rfl

def deployedPrefixFiber
    (target : MerkleDigest208) : Set RuntimeDigest256 :=
  {digest | runtimeDigest256PrefixToMerkleDigest digest = target}

def deployedPrefixFiberEquiv (target : MerkleDigest208) :
    ↑(deployedPrefixFiber target) ≃ RuntimeDigestTail48 where
  toFun digest := (runtimeDigestSplitEquiv digest.1).2
  invFun tail :=
    ⟨runtimeDigestSplitEquiv.symm (target, tail), by
      change runtimeDigest256PrefixToMerkleDigest
          (runtimeDigestSplitEquiv.symm (target, tail)) = target
      rw [← runtime_digest_split_prefix_is_deployed_projection]
      simp⟩
  left_inv digest := by
    apply Subtype.ext
    apply runtimeDigestSplitEquiv.injective
    simp only [Equiv.apply_symm_apply]
    apply Prod.ext
    · calc
        target = runtimeDigest256PrefixToMerkleDigest digest.1 := digest.2.symm
        _ = (runtimeDigestSplitEquiv digest.1).1 :=
          (runtime_digest_split_prefix_is_deployed_projection digest.1).symm
    · simp
  right_inv tail := by
    simp

theorem runtime_digest_tail48_cardinality :
    Fintype.card RuntimeDigestTail48 = 2 ^ 48 := by
  calc
    Fintype.card RuntimeDigestTail48 =
        Fintype.card (Fin 6 → Fin 256) :=
      Fintype.card_congr
        (Equiv.arrowCongr (Equiv.refl (Fin 6)) uint8EquivFin256)
    _ = 2 ^ 48 := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
      calc
        256 ^ 6 = (2 ^ 8) ^ 6 := by norm_num
        _ = 2 ^ (8 * 6) := by rw [pow_mul]
        _ = 2 ^ 48 := by norm_num

noncomputable instance deployedPrefixFiberFintype
    (target : MerkleDigest208) : Fintype ↑(deployedPrefixFiber target) :=
  Fintype.ofFinite _

theorem deployed_prefix_fiber_cardinality (target : MerkleDigest208) :
    Fintype.card ↑(deployedPrefixFiber target) = 2 ^ 48 := by
  rw [Fintype.card_congr (deployedPrefixFiberEquiv target)]
  exact runtime_digest_tail48_cardinality

/-- Every concrete 208-bit prefix has exactly `2^48` full SHA outputs above
it, hence exactly mass `2^-208` under the deployed uniform 256-bit law. -/
theorem uniform_digest256_deployed_prefix_probability_exact
    (target : MerkleDigest208) :
    uniformDigest256.toOuterMeasure (deployedPrefixFiber target) =
      (1 : ENNReal) / ((2 : ENNReal) ^ 208) := by
  classical
  unfold uniformDigest256
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  rw [deployed_prefix_fiber_cardinality]
  have digestCard :
      (Fintype.card RuntimeDigest256 : ENNReal) = (2 : ENNReal) ^ 256 := by
    rw [deployed_digest_256_cardinality]
    norm_num
  rw [digestCard]
  have cast48 :
      ((2 ^ 48 : Nat) : ENNReal) = (2 : ENNReal) ^ 48 := by
    norm_num
  rw [cast48, show 256 = 48 + 208 by norm_num, pow_add]
  simpa using
    (ENNReal.mul_div_mul_left (c := (2 : ENNReal) ^ 48)
      1 ((2 : ENNReal) ^ 208) (by positivity) (by finiteness))

#print axioms runtime_digest_split_prefix_is_deployed_projection
#print axioms deployed_prefix_fiber_cardinality
#print axioms uniform_digest256_deployed_prefix_probability_exact

end

end AspisK1.V7Tag73K12Merkle208PrefixProjection

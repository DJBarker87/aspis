import AspisFormal.V5ComponentCDeploymentLedger
import AspisFormal.V5ComponentCQM31TowerExact

/-!
# v5 Component C: exact QM31 tower deployment specialization

This leaf removes the arbitrary `P^4` cardinality equivalence from the
deployment ledger.  The sampler, codec, and arithmetic bundle are instantiated
with the explicit M31 -> CM31 -> QM31 tower, and one precise Rust source-function
equality implies the complete representation premise expected by the ledger.

The theorem does not prove Rust semantics.  It reduces that executable edge to
equality with the literal functions whose algebra is already kernel checked.
-/

namespace AspisV5ComponentCExactTowerDeployment

open AspisV5ComponentCDeploymentLedger
open AspisV5ComponentCQM31Representation
open AspisV5ComponentCQM31TowerExact
open AspisV5ComponentCRejectionSampler
open AspisV5ComponentCStoppingTimeSampler

/-- The full ledger representation bundle is inhabited by the exact tower,
pinned limb codec, and proved Karatsuba/inversion operations. -/
theorem exactTowerDeploymentRepresentationMatches :
    DeployedQM31RepresentationMatches qm31ExactLimbEquiv limbsToQM31Exact
      encodeQM31LE decodeQM31LE limbZero limbOne limbAdd limbMul limbNeg
      limbTryInv := by
  exact ⟨exactTowerSamplerAssemblyMatches, ⟨rfl, rfl⟩,
    exactTowerArithmeticMatches⟩

/-- Encoding an exact-tower value assembled from four limbs is exactly the
pinned four-limb codec. -/
theorem encodeQM31ExactLE_after_assembly :
    encodeQM31ExactLE ∘ limbsToQM31Exact = encodeQM31LE := by
  funext limbs
  simp [encodeQM31ExactLE, qm31ExactLimbEquiv]

/-- Decoding an exact-tower value and projecting back to limbs is exactly the
pinned four-limb decoder. -/
theorem decodeQM31ExactLE_to_limbs :
    (fun bytes => (decodeQM31ExactLE bytes).map qm31ExactLimbEquiv.symm) =
      decodeQM31LE := by
  funext bytes
  rw [decodeQM31ExactLE]
  cases decodeQM31LE bytes <;> simp

/-- One exact Rust source-function equality discharges the ledger's complete
assembly/codec/tower-arithmetic bundle.  The limb codec is obtained by
composing the source encoder/decoder with the same assembly equivalence. -/
theorem deployedRepresentationMatches_of_sourceFunctions
    (rustAssemble : QM31Limbs → QM31Exact)
    (rustZero rustOne : QM31Limbs)
    (rustAdd rustMul : QM31Limbs → QM31Limbs → QM31Limbs)
    (rustNeg : QM31Limbs → QM31Limbs)
    (rustTryInv : QM31Limbs → Option QM31Limbs)
    (rustEncode : QM31Exact → QM31Bytes)
    (rustDecode : QM31Bytes → Option QM31Exact)
    (hsource : RustQM31SourceFunctionsMatch rustAssemble rustZero rustOne
      rustAdd rustMul rustNeg rustTryInv rustEncode rustDecode) :
    DeployedQM31RepresentationMatches qm31ExactLimbEquiv rustAssemble
      (rustEncode ∘ rustAssemble)
      (fun bytes => (rustDecode bytes).map qm31ExactLimbEquiv.symm)
      rustZero rustOne rustAdd rustMul rustNeg rustTryInv := by
  rcases hsource with
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  rw [encodeQM31ExactLE_after_assembly, decodeQM31ExactLE_to_limbs]
  exact exactTowerDeploymentRepresentationMatches

/-- The source-function premise is satisfiable by the explicit mathematical
functions; it is not an inconsistent deployment gate. -/
theorem rustQM31SourceFunctionsMatch_nonvacuous :
    RustQM31SourceFunctionsMatch limbsToQM31Exact limbZero limbOne limbAdd
      limbMul limbNeg limbTryInv encodeQM31ExactLE decodeQM31ExactLE := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Literal variable-consumption sampling, exact four-limb assembly, and the
pivot encoder give the uniform law on `ker ell` in the concrete QM31 tower. -/
theorem successfulExactQM31StoppingTimeKernelLaw_eq_uniform
    (ell : (Fin 1024 → QM31Exact) →ₗ[QM31Exact] QM31Exact)
    (pivot : Fin 1024) (hpivot : ell (Pi.single pivot 1) = 1) :
    (successfulComponentCStoppingTimeFreeCoordinateLaw qm31ExactLimbEquiv).map
        (AspisV5ComponentCSamplerKernel.componentCEncoderEquiv
          ell pivot hpivot) =
      PMF.uniformOfFintype (LinearMap.ker ell) :=
  successfulComponentCStoppingTimeKernelLaw_eq_uniform
    qm31ExactLimbEquiv ell pivot hpivot

/-! ## Axiom audit -/

#print axioms exactTowerDeploymentRepresentationMatches
#print axioms encodeQM31ExactLE_after_assembly
#print axioms decodeQM31ExactLE_to_limbs
#print axioms deployedRepresentationMatches_of_sourceFunctions
#print axioms rustQM31SourceFunctionsMatch_nonvacuous
#print axioms successfulExactQM31StoppingTimeKernelLaw_eq_uniform

end AspisV5ComponentCExactTowerDeployment

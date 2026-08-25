import AspisFormal.V6RelationFold

/-!
# V6 explicit-final hiding factorization

The V6 wire publishes the complete 256-coefficient result of the sole
arity-four fold.  This file records the exact algebra needed by the hiding
argument: that view is a deterministic linear post-processing of the
coefficientwise gamma-batched 1024-message.  Consequently every difference
in the kernel of the complete batched-message projection is also in the
kernel of the explicit-final projection.

No random-oracle or rank premise is introduced here.  Those premises belong
to the separate affine-image and paired-salt arguments.
-/

set_option autoImplicit false

namespace AspisV6HidingFinalFactorization

open AspisV5ComponentCConcreteFoldLinearity

variable {K : Type*} [Field K]

/-- Exact 26-M31 plus 3-QM31 V6 commitment-lane count.  All lanes are viewed
over the common verifier field after the M31 lanes are embedded. -/
def gammaBatchedMessage (gamma : K)
    (columns : Fin 29 → Fin 1024 → K) : Fin 1024 → K :=
  fun coefficient =>
    ∑ lane : Fin 29, gamma ^ lane.val * columns lane coefficient

/-- The explicit 256-vector serialized by V6 after its sole committed fold. -/
def explicitFinalProjection (alpha gamma : K)
    (columns : Fin 29 → Fin 1024 → K) : Fin 256 → K :=
  coefficientFoldLayer 256 alpha (gammaBatchedMessage gamma columns)

/-- The serialized final vector factors definitionally through the complete
gamma-batched message. -/
theorem explicit_final_factors_through_batched_message
    (alpha gamma : K) (columns : Fin 29 → Fin 1024 → K) :
    explicitFinalProjection alpha gamma columns =
      coefficientFoldLayer 256 alpha (gammaBatchedMessage gamma columns) := by
  rfl

/-- Publishing all 256 folded coefficients adds no coordinate when the
coefficientwise batched-message difference is zero. -/
theorem explicit_final_difference_zero
    (alpha : K) (deltaRgamma : Fin 1024 → K)
    (hzero : deltaRgamma = 0) :
    coefficientFoldLayer 256 alpha deltaRgamma = 0 := by
  subst deltaRgamma
  funext coefficient
  simp [coefficientFoldLayer]

/-- Concrete kernel inclusion for the two complete 29-lane V6 messages. -/
theorem batched_message_kernel_le_explicit_final_kernel
    (alpha gamma : K)
    (left right : Fin 29 → Fin 1024 → K)
    (hbatched : gammaBatchedMessage gamma left =
      gammaBatchedMessage gamma right) :
    explicitFinalProjection alpha gamma left =
      explicitFinalProjection alpha gamma right := by
  simp only [explicitFinalProjection, hbatched]

/-- Any later deterministic observer of the published 256-vector also
factors through the complete batched-message projection. -/
theorem final_observer_kernel_inclusion
    {View : Type*} (observe : (Fin 256 → K) → View)
    (alpha gamma : K)
    (left right : Fin 29 → Fin 1024 → K)
    (hbatched : gammaBatchedMessage gamma left =
      gammaBatchedMessage gamma right) :
    observe (explicitFinalProjection alpha gamma left) =
      observe (explicitFinalProjection alpha gamma right) := by
  rw [batched_message_kernel_le_explicit_final_kernel alpha gamma left right hbatched]

#print axioms explicit_final_difference_zero
#print axioms batched_message_kernel_le_explicit_final_kernel
#print axioms final_observer_kernel_inclusion

end AspisV6HidingFinalFactorization

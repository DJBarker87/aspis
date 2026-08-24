import AspisFormal.V5FriRelationCandidateBridge

/-!
# V6 relation-fold algebra

The V6 blueprint needs one algebraic identity at four successive sizes:

* the committed `1024 -> 256` fold; and
* the relation-only `256 -> 64 -> 16 -> 4` folds.

This is not new algebra.  The generic V5 relation proof already establishes,
for every arity-four layer, that the degree-six relation message has the
incoming dot product as its boundary and the folded dot product as its value
at the fresh challenge.  This file records the exact V6 instantiation without
copying that proof.
-/

namespace AspisV6RelationFold

open AspisV5ComponentCConcreteFoldLinearity
open AspisV5ComponentCRelationRowLinearity
open AspisV5FriRelationCandidateBridge
open AspisV5RelationSumcheckSoundness

variable {K : Type*} [Field K]

/-- The one reusable identity behind all four V6 relation stages. -/
theorem boundary_and_folded_evaluation
    (n : Nat) (alpha : K) (weights values : Fin (4 * n) → K)
    (hfour : (4 : K) ≠ 0) :
    relationBoundary (polynomialForExtension n weights values) =
        ∑ i, values i * weights i ∧
      (relationPolynomial (polynomialForExtension n weights values)).eval alpha =
        ∑ fibre,
          coefficientFoldLayer n alpha values fibre *
            dualWeightFoldLayer n alpha weights fibre := by
  exact ⟨relationBoundary_polynomialForExtension n weights values hfour,
    relationPolynomial_polynomialForExtension_eval n alpha weights values⟩

/-- Every honest message used by the identity is a polynomial of degree at
most six, so a dishonest nonzero difference has at most six roots over a
field. -/
theorem honest_relation_message_degree_le_six
    (n : Nat) (weights values : Fin (4 * n) → K) :
    (relationPolynomial (polynomialForExtension n weights values)).natDegree ≤ 6 :=
  natDegree_relationPolynomial_le_six _

/-- The four instantiations have exactly the V6 coefficient dimensions. -/
theorem exact_v6_relation_fold_sizes :
    4 * 256 = 1024 ∧
      4 * 64 = 256 ∧
      4 * 16 = 64 ∧
      4 * 4 = 16 := by
  norm_num

#print axioms boundary_and_folded_evaluation
#print axioms honest_relation_message_degree_le_six
#print axioms exact_v6_relation_fold_sizes

end AspisV6RelationFold

import RuntimeFourRoundLaterRelease
import AspisFormal.V5ComponentCConcreteFoldLinearity

set_option autoImplicit false

open Aeneas Aeneas.Std Result

namespace aspis_prover.ComponentCRuntimeLaterReleasedMaintainedBridge

open aspis_prover
open AspisV5ComponentCConcreteFoldLinearity
open ComponentCRuntimeLaterRoundLoopCorrespondence

abbrev RawQM31 := aspis_core.field.QM31

/-- A flattened source-authentic runtime later vector is exactly the
maintained `readFibres` map whenever the generated fibre words decode to the
same finite query map and the generated folded vector decodes pointwise to the
maintained layer.  Traversal and slot order are conclusions, not premises. -/
theorem released_fibres_prefix_decodes_to_readFibres
    {K : Type*} [Field K]
    (view : RawQM31 → K)
    (folded : Slice RawQM31)
    (fibres : alloc.vec.Vec Std.U32)
    (n : Nat)
    (queries : Fin fibres.val.length → Fin n)
    (layer : Fin (4 * n) → K)
    (hqueries : ∀ index : Fin fibres.val.length,
      (queries index).val = fibres.val[index.val]!.val)
    (hfolded : ∀ row : Fin (4 * n),
      view folded.val[row.val]! = layer row) :
    ∀ (index : Fin fibres.val.length) (slot : Fin 4),
      view ((releasedFibresPrefix folded fibres fibres.val.length)[
        4 * index.val + slot.val]!) =
      readFibres queries layer (index, slot) := by
  intro index slot
  rw [releasedFibresPrefix_get folded fibres fibres.val.length
    index.val slot.val index.isLt slot.isLt]
  have hrow := hfolded (childIndex (queries index) slot)
  simpa [readFibres_apply, hqueries index] using hrow

#print axioms released_fibres_prefix_decodes_to_readFibres

end aspis_prover.ComponentCRuntimeLaterReleasedMaintainedBridge

import AspisFormal.Pool.V7PackedLimbDecoder

/-! Exact slot/column/helper/basis indices for Tag-73 packed fibres. -/

set_option autoImplicit false

namespace AspisPool.V7PackedFibreIndices

/-- C1 is slot-major and then column-major. -/
def c1LimbIndex (slot : Fin 4) (column : Fin 26) : Fin 104 :=
  ⟨slot.val * 26 + column.val, by
    have hslot := slot.isLt
    have hcolumn := column.isLt
    omega⟩

/-- C2 is helper-major, then slot-major, with four tower limbs per value. -/
def c2LimbIndex (helper : Fin 3) (slot basis : Fin 4) : Fin 48 :=
  ⟨(helper.val * 4 + slot.val) * 4 + basis.val, by
    have hhelper := helper.isLt
    have hslot := slot.isLt
    have hbasis := basis.isLt
    omega⟩

theorem c1_index_exact (slot : Fin 4) (column : Fin 26) :
    (c1LimbIndex slot column).val = slot.val * 26 + column.val := rfl

theorem c2_index_exact (helper : Fin 3) (slot basis : Fin 4) :
    (c2LimbIndex helper slot basis).val =
      (helper.val * 4 + slot.val) * 4 + basis.val := rfl

#print axioms c1_index_exact
#print axioms c2_index_exact

end AspisPool.V7PackedFibreIndices

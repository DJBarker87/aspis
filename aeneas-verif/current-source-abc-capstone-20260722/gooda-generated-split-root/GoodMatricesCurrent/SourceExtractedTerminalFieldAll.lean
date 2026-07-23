import GoodMatricesCurrent.SourceExtractedTerminalFieldPreparedMul

/-! The complete current-source field correspondence layer. -/

open Aeneas Aeneas.Std Result

namespace Aeneas.Std

theorem Array.index_usize_eq_ok_of_getElem_eq
    {α : Type u} {n : Usize} (values : Array α n) (index : Usize)
    (hbound : index.val < values.val.length)
    (value : α)
    (hvalue : values.val[index.val]'hbound = value) :
    Array.index_usize values index = .ok value := by
  unfold Array.index_usize
  rw [Array.getElem?_Usize_eq]
  rw [List.getElem?_eq_getElem hbound]
  exact congrArg Result.ok hvalue

theorem Array.update_eq_ok
    {α : Type u} {n : Usize} (values : Array α n) (index : Usize)
    (value : α) (hbound : index.val < values.val.length) :
    Array.update values index value = .ok (Array.set values index value) := by
  unfold Array.update Array.set
  rw [Array.getElem?_Usize_eq]
  rw [List.getElem?_eq_getElem hbound]

end Aeneas.Std

import V7Tag73CurrentHelpersOpaque.FunsExternal

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
namespace staged_circle_tables

def circle_pair (x y : Std.U32) : Array Std.U32 2#usize :=
  ⟨[x, y], by rfl⟩

def append16 {T : Type} (left right : Array T 16#usize) :
    Array T 32#usize :=
  ⟨left.val ++ right.val, by
    simp only [List.length_append, Array.length_eq]
    rfl⟩

def append32 {T : Type} (left right : Array T 32#usize) :
    Array T 64#usize :=
  ⟨left.val ++ right.val, by
    simp only [List.length_append, Array.length_eq]
    rfl⟩

def append64 {T : Type} (left right : Array T 64#usize) :
    Array T 128#usize :=
  ⟨left.val ++ right.val, by
    simp only [List.length_append, Array.length_eq]
    rfl⟩

def append128 {T : Type} (left right : Array T 128#usize) :
    Array T 256#usize :=
  ⟨left.val ++ right.val, by
    simp only [List.length_append, Array.length_eq]
    rfl⟩

def append256 {T : Type} (left right : Array T 256#usize) :
    Array T 512#usize :=
  ⟨left.val ++ right.val, by
    simp only [List.length_append, Array.length_eq]
    rfl⟩

end staged_circle_tables
end V7Tag73CurrentHelpersOpaque

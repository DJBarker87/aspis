import Mathlib

/-!
# Arithmetic equivalences used by the selected V7 Pool CU path

These are relation-preservation theorems, not performance assumptions.  The
first pair proves that the exact four-term QM31 tower map may factor a shared
selector after packing.  The second pair proves the generated Copy-weight
specialization when every weight is exactly zero or one.  Rust/Aeneas source
bridges separately identify the production functions and generated tables
with these pure operations.
-/

set_option autoImplicit false

namespace AspisPool.V7PairForestCuArithmeticEquivalences

/-- The mathematical four-value map implemented by `qm31_pack_base4`:
`v0 + i*v1 + u*v2 + i*u*v3`. -/
def packBase4 {K : Type*} [CommRing K]
    (i u : K) (values : Fin 4 → K) : K :=
  values 0 + i * values 1 + u * values 2 + i * u * values 3

/-- Packing four selector-weighted differences is exactly one selector
multiplication after packing the differences. -/
theorem packBase4_shared_selector
    {K : Type*} [CommRing K]
    (i u selector : K) (differences : Fin 4 → K) :
    packBase4 i u (fun lane => selector * differences lane) =
      selector * packBase4 i u differences := by
  simp only [packBase4]
  ring

/-- Literal pre-optimisation digest accumulation over every public binding. -/
def literalDigestAccumulation
    {Binding K : Type*} [Fintype Binding] [CommRing K]
    (i u : K)
    (selector : Binding → K)
    (difference : Binding → Fin 4 → K) : K :=
  ∑ binding,
    packBase4 i u (fun lane => selector binding * difference binding lane)

/-- Selected accumulation after factoring the selector from each group. -/
def factoredDigestAccumulation
    {Binding K : Type*} [Fintype Binding] [CommRing K]
    (i u : K)
    (selector : Binding → K)
    (difference : Binding → Fin 4 → K) : K :=
  ∑ binding, selector binding * packBase4 i u (difference binding)

/-- The complete accumulation is unchanged for any number of transfer or
withdrawal bindings and at every off-domain point. -/
theorem factoredDigestAccumulation_eq_literal
    {Binding K : Type*} [Fintype Binding] [CommRing K]
    (i u : K)
    (selector : Binding → K)
    (difference : Binding → Fin 4 → K) :
    factoredDigestAccumulation i u selector difference =
      literalDigestAccumulation i u selector difference := by
  simp only [factoredDigestAccumulation, literalDigestAccumulation]
  apply Finset.sum_congr rfl
  intro binding _member
  exact (packBase4_shared_selector i u (selector binding)
    (difference binding)).symm

/-- Runtime skip/add operation used after the generated table has established
that one endpoint weight is binary.  The nonbinary branch is deliberately
unspecified here: production source rejects it as unreachable. -/
def addBinaryWeight
    {K : Type*} [DecidableEq K] [Zero K] [Add K]
    (sum selector weight : K) : K :=
  if weight = 0 then sum else sum + selector

/-- Skip/add is exactly the old multiply/add expression for a binary weight. -/
theorem addBinaryWeight_eq_mul
    {K : Type*} [CommRing K] [Nontrivial K] [DecidableEq K]
    (sum selector weight : K)
    (binary : weight = 0 ∨ weight = 1) :
    addBinaryWeight sum selector weight = sum + selector * weight := by
  rcases binary with rfl | rfl <;> simp [addBinaryWeight]

/-- Pointwise binary table evidence lifts to the complete Copy-weight sum. -/
theorem binaryWeightAccumulation_eq
    {Endpoint K : Type*} [Fintype Endpoint] [CommRing K] [Nontrivial K]
    [DecidableEq K]
    (selector weight : Endpoint → K)
    (binary : ∀ endpoint, weight endpoint = 0 ∨ weight endpoint = 1) :
    (∑ endpoint,
        (if weight endpoint = 0 then 0 else selector endpoint)) =
      ∑ endpoint, selector endpoint * weight endpoint := by
  apply Finset.sum_congr rfl
  intro endpoint _member
  rcases binary endpoint with zero | one
  · simp [zero]
  · simp [one]

/-- Pure model of the selected 32-entry direct-mapped endpoint-selector
cache.  The slot function is deliberately arbitrary: the proof below makes
collisions a performance concern only. -/
structure SelectorCache (Row K : Type*) where
  rows : Fin 32 → Option Row
  values : Fin 32 → K

/-- Every occupied tag carries the literal selector for that exact row. -/
def SelectorCache.Sound
    {Row K : Type*}
    (literal : Row → K) (cache : SelectorCache Row K) : Prop :=
  ∀ slot row, cache.rows slot = some row → cache.values slot = literal row

/-- One exact-tag lookup.  A miss computes the literal value and replaces
both the tag and value in the chosen slot. -/
def selectorWithCache
    {Row K : Type*} [DecidableEq Row]
    (slotOf : Row → Fin 32)
    (literal : Row → K)
    (cache : SelectorCache Row K)
    (row : Row) : K × SelectorCache Row K :=
  let slot := slotOf row
  if cache.rows slot = some row then
    (cache.values slot, cache)
  else
    let value := literal row
    (value, {
      rows := Function.update cache.rows slot (some row)
      values := Function.update cache.values slot value
    })

/-- On every hit or miss, the cached lookup returns the same selector as a
fresh literal evaluation. -/
theorem selectorWithCache_value_eq_literal
    {Row K : Type*} [DecidableEq Row]
    (slotOf : Row → Fin 32)
    (literal : Row → K)
    (cache : SelectorCache Row K)
    (sound : cache.Sound literal)
    (row : Row) :
    (selectorWithCache slotOf literal cache row).1 = literal row := by
  simp only [selectorWithCache]
  split
  · rename_i hit
    exact sound (slotOf row) row hit
  · rfl

/-- A lookup preserves the exact-tag invariant.  In particular, any two rows
that collide in the 32-slot map merely cause a miss and replacement. -/
theorem selectorWithCache_preserves_sound
    {Row K : Type*} [DecidableEq Row]
    (slotOf : Row → Fin 32)
    (literal : Row → K)
    (cache : SelectorCache Row K)
    (sound : cache.Sound literal)
    (row : Row) :
    (selectorWithCache slotOf literal cache row).2.Sound literal := by
  simp only [selectorWithCache]
  split
  · exact sound
  · intro slot tagged tag_eq
    by_cases same_slot : slot = slotOf row
    · subst slot
      simp at tag_eq
      subst tagged
      simp
    · have old_tag : cache.rows slot = some tagged := by
        simpa [Function.update, same_slot] using tag_eq
      have old_value := sound slot tagged old_tag
      simpa [Function.update, same_slot] using old_value

#print axioms packBase4_shared_selector
#print axioms factoredDigestAccumulation_eq_literal
#print axioms addBinaryWeight_eq_mul
#print axioms binaryWeightAccumulation_eq
#print axioms selectorWithCache_value_eq_literal
#print axioms selectorWithCache_preserves_sound

end AspisPool.V7PairForestCuArithmeticEquivalences

import V7FirstCompactK13RawScheduleBridge
import V5QuerySamplerGeneratedSemantics

/-!
# Current Tag-73 inner-sampler increment bridge

The current extraction differs from the older verified sampler body in one
place: Rust's checked `draws += 1` is translated as fallible scalar addition,
whereas the older extraction used lifted wrapping addition.  The loop admits
this branch only below the fixed 64-draw cap.  The theorems below prove that the
checked operation therefore cannot fail and returns exactly the older value.
-/

open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false

namespace V7FirstCompactSamplerInnerBridge

/-- Below the deployed cap, the current checked draw increment succeeds and
increments the natural value exactly. -/
theorem current_checked_draw_increment_exact
    (draws : Std.Usize) (active : draws.val < 64) :
    draws + 1#usize ⦃ next => next.val = draws.val + 1 ⦄ := by
  apply Std.Usize.add_spec
  have : draws.val + 1 ≤ 64 := by omega
  scalar_tac

/-- The current checked increment returns the same scalar as the wrapping
increment used by the already verified generated sampler semantics. -/
theorem current_checked_draw_increment_matches_verified
    (draws : Std.Usize) (active : draws.val < 64) :
    (draws + 1#usize : Result Std.Usize) =
      Result.ok (Std.Usize.wrapping_add draws 1#usize) := by
  have spec := current_checked_draw_increment_exact draws active
  obtain ⟨next, run, value⟩ := Aeneas.Std.WP.spec_imp_exists spec
  rw [run]
  congr 1
  apply UScalar.eq_of_val_eq
  rw [value]
  simp [Std.Usize.wrapping_add_val_eq]
  symm
  apply Nat.mod_eq_of_lt
  have : draws.val + 1 ≤ 64 := by omega
  scalar_tac

#print axioms current_checked_draw_increment_exact
#print axioms current_checked_draw_increment_matches_verified

end V7FirstCompactSamplerInnerBridge

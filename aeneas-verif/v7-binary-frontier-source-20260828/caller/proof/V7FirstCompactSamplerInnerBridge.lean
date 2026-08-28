import V7FirstCompactK13RawScheduleBridge
import V5QuerySamplerGeneratedSemantics
import AspisFormal.K1.V7Tag73SecureCircleMap

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

open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SecureCircleMap

/-- The literal Rust `u32` mask used by q16 is exactly K1.3's mathematical
reduction modulo `2^18`; there is no codec or signedness boundary here. -/
theorem current_q16_mask_is_exact (word : Std.U32) :
    (word &&& 262143#u32).val = q16Candidate word.val := by
  rw [UScalar.val_and]
  norm_num
  exact bitAnd_low18_eq_q16Candidate word.val

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
#print axioms current_q16_mask_is_exact

end V7FirstCompactSamplerInnerBridge

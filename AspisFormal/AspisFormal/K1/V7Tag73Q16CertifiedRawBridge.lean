import AspisFormal.K1.V7Tag73K13IdealErrorLedger
import AspisFormal.K1.V7Tag73Q16CertifiedCountBridge

/-!
# Certified raw q16 ledger bridge for Tag 73

The executable first-cap-203 proof counts successful schedules through the
semantic recurrence.  The generated release certificate evaluates exactly
that recurrence, while the small K1.3 ledger stores its frozen decimal value.
This file joins those two equalities and nothing else.

In particular, there is no proof-of-work division or normalization here.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73Q16CertifiedRawBridge

open scoped ENNReal
open AspisK1.V7Tag73K13IdealErrorLedger
open AspisK1.V7Tag73Q16CertifiedCountBridge
open AspisK1.V7Tag73Q16CompactScheduleCount
open AspisV7CompactFrontierCertificate

/-- The semantic successful-schedule count is the exact integer frozen in
the raw K1.3 ledger. -/
theorem semanticCompactFavourable_eq_exactK13CompactFavourable :
    semanticCompactFavourable = exactK13CompactFavourable := by
  calc
    semanticCompactFavourable = compactFavourable :=
      semanticCompactFavourable_eq_compactFavourable
    _ = exactK13CompactFavourable := by
      rw [compactFavourable_eq_exact]
      rfl

/-- Consequently the certified semantic q16 ratio is definitionally the raw
q16 term charged by K1.3. -/
theorem semantic_choose_ratio_eq_exactQ16IdealRawError :
    (Nat.choose 9557 16 : ENNReal) /
        (semanticCompactFavourable : ENNReal) =
      exactQ16IdealRawError := by
  unfold exactQ16IdealRawError
  rw [semanticCompactFavourable_eq_exactK13CompactFavourable]

#print axioms semanticCompactFavourable_eq_exactK13CompactFavourable
#print axioms semantic_choose_ratio_eq_exactQ16IdealRawError

end AspisK1.V7Tag73Q16CertifiedRawBridge

import AspisFormal.K1.V7Tag73K13IdealErrorLedger
import AspisFormal.K1.V7Tag73Q16CompactScheduleCount
import AspisFormal.V7CompactFrontierCertificate

/-!
# Exact q16 semantic-count certificate bridge

The q16 probability theorem counts the semantic depth-18, sixteen-leaf
frontier shapes admitted at cap 203.  The release ledger stores the same
count as a frozen decimal so that ordinary K1 builds do not import the large
generated frontier certificate.  This module closes that intentional seam:
the semantic recurrence, generated cap-203 certificate, and frozen ledger
integer are exactly equal.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisK1.V7Tag73Q16CountCertificateBridge

open AspisK1.V7Tag73K13IdealErrorLedger
open AspisK1.V7Tag73Q16CompactScheduleCount
open AspisV6CompactFrontierPrefactorization
open AspisV6CompactFrontierRecurrence
open AspisV6CompactFrontierSemantics
open AspisV7CompactFrontierCertificate

noncomputable section

/-- The semantic favourable-schedule denominator consumed by the q16
probability theorem is exactly the frozen release denominator. -/
theorem semanticCompactFavourable_eq_exactK13CompactFavourable :
    semanticCompactFavourable = exactK13CompactFavourable := by
  calc
    semanticCompactFavourable =
        ∑ frontier ∈ Finset.range 204,
          semanticCount 18 16 frontier := rfl
    _ = ∑ frontier ∈ Finset.range 204,
          concreteFrontierCount 18 16 frontier := by
      apply Finset.sum_congr rfl
      intro frontier _member
      rw [← rawFrontierCount_eq_semanticCount,
        rawFrontierCount_eq_concreteFrontierCount]
    _ = compactFavourable := compactFavourable_eq_recurrence.symm
    _ = exactK13CompactFavourable := by
      rw [compactFavourable_eq_exact]
      rfl

end

#print axioms semanticCompactFavourable_eq_exactK13CompactFavourable

end AspisK1.V7Tag73Q16CountCertificateBridge

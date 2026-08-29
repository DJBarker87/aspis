import AspisFormal.K1.V7Tag73Q16SemanticProbability
import AspisFormal.V7CompactFrontierCertificate

/-!
# Certified cap-203 schedule-count bridge for Tag-73

The semantic q16 development counts admitted schedules through the executable
binary-frontier recurrence.  The release certificate evaluates the same
recurrence to one frozen natural number.  This module proves that those two
counts are identical.

It intentionally contains no proof-of-work normalization and no false-
acceptance theorem.  K1.3 consumes the resulting raw compact-schedule ratio.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AspisK1.V7Tag73Q16CertifiedCountBridge

open AspisK1.V7Tag73Q16CompactScheduleCount
open AspisK1.V7Tag73Q16SemanticFrontierBridge
open AspisV7BinaryFrontier
open AspisV7CompactFrontierCertificate

/-- The semantic cap-203 schedule count is exactly the independently
generated release-certificate value. -/
theorem semanticCompactFavourable_eq_compactFavourable :
    semanticCompactFavourable = compactFavourable := by
  calc
    semanticCompactFavourable =
        ∑ frontierCount ∈ Finset.range 204,
          concreteFrontierCount 18 16 frontierCount := by
      unfold semanticCompactFavourable
      apply Finset.sum_congr rfl
      intro frontierCount _membership
      exact
        (rawFrontierCount_eq_semanticCount 18 16 frontierCount).symm.trans
          (rawFrontierCount_eq_concreteFrontierCount 18 16 frontierCount)
    _ = compactFavourable := compactFavourable_eq_recurrence.symm

#print axioms semanticCompactFavourable_eq_compactFavourable

end AspisK1.V7Tag73Q16CertifiedCountBridge

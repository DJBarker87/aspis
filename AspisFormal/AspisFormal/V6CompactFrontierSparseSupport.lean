import AspisFormal.V6CompactFrontierSupport

/-!
# Sparse evaluation of the compact-frontier recurrence

The exact support theorem lets the numeric release certificate remove every
convolution term that is already proved zero.  This avoids asking a general
normalizer to explore impossible recurrence branches.
-/

set_option autoImplicit false

namespace AspisV6CompactFrontierSupport

open AspisV6CompactFrontierRecurrence

/-- Previous-depth frontier splits that can survive the exact support bound. -/
def supportedSplitFrontiers
    (depth leftSelected rightSelected frontier : Nat) : Finset Nat :=
  (Finset.range (frontier + 1)).filter fun leftFrontier =>
    leftFrontier ≤ frontierSupportMax depth leftSelected ∧
      frontier - leftFrontier ≤ frontierSupportMax depth rightSelected

/-- The support rectangle is the concrete closed interval forced by the two
upper bounds.  This form lets numeric certificates expand only live terms. -/
theorem supportedSplitFrontiers_eq_Icc
    (depth leftSelected rightSelected frontier : Nat) :
    supportedSplitFrontiers depth leftSelected rightSelected frontier =
      Finset.Icc
        (frontier - frontierSupportMax depth rightSelected)
        (min frontier (frontierSupportMax depth leftSelected)) := by
  ext leftFrontier
  simp [supportedSplitFrontiers]
  omega

/-- Filtering a convolution to the exact support rectangle changes no value. -/
theorem frontierConvolution_eq_supported
    (depth leftSelected rightSelected frontier : Nat) :
    (∑ leftFrontier ∈ Finset.range (frontier + 1),
        frontierCoeff depth leftSelected leftFrontier *
          frontierCoeff depth rightSelected (frontier - leftFrontier)) =
      ∑ leftFrontier ∈
          supportedSplitFrontiers depth leftSelected rightSelected frontier,
        frontierCoeff depth leftSelected leftFrontier *
          frontierCoeff depth rightSelected (frontier - leftFrontier) := by
  rw [supportedSplitFrontiers, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro leftFrontier leftMember
  by_cases supported :
      leftFrontier ≤ frontierSupportMax depth leftSelected ∧
        frontier - leftFrontier ≤ frontierSupportMax depth rightSelected
  · simp [supported]
  · simp only [supported, ↓reduceIte]
    by_cases leftWithin :
        leftFrontier ≤ frontierSupportMax depth leftSelected
    · have rightAbove :
          frontierSupportMax depth rightSelected <
            frontier - leftFrontier := by
        omega
      rw [frontierCoeff_eq_zero_of_frontier_gt_support
        depth rightSelected (frontier - leftFrontier) rightAbove]
      simp
    · have leftAbove :
          frontierSupportMax depth leftSelected < leftFrontier := by
        omega
      rw [frontierCoeff_eq_zero_of_frontier_gt_support
        depth leftSelected leftFrontier leftAbove]
      simp

/-- One unfolded recurrence whose convolutions are already restricted to the
proved support rectangle. -/
theorem frontierCoeff_succ_eq_supported
    (depth selected frontier : Nat) :
    frontierCoeff (depth + 1) selected frontier =
      (if frontier = 0 then 0
       else frontierCoeff depth selected (frontier - 1)) +
      ∑ offset ∈ Finset.range (selected - 1),
        ∑ leftFrontier ∈ supportedSplitFrontiers depth (offset + 1)
            (selected - (offset + 1)) frontier,
          frontierCoeff depth (offset + 1) leftFrontier *
            frontierCoeff depth (selected - (offset + 1))
              (frontier - leftFrontier) := by
  rw [frontierCoeff]
  apply congrArg (fun tail =>
    (if frontier = 0 then 0
     else frontierCoeff depth selected (frontier - 1)) + tail)
  apply Finset.sum_congr rfl
  intro offset offsetMember
  exact frontierConvolution_eq_supported depth (offset + 1)
    (selected - (offset + 1)) frontier

#print axioms frontierConvolution_eq_supported
#print axioms frontierCoeff_succ_eq_supported
#print axioms supportedSplitFrontiers_eq_Icc

end AspisV6CompactFrontierSupport

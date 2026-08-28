import Mathlib

/-!
# First-compact query selection

The prover must not be allowed to supply an arbitrary compact retry counter.
This file states the exact deterministic rule: scan a public candidate stream
and use its first compact schedule. It proves uniqueness, proves that no
earlier compact candidate can be skipped, and proves equivariance under every
permutation that preserves compactness. The last fact is the finite symmetry
needed to conclude uniformity over compact schedules when the random-oracle
candidates are independent and uniform.

Random-oracle independence and the concrete hash-to-query decoder remain
explicit transcript assumptions; they are not manufactured here.
-/

namespace AspisV6FirstCompactSampler

variable {Schedule : Type*} {attempts : Nat}

/-- `selected` is the value at the first compact position in `candidates`. -/
def FirstCompactResult
    (compact : Schedule → Prop)
    (candidates : Fin attempts → Schedule)
    (selected : Schedule) : Prop :=
  ∃ position : Fin attempts,
    candidates position = selected ∧
      compact selected ∧
      ∀ earlier : Fin attempts, earlier.val < position.val →
        ¬ compact (candidates earlier)

theorem firstCompactResult_cannot_skip
    (compact : Schedule → Prop)
    (candidates : Fin attempts → Schedule)
    (selected : Schedule)
    (hresult : FirstCompactResult compact candidates selected) :
    ∃ position : Fin attempts,
      candidates position = selected ∧
        compact selected ∧
        ∀ earlier : Fin attempts, earlier.val < position.val →
          ¬ compact (candidates earlier) :=
  hresult

theorem firstCompactResult_unique
    (compact : Schedule → Prop)
    (candidates : Fin attempts → Schedule)
    {left right : Schedule}
    (hleft : FirstCompactResult compact candidates left)
    (hright : FirstCompactResult compact candidates right) :
    left = right := by
  obtain ⟨leftPosition, hleftValue, hleftCompact, hleftEarlier⟩ := hleft
  obtain ⟨rightPosition, hrightValue, hrightCompact, hrightEarlier⟩ := hright
  rcases lt_trichotomy leftPosition.val rightPosition.val with hlt | heq | hgt
  · have hcompactAtLeft : compact (candidates leftPosition) := by
      rw [hleftValue]
      exact hleftCompact
    exact False.elim (hrightEarlier leftPosition hlt hcompactAtLeft)
  · have hpositions : leftPosition = rightPosition := Fin.ext heq
    rw [hpositions] at hleftValue
    exact hleftValue.symm.trans hrightValue
  · have hcompactAtRight : compact (candidates rightPosition) := by
      rw [hrightValue]
      exact hrightCompact
    exact False.elim (hleftEarlier rightPosition hgt hcompactAtRight)

/-- If candidate zero is compact, it is necessarily the selected result of
the existing first-compact rule.  This is the deterministic fact needed by an
honest prover that searches for a transcript whose first candidate is already
compact: the verifier rule and accepted language are unchanged, and no later
candidate is skipped.  This theorem deliberately makes no probabilistic or
zero-knowledge claim about how such a transcript is found. -/
theorem compact_candidate_zero_is_first
    [NeZero attempts]
    (compact : Schedule → Prop)
    (candidates : Fin attempts → Schedule)
    (hzero : compact (candidates 0)) :
    FirstCompactResult compact candidates (candidates 0) := by
  refine ⟨0, rfl, hzero, ?_⟩
  intro earlier hearlier
  change earlier.val < 0 at hearlier
  omega

/-- A first-compact result cannot differ from compact candidate zero. -/
theorem firstCompactResult_eq_candidate_zero_of_compact
    [NeZero attempts]
    (compact : Schedule → Prop)
    (candidates : Fin attempts → Schedule)
    (selected : Schedule)
    (hzero : compact (candidates 0))
    (hselected : FirstCompactResult compact candidates selected) :
    selected = candidates 0 := by
  exact firstCompactResult_unique compact candidates hselected
    (compact_candidate_zero_is_first compact candidates hzero)

/-- Applying the same compactness-preserving permutation to every candidate
also applies it to the unique selected result. This is the symmetry used by
the uniform-conditioned-on-compact argument. -/
theorem firstCompactResult_equivariant
    (compact : Schedule → Prop)
    (candidates : Fin attempts → Schedule)
    (selected : Schedule)
    (permutation : Schedule ≃ Schedule)
    (hpreserves : ∀ schedule,
      compact (permutation schedule) ↔ compact schedule)
    (hresult : FirstCompactResult compact candidates selected) :
    FirstCompactResult compact (fun position => permutation (candidates position))
      (permutation selected) := by
  obtain ⟨position, hvalue, hcompact, hearlier⟩ := hresult
  refine ⟨position, ?_, (hpreserves selected).2 hcompact, ?_⟩
  · exact congrArg permutation hvalue
  · intro earlier hlt hearlierCompact
    exact hearlier earlier hlt ((hpreserves (candidates earlier)).1 hearlierCompact)

/-- There is no selected output when every bounded candidate is noncompact. -/
theorem no_firstCompactResult_of_all_noncompact
    (compact : Schedule → Prop)
    (candidates : Fin attempts → Schedule)
    (hnone : ∀ position, ¬ compact (candidates position)) :
    ¬ ∃ selected, FirstCompactResult compact candidates selected := by
  rintro ⟨selected, position, _hvalue, hcompact, _hearlier⟩
  apply hnone position
  rw [_hvalue]
  exact hcompact

#print axioms firstCompactResult_unique
#print axioms compact_candidate_zero_is_first
#print axioms firstCompactResult_eq_candidate_zero_of_compact
#print axioms firstCompactResult_equivariant
#print axioms no_firstCompactResult_of_all_noncompact

end AspisV6FirstCompactSampler

import ComponentBSamplerMixingEvaluateUnified20260722

open Aeneas Aeneas.Std Result ControlFlow Error

namespace ComponentBGenerated.v5_sumcheck_mask

private abbrev QM31 := aspis_core.field.QM31
private abbrev Polynomial := Array QM31 28#usize

private def storedRound
    (mask : V5SumcheckMask) (round : Std.Usize)
    (hround : round.val < 10) : Polynomial :=
  mask.zero_boundary_rounds.val[round.val]'(by simpa using hround)

theorem generated_round_polynomial_out_of_range
    (mask : V5SumcheckMask) (round : Std.Usize) (incoming : QM31)
    (hround : 10 ≤ round.val) :
    V5SumcheckMask.round_polynomial mask round incoming = ok none := by
  have hnone : mask.zero_boundary_rounds.val[round.val]? = none := by
    simp [hround]
  simp [V5SumcheckMask.round_polynomial, lift, Array.to_slice,
    core.slice.Slice.get, core.slice.index.Usize.get, hnone]

theorem generated_round_polynomial_exact_update
    (mask : V5SumcheckMask) (round : Std.Usize) (incoming half updated : QM31)
    (hround : round.val < 10)
    (hhalf : aspis_core.field.QM31.half incoming = ok half)
    (hadd : aspis_core.field.QM31.add (storedRound mask round hround).val[0] half =
      ok updated) :
    V5SumcheckMask.round_polynomial mask round incoming =
      ok (some ((storedRound mask round hround).set 0#usize updated)) := by
  have hsome : mask.zero_boundary_rounds.val[round.val]? =
      some (storedRound mask round hround) := by
    simp [storedRound, hround]
  simp [V5SumcheckMask.round_polynomial, lift, Array.to_slice,
    core.slice.Slice.get, core.slice.index.Usize.get, hsome, hhalf, hadd,
    Array.index_usize, Array.update]
  apply Subtype.ext
  rfl

#print axioms generated_round_polynomial_out_of_range
#print axioms generated_round_polynomial_exact_update

end ComponentBGenerated.v5_sumcheck_mask

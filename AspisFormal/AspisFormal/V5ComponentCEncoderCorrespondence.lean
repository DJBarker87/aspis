import AspisFormal.V5ComponentCSamplerKernel

/-!
# v5 Component C: deployed-encoder / model-encoder correspondence

This leaf closes — as far as it can be closed inside Lean — the deployed
Component-C **encoder** seam.  The model side, in
`V5ComponentCSamplerKernel`, records the Rust-facing obligation as the single
opaque predicate

    RustEncoderMatchesKernelEquiv ell pivot hpivot rustEncode
      :=  rustEncode = componentCEncoderEquiv ell pivot hpivot,

i.e. "the executable encoder equals the abstract pivot-correction linear
equivalence onto `ker ell`".  That premise silently bundles three distinct
facts: the free-index → stored-row *permutation*, the *pivot correction*, and
the identity of the *functional* whose kernel is targeted.  This file
transcribes the actual Rust encoder
(`crates/aspis-prover/src/v5_c_mask.rs :: V5ComponentCLane`) coordinate by
coordinate and **proves** that transcription equal to the model encoder, so
the residual seam shrinks to one syntactic transcription premise.

## What the deployed Rust encoder actually does

`encode_free_coordinates` (paraphrased):

    let pivot = v5_c_pivot_row();                       // least inactive row
    let mut values = [ZERO; 1024];                      // scatter target
    for (i, v) in free.enumerate() {                    // 1023 free coords
        values[free_coordinate_row(i, pivot)] = v;      // place off the pivot
    }
    values[pivot] = -v5_c_inactive_functional(values);  // pivot correction

with

    free_coordinate_row(i, pivot) = if i < pivot { i } else { i + 1 }
    v5_c_inactive_functional(x)   = Σ_{r : inactive_row(masks, r)} x[r]
    v5_c_pivot_row()              = first r with inactive_row(masks, r).

Two facts are pinned here, neither assumed to be row 0:

* the placement `free_coordinate_row(·, pivot)` is **exactly** `Fin.succAbove`
  — there is no bit reversal, natural/ordinary basis conversion, or any other
  reindexing in the encoder (`deployedRow_eq_succAbove`).  The circle-encoder
  bit machinery lives only in the *downstream* `Emat` evaluator, which is a
  separate seam (`RustEvaluatorLinear` / `RustBasisColumnsMatch`), not the
  encoder;
* the pivot is `Finset.min'` of the inactive-row set — the least inactive row,
  which is what the source's `(0..1024).find(inactive)` returns (`pivotC`).
  The deployed schedule's own test shows this value is `0` for the atomic-v3
  masks, but nothing below hard-codes `0`.

The inactive-row set `S` is kept an *arbitrary* nonempty `Finset (Fin 1024)`;
every theorem is universal in `S` and in the field `K`.  Which rows are
inactive is precisely the content of the mask table
`atomic_state_only_copy_inactive_row_masks_v3`, and identifying that table
with a concrete `S` is part of the one named premise below — it is not
assumed.

## What is proved (unconditional, default-heartbeat, kernel-checked)

* `deployedRow_eq_succAbove` — the free-index permutation is `succAbove`.
* `ellC_single` / `ellC_pivot` — the mask functional's value on a standard
  basis vector is the membership indicator, so the least inactive row has
  unit coefficient; this is exactly the unit-pivot hypothesis the model needs,
  *derived* from `pivot ∈ S`.
* `deployedInsert_eq_freeInsert` — the scatter loop equals `Fin.insertNth 0`.
* `deployedEncode_eq_pivotEncoder` — the whole place-then-correct encoder
  equals the model `pivotEncoder (ellC S) (pivotC S hne)`.  This is **not**
  `rfl`: the deployed encoder is built from a `Finset.sum` of single-index
  writes and a `Function.update` correction, and is proved equal to the linear
  map through the pivot-split extensionality lemma.
* `ellC_deployedEncode` — the inserted pivot coordinate forces `ellC S c = 0`.
* `deployedDecode_deployedEncode` / `deployedEncode_deployedDecode` — the Rust
  `free_coordinates` reader is a two-sided inverse on `ker (ellC S)`, so the
  deployed map is a linear equivalence onto the kernel with an explicit,
  executable inverse.
* `deployedEncode_eq_componentCEncoderEquiv` — the deployed encoder commutes
  with the committed `componentCEncoderEquiv` model map.

## The one remaining seam (single named premise)

`RustEncodeMatchesDeployedSpec S hne rustEncode` asserts, pointwise, that the
executable Rust encoder (transported across the QM31 ≃ K field identification)
equals the Lean transcription `deployedEncode S hne`.  This is the sole
irreducible edge: it is a byte-for-byte "Rust source = this specification"
claim (plus the QM31 codec identification, itself a separate named seam
elsewhere), and Lean cannot inspect Rust object code.  Under it,
`rustEncoderMatchesKernelEquiv_of_deployedSpec` discharges the original
`RustEncoderMatchesKernelEquiv` obligation.  Nothing here asserts the premise
for the real binary; and none of the entropy/rejection-sampler, PRG,
QM31-limb-codec, `Emat`-evaluator, PCS-binding, or Fiat–Shamir seams is
touched.
-/

set_option autoImplicit false

namespace AspisV5ComponentCEncoderCorrespondence

open AspisV5ComponentCEmatModel
open AspisV5ComponentCSamplerKernel

/-! ## The deployed free-index → stored-row permutation -/

section Field

variable {K : Type*} [Field K]

/-- Transcription of the Rust `free_coordinate_row(i, pivot)`:
`if i < pivot { i } else { i + 1 }`, embedded into `Fin 1024`.  Written from
the Rust source, independently of `Fin.succAbove`; the equality with
`succAbove` is the theorem immediately below, not the definition. -/
def deployedRow (p : Fin 1024) (i : Fin 1023) : Fin 1024 :=
  if (i : ℕ) < (p : ℕ) then i.castSucc else i.succ

/-- **The deployed placement is exactly `Fin.succAbove`.**  Proved through the
public `succAbove` characterisations, not by `rfl`.  This is the pinning of
the encoder permutation: no bit reversal, no basis conversion, only the hole
around the pivot. -/
theorem deployedRow_eq_succAbove (p : Fin 1024) (i : Fin 1023) :
    deployedRow p i = p.succAbove i := by
  unfold deployedRow
  by_cases h : (i : ℕ) < (p : ℕ)
  · rw [if_pos h]
    exact (Fin.succAbove_of_castSucc_lt p i (by rw [Fin.lt_def]; simpa using h)).symm
  · rw [if_neg h]
    refine (Fin.succAbove_of_le_castSucc p i ?_).symm
    rw [Fin.le_def]; simpa using Nat.not_lt.mp h

/-! ## The mask functional and its least-inactive pivot -/

/-- Exact mathematical specification of `v5_c_inactive_functional`: the sum of
coordinate projections over the inactive-row set `S`.  Rust folds
`x[r]` over the rows selected by the mask table; field addition is
commutative, so the ordered fold equals this `Finset` sum. -/
def ellC (S : Finset (Fin 1024)) : (Fin 1024 → K) →ₗ[K] K :=
  ∑ r ∈ S, LinearMap.proj r

/-- Closed form of the mask functional. -/
theorem ellC_apply (S : Finset (Fin 1024)) (x : Fin 1024 → K) :
    ellC S x = ∑ r ∈ S, x r := by
  simp only [ellC, LinearMap.sum_apply, LinearMap.proj_apply]

/-- The mask functional on a standard basis vector is the membership
indicator of its index. -/
theorem ellC_single (S : Finset (Fin 1024)) (j : Fin 1024) :
    ellC S (Pi.single j (1 : K)) = if j ∈ S then 1 else 0 := by
  rw [ellC_apply, Finset.sum_pi_single']

/-- Exact mathematical specification of `v5_c_pivot_row`: the least inactive
row.  `Finset.min'` is the least element, matching the source's ascending
`find`. -/
def pivotC (S : Finset (Fin 1024)) (hne : S.Nonempty) : Fin 1024 := S.min' hne

/-- The deployed pivot is an inactive row. -/
theorem pivotC_mem (S : Finset (Fin 1024)) (hne : S.Nonempty) : pivotC S hne ∈ S :=
  Finset.min'_mem S hne

/-- **The unit-pivot coefficient, derived — not assumed.**  Because the pivot
is an inactive row, the mask functional reads coefficient `1` there.  This is
exactly the hypothesis `componentCEncoderEquiv` requires. -/
theorem ellC_pivot (S : Finset (Fin 1024)) (hne : S.Nonempty) :
    ellC S (Pi.single (pivotC S hne) (1 : K)) = 1 := by
  rw [ellC_single, if_pos (pivotC_mem S hne)]

/-! ## The deployed scatter and its equality with `freeInsert` -/

/-- Transcription of the Rust scatter loop
`for (i, v) in free { values[free_coordinate_row(i, pivot)] = v }` on a
zero-initialised array: distinct single-index writes, i.e. a sum of
one-point functions supported on the `deployedRow` positions. -/
def deployedInsert (p : Fin 1024) (free : Fin 1023 → K) : Fin 1024 → K :=
  ∑ i : Fin 1023, Pi.single (deployedRow p i) (free i)

/-- The scatter over `succAbove` positions is exactly `Fin.insertNth 0`. -/
theorem sum_single_succAbove (p : Fin 1024) (free : Fin 1023 → K) :
    ∑ i : Fin 1023, Pi.single (p.succAbove i) (free i) = freeInsert p free := by
  refine pivot_free_funext p ?_ (fun k => ?_)
  · rw [Finset.sum_apply, freeInsert_apply_pivot]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    rw [Pi.single_eq_of_ne (Fin.succAbove_ne p i).symm]
  · rw [Finset.sum_apply, freeInsert_apply_succAbove, Finset.sum_eq_single k]
    · rw [Pi.single_eq_same]
    · intro j _ hjk
      rw [Pi.single_eq_of_ne ((Fin.succAbove_right_injective (p := p)).ne hjk).symm]
    · intro hk
      exact absurd (Finset.mem_univ k) hk

/-- **The deployed scatter equals the model placement.**  Uses only that the
permutation is `succAbove`. -/
theorem deployedInsert_eq_freeInsert (p : Fin 1024) (free : Fin 1023 → K) :
    deployedInsert p free = freeInsert p free := by
  unfold deployedInsert
  simp only [deployedRow_eq_succAbove]
  exact sum_single_succAbove p free

/-! ## The deployed encoder and its equality with the model encoder -/

/-- Transcription of the whole `encode_free_coordinates`: scatter the free
coordinates off the pivot, then overwrite the pivot row with the negated mask
functional of the scatter.  The correction is a `Function.update`, mirroring
the Rust index assignment `values[pivot] = ...`. -/
def deployedEncode (S : Finset (Fin 1024)) (hne : S.Nonempty)
    (free : Fin 1023 → K) : Fin 1024 → K :=
  Function.update (deployedInsert (pivotC S hne) free) (pivotC S hne)
    (-ellC S (deployedInsert (pivotC S hne) free))

/-- **The deployed encoder equals the model pivot encoder.**  This is the
central correspondence and is genuinely proved, not definitional: the left
side is a `Function.update` on a `Finset.sum`, the right side the linear map
`freeInsert - ell(freeInsert) • single`, reconciled through the pivot-split
extensionality lemma. -/
theorem deployedEncode_eq_pivotEncoder (S : Finset (Fin 1024)) (hne : S.Nonempty)
    (free : Fin 1023 → K) :
    deployedEncode S hne free = pivotEncoder (ellC S) (pivotC S hne) free := by
  unfold deployedEncode
  rw [deployedInsert_eq_freeInsert, pivotEncoder_apply]
  set p := pivotC S hne
  set c := ellC S (freeInsert p free)
  refine pivot_free_funext p ?_ (fun i => ?_)
  · rw [Function.update_self, Pi.sub_apply, freeInsert_apply_pivot, Pi.smul_apply,
      Pi.single_eq_same, smul_eq_mul, mul_one, zero_sub]
  · rw [Function.update_of_ne (Fin.succAbove_ne p i), Pi.sub_apply, Pi.smul_apply,
      Pi.single_eq_of_ne (Fin.succAbove_ne p i), smul_zero, sub_zero]

/-- **The inserted pivot coordinate enforces the kernel equation.**  The
deployed encoder always lands on the hyperplane `ellC S c = 0`. -/
theorem ellC_deployedEncode (S : Finset (Fin 1024)) (hne : S.Nonempty)
    (free : Fin 1023 → K) :
    ellC S (deployedEncode S hne free) = 0 := by
  rw [deployedEncode_eq_pivotEncoder]
  exact ell_pivotEncoder (ellC S) (pivotC S hne) (ellC_pivot S hne) free

/-- Kernel-membership form of `ellC_deployedEncode`. -/
theorem deployedEncode_mem_ker (S : Finset (Fin 1024)) (hne : S.Nonempty)
    (free : Fin 1023 → K) :
    deployedEncode S hne free ∈ LinearMap.ker (ellC S) :=
  LinearMap.mem_ker.mpr (ellC_deployedEncode S hne free)

/-- The deployed encoder is (extensionally) a linear map: it agrees
everywhere with `pivotEncoder`, which is bundled linear. -/
theorem deployedEncode_isLinear (S : Finset (Fin 1024)) (hne : S.Nonempty) :
    ∃ L : (Fin 1023 → K) →ₗ[K] (Fin 1024 → K),
      ∀ free, deployedEncode S hne free = L free :=
  ⟨pivotEncoder (ellC S) (pivotC S hne), deployedEncode_eq_pivotEncoder S hne⟩

/-! ## The deployed decoder is an explicit two-sided inverse on `ker (ellC S)` -/

/-- Transcription of the Rust `free_coordinates`:
`from_fn(|i| values[free_coordinate_row(i, pivot)])`. -/
def deployedDecode (p : Fin 1024) (c : Fin 1024 → K) : Fin 1023 → K :=
  fun i => c (deployedRow p i)

/-- The decoder recovers every free coordinate: `decode ∘ encode = id`.
Mirrors the Rust round-trip test. -/
theorem deployedDecode_deployedEncode (S : Finset (Fin 1024)) (hne : S.Nonempty)
    (free : Fin 1023 → K) :
    deployedDecode (pivotC S hne) (deployedEncode S hne free) = free := by
  funext i
  simp only [deployedDecode]
  rw [deployedRow_eq_succAbove, deployedEncode_eq_pivotEncoder,
    pivotEncoder_apply_succAbove]

/-- The encoder reconstructs every kernel word from its free coordinates:
`encode ∘ decode = id` on `ker (ellC S)`.  This is surjectivity onto the
kernel with the explicit deployed preimage. -/
theorem deployedEncode_deployedDecode (S : Finset (Fin 1024)) (hne : S.Nonempty)
    (c : Fin 1024 → K) (hc : ellC S c = 0) :
    deployedEncode S hne (deployedDecode (pivotC S hne) c) = c := by
  rw [deployedEncode_eq_pivotEncoder]
  refine ker_ell_ext (ellC S) (pivotC S hne) (ellC_pivot S hne)
    (ell_pivotEncoder (ellC S) (pivotC S hne) (ellC_pivot S hne) _) hc (fun i => ?_)
  rw [pivotEncoder_apply_succAbove]
  simp only [deployedDecode]
  rw [deployedRow_eq_succAbove]

end Field

/-! ## Commutation with the committed model equivalence, and the seam reduction

`componentCEncoderEquiv` was introduced in a finite-field section, but Lean
elides those unused section instances from the committed declaration, so only
`[Field K]` is required here. -/

section Commutation

variable {K : Type*} [Field K]

/-- **The deployed encoder commutes with the committed `componentCEncoderEquiv`.**
Its output on every free vector is the underlying word of the model kernel
equivalence, at the derived functional `ellC S` and derived pivot
`pivotC S hne`. -/
theorem deployedEncode_eq_componentCEncoderEquiv (S : Finset (Fin 1024))
    (hne : S.Nonempty) (free : Fin 1023 → K) :
    deployedEncode S hne free =
      ((componentCEncoderEquiv (ellC S) (pivotC S hne) (ellC_pivot S hne) free :
          LinearMap.ker (ellC S)) : Fin 1024 → K) := by
  rw [componentCEncoder_apply_coe]
  exact deployedEncode_eq_pivotEncoder S hne free

/-- **The single named code/model premise.**  Pointwise, the executable Rust
encoder (transported across the QM31 ≃ K identification) coincides with the
Lean transcription `deployedEncode S hne`.  This is the only edge Lean cannot
discharge: a byte-level "Rust source = this specification" fact together with
the QM31 codec identification.  It is deliberately the *whole* residual seam,
stated once. -/
def RustEncodeMatchesDeployedSpec (S : Finset (Fin 1024)) (hne : S.Nonempty)
    (rustEncode : FreeCoordinates K → LinearMap.ker (ellC (K := K) S)) : Prop :=
  ∀ free : FreeCoordinates K,
    ((rustEncode free : LinearMap.ker (ellC (K := K) S)) : Fin 1024 → K) =
      deployedEncode S hne free

/-- **Seam reduction.**  The committed `RustEncoderMatchesKernelEquiv`
obligation follows from the single transcription premise.  All of the linear
algebra — permutation, correction, kernel landing, and equivalence onto the
kernel — has been discharged above, so the human-audited gap shrinks to
"the Rust encoder equals its transcription". -/
theorem rustEncoderMatchesKernelEquiv_of_deployedSpec (S : Finset (Fin 1024))
    (hne : S.Nonempty) (rustEncode : FreeCoordinates K → LinearMap.ker (ellC (K := K) S))
    (hspec : RustEncodeMatchesDeployedSpec S hne rustEncode) :
    RustEncoderMatchesKernelEquiv (ellC S) (pivotC S hne) (ellC_pivot S hne) rustEncode := by
  change rustEncode = componentCEncoderEquiv (ellC S) (pivotC S hne) (ellC_pivot S hne)
  funext free
  apply Subtype.ext
  rw [componentCEncoder_apply_coe, ← deployedEncode_eq_pivotEncoder]
  exact hspec free

end Commutation

/-! ## Non-vacuity: the premise is satisfiable and the seam is reachable

Over the finite field `ZMod 2`, with the singleton inactive set `{0}`, the
deployed encoder itself satisfies the transcription premise (by construction),
so the reduced obligation `RustEncoderMatchesKernelEquiv` is actually
attained.  This witnesses that none of the hypotheses is vacuous. -/

namespace NonVacuity

/-- A concrete nonempty inactive-row set. -/
def z2S : Finset (Fin 1024) := {0}

theorem z2S_nonempty : z2S.Nonempty := Finset.singleton_nonempty 0

/-- The canonical executable encoder for the witness: the deployed encoder,
corestricted to the kernel. -/
noncomputable def z2RustEncode :
    FreeCoordinates (ZMod 2) → LinearMap.ker (ellC (K := ZMod 2) z2S) :=
  fun free => ⟨deployedEncode z2S z2S_nonempty free,
    deployedEncode_mem_ker z2S z2S_nonempty free⟩

/-- The canonical encoder satisfies the transcription premise. -/
theorem z2_spec :
    RustEncodeMatchesDeployedSpec z2S z2S_nonempty z2RustEncode :=
  fun _ => rfl

/-- Consequently the reduced `RustEncoderMatchesKernelEquiv` obligation is
attained for a concrete finite-field instance: the hypotheses are not
vacuous. -/
theorem z2_seam :
    RustEncoderMatchesKernelEquiv (ellC z2S) (pivotC z2S z2S_nonempty)
      (ellC_pivot z2S z2S_nonempty) z2RustEncode :=
  rustEncoderMatchesKernelEquiv_of_deployedSpec z2S z2S_nonempty z2RustEncode z2_spec

end NonVacuity

/-! ## Negative tooth: a wrong permutation breaks commutation

Dropping the pivot skip from `free_coordinate_row` (using the always-`castSucc`
placement `i ↦ i` instead of `succAbove`) yields an encoder that no longer
agrees with the model.  This shows the permutation is load-bearing: the
correspondence is not robust to a wrong reindexing, so `deployedRow_eq_succAbove`
is doing real work. -/

namespace NegativeTooth

variable {K : Type*} [Field K]

/-- The buggy placement: always `castSucc`, i.e. it forgets to skip the pivot. -/
def deployedRowBad (i : Fin 1023) : Fin 1024 := i.castSucc

/-- Scatter under the buggy placement. -/
def deployedInsertBad (free : Fin 1023 → K) : Fin 1024 → K :=
  ∑ i : Fin 1023, Pi.single (deployedRowBad i) (free i)

/-- Encoder under the buggy placement (same pivot correction as the real one). -/
def deployedEncodeBad (S : Finset (Fin 1024)) (hne : S.Nonempty)
    (free : Fin 1023 → K) : Fin 1024 → K :=
  Function.update (deployedInsertBad free) (pivotC S hne)
    (-ellC S (deployedInsertBad free))

/-- The buggy scatter of the first basis vector sits at row `0`, not at
`succAbove pivot 0`. -/
theorem deployedInsertBad_single_zero :
    deployedInsertBad (Pi.single (0 : Fin 1023) (1 : K)) = Pi.single (0 : Fin 1024) (1 : K) := by
  rw [deployedInsertBad,
    Finset.sum_eq_single (0 : Fin 1023)
      (fun j _ hj => by rw [Pi.single_eq_of_ne hj, Pi.single_zero])
      (fun hj => absurd (Finset.mem_univ _) hj),
    Pi.single_eq_same, deployedRowBad, Fin.castSucc_zero']

/-- **Wrong permutation ⇒ commutation fails.**  With the buggy placement the
encoder of `Pi.single 0 1` differs from the model `pivotEncoder` at the row
`succAbove pivot 0`: the model carries the recovered coordinate `1` there,
the buggy encoder carries `0`. -/
theorem wrongPermutation_breaks_commutation :
    deployedEncodeBad (K := ZMod 2) NonVacuity.z2S NonVacuity.z2S_nonempty
        (Pi.single (0 : Fin 1023) (1 : ZMod 2))
      ≠ pivotEncoder (ellC NonVacuity.z2S) (pivotC NonVacuity.z2S NonVacuity.z2S_nonempty)
          (Pi.single (0 : Fin 1023) (1 : ZMod 2)) := by
  intro h
  have hpiv : pivotC NonVacuity.z2S NonVacuity.z2S_nonempty = 0 := by
    have hmem : pivotC NonVacuity.z2S NonVacuity.z2S_nonempty ∈ ({0} : Finset (Fin 1024)) :=
      pivotC_mem NonVacuity.z2S NonVacuity.z2S_nonempty
    exact Finset.mem_singleton.mp hmem
  have hrp : (pivotC NonVacuity.z2S NonVacuity.z2S_nonempty).succAbove 0
      ≠ pivotC NonVacuity.z2S NonVacuity.z2S_nonempty := Fin.succAbove_ne _ _
  have hr0 : (pivotC NonVacuity.z2S NonVacuity.z2S_nonempty).succAbove 0 ≠ 0 := by
    rw [hpiv]; exact Fin.succAbove_ne 0 0
  have hcontra := congrFun h ((pivotC NonVacuity.z2S NonVacuity.z2S_nonempty).succAbove 0)
  unfold deployedEncodeBad at hcontra
  rw [Function.update_of_ne hrp, deployedInsertBad_single_zero, Pi.single_eq_of_ne hr0,
    pivotEncoder_apply_succAbove, Pi.single_eq_same] at hcontra
  exact zero_ne_one hcontra

end NegativeTooth

/-! ## Axiom audit -/

#print axioms deployedRow
#print axioms deployedRow_eq_succAbove
#print axioms ellC
#print axioms ellC_apply
#print axioms ellC_single
#print axioms pivotC
#print axioms pivotC_mem
#print axioms ellC_pivot
#print axioms deployedInsert
#print axioms sum_single_succAbove
#print axioms deployedInsert_eq_freeInsert
#print axioms deployedEncode
#print axioms deployedEncode_eq_pivotEncoder
#print axioms ellC_deployedEncode
#print axioms deployedEncode_mem_ker
#print axioms deployedEncode_isLinear
#print axioms deployedDecode
#print axioms deployedDecode_deployedEncode
#print axioms deployedEncode_deployedDecode
#print axioms deployedEncode_eq_componentCEncoderEquiv
#print axioms RustEncodeMatchesDeployedSpec
#print axioms rustEncoderMatchesKernelEquiv_of_deployedSpec
#print axioms NonVacuity.z2S_nonempty
#print axioms NonVacuity.z2_spec
#print axioms NonVacuity.z2_seam
#print axioms NegativeTooth.deployedInsertBad_single_zero
#print axioms NegativeTooth.wrongPermutation_breaks_commutation

end AspisV5ComponentCEncoderCorrespondence

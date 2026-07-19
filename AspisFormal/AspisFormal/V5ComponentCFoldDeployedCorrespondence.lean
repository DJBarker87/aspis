import AspisFormal.V5ComponentCConditionalDecoupling

/-!
# v5 Component C: the *deployed* fold-read correspondence seam

This file states the **smallest exact premises** that tie the serialized
frozen-`q18` Component-C wire reads — the four arity-four relation folds, their
out-of-domain (OOD) points/values, the layer roots, and the transcript-derived
`q18` query positions read by the deployed verifier — to the *abstract*
`E`/`F`/released-view maps that
`AspisFormal.V5ComponentCConditionalDecoupling` proves the C-DEC decoupling
theorem about.  It proves a **conditional** correspondence and nothing
stronger: *given* the named seam premises, the deployed Component-C fold reads
equal the abstract released view that the (arity-four circle) transport theorem
simulates.

`V5ComponentCFoldTransport.lean` **is not present in this repository yet**.  The
transport step is therefore consumed here as the abstract, *unproved* interface
`AspisV5ComponentCConditionalDecoupling.UnresolvedInterfaces.CircleArityFourFoldTransport`
(`concreteFoldView = F` on the mask), and the correspondence below is stated
against the abstract `E`/`F`/released-view **shape** exported by that file.  When
the transport file lands, its conclusion is exactly the `Q18FoldTransport`
hypothesis of `deployed_fold_reads_eq_released_view`; nothing else in the
statement changes.

## Deployed provenance (read-only)

The teeth are transcribed verbatim from the deployed Rust; no constant is
invented here.

* `programs/aspis-verifier/src/v5_cu_probe.rs` — mode 9 (`COMPOSITE`): the
  account layout (`AV5CUP07`; `GAMMA_OFFSET = 8`), the real-witness prefix
  (`AV5PFX03`; `C1_ROOT@23`, `C2_ROOT@55`, `TERMINAL@5799` (3×QM31),
  `INACTIVE@5847` (1×QM31), five 32-byte FS salts @5863), the four-round replay
  `replay_real_v5_relation_rounds`, and the `q18` draw
  `derive_v5_complete_queries_from_transcript`
  (`challenge_queries_without_replacement(18, 1<<17, 64)`).
* `programs/aspis-verifier/src/v5_relation_stress.rs` — the 928-byte
  post-combination block: `CIRCLE@0` (4), `LINE@64` (6), `OOD@160` (8),
  `MIX@288` (8), `SUMCHECK@416` (28), `FINAL@864` (4) QM31 values;
  `ROUNDS = 4`, `OOD_SAMPLES = 2`, `SUMCHECK_COEFFICIENTS = 7`.
* `crates/aspis-prover/src/v5_c_mask.rs` — mask space `C = ker ℓ ⊂ QM31^1024`,
  `V5_C_FREE_COORDINATES = 1023`, `V5_C_POINT_CLAIMS = 3`, `V5_C_TOTAL_CLAIMS = 4`.
* `crates/aspis-prover/src/v5_split_layer_zero.rs` — `19 = 16 + 3` lanes,
  candidate C1 leaf `256 B`, C2 leaf `192 B`, `V5_LAYER_ZERO_LEAVES = 1<<17`.

## Deployed vs abstract — blunt status

* **Kernel-certified here** (section `Teeth`): the offset/count/order/byte
  arithmetic — that the deployed constants recompose into the abstract
  `76 = 72 + 3 + 1`, `256 = 4·(2+7) + 4·(18+18+18) + 4`, `332 = 76 + 256`,
  `1023 = 1024 − 1`; the 928-byte stress layout; the M31/QM31 byte split; and
  the fold-challenge order `γ ≺ α₀ ≺ α₁ ≺ α₂ ≺ α₃ ≺ q18`.
* **A named code-model interface, NOT discharged** (the four seam premises):
  that the deployed byte reads *evaluate* to the abstract `E`/`F` linear
  functionals (`Q18CLaneJointReads`), that the 256 fold/OOD reads enumerate `F`
  once (`Q18FoldReadsEnumerateF`), that the concrete arity-four fold view *is*
  `F` (`Q18FoldTransport`, the absent transport theorem), and that the batching
  `γ` is bound after the C1/C2 commitment and is nonzero
  (`Q18BatchingBoundAfterCommit`).  These are the abstract file's own
  `UnresolvedInterfaces`, reused unchanged; the correspondence theorem *consumes
  every one of them* and derives no security claim without them.

## M31 vs QM31 (base field vs extension) — which reads are which

The **entire** fold/OOD/challenge/claim/final post-combination view `F` is read
in the extension field **QM31** (16-byte words): the four fold challenges
`α_r`, the OOD circle point (round 0) and line points (rounds 1–3), the OOD
values, the mix challenges, the seven-coefficient relation-sumcheck polynomials,
the four final-tensor coefficients, `γ`, `κ`, `η`, `λ`, `χ`, the ten sumcheck
round challenges, the `3×10` statement points, the `4×19` lane claims, the three
terminal + one inactive claims, and the C2 leaf columns.  The **only** base-field
**M31** (4-byte) reads in the whole C-lane are the candidate C1 leaf columns
(`16` columns × `4` fiber slots per query).  The `72` released layer-zero
coordinates of `E` are QM31-*valued* (one `γ`-recombination per (query, slot))
but are backed by those M31 leaf columns plus the QM31 C2 columns.  Hence `F` is
purely QM31; the M31/QM31 boundary sits exactly at the C1 leaf openings.
-/

namespace AspisV5ComponentCFoldDeployedCorrespondence

open AspisV5ComponentCConditionalDecoupling
open AspisV5ComponentCConditionalDecoupling.UnresolvedInterfaces

/-! ## Section 1 — deployed wire teeth (kernel-certified `ℕ` arithmetic)

Every value below is a deployed constant; every theorem is checked by the
kernel with `decide` and consumes no interface premise.  These are *counts and
offsets*, never evidence for C-DEC. -/

section Teeth

/-- M31 base-field word width (bytes). -/
def m31Bytes : ℕ := 4
/-- QM31 extension word width (bytes). -/
def qm31Bytes : ℕ := 16

/-- `V5_CU_PROBE_QUERY_COUNT`: the `q18` query count. -/
def queryCount : ℕ := 18
/-- Candidate C1 lanes (`V5_C1_LANES`), read as M31. -/
def c1Lanes : ℕ := 16
/-- C2 lanes (`V5_C2_LANES`), read as QM31. -/
def c2Lanes : ℕ := 3
/-- Total PCS lanes `V5_RELATION_LANES = 16 + 3`. -/
def relationLanes : ℕ := 19
/-- `STATE_ONLY_FIBER_SLOTS`. -/
def fiberSlots : ℕ := 4
/-- `V5_RELATION_STRESS_ROUNDS`: the four arity-four folds. -/
def relationFolds : ℕ := 4
/-- `V5_RELATION_STRESS_OOD_SAMPLES` per round. -/
def oodSamples : ℕ := 2
/-- `SUMCHECK_COEFFICIENTS` per round. -/
def sumcheckCoeffs : ℕ := 7
/-- `V5_RELATION_STRESS_FINAL_COEFFICIENTS`. -/
def finalValues : ℕ := 4
/-- `V5_C_POINT_CLAIMS`: the three MLE claims. -/
def pointClaims : ℕ := 3
/-- `V5_C_ROWS`. -/
def cRows : ℕ := 1024
/-- `V5_CU_PROBE_RELATION_LOG_ROWS`. -/
def logRows : ℕ := 10
/-- FRI domain log: `1 << 17` leaves. -/
def friDomainLog : ℕ := 17
/-- Frozen `q18` per-later-layer opening multiplicity `n₁ = n₂ = n₃ = 18`. -/
def q18N : ℕ := 18
/-- Private opening roots: C1, C2, and three later layers. -/
def privateRootCount : ℕ := 5
/-- The three later FRI opening layers (`V5PrivateOpeningRoots.later`). -/
def laterRootCount : ℕ := 3
/-- `V5_CU_REAL_PREFIX_PUBLIC_FS_SALT_COUNT`. -/
def fsSaltCount : ℕ := 5

/-- `V5_CU_PROBE_GAMMA_OFFSET`: γ (QM31) begins at byte 8 of `AV5CUP07`. -/
def gammaOffset : ℕ := 8
/-- `V5_CU_REAL_PREFIX_C1_ROOT_OFFSET`. -/
def c1RootOffset : ℕ := 23
/-- `V5_CU_REAL_PREFIX_C2_ROOT_OFFSET`. -/
def c2RootOffset : ℕ := 55
/-- `V5_CU_REAL_PREFIX_TERMINAL_OFFSET` (three terminal QM31 claims). -/
def terminalOffset : ℕ := 5799
/-- `V5_CU_REAL_PREFIX_INACTIVE_CLAIM_OFFSET` (one inactive QM31 claim). -/
def inactiveClaimOffset : ℕ := 5847

/-! ### The 928-byte post-combination (`F`) stress block, byte offsets -/

/-- Round-0 OOD circle coordinates (x,y per sample). -/
def circleCoords : ℕ := 2 * oodSamples
/-- Rounds 1–3 line OOD points. -/
def linePoints : ℕ := (relationFolds - 1) * oodSamples
/-- All OOD values across the four rounds. -/
def oodValues : ℕ := relationFolds * oodSamples
/-- All mix challenges across the four rounds. -/
def oodMixes : ℕ := relationFolds * oodSamples
/-- All relation-sumcheck coefficients across the four rounds. -/
def sumcheckValues : ℕ := relationFolds * sumcheckCoeffs
/-- `V5_RELATION_STRESS_CIRCLE_OFFSET`. -/
def circleOffset : ℕ := 0
/-- `V5_RELATION_STRESS_LINE_OFFSET`. -/
def lineOffset : ℕ := 64
/-- `V5_RELATION_STRESS_OOD_OFFSET`. -/
def oodOffset : ℕ := 160
/-- `V5_RELATION_STRESS_MIX_OFFSET`. -/
def mixOffset : ℕ := 288
/-- `V5_RELATION_STRESS_SUMCHECK_OFFSET`. -/
def sumcheckOffset : ℕ := 416
/-- `V5_RELATION_STRESS_FINAL_OFFSET`. -/
def finalOffset : ℕ := 864
/-- `V5_RELATION_STRESS_BYTES`. -/
def stressBytes : ℕ := 928
/-- QM31 words in the stress block. -/
def stressQm31Count : ℕ := 58

/-- Lane count tooth: `16 + 3 = 19`. -/
theorem tooth_lanes : c1Lanes + c2Lanes = relationLanes := by decide
/-- Per-round post-combination coordinate count `2 + 7 = 9`. -/
theorem tooth_per_round : oodSamples + sumcheckCoeffs = 9 := by decide
/-- Stress circle sub-block begins at 0. -/
theorem tooth_stress_circle : circleOffset = 0 := by decide
/-- Line offset accumulates the circle sub-block: `0 + 4·16 = 64`. -/
theorem tooth_stress_line : lineOffset = circleOffset + circleCoords * qm31Bytes := by decide
/-- OOD-value offset: `64 + 6·16 = 160`. -/
theorem tooth_stress_ood : oodOffset = lineOffset + linePoints * qm31Bytes := by decide
/-- Mix offset: `160 + 8·16 = 288`. -/
theorem tooth_stress_mix : mixOffset = oodOffset + oodValues * qm31Bytes := by decide
/-- Sumcheck offset: `288 + 8·16 = 416`. -/
theorem tooth_stress_sumcheck : sumcheckOffset = mixOffset + oodMixes * qm31Bytes := by decide
/-- Final-coefficient offset: `416 + 28·16 = 864`. -/
theorem tooth_stress_final : finalOffset = sumcheckOffset + sumcheckValues * qm31Bytes := by decide
/-- Total stress bytes: `864 + 4·16 = 928`. -/
theorem tooth_stress_bytes : stressBytes = finalOffset + finalValues * qm31Bytes := by decide
/-- The block is `58` QM31 words: `58·16 = 928`. -/
theorem tooth_stress_all_qm31 : stressBytes = stressQm31Count * qm31Bytes := by decide
/-- The `58` QM31 words decompose as `4 + 6 + 8 + 8 + 28 + 4`. -/
theorem tooth_stress_qm31_count :
    stressQm31Count
      = circleCoords + linePoints + oodValues + oodMixes + sumcheckValues + finalValues := by
  decide

/-! ### Conditioned `E` (76) and post-combination `F` (256) dimension teeth -/

/-- Conditioned coordinates `E`: `72 = 18·4` layer-zero + `3` MLE + `1` terminal `= 76`. -/
theorem tooth_conditioned : fiberSlots * queryCount + pointClaims + 1 = 76 := by decide
/-- Layer-zero coordinates: `18·4 = 72`. -/
theorem tooth_layerzero_total : fiberSlots * queryCount = 72 := by decide
/-- Post-combination coordinates `F` at frozen `q18`:
`4·(2+7) + 4·(18+18+18) + 4 = 256`. -/
theorem tooth_post_combination :
    relationFolds * (oodSamples + sumcheckCoeffs)
        + relationFolds * (q18N + q18N + q18N) + finalValues = 256 := by
  decide
/-- The stress block supplies the `40` non-FRI `F` coordinates: `8 + 28 + 4 = 40`. -/
theorem tooth_stress_supplies_forty : oodValues + sumcheckValues + finalValues = 40 := by decide
/-- Joint worst-case inventory: `76 + 256 = 332`. -/
theorem tooth_joint : 76 + 256 = 332 := by decide
/-- Mask free coordinates: `1024 − 1 = 1023`. -/
theorem tooth_free_coordinates : cRows - 1 = 1023 := by decide
/-- The three later FRI opening layers: `4 − 1 = 3`. -/
theorem tooth_later_layers : laterRootCount = relationFolds - 1 := by decide
/-- Five private opening roots span `5·32 = 160` bytes. -/
theorem tooth_private_roots : privateRootCount * 32 = 160 := by decide
/-- Five public FS salts span `5·32 = 160` bytes. -/
theorem tooth_fs_salts : fsSaltCount * 32 = 160 := by decide

/-! ### M31 (base field) vs QM31 (extension) separation -/

/-- Candidate C1 leaf (M31): `4 slots · 16 cols · 4 B = 256`. -/
def candidateC1LeafBytes : ℕ := 256
/-- C2 leaf (QM31): `3 cols · 4 slots · 16 B = 192`. -/
def c2LeafBytes : ℕ := 192
/-- The C1 leaf is base-field: `256 = 4·16·4` (M31). -/
theorem tooth_c1_leaf_m31 : candidateC1LeafBytes = fiberSlots * c1Lanes * m31Bytes := by decide
/-- The C2 leaf is extension-field: `192 = 3·4·16` (QM31). -/
theorem tooth_c2_leaf_qm31 : c2LeafBytes = c2Lanes * fiberSlots * qm31Bytes := by decide
/-- The whole fold/OOD/post-combination block is a whole number of QM31 words:
it contains no base-field read. -/
theorem tooth_fold_block_extension_only : stressBytes % qm31Bytes = 0 := by decide
/-- Base-field (M31) reads per query: `4 slots · 16 C1 cols = 64`. -/
theorem tooth_c1_m31_values_per_query : fiberSlots * c1Lanes = 64 := by decide
/-- Extension (QM31) C2 reads per query: `3 cols · 4 slots = 12`. -/
theorem tooth_c2_qm31_values_per_query : c2Lanes * fiberSlots = 12 := by decide
/-- Recombined (QM31) released layer-zero values per query: `4`. -/
theorem tooth_recombined_layerzero_per_query : fiberSlots = 4 := by decide

/-! ### Challenge-order teeth: `γ ≺ α₀ ≺ α₁ ≺ α₂ ≺ α₃ ≺ q18`

The batching challenge `γ` (`challenge_nonzero_qm31` in `verify_v5_wire_prefix`,
bound *after* the C1 root @23 and C2 root @55 are absorbed) precedes all four
fold challenges; the four `α_r` (`challenge_qm31` per round in
`replay_real_v5_relation_rounds`, each derived after that round's OOD point, OOD
value, mix, seven sumcheck coefficients and fold nonce) are in strict round
order; and the `q18` positions are drawn last, after the final-tensor poly, the
grind nonce and the query selector.  Only the strict order relations are
claimed; the absolute integers are a monotone witness. -/

/-- The salient Fiat–Shamir challenge events of the deployed C-lane fold. -/
inductive FoldEvent
  | gamma
  | alpha (r : Fin 4)
  | q18

/-- A monotone position witness reflecting the deployed derivation order. -/
def eventPos : FoldEvent → ℕ
  | .gamma => 0
  | .alpha r => 1 + r.val
  | .q18 => 5

/-- **Order tooth.**  `γ` precedes all four fold challenges, the four fold
challenges are in strict round order, and the `q18` draw follows them all. -/
theorem tooth_challenge_order :
    eventPos .gamma < eventPos (.alpha 0)
      ∧ eventPos (.alpha 0) < eventPos (.alpha 1)
      ∧ eventPos (.alpha 1) < eventPos (.alpha 2)
      ∧ eventPos (.alpha 2) < eventPos (.alpha 3)
      ∧ eventPos (.alpha 3) < eventPos .q18 := by
  decide

end Teeth

/-! ## Section 2 — the conditional correspondence theorem

Each seam premise is one of the abstract file's `UnresolvedInterfaces`,
specialised to the frozen-`q18` Component-C dimensions and given a
deployment-facing name.  Nothing here proves any of them: the theorem is
strictly conditional. -/

section Correspondence

variable {K : Type*} [Field K]
variable {C : Type*} [AddCommGroup C] [Module K C]
variable {T P : Type*}

/-- **Seam premise (E/F residual ↔ serializer rows).**  The `332` deployed
Component-C joint rows (76 conditioned followed by 256 post-combination, in
serialisation order) evaluate, on every mask, to the abstract `E ⊕ F`. -/
abbrev Q18CLaneJointReads (deployedJoint : Fin 332 → C →ₗ[K] K)
    (E : C →ₗ[K] Fin 76 → K) (F : C →ₗ[K] Fin 256 → K) : Prop :=
  RustLeanRowCorrespondence332 deployedJoint E F

/-- **Seam premise (fold/OOD reads ↔ `F`).**  The `256` serialized post-combination
reads across the four folds enumerate the coordinate functionals of `F` exactly
once (no omission, no duplication). -/
abbrev Q18FoldReadsEnumerateF (serializedFRow : Fin 256 → C →ₗ[K] K)
    (F : C →ₗ[K] Fin 256 → K) : Prop :=
  SerializationEnumeratesFExactlyOnce serializedFRow F

/-- **Seam premise (arity-four fold transport).**  The concrete circle /
arity-four fold view (four folds, three later opening layers, final
coefficients) acts on the mask as the abstract linear map `F`.  This is the
conclusion the absent `V5ComponentCFoldTransport.lean` must supply. -/
abbrev Q18FoldTransport (concreteFoldView : C → Fin 256 → K)
    (F : C →ₗ[K] Fin 256 → K) : Prop :=
  CircleArityFourFoldTransport concreteFoldView F

/-- **Seam premise (challenge schedule).**  The batching challenge `γ` is a
function of the transcript prefix up to and including the binding C1/C2
commitment (commitment strictly precedes `γ`), and `γ ≠ 0`. -/
abbrev Q18BatchingBoundAfterCommit (commitPrefix : T → P) (gammaOf : T → K) : Prop :=
  CommitmentBeforeGammaAndGammaNeZero commitPrefix gammaOf

/-- **Deployed⇔abstract conditional correspondence for the Component-C fold reads.**

*Given* the four seam premises — every one of the abstract file's relevant
`UnresolvedInterfaces`, specialised to frozen `q18` — the deployed serialized
Component-C fold reads are exactly the abstract released view that the
(arity-four circle) transport theorem simulates.  Concretely, for the deployed
`γ = gammaOf t`:

* **(A)** the `256` serialized fold/OOD reads coincide, coordinate for
  coordinate (through the serialisation permutation `σ`), with the concrete
  arity-four fold view — hence with the abstract `F` — on every mask
  *(uses `hfoldReads` and `htransport`)*;
* **(B)** the concrete fold view *is* the abstract released view `F`
  *(uses `htransport`)*;
* **(C)** the `332` deployed joint rows are `E ⊕ F` in serialisation order
  *(uses `hjoint`)*;
* **(D)** because `γ ≠ 0`, the audit's `J_σ`-form governs the released view:
  C-DEC is equivalent to `(0, δ) ∈ image (Jmap E F γ)` for every legal `δ`
  *(uses `hschedule.left`)*;
* **(E)** because the commitment binds `γ`, it binds the batched joint map:
  equal commitment prefixes give equal `Jmap E F γ` *(uses `hschedule.right`)*.

No premise is idle, and no unconditional security claim is made: strip any seam
premise and the corresponding conjunct is unavailable. -/
theorem deployed_fold_reads_eq_released_view
    (E : C →ₗ[K] Fin 76 → K) (F : C →ₗ[K] Fin 256 → K)
    (concreteFoldView : C → Fin 256 → K)
    (deployedJoint : Fin 332 → C →ₗ[K] K)
    (serializedFRow : Fin 256 → C →ₗ[K] K)
    (commitPrefix : T → P) (gammaOf : T → K) (t : T)
    (htransport : Q18FoldTransport concreteFoldView F)
    (hjoint : Q18CLaneJointReads deployedJoint E F)
    (hfoldReads : Q18FoldReadsEnumerateF serializedFRow F)
    (hschedule : Q18BatchingBoundAfterCommit commitPrefix gammaOf) :
    -- (A) deployed fold reads = concrete fold view coordinates (= abstract F)
    (∃ σ : Equiv.Perm (Fin 256), ∀ (j : Fin 256) (c : C),
        serializedFRow j c = concreteFoldView c (σ j))
      -- (B) concrete fold view = abstract released view F
      ∧ (∀ c : C, concreteFoldView c = F c)
      -- (C) joint 332 rows = abstract E ⊕ F in serialisation order
      ∧ (∀ c : C, (fun i : Fin 332 => deployedJoint i c)
          = Fin.append (fun i : Fin 76 => E c i) (fun j : Fin 256 => F c j)
            ∘ Fin.cast (by norm_num : (332 : ℕ) = 76 + 256))
      -- (D) deployed γ is invertible ⇒ the audit's J-form governs the released view
      ∧ (∀ Δ : Submodule K (Fin 256 → K),
          CDec E F Δ
            ↔ ∀ δ ∈ Δ, ((0 : Fin 76 → K), δ) ∈ LinearMap.range (Jmap E F (gammaOf t)))
      -- (E) commitment binds γ ⇒ binds the batched joint map
      ∧ (∀ t₁ t₂ : T, commitPrefix t₁ = commitPrefix t₂
          → Jmap E F (gammaOf t₁) = Jmap E F (gammaOf t₂)) := by
  refine ⟨?_, htransport, hjoint, ?_, ?_⟩
  · -- (A): compose the serialisation permutation with the transport equality
    obtain ⟨σ, hσ⟩ := hfoldReads
    exact ⟨σ, fun j c => by rw [hσ j c, htransport c]⟩
  · -- (D): γ ≠ 0 from the schedule premise feeds `cDec_iff_J`
    exact fun Δ => cDec_iff_J E F Δ (hschedule.left t)
  · -- (E): the commitment determines γ, hence the batched joint map
    exact fun t₁ t₂ h => congrArg (Jmap E F) (hschedule.right t₁ t₂ h)

end Correspondence

/-! ## Axiom audit -/

#print axioms deployed_fold_reads_eq_released_view
#print axioms tooth_challenge_order
#print axioms tooth_conditioned
#print axioms tooth_post_combination
#print axioms tooth_joint
#print axioms tooth_stress_bytes
#print axioms tooth_stress_all_qm31
#print axioms tooth_stress_qm31_count
#print axioms tooth_c1_leaf_m31
#print axioms tooth_c2_leaf_qm31
#print axioms tooth_fold_block_extension_only
#print axioms tooth_lanes
#print axioms tooth_free_coordinates
#print axioms tooth_later_layers

end AspisV5ComponentCFoldDeployedCorrespondence

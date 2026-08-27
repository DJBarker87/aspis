import AspisFormal.K1.V7Tag73Q16CompilerTapeCoordinates

/-!
# Causal routing of uniform compiler coordinates into q16 slots

A static tape split is not enough for the deployed q16 scan: the exact
fresh-answer indices occupied by its cloned branches depend on earlier oracle
answers.  This file proves the generic finite theorem needed for the honest
coupling.

A `CausalSlotRouter` decides, before seeing the current answer, whether that
answer fills one named special slot or the residual tape.  Its continuation
may depend on the answer just exposed.  Every special slot is filled exactly
once.  The induced map from the original uniform tape to the named-slot
function and residual tape is an equivalence, so adaptive chronological
routing loses no entropy and needs no independence assumption.

The remaining protocol-specific theorem must construct this router from the
literal Tag-73 scheduler and prove that the named slots are exactly the q16
candidate output blocks.  No such source-alignment claim is assumed here.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73CausalQ16CoordinateRouter

open AspisK1.V7Tag73AdaptiveLazyOracle
open AspisK1.V7Tag73Q16CompilerTapeCoordinates
open AspisK1.V7Tag73Q16DigestDrawReindex
open AspisK1.V7Tag73TranscriptSchedule

noncomputable section

/-! ## Removing one named function coordinate -/

/-- A function on a finite set is exactly its value at one chosen member plus
a function on the set with that member erased. -/
def eraseFunctionEquiv
    {Slot Output : Type} [DecidableEq Slot]
    (slots : Finset Slot) (chosen : ↥slots) :
    (↥slots → Output) ≃
      Output × (↥(slots.erase chosen.1) → Output) where
  toFun values :=
    (values chosen, fun remaining =>
      values ⟨remaining.1, Finset.mem_of_mem_erase remaining.2⟩)
  invFun split current :=
    if equal : current.1 = chosen.1 then split.1
    else split.2 ⟨current.1, Finset.mem_erase.mpr ⟨equal, current.2⟩⟩
  left_inv values := by
    funext current
    by_cases equal : current.1 = chosen.1
    · have currentEq : current = chosen := Subtype.ext equal
      subst current
      simp
    · simp [equal]
  right_inv split := by
    apply Prod.ext
    · simp
    · funext remaining
      have different : remaining.1 ≠ chosen.1 :=
        (Finset.mem_erase.mp remaining.2).1
      simp [different]

/-! ## A structurally causal named-slot router -/

/-- At every exposure the router commits to its destination before receiving
that exposure's answer.  A special step erases one named slot; a residual
step consumes one residual coordinate.  The recursive continuation may use
the answer just received, exactly matching an adaptive lazy-oracle run. -/
inductive CausalSlotRouter (Output Slot : Type) [DecidableEq Slot] :
    Finset Slot → Nat → Type
  | done : CausalSlotRouter Output Slot ∅ 0
  | special {slots : Finset Slot} {residual : Nat}
      (chosen : ↥slots)
      (next : Output →
        CausalSlotRouter Output Slot (slots.erase chosen.1) residual) :
      CausalSlotRouter Output Slot slots residual
  | residual {slots : Finset Slot} {remaining : Nat}
      (next : Output → CausalSlotRouter Output Slot slots remaining) :
      CausalSlotRouter Output Slot slots (remaining + 1)

/-- Transport a length-indexed answer tape across an exact length equality. -/
def castFreshAnswerTape
    {Output : Type} {source target : Nat} (equal : source = target) :
    FreshAnswerTape Output source ≃ FreshAnswerTape Output target :=
  Equiv.cast (congrArg (FreshAnswerTape Output) equal)

/-- The exact adaptive-routing equivalence.  Because each destination choice
precedes the current answer, inversion can replay the same choices from the
named-slot values and residual tape. -/
def CausalSlotRouter.coordinateEquiv
    {Output Slot : Type} [DecidableEq Slot] :
    {slots : Finset Slot} → {residual : Nat} →
      CausalSlotRouter Output Slot slots residual →
      FreshAnswerTape Output (slots.card + residual) ≃
        (↥slots → Output) × FreshAnswerTape Output residual
  | _, _, .done =>
      { toFun := fun _ =>
          (fun impossible => isEmptyElim impossible,
            PUnit.unit)
        invFun := fun _ => PUnit.unit
        left_inv := by intro tape; cases tape; rfl
        right_inv := by
          intro result
          rcases result with ⟨values, residual⟩
          apply Prod.ext
          · funext impossible
            exact isEmptyElim impossible
          · cases residual
            rfl }
  | slots, residualCount, .special chosen next => by
      let erased := slots.erase chosen.1
      have chosenMember : chosen.1 ∈ slots := chosen.2
      have cardErase : erased.card = slots.card - 1 := by
        exact Finset.card_erase_of_mem chosenMember
      have cardPositive : 0 < slots.card := Finset.card_pos.mpr
        ⟨chosen.1, chosenMember⟩
      have totalEq : slots.card + residualCount =
          (erased.card + residualCount) + 1 := by
        omega
      exact
        (castFreshAnswerTape (Output := Output) totalEq).trans
          ((Equiv.sigmaEquivProd Output
              (FreshAnswerTape Output (erased.card + residualCount))).symm.trans
            ((Equiv.sigmaCongrRight fun answer =>
                CausalSlotRouter.coordinateEquiv (next answer)).trans
              ((Equiv.sigmaEquivProd Output
                  ((↥erased → Output) ×
                    FreshAnswerTape Output residualCount)).trans
                ((Equiv.prodAssoc Output (↥erased → Output)
                    (FreshAnswerTape Output residualCount)).symm.trans
                  (Equiv.prodCongr
                    (eraseFunctionEquiv slots chosen).symm
                    (Equiv.refl (FreshAnswerTape Output residualCount)))))))
  | slots, remaining + 1, .residual next => by
      have totalEq : slots.card + (remaining + 1) =
          (slots.card + remaining) + 1 := by omega
      exact
        (castFreshAnswerTape (Output := Output) totalEq).trans
          ((Equiv.sigmaEquivProd Output
              (FreshAnswerTape Output (slots.card + remaining))).symm.trans
            ((Equiv.sigmaCongrRight fun answer =>
                CausalSlotRouter.coordinateEquiv (next answer)).trans
              ((Equiv.sigmaEquivProd Output
                  ((↥slots → Output) ×
                    FreshAnswerTape Output remaining)).trans
                ((Equiv.prodAssoc Output (↥slots → Output)
                    (FreshAnswerTape Output remaining)).symm.trans
                  ((Equiv.prodCongr
                      (Equiv.prodComm Output (↥slots → Output))
                      (Equiv.refl (FreshAnswerTape Output remaining))).trans
                    (Equiv.prodAssoc (↥slots → Output) Output
                      (FreshAnswerTape Output remaining)))))))

/-! ## Full finite-index and q16 specializations -/

def univSubtypeEquiv (Slot : Type) [Fintype Slot] [DecidableEq Slot] :
    ↥(Finset.univ : Finset Slot) ≃ Slot where
  toFun value := value.1
  invFun value := ⟨value, Finset.mem_univ value⟩
  left_inv value := by ext; rfl
  right_inv value := rfl

/-- A router that fills every member of a finite slot type induces a
lossless factorisation into a total named-slot function and residual tape. -/
def CausalSlotRouter.fullCoordinateEquiv
    {Output Slot : Type} [Fintype Slot] [DecidableEq Slot]
    {residual : Nat}
    (router : CausalSlotRouter Output Slot Finset.univ residual) :
    FreshAnswerTape Output (Fintype.card Slot + residual) ≃
      (Slot → Output) × FreshAnswerTape Output residual := by
  have cardEq : (Finset.univ : Finset Slot).card = Fintype.card Slot :=
    Finset.card_univ
  exact
    (castFreshAnswerTape (Output := Output)
      (congrArg (fun count => count + residual) cardEq).symm).trans
        (router.coordinateEquiv.trans
          (Equiv.prodCongr
            ((univSubtypeEquiv Slot).arrowCongr (Equiv.refl Output))
            (Equiv.refl (FreshAnswerTape Output residual))))

abbrev Q16DigestSlot := Fin 64 × Fin 8

def q16DigestSlotFunctionEquiv :
    (Q16DigestSlot → Digest256) ≃ Q16CandidateDigestForest where
  toFun values counter block := values (counter, block)
  invFun forest slot := forest slot.1 slot.2
  left_inv values := by funext slot; rcases slot with ⟨counter, block⟩; rfl
  right_inv forest := by funext counter block; rfl

/-- Final generic q16 form: any causal router that fills the 512 named
candidate/block slots produces exactly a complete digest forest and an
independent residual coordinate tape. -/
def CausalSlotRouter.q16CoordinateEquiv
    {residual : Nat}
    (router : CausalSlotRouter Digest256 Q16DigestSlot Finset.univ residual) :
    FreshAnswerTape Digest256 (512 + residual) ≃
      Q16CandidateDigestForest × FreshAnswerTape Digest256 residual := by
  have cardEq : Fintype.card Q16DigestSlot = 512 := by
    simp [Q16DigestSlot]
  exact
    (castFreshAnswerTape (Output := Digest256)
      (congrArg (fun count => count + residual) cardEq).symm).trans
        (router.fullCoordinateEquiv.trans
          (Equiv.prodCongr q16DigestSlotFunctionEquiv
            (Equiv.refl (FreshAnswerTape Digest256 residual))))

#print axioms eraseFunctionEquiv
#print axioms CausalSlotRouter.coordinateEquiv
#print axioms CausalSlotRouter.fullCoordinateEquiv
#print axioms q16DigestSlotFunctionEquiv
#print axioms CausalSlotRouter.q16CoordinateEquiv

end

end AspisK1.V7Tag73CausalQ16CoordinateRouter

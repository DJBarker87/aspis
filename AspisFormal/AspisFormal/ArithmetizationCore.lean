import Mathlib
import AspisFormal.ValueConservation

/-!
# Arithmetization core: soundness-side analogue of the hiding formalization

This file makes a START on the *soundness* direction for the Aspis atomic
same-path spend relation (`paper/aspis-spend/sections/relation.tex`,
`def:spend-relation`): does the deployed constraint system actually capture the
spend relation `RProfile(x,w)=1`?

The relation has ten clauses (Equations (owner-key)…(range-out) in the paper).
They split cleanly into two groups:

* **Finite algebra** — the three 30-bit range checks and the integer balance
  `v' + f = v`.  These are pure field identities over `F = ZMod (2^31-1)` and
  are proved here IN-KERNEL, sorry-free, discharging directly from the shape of
  the deployed evaluator (`crates/aspis-statement/src/atomic_state_only_terminal.rs`,
  `SemanticRange` block, and `direct_range_hiding_v4.rs`).

* **Hash / Merkle** — the four domain-separated Poseidon2 hash equations
  (owner key, input note, nullifier, output note) and the two Merkle
  same-path root bindings.  These need either an exhaustive symbolic check of
  the deployed Poseidon2 gate bytes or a full Poseidon2/Merkle model in Lean.
  They are NOT proved here.  They are stated as an EXPLICIT named interface
  (`ArithmetizationModels`) whose fields are exactly the unproved obligations
  "constraint-satisfaction ⟹ this clause", clearly flagged.

`arithmetization_sound` then assembles the full `SpendRelation` from a
`ConstraintsSatisfied` witness: the range/balance/asset clauses are discharged
by the in-kernel lemmas below, and the hash/Merkle clauses are discharged from
the interface fields.  Nothing is faked and there is no `sorry`.

## Honesty ledger (see `#print axioms` at the bottom)

| Relation clause (paper eq.)      | Status in this file                         |
|----------------------------------|---------------------------------------------|
| (range-in)  `v = ℓ0+2^10ℓ1+2^20ℓ2` | PROVED in-kernel (`range_value_sound`)    |
| (range-out) same for `v'`          | PROVED in-kernel (`range_value_sound`)    |
| 30-bit bound `v,v' < 2^30`         | PROVED in-kernel (`range_value_sound`)    |
| (balance)   `v' + f = v` (ℤ)       | PROVED in-kernel (`range_balance_sound`,  |
|                                    |   composing with `ValueConservation`)     |
| (asset-eq)  `a_in = a`             | PROVED in-kernel (terminal field binding) |
| (owner-key) `pk_in = H_own(k_ν)`   | INTERFACE obligation (Poseidon2 gate)     |
| (input-note)`L_in = H_note(...)`   | INTERFACE obligation (Poseidon2 gate)     |
| (nullifier) `ν = H_nul(...)`       | INTERFACE obligation (Poseidon2 gate)     |
| (output-note)`C_out = H_note(...)` | INTERFACE obligation (Poseidon2 gate)     |
| (input-root)`A = Root(L_in;i,σ)`   | INTERFACE obligation (Merkle selection)   |
| (output-root)`A' = Root(C_out;i,σ)`| INTERFACE obligation (Merkle selection)   |

Closing the six interface obligations requires either an exhaustive symbolic
check of the deployed constraint bytes (the atomic-v3 registry / Poseidon2
gate polynomials) or a Poseidon2 permutation + two-to-one compression model in
Lean, matching the trace realization argument of `prop:relation-realization`.
-/

namespace AspisFormal.ArithmetizationCore

open Finset

/-- The M31 base field of the relation, `p = 2^31 - 1`. -/
abbrev p : ℕ := 2147483647

/-- `p = 2^31 - 1` is the Mersenne prime M31; needed for `F` to be a domain
    (so a booleanity constraint `b(b-1)=0` forces `b ∈ {0,1}`). -/
instance : Fact (Nat.Prime p) := ⟨by norm_num⟩

/-- The relation's base field `F = F_p`. -/
abbrev F : Type := ZMod p

/-- A payment digest is an element of `F^8`. -/
abbrev Digest : Type := Fin 8 → F

/-! ## Part 1: in-kernel lemmas (pure finite algebra) -/

/-- Field-to-nat bridge: two naturals below `p` that agree in `F` are equal.
    This is what turns a modular (field) identity into an integer identity. -/
theorem nat_of_field_eq {a b : ℕ} (ha : a < p) (hb : b < p) (h : (a : F) = (b : F)) :
    a = b := by
  rw [ZMod.natCast_eq_natCast_iff] at h
  have hha := Nat.mod_eq_of_lt ha
  have hhb := Nat.mod_eq_of_lt hb
  unfold Nat.ModEq at h
  omega

/-- A booleanity constraint `x(x-1)=0` over the field forces `x ∈ {0,1}`. -/
theorem field_bool {x : F} (h : x * (x - 1) = 0) : x = 0 ∨ x = 1 := by
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

/-- A boolean field element is the cast of a nat `≤ 1`. -/
theorem bit_val {x : F} (h : x * (x - 1) = 0) :
    ∃ b : ℕ, b ≤ 1 ∧ x = (b : F) := by
  rcases field_bool h with rfl | rfl
  · exact ⟨0, by norm_num, by norm_num⟩
  · exact ⟨1, by norm_num, by norm_num⟩

/-- The residuals of the deployed direct-range block for ONE 30-bit value:
    30 bit columns (3 limbs × 10 bits), 3 reconstruction columns, and the
    combined value column `z[11]`.  Mirrors `SemanticRange` in
    `atomic_state_only_terminal.rs` and the layout in `direct_range_hiding_v4.rs`. -/
structure RangeWitness where
  /-- bit columns, `bit j k` = k-th bit of limb `j`. -/
  bit : Fin 3 → Fin 10 → F
  /-- committed reconstruction column for limb `j` (`view[10]`). -/
  limb : Fin 3 → F
  /-- combined value column `z[11]` (input `v` or output `v'`). -/
  value : F

/-- The deployed range residuals all vanish, exactly as in the evaluator:
    each bit is boolean, each limb reconstructs from its ten bits, and the
    value reconstructs from the three limbs. -/
structure RangeResiduals (rw : RangeWitness) : Prop where
  /-- `bit(bit-1)=0` for all 30 bits. -/
  bitness : ∀ j k, rw.bit j k * (rw.bit j k - 1) = 0
  /-- `limb_j = Σ_{k<10} bit_{j,k} 2^k`. -/
  limbRecon : ∀ j, rw.limb j = ∑ k : Fin 10, rw.bit j k * (2 : F) ^ (k : ℕ)
  /-- `value = Σ_{j<3} limb_j 2^{10 j}` (paper eq. range-in / range-out). -/
  valueRecon : rw.value = ∑ j : Fin 3, rw.limb j * (2 : F) ^ (10 * (j : ℕ))

/-- Sum of the first ten powers of two. -/
private theorem sum_pow_two_ten : (∑ k : Fin 10, (2 : ℕ) ^ (k : ℕ)) = 1023 := by
  simp [Fin.sum_univ_succ]

/-- **Range check (paper eqs. range-in / range-out).**  If the deployed range
    residuals vanish, the value column is the cast of a natural number that is
    genuinely `< 2^30`, reconstructed from its ten-bit limbs.  Proved in-kernel. -/
theorem range_value_sound (rw : RangeWitness) (h : RangeResiduals rw) :
    ∃ V : ℕ, V < 2 ^ 30 ∧ rw.value = (V : F) := by
  -- nat bit values with `B j k ≤ 1` and `bit j k = (B j k : F)`
  choose B hB using fun (j : Fin 3) (k : Fin 10) => bit_val (h.bitness j k)
  -- nat limb value
  set L : Fin 3 → ℕ := fun j => ∑ k : Fin 10, B j k * 2 ^ (k : ℕ) with hLdef
  -- each limb is the cast of `L j`
  have hlimbCast : ∀ j, rw.limb j = ((L j : ℕ) : F) := by
    intro j
    rw [h.limbRecon j, hLdef]
    push_cast
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [(hB j k).2]
  -- each limb value is `< 2^10`
  have hLlt : ∀ j, L j < 2 ^ 10 := by
    intro j
    have hle : L j ≤ ∑ k : Fin 10, (2 : ℕ) ^ (k : ℕ) := by
      apply Finset.sum_le_sum
      intro k _
      calc B j k * 2 ^ (k : ℕ) ≤ 1 * 2 ^ (k : ℕ) :=
            Nat.mul_le_mul_right _ (hB j k).1
        _ = 2 ^ (k : ℕ) := one_mul _
    rw [sum_pow_two_ten] at hle
    omega
  -- combined nat value
  refine ⟨L 0 + L 1 * 2 ^ 10 + L 2 * 2 ^ 20, ?_, ?_⟩
  · have h0 := hLlt 0
    have h1 := hLlt 1
    have h2 := hLlt 2
    omega
  · rw [h.valueRecon, Fin.sum_univ_three, hlimbCast 0, hlimbCast 1, hlimbCast 2]
    norm_num

/-- **Balance ⟹ conservation (paper eq. balance).**  Given the range residuals
    for the input value column and the output value column, plus the deployed
    balance constraint `value_in = value_out + f` over the field and the public
    fee bound `f < 2^30`, the balance holds as an INTEGER equality `v' + f = v`.

    The final `omega` is exactly `value_conservation_no_wraparound` from
    `AspisFormal.ValueConservation`: because `v, v', f < 2^30` and
    `2·(2^30-1) < p`, the modular balance cannot wrap.  Proved in-kernel. -/
theorem range_balance_sound
    (rin rout : RangeWitness) (f : ℕ)
    (hin : RangeResiduals rin) (hout : RangeResiduals rout) (hf : f < 2 ^ 30)
    (hbal : rin.value = rout.value + (f : F)) :
    ∃ v v' : ℕ, v < 2 ^ 30 ∧ v' < 2 ^ 30 ∧
      rin.value = (v : F) ∧ rout.value = (v' : F) ∧ v' + f = v := by
  obtain ⟨v, hv, hvval⟩ := range_value_sound rin hin
  obtain ⟨v', hv', hv'val⟩ := range_value_sound rout hout
  refine ⟨v, v', hv, hv', hvval, hv'val, ?_⟩
  -- transfer the field balance to a nat identity via the no-wraparound bridge
  have hfield : ((v' + f : ℕ) : F) = (v : F) := by
    rw [hvval, hv'val] at hbal
    push_cast
    rw [hbal]
  have hp : p = 2147483647 := rfl
  have hlt1 : v' + f < p := by omega
  have hlt2 : v < p := by omega
  have : v' + f = v := nat_of_field_eq hlt1 hlt2 hfield
  omega

/-! ## Part 2: the relation and the (unproved) arithmetization interface

The finite-algebra clauses above are packaged, together with the hash/Merkle
clauses that remain interface obligations, into a single `SpendRelation`
predicate and a `ConstraintsSatisfied` / `ArithmetizationModels` pair. -/

/-- Merkle direction step (paper `Parent_b`). -/
def Parent (Hnode : Digest → Digest → Digest) (b : Bool) (X S : Digest) : Digest :=
  if b then Hnode S X else Hnode X S

/-- Merkle root along a private path of twenty siblings (paper `Root`). -/
def Root (Hnode : Digest → Digest → Digest)
    (L : Digest) (bits : Fin 20 → Bool) (sib : Fin 20 → Digest) : Digest :=
  Fin.foldl 20 (fun X j => Parent Hnode (bits j) X (sib j)) L

/-- All opened columns of a candidate accepting trace that the relation and the
    constraint families refer to.  These are the values the polynomial opening
    exposes; the `RangeWitness` fields carry the value/limb/bit columns. -/
structure OpenedColumns where
  /-- input-value range block (columns for `v`). -/
  rin : RangeWitness
  /-- output-value range block (columns for `v'`). -/
  rout : RangeWitness
  -- opened digest columns of the four hash blocks and two roots
  k_nu : Digest
  r_in : Digest
  r_out : Digest
  pk_out : Digest
  pk_in : Digest
  L_in : Digest
  nu : Digest
  C_out : Digest
  A : Digest
  A' : Digest
  -- opened input-asset and public asset columns
  a_in : F
  a : F
  /-- shared Merkle direction bits and siblings (same in both roots). -/
  bits : Fin 20 → Bool
  sib : Fin 20 → Digest
  /-- public fee and its statement-level 30-bit bound. -/
  f : ℕ
  hf : f < 2 ^ 30

/-- The deployed constraint families all vanish on these opened columns.  The
    range/balance/asset fields are the exact field residuals of the evaluator
    (`SemanticRange`, `SemanticPublic`); the Poseidon2 and copy/selection
    residuals are represented by the interface below, since their *content*
    (that vanishing forces the hash/Merkle equations) is the unproved part. -/
structure ConstraintsSatisfied (O : OpenedColumns) : Prop where
  /-- input 30-bit range residuals vanish. -/
  rangeIn : RangeResiduals O.rin
  /-- output 30-bit range residuals vanish. -/
  rangeOut : RangeResiduals O.rout
  /-- balance residual `z[11] - z[12] - fee = 0`. -/
  balance : O.rin.value = O.rout.value + (O.f : F)
  /-- input-asset public-terminal binding `opened = statement.asset_id`. -/
  assetIn : O.a_in = O.a

/-- **The frontier, stated not faked.**  Each field is an UNPROVED obligation
    that the deployed constraint system realizes the corresponding relation
    clause: constraint-satisfaction implies the hash / Merkle equation.  These
    are precisely the facts that need the deployed Poseidon2 gate bytes or a
    Poseidon2/Merkle model in Lean (`prop:relation-realization`, forward
    direction).  They are assumptions here, never proved and never `sorry`. -/
structure ArithmetizationModels
    (Hown : Digest → Digest)
    (Hnote : Digest → F → F → Digest → Digest)
    (Hnul : Digest → Digest → Digest)
    (Hnode : Digest → Digest → Digest)
    (O : OpenedColumns) : Prop where
  /-- owner-key Poseidon2 block ⟹ paper eq. owner-key. -/
  owner : ConstraintsSatisfied O → O.pk_in = Hown O.k_nu
  /-- input-note sponge block ⟹ paper eq. input-note (value bound to nat `v`). -/
  input_note : ConstraintsSatisfied O →
    ∀ v : ℕ, O.rin.value = (v : F) → O.L_in = Hnote O.pk_in (v : F) O.a_in O.r_in
  /-- nullifier sponge block ⟹ paper eq. nullifier. -/
  nullifier : ConstraintsSatisfied O → O.nu = Hnul O.k_nu O.r_in
  /-- output-note sponge block ⟹ paper eq. output-note. -/
  output_note : ConstraintsSatisfied O →
    ∀ v' : ℕ, O.rout.value = (v' : F) → O.C_out = Hnote O.pk_out (v' : F) O.a O.r_out
  /-- input Merkle selection/copy lane ⟹ paper eq. input-root. -/
  input_root : ConstraintsSatisfied O → O.A = Root Hnode O.L_in O.bits O.sib
  /-- output Merkle selection/copy lane, same path ⟹ paper eq. output-root. -/
  output_root : ConstraintsSatisfied O → O.A' = Root Hnode O.C_out O.bits O.sib

/-- The full atomic same-path spend relation `RProfile(x,w)=1`
    (paper `def:spend-relation`), stated over the opened columns and the two
    extracted integer values `v, v'`. -/
structure SpendRelation
    (Hown : Digest → Digest)
    (Hnote : Digest → F → F → Digest → Digest)
    (Hnul : Digest → Digest → Digest)
    (Hnode : Digest → Digest → Digest)
    (O : OpenedColumns) (v v' : ℕ) : Prop where
  owner_key : O.pk_in = Hown O.k_nu
  input_note : O.L_in = Hnote O.pk_in (v : F) O.a_in O.r_in
  nullifier : O.nu = Hnul O.k_nu O.r_in
  output_note : O.C_out = Hnote O.pk_out (v' : F) O.a O.r_out
  input_root : O.A = Root Hnode O.L_in O.bits O.sib
  output_root : O.A' = Root Hnode O.C_out O.bits O.sib
  asset_equality : O.a_in = O.a
  /-- integer balance (paper eq. balance). -/
  balance : v' + O.f = v
  /-- 30-bit range and reconstruction of `v` (paper eq. range-in). -/
  range_in : v < 2 ^ 30 ∧ O.rin.value = (v : F)
  /-- 30-bit range and reconstruction of `v'` (paper eq. range-out). -/
  range_out : v' < 2 ^ 30 ∧ O.rout.value = (v' : F)

/-- **Interface-conditional arithmetization soundness.**  Assuming the six
    hash/Merkle obligations of `ArithmetizationModels`, a satisfying assignment
    of the deployed constraints yields integer values `v, v'` for which the full
    spend relation holds.  The range, balance, and asset clauses are discharged
    IN-KERNEL by `range_balance_sound` and the terminal field binding; the
    hash/Merkle clauses are discharged from the interface fields. -/
theorem arithmetization_sound
    {Hown : Digest → Digest}
    {Hnote : Digest → F → F → Digest → Digest}
    {Hnul : Digest → Digest → Digest}
    {Hnode : Digest → Digest → Digest}
    {O : OpenedColumns}
    (I : ArithmetizationModels Hown Hnote Hnul Hnode O)
    (C : ConstraintsSatisfied O) :
    ∃ v v' : ℕ, SpendRelation Hown Hnote Hnul Hnode O v v' := by
  obtain ⟨v, v', hv, hv', hvval, hv'val, hbal⟩ :=
    range_balance_sound O.rin O.rout O.f C.rangeIn C.rangeOut O.hf C.balance
  exact ⟨v, v',
    { owner_key := I.owner C
      input_note := I.input_note C v hvval
      nullifier := I.nullifier C
      output_note := I.output_note C v' hv'val
      input_root := I.input_root C
      output_root := I.output_root C
      asset_equality := C.assetIn
      balance := hbal
      range_in := ⟨hv, hvval⟩
      range_out := ⟨hv', hv'val⟩ }⟩

end AspisFormal.ArithmetizationCore

#print axioms AspisFormal.ArithmetizationCore.range_value_sound
#print axioms AspisFormal.ArithmetizationCore.range_balance_sound
#print axioms AspisFormal.ArithmetizationCore.arithmetization_sound

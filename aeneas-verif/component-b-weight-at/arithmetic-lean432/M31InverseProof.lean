import AspisCoreM31Inverse
import M31MulProof
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum.Prime

/-!
# Source-authentic M31 inverse correspondence

This file proves the Lean 4.31 model extracted by Aeneas from the production
`M31::inv` body.  The generated model contains the Rust assertion, its actual
`square_n` iterator loop, and the complete addition chain.  The independent
Lean 4.32 file `V5M31InverseAdditionChain.lean` was read only as a specification
cross-check; it is deliberately not imported across the toolchain boundary.
-/

open Aeneas Aeneas.Std Result

namespace AspisAeneasM31Inverse

open AspisCoreM31Inverse

abbrev RustM31 := field.M31
abbrev m31Modulus : Nat := 2147483647
def CanonicalRawM31 (x : Nat) : Prop := x < m31Modulus
instance m31PrimeFact : Fact m31Modulus.Prime := ⟨by norm_num [m31Modulus]⟩
abbrev M31Exact := ZMod m31Modulus

/-! ## Transfer of the already-proved source-authentic M31 multiplication -/

theorem extracted_reduce_u64_eq_existing (x : Std.U64) :
    field.reduce_u64 x = AspisCoreMul.field.reduce_u64 x := by
  have hP : field.P = AspisCoreMul.field.P := by
    apply UScalar.eq_of_val_eq
    unfold field.P AspisCoreMul.field.P
    rfl
  unfold field.reduce_u64 AspisCoreMul.field.reduce_u64
  rw [hP]

theorem extracted_m31_mul_eq_existing (a b : RustM31) :
    field.M31.mul a b = AspisCoreMul.field.M31.mul a b := by
  unfold field.M31.mul AspisCoreMul.field.M31.mul
  simp only [Std.lift, bind_tc_ok]
  rw [extracted_reduce_u64_eq_existing]

theorem extracted_m31_mul_corresponds
    (a b : RustM31)
    (ha : CanonicalRawM31 a.val) (hb : CanonicalRawM31 b.val) :
    ∃ out : RustM31,
      field.M31.mul a b = ok out ∧
      CanonicalRawM31 out.val ∧
      ((out.val : Nat) : M31Exact) =
        (a.val : M31Exact) * (b.val : M31Exact) := by
  have ha' : AspisAeneasM31Mul.CanonicalRawM31 a.val := ha
  have hb' : AspisAeneasM31Mul.CanonicalRawM31 b.val := hb
  rcases AspisAeneasM31Mul.extracted_m31_mul_corresponds a b ha' hb' with
    ⟨out, hout, _hraw, hcanonical, hexact⟩
  refine ⟨out, ?_, hcanonical, hexact⟩
  rw [extracted_m31_mul_eq_existing]
  exact hout

/-! ## The generated `square_n` iterator loop -/

theorem extracted_square_n_loop_corresponds
    (remaining : Nat)
    (iter : core.ops.range.Range Std.Usize)
    (hspan : iter.start.val + remaining = iter.end.val)
    (value : RustM31) (hvalue : CanonicalRawM31 value.val) :
    ∃ out : RustM31,
      field.square_n_loop iter value = ok out ∧
      CanonicalRawM31 out.val ∧
      ((out.val : Nat) : M31Exact) =
        (value.val : M31Exact) ^ (2 ^ remaining) := by
  induction remaining generalizing iter value with
  | zero =>
      have hge : iter.start.val ≥ iter.end.val := by omega
      have hs := core.iter.range.IteratorRange.next_Usize_none_spec iter hge
      rcases Aeneas.Std.WP.spec_imp_exists hs with
        ⟨⟨opt, iter'⟩, hnext, hopt, hiter⟩
      rw [hopt, hiter] at hnext
      refine ⟨value, ?_, hvalue, ?_⟩
      · rw [field.square_n_loop.eq_def, hnext]
        rfl
      · simp
  | succ n ih =>
      have hlt : iter.start.val < iter.end.val := by omega
      have hs := core.iter.range.IteratorRange.next_Usize_some_spec iter hlt
      rcases Aeneas.Std.WP.spec_imp_exists hs with
        ⟨⟨opt, iter'⟩, hnext, hopt, hstart, hend⟩
      rw [hopt] at hnext
      rcases extracted_m31_mul_corresponds value value hvalue hvalue with
        ⟨value', hmul, hvalue', hexact⟩
      have hspan' : iter'.start.val + n = iter'.end.val := by
        rw [hend, hstart]
        omega
      rcases ih iter' hspan' value' hvalue' with
        ⟨out, hloop, hout, houtExact⟩
      refine ⟨out, ?_, hout, ?_⟩
      · rw [field.square_n_loop.eq_def, hnext]
        simp only [bind_tc_ok]
        rw [hmul]
        simp only [bind_tc_ok]
        change field.square_n_loop iter' value' = ok out
        exact hloop
      · rw [houtExact, hexact, ← pow_two, ← pow_mul]
        congr 1
        simp [pow_succ, Nat.mul_comm]

theorem extracted_square_n_corresponds
    (value : RustM31) (hvalue : CanonicalRawM31 value.val)
    (count : Std.Usize) :
    ∃ out : RustM31,
      field.square_n value count = ok out ∧
      CanonicalRawM31 out.val ∧
      ((out.val : Nat) : M31Exact) =
        (value.val : M31Exact) ^ (2 ^ count.val) := by
  exact extracted_square_n_loop_corresponds count.val
    { start := 0#usize, «end» := count } (by simp) value hvalue

/-! ## Exact production addition-chain trace -/

/-- Every value produced by the actual Rust `M31::inv` call graph, in source
order.  The names `t2Squared2` etc. correspond to the anonymous `m1`, `m2`, …
temporaries in the generated Aeneas definition. -/
structure InverseChainTrace where
  x2 : RustM31
  t2 : RustM31
  t2Squared2 : RustM31
  t4 : RustM31
  t4Squared4 : RustM31
  t8 : RustM31
  t8Squared8 : RustM31
  t16 : RustM31
  t16Squared8 : RustM31
  t24 : RustM31
  t24Squared4 : RustM31
  t28 : RustM31
  t28Squared : RustM31
  t29 : RustM31
  t30 : RustM31
  t30Squared : RustM31
  out : RustM31

/-- The trace is tied to the generated functions, rather than merely to a
separately transcribed value-level chain. -/
def TraceRuns (x : RustM31) (t : InverseChainTrace) : Prop :=
  field.M31.mul x x = ok t.x2 ∧
  field.M31.mul t.x2 x = ok t.t2 ∧
  field.square_n t.t2 2#usize = ok t.t2Squared2 ∧
  field.M31.mul t.t2Squared2 t.t2 = ok t.t4 ∧
  field.square_n t.t4 4#usize = ok t.t4Squared4 ∧
  field.M31.mul t.t4Squared4 t.t4 = ok t.t8 ∧
  field.square_n t.t8 8#usize = ok t.t8Squared8 ∧
  field.M31.mul t.t8Squared8 t.t8 = ok t.t16 ∧
  field.square_n t.t16 8#usize = ok t.t16Squared8 ∧
  field.M31.mul t.t16Squared8 t.t8 = ok t.t24 ∧
  field.square_n t.t24 4#usize = ok t.t24Squared4 ∧
  field.M31.mul t.t24Squared4 t.t4 = ok t.t28 ∧
  field.M31.mul t.t28 t.t28 = ok t.t28Squared ∧
  field.M31.mul t.t28Squared x = ok t.t29 ∧
  field.M31.mul t.t29 t.t29 = ok t.t30 ∧
  field.M31.mul t.t30 t.t30 = ok t.t30Squared ∧
  field.M31.mul t.t30Squared x = ok t.out

/-- Canonicality is recorded for every Rust intermediate, not just the final
return value. -/
def TraceCanonical (t : InverseChainTrace) : Prop :=
  CanonicalRawM31 t.x2.val ∧
  CanonicalRawM31 t.t2.val ∧
  CanonicalRawM31 t.t2Squared2.val ∧
  CanonicalRawM31 t.t4.val ∧
  CanonicalRawM31 t.t4Squared4.val ∧
  CanonicalRawM31 t.t8.val ∧
  CanonicalRawM31 t.t8Squared8.val ∧
  CanonicalRawM31 t.t16.val ∧
  CanonicalRawM31 t.t16Squared8.val ∧
  CanonicalRawM31 t.t24.val ∧
  CanonicalRawM31 t.t24Squared4.val ∧
  CanonicalRawM31 t.t28.val ∧
  CanonicalRawM31 t.t28Squared.val ∧
  CanonicalRawM31 t.t29.val ∧
  CanonicalRawM31 t.t30.val ∧
  CanonicalRawM31 t.t30Squared.val ∧
  CanonicalRawM31 t.out.val

/-- Exact exponent carried by every addition-chain intermediate. -/
def TraceExact (x : RustM31) (t : InverseChainTrace) : Prop :=
  let z : M31Exact := x.val
  (t.x2.val : M31Exact) = z ^ 2 ∧
  (t.t2.val : M31Exact) = z ^ 3 ∧
  (t.t2Squared2.val : M31Exact) = z ^ 12 ∧
  (t.t4.val : M31Exact) = z ^ 15 ∧
  (t.t4Squared4.val : M31Exact) = z ^ 240 ∧
  (t.t8.val : M31Exact) = z ^ 255 ∧
  (t.t8Squared8.val : M31Exact) = z ^ 65280 ∧
  (t.t16.val : M31Exact) = z ^ 65535 ∧
  (t.t16Squared8.val : M31Exact) = z ^ 16776960 ∧
  (t.t24.val : M31Exact) = z ^ 16777215 ∧
  (t.t24Squared4.val : M31Exact) = z ^ 268435440 ∧
  (t.t28.val : M31Exact) = z ^ 268435455 ∧
  (t.t28Squared.val : M31Exact) = z ^ 536870910 ∧
  (t.t29.val : M31Exact) = z ^ 536870911 ∧
  (t.t30.val : M31Exact) = z ^ 1073741822 ∧
  (t.t30Squared.val : M31Exact) = z ^ 2147483644 ∧
  (t.out.val : M31Exact) = z ^ (m31Modulus - 2)

/-! ## Domain and exact inverse facts -/

theorem canonical_raw_ne_zero_is_residue_ne_zero
    (x : RustM31) (hxCanonical : CanonicalRawM31 x.val)
    (hxNonzero : x.val ≠ 0) :
    ((x.val : Nat) : M31Exact) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hdiv
  have hle : m31Modulus ≤ x.val :=
    Nat.le_of_dvd (Nat.zero_lt_of_ne_zero hxNonzero) hdiv
  exact (Nat.not_le_of_lt hxCanonical) hle

theorem pow_m31_sub_two_eq_inv (z : M31Exact) :
    z ^ (m31Modulus - 2) = z⁻¹ := by
  by_cases hz : z = 0
  · subst hz
    rw [zero_pow (by norm_num [m31Modulus]), inv_zero]
  · rw [inv_eq_one_div, eq_div_iff hz, ← pow_succ,
      show (m31Modulus - 2) + 1 = m31Modulus - 1 by
        norm_num [m31Modulus]]
    exact ZMod.pow_card_sub_one_eq_one hz

/-- The generated assertion rejects precisely the forbidden zero input. -/
theorem extracted_m31_inv_zero_assertion_failure :
    field.M31.inv 0#u32 = fail Error.assertionFailure := by
  simp [field.M31.inv, massert]

/-! ## Teeth -/

/-- If the `t28` dependency is changed from `t4` to `t8`, the natural-number
addition chain carries a different exponent.  This catches a concrete
dependency/order transcription error before any field reduction can hide it. -/
theorem wrong_t28_dependency_changes_exponent :
    16777215 * (2 ^ 4) + 255 ≠ (268435455 : Nat) := by
  norm_num

/-- The same concrete dependency error propagates to a wrong final exponent,
so later squarings cannot repair the schedule. -/
theorem wrong_t28_dependency_changes_final_exponent :
    let wrongT28 := 16777215 * (2 ^ 4) + 255
    let wrongT29 := wrongT28 + wrongT28 + 1
    let wrongT30 := wrongT29 + wrongT29
    wrongT30 + wrongT30 + 1 ≠ m31Modulus - 2 := by
  norm_num [m31Modulus]

/-! ## Source-authentic capstone -/

/-- The actual extracted Rust inverse succeeds on exactly the stated nonzero
canonical domain.  Its full generated call graph has a trace in which every
intermediate is canonical, every intermediate carries the source-schedule
exponent, the final exponent is `P - 2`, and the returned residue is the
two-sided field inverse. -/
theorem extracted_m31_inv_corresponds
    (x : RustM31) (hxCanonical : CanonicalRawM31 x.val)
    (hxNonzero : x.val ≠ 0) :
    ∃ trace : InverseChainTrace,
      TraceRuns x trace ∧
      TraceCanonical trace ∧
      TraceExact x trace ∧
      field.M31.inv x = ok trace.out ∧
      ((trace.out.val : Nat) : M31Exact) =
        ((x.val : Nat) : M31Exact)⁻¹ ∧
      ((x.val : Nat) : M31Exact) *
          ((trace.out.val : Nat) : M31Exact) = 1 ∧
      ((trace.out.val : Nat) : M31Exact) *
          ((x.val : Nat) : M31Exact) = 1 := by
  rcases extracted_m31_mul_corresponds x x hxCanonical hxCanonical with
    ⟨x2, hx2Run, hx2Canonical, hx2Exact⟩
  rcases extracted_m31_mul_corresponds x2 x hx2Canonical hxCanonical with
    ⟨t2, ht2Run, ht2Canonical, ht2Exact⟩
  rcases extracted_square_n_corresponds t2 ht2Canonical 2#usize with
    ⟨t2Squared2, ht2Squared2Run, ht2Squared2Canonical, ht2Squared2Exact⟩
  rcases extracted_m31_mul_corresponds
      t2Squared2 t2 ht2Squared2Canonical ht2Canonical with
    ⟨t4, ht4Run, ht4Canonical, ht4Exact⟩
  rcases extracted_square_n_corresponds t4 ht4Canonical 4#usize with
    ⟨t4Squared4, ht4Squared4Run, ht4Squared4Canonical, ht4Squared4Exact⟩
  rcases extracted_m31_mul_corresponds
      t4Squared4 t4 ht4Squared4Canonical ht4Canonical with
    ⟨t8, ht8Run, ht8Canonical, ht8Exact⟩
  rcases extracted_square_n_corresponds t8 ht8Canonical 8#usize with
    ⟨t8Squared8, ht8Squared8Run, ht8Squared8Canonical, ht8Squared8Exact⟩
  rcases extracted_m31_mul_corresponds
      t8Squared8 t8 ht8Squared8Canonical ht8Canonical with
    ⟨t16, ht16Run, ht16Canonical, ht16Exact⟩
  rcases extracted_square_n_corresponds t16 ht16Canonical 8#usize with
    ⟨t16Squared8, ht16Squared8Run, ht16Squared8Canonical, ht16Squared8Exact⟩
  rcases extracted_m31_mul_corresponds
      t16Squared8 t8 ht16Squared8Canonical ht8Canonical with
    ⟨t24, ht24Run, ht24Canonical, ht24Exact⟩
  rcases extracted_square_n_corresponds t24 ht24Canonical 4#usize with
    ⟨t24Squared4, ht24Squared4Run, ht24Squared4Canonical, ht24Squared4Exact⟩
  rcases extracted_m31_mul_corresponds
      t24Squared4 t4 ht24Squared4Canonical ht4Canonical with
    ⟨t28, ht28Run, ht28Canonical, ht28Exact⟩
  rcases extracted_m31_mul_corresponds
      t28 t28 ht28Canonical ht28Canonical with
    ⟨t28Squared, ht28SquaredRun, ht28SquaredCanonical, ht28SquaredExact⟩
  rcases extracted_m31_mul_corresponds
      t28Squared x ht28SquaredCanonical hxCanonical with
    ⟨t29, ht29Run, ht29Canonical, ht29Exact⟩
  rcases extracted_m31_mul_corresponds
      t29 t29 ht29Canonical ht29Canonical with
    ⟨t30, ht30Run, ht30Canonical, ht30Exact⟩
  rcases extracted_m31_mul_corresponds
      t30 t30 ht30Canonical ht30Canonical with
    ⟨t30Squared, ht30SquaredRun, ht30SquaredCanonical, ht30SquaredExact⟩
  rcases extracted_m31_mul_corresponds
      t30Squared x ht30SquaredCanonical hxCanonical with
    ⟨out, houtRun, houtCanonical, houtExact⟩

  have hx2Pow :
      ((x2.val : Nat) : M31Exact) = ((x.val : Nat) : M31Exact) ^ 2 := by
    calc
      ((x2.val : Nat) : M31Exact) =
          (x.val : M31Exact) * (x.val : M31Exact) := hx2Exact
      _ = (x.val : M31Exact) ^ 2 := (pow_two _).symm
  have ht2Pow :
      ((t2.val : Nat) : M31Exact) = ((x.val : Nat) : M31Exact) ^ 3 := by
    calc
      ((t2.val : Nat) : M31Exact) =
          (x2.val : M31Exact) * (x.val : M31Exact) := ht2Exact
      _ = (x.val : M31Exact) ^ 2 * (x.val : M31Exact) := by rw [hx2Pow]
      _ = (x.val : M31Exact) ^ 3 := (pow_succ _ 2).symm
  have ht2Squared2Pow :
      ((t2Squared2.val : Nat) : M31Exact) =
        ((x.val : Nat) : M31Exact) ^ 12 := by
    rw [ht2Squared2Exact, ht2Pow, ← pow_mul]
    norm_num
  have ht4Pow :
      ((t4.val : Nat) : M31Exact) = ((x.val : Nat) : M31Exact) ^ 15 := by
    rw [ht4Exact, ht2Squared2Pow, ht2Pow, ← pow_add]
  have ht4Squared4Pow :
      ((t4Squared4.val : Nat) : M31Exact) =
        ((x.val : Nat) : M31Exact) ^ 240 := by
    rw [ht4Squared4Exact, ht4Pow, ← pow_mul]
    norm_num
  have ht8Pow :
      ((t8.val : Nat) : M31Exact) = ((x.val : Nat) : M31Exact) ^ 255 := by
    rw [ht8Exact, ht4Squared4Pow, ht4Pow, ← pow_add]
  have ht8Squared8Pow :
      ((t8Squared8.val : Nat) : M31Exact) =
        ((x.val : Nat) : M31Exact) ^ 65280 := by
    rw [ht8Squared8Exact, ht8Pow, ← pow_mul]
    norm_num
  have ht16Pow :
      ((t16.val : Nat) : M31Exact) = ((x.val : Nat) : M31Exact) ^ 65535 := by
    rw [ht16Exact, ht8Squared8Pow, ht8Pow, ← pow_add]
  have ht16Squared8Pow :
      ((t16Squared8.val : Nat) : M31Exact) =
        ((x.val : Nat) : M31Exact) ^ 16776960 := by
    rw [ht16Squared8Exact, ht16Pow, ← pow_mul]
    norm_num
  have ht24Pow :
      ((t24.val : Nat) : M31Exact) = ((x.val : Nat) : M31Exact) ^ 16777215 := by
    rw [ht24Exact, ht16Squared8Pow, ht8Pow, ← pow_add]
  have ht24Squared4Pow :
      ((t24Squared4.val : Nat) : M31Exact) =
        ((x.val : Nat) : M31Exact) ^ 268435440 := by
    rw [ht24Squared4Exact, ht24Pow, ← pow_mul]
    norm_num
  have ht28Pow :
      ((t28.val : Nat) : M31Exact) = ((x.val : Nat) : M31Exact) ^ 268435455 := by
    rw [ht28Exact, ht24Squared4Pow, ht4Pow, ← pow_add]
  have ht28SquaredPow :
      ((t28Squared.val : Nat) : M31Exact) =
        ((x.val : Nat) : M31Exact) ^ 536870910 := by
    rw [ht28SquaredExact, ht28Pow, ← pow_add]
  have ht29Pow :
      ((t29.val : Nat) : M31Exact) = ((x.val : Nat) : M31Exact) ^ 536870911 := by
    calc
      ((t29.val : Nat) : M31Exact) =
          (t28Squared.val : M31Exact) * (x.val : M31Exact) := ht29Exact
      _ = (x.val : M31Exact) ^ 536870910 * (x.val : M31Exact) := by
        rw [ht28SquaredPow]
      _ = (x.val : M31Exact) ^ (536870910 + 1) :=
        (pow_succ _ 536870910).symm
      _ = (x.val : M31Exact) ^ 536870911 := by norm_num
  have ht30Pow :
      ((t30.val : Nat) : M31Exact) = ((x.val : Nat) : M31Exact) ^ 1073741822 := by
    rw [ht30Exact, ht29Pow, ← pow_add]
  have ht30SquaredPow :
      ((t30Squared.val : Nat) : M31Exact) =
        ((x.val : Nat) : M31Exact) ^ 2147483644 := by
    rw [ht30SquaredExact, ht30Pow, ← pow_add]
  have houtPow :
      ((out.val : Nat) : M31Exact) =
        ((x.val : Nat) : M31Exact) ^ (m31Modulus - 2) := by
    calc
      ((out.val : Nat) : M31Exact) =
          (t30Squared.val : M31Exact) * (x.val : M31Exact) := houtExact
      _ = (x.val : M31Exact) ^ 2147483644 * (x.val : M31Exact) := by
        rw [ht30SquaredPow]
      _ = (x.val : M31Exact) ^ (2147483644 + 1) :=
        (pow_succ _ 2147483644).symm
      _ = (x.val : M31Exact) ^ (m31Modulus - 2) := by
        norm_num [m31Modulus]

  let trace : InverseChainTrace := {
    x2, t2, t2Squared2, t4, t4Squared4, t8, t8Squared8, t16,
    t16Squared8, t24, t24Squared4, t28, t28Squared, t29, t30,
    t30Squared, out }
  have hRuns : TraceRuns x trace := by
    simp only [TraceRuns, trace]
    exact ⟨hx2Run, ht2Run, ht2Squared2Run, ht4Run, ht4Squared4Run,
      ht8Run, ht8Squared8Run, ht16Run, ht16Squared8Run, ht24Run,
      ht24Squared4Run, ht28Run, ht28SquaredRun, ht29Run, ht30Run,
      ht30SquaredRun, houtRun⟩
  have hCanonical : TraceCanonical trace := by
    simp only [TraceCanonical, trace]
    exact ⟨hx2Canonical, ht2Canonical, ht2Squared2Canonical, ht4Canonical,
      ht4Squared4Canonical, ht8Canonical, ht8Squared8Canonical, ht16Canonical,
      ht16Squared8Canonical, ht24Canonical, ht24Squared4Canonical,
      ht28Canonical, ht28SquaredCanonical, ht29Canonical, ht30Canonical,
      ht30SquaredCanonical, houtCanonical⟩
  have hExact : TraceExact x trace := by
    simp only [TraceExact, trace]
    exact ⟨hx2Pow, ht2Pow, ht2Squared2Pow, ht4Pow, ht4Squared4Pow,
      ht8Pow, ht8Squared8Pow, ht16Pow, ht16Squared8Pow, ht24Pow,
      ht24Squared4Pow, ht28Pow, ht28SquaredPow, ht29Pow, ht30Pow,
      ht30SquaredPow, houtPow⟩
  have hxRust : x ≠ 0#u32 := by
    intro hx
    apply hxNonzero
    exact congrArg UScalar.val hx
  have hassert : massert (x != 0#u32) = ok () :=
    (Aeneas.Std.massert_ok _).2 (bne_iff_ne.mpr hxRust)
  have hInvRun : field.M31.inv x = ok out := by
    simp only [field.M31.inv, hassert, bind_tc_ok,
      hx2Run, ht2Run, ht2Squared2Run, ht4Run, ht4Squared4Run,
      ht8Run, ht8Squared8Run, ht16Run, ht16Squared8Run, ht24Run,
      ht24Squared4Run, ht28Run, ht28SquaredRun, ht29Run, ht30Run,
      ht30SquaredRun, houtRun]
  have hxExactNonzero : ((x.val : Nat) : M31Exact) ≠ 0 :=
    canonical_raw_ne_zero_is_residue_ne_zero x hxCanonical hxNonzero
  have houtInv :
      ((out.val : Nat) : M31Exact) = ((x.val : Nat) : M31Exact)⁻¹ := by
    rw [houtPow, pow_m31_sub_two_eq_inv]
  refine ⟨trace, hRuns, hCanonical, hExact, ?_, ?_, ?_, ?_⟩
  · simpa only [trace] using hInvRun
  · simpa only [trace] using houtInv
  · rw [houtInv]
    exact mul_inv_cancel₀ hxExactNonzero
  · rw [houtInv]
    exact inv_mul_cancel₀ hxExactNonzero

/-- On canonical Rust representatives, `assertionFailure` is returned exactly
at zero.  This is the executable domain statement complementary to the
nonzero-success capstone. -/
theorem extracted_m31_inv_assertion_failure_iff_zero
    (x : RustM31) (hxCanonical : CanonicalRawM31 x.val) :
    field.M31.inv x = fail Error.assertionFailure ↔ x.val = 0 := by
  constructor
  · intro hfail
    by_contra hxNonzero
    rcases extracted_m31_inv_corresponds x hxCanonical hxNonzero with
      ⟨trace, _hRuns, _hCanonical, _hExact, hrun, _hInv, _hLeft, _hRight⟩
    rw [hrun] at hfail
    cases hfail
  · intro hxZero
    have hx : x = 0#u32 := by
      apply UScalar.eq_of_val_eq
      exact hxZero
    subst x
    exact extracted_m31_inv_zero_assertion_failure

/-! ## Axiom audit -/

#print axioms extracted_reduce_u64_eq_existing
#print axioms extracted_m31_mul_corresponds
#print axioms extracted_square_n_loop_corresponds
#print axioms extracted_square_n_corresponds
#print axioms canonical_raw_ne_zero_is_residue_ne_zero
#print axioms pow_m31_sub_two_eq_inv
#print axioms extracted_m31_inv_zero_assertion_failure
#print axioms wrong_t28_dependency_changes_exponent
#print axioms wrong_t28_dependency_changes_final_exponent
#print axioms extracted_m31_inv_corresponds
#print axioms extracted_m31_inv_assertion_failure_iff_zero

end AspisAeneasM31Inverse

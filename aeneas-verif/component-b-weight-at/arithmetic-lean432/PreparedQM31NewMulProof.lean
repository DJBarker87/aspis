import QM31MulProof

/-!
# Source-authentic prepared QM31 construction and multiplication

The representation relation records the underlying lists of Aeneas fixed
arrays.  This makes all three deployed cache rows explicit while keeping the
proof tied to the generated `PreparedQm31Multiplier.new` and `mul` bodies.
-/

open Aeneas Aeneas.Std Result

namespace AspisAeneasPreparedQM31

open AspisAeneasQM31Mul

abbrev RustM31 := AspisCoreCM31Multiplicative.field.M31
abbrev RustCM31 := AspisCoreCM31Multiplicative.field.CM31
abbrev RustQM31 := AspisCoreCM31Multiplicative.field.QM31
abbrev RustPrepared :=
  AspisCoreCM31Multiplicative.field.PreparedQm31Multiplier

/-- A cache row stores the two source limbs and the result of the actual
generated base-field addition used for its Karatsuba sum. -/
def RepresentsCM31Row (row : Array RustM31 3#usize) (x : RustCM31) : Prop :=
  ∃ sum : RustM31,
    AspisCoreCM31Multiplicative.field.M31.add x.a x.b = ok sum ∧
    CanonicalRawM31 sum.val ∧
    row.val = [x.a, x.b, sum]

/-- The three cache rows are, in order, those for `c0`, `c1`, and the result
of the actual generated `c0.add(c1)` call. -/
def RepresentsPrepared (prepared : RustPrepared) (left : RustQM31) : Prop :=
  ∃ leftSum : RustCM31,
  ∃ row0 row1 row2 : Array RustM31 3#usize,
    AspisCoreCM31Multiplicative.field.CM31.add left.c0 left.c1 = ok leftSum ∧
    CanonicalCM31 leftSum ∧
    RepresentsCM31Row row0 left.c0 ∧
    RepresentsCM31Row row1 left.c1 ∧
    RepresentsCM31Row row2 leftSum ∧
    prepared.components.val = [row0, row1, row2]

private theorem index_zero_of_val
    {α : Type} (row : Array α 3#usize) (x0 x1 x2 : α)
    (hrow : row.val = [x0, x1, x2]) :
    Array.index_usize row 0#usize = ok x0 := by
  simp [Array.index_usize, hrow]

private theorem index_one_of_val
    {α : Type} (row : Array α 3#usize) (x0 x1 x2 : α)
    (hrow : row.val = [x0, x1, x2]) :
    Array.index_usize row 1#usize = ok x1 := by
  simp [Array.index_usize, hrow]

private theorem index_two_of_val
    {α : Type} (row : Array α 3#usize) (x0 x1 x2 : α)
    (hrow : row.val = [x0, x1, x2]) :
    Array.index_usize row 2#usize = ok x2 := by
  simp [Array.index_usize, hrow]

private theorem extracted_cm31_add_succeeds
    (x y : RustCM31) (hx : CanonicalCM31 x) (hy : CanonicalCM31 y) :
    ∃ out : RustCM31,
      AspisCoreCM31Multiplicative.field.CM31.add x y = ok out ∧
      CanonicalCM31 out := by
  rcases AspisAeneasCM31Multiplicative.extracted_m31_add_corresponds
      x.a y.a hx.1 hy.1 with
    ⟨oa, hcallA, hcanA, _⟩
  rcases AspisAeneasCM31Multiplicative.extracted_m31_add_corresponds
      x.b y.b hx.2 hy.2 with
    ⟨ob, hcallB, hcanB, _⟩
  refine ⟨⟨oa, ob⟩, ?_, ⟨hcanA, hcanB⟩⟩
  simp [AspisCoreCM31Multiplicative.field.CM31.add, hcallA, hcallB]

private theorem prepare_closure_establishes_row
    (x : RustCM31) (hx : CanonicalCM31 x) :
    ∃ row : Array RustM31 3#usize,
      AspisCoreCM31Multiplicative.field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call
          () x = ok row ∧
      RepresentsCM31Row row x := by
  rcases AspisAeneasCM31Multiplicative.extracted_m31_add_corresponds
      x.a x.b hx.1 hx.2 with
    ⟨sum, hsum, hsumCanonical, _⟩
  let row : Array RustM31 3#usize :=
    Array.make 3#usize [x.a, x.b, sum]
  refine ⟨row, ?_, ⟨sum, hsum, hsumCanonical, ?_⟩⟩
  · simp [AspisCoreCM31Multiplicative.field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call,
      hsum, row]
  · rfl

/-- The actual generated constructor succeeds for every canonical QM31 and
establishes all three exact cache rows in their deployed order. -/
theorem extracted_prepared_new_establishes
    (left : RustQM31) (hleft : CanonicalQM31 left) :
    ∃ prepared : RustPrepared,
      AspisCoreCM31Multiplicative.field.PreparedQm31Multiplier.new left =
        ok prepared ∧
      RepresentsPrepared prepared left := by
  rcases prepare_closure_establishes_row left.c0 hleft.1 with
    ⟨row0, hrow0Call, hrow0⟩
  rcases prepare_closure_establishes_row left.c1 hleft.2 with
    ⟨row1, hrow1Call, hrow1⟩
  rcases extracted_cm31_add_succeeds left.c0 left.c1 hleft.1 hleft.2 with
    ⟨leftSum, hleftSumCall, hleftSumCanonical⟩
  rcases prepare_closure_establishes_row leftSum hleftSumCanonical with
    ⟨row2, hrow2Call, hrow2⟩
  let prepared : RustPrepared :=
    ⟨Array.make 3#usize [row0, row1, row2]⟩
  refine ⟨prepared, ?_, ?_⟩
  · simp [AspisCoreCM31Multiplicative.field.PreparedQm31Multiplier.new,
      hrow0Call, hrow1Call, hleftSumCall, hrow2Call, prepared]
  · exact ⟨leftSum, row0, row1, row2, hleftSumCall,
      hleftSumCanonical, hrow0, hrow1, hrow2, rfl⟩

private theorem represented_row_call_eq_cm31_mul
    (row : Array RustM31 3#usize) (left right : RustCM31)
    (hrow : RepresentsCM31Row row left) :
    AspisCoreCM31Multiplicative.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
        () (row, right) =
      AspisCoreCM31Multiplicative.field.CM31.mul left right := by
  rcases hrow with ⟨sum, hsum, _hsumCanonical, hrowVal⟩
  simp [AspisCoreCM31Multiplicative.field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call,
    AspisCoreCM31Multiplicative.field.CM31.mul,
    Array.index_usize, hrowVal, hsum]

private theorem represented_prepared_mul_eq_qm31_mul
    (prepared : RustPrepared) (left right : RustQM31)
    (hprepared : RepresentsPrepared prepared left) :
    AspisCoreCM31Multiplicative.field.PreparedQm31Multiplier.mul
        prepared right =
      AspisCoreCM31Multiplicative.field.QM31.mul left right := by
  rcases hprepared with
    ⟨leftSum, row0, row1, row2, hleftSum, _hleftSumCanonical,
      hrow0, hrow1, hrow2, hcomponents⟩
  have hcomponent0 := index_zero_of_val
    prepared.components row0 row1 row2 hcomponents
  have hcomponent1 := index_one_of_val
    prepared.components row0 row1 row2 hcomponents
  have hcomponent2 := index_two_of_val
    prepared.components row0 row1 row2 hcomponents
  unfold AspisCoreCM31Multiplicative.field.PreparedQm31Multiplier.mul
  rw [hcomponent0, hcomponent1, hcomponent2]
  simp only [bind_tc_ok]
  rw [represented_row_call_eq_cm31_mul row0 left.c0 right.c0 hrow0]
  rw [represented_row_call_eq_cm31_mul row1 left.c1 right.c1 hrow1]
  simp_rw [represented_row_call_eq_cm31_mul row2 leftSum _ hrow2]
  unfold AspisCoreCM31Multiplicative.field.QM31.mul
  rw [hleftSum]
  simp only [bind_tc_ok]

/-- Every represented generated cache multiplies an arbitrary canonical right
operand with the exact source value, returning canonical limbs. -/
theorem extracted_prepared_mul_corresponds
    (prepared : RustPrepared) (left right : RustQM31)
    (hprepared : RepresentsPrepared prepared left)
    (hleft : CanonicalQM31 left) (hright : CanonicalQM31 right) :
    ∃ out : RustQM31,
      AspisCoreCM31Multiplicative.field.PreparedQm31Multiplier.mul
          prepared right = ok out ∧
      CanonicalQM31 out ∧
      qm31ToExact out = qm31ToExact left * qm31ToExact right := by
  rw [represented_prepared_mul_eq_qm31_mul prepared left right hprepared]
  exact extracted_qm31_mul_corresponds left right hleft hright

/-- End-to-end source correspondence for constructor followed by prepared
multiplication, quantified over both canonical Rust operands. -/
theorem extracted_new_then_prepared_mul_corresponds
    (left right : RustQM31)
    (hleft : CanonicalQM31 left) (hright : CanonicalQM31 right) :
    ∃ prepared : RustPrepared,
    ∃ out : RustQM31,
      AspisCoreCM31Multiplicative.field.PreparedQm31Multiplier.new left =
        ok prepared ∧
      RepresentsPrepared prepared left ∧
      AspisCoreCM31Multiplicative.field.PreparedQm31Multiplier.mul
          prepared right = ok out ∧
      CanonicalQM31 out ∧
      qm31ToExact out = qm31ToExact left * qm31ToExact right := by
  rcases extracted_prepared_new_establishes left hleft with
    ⟨prepared, hnew, hrep⟩
  rcases extracted_prepared_mul_corresponds
      prepared left right hrep hleft hright with
    ⟨out, hmul, houtCanonical, houtExact⟩
  exact ⟨prepared, out, hnew, hrep, hmul, houtCanonical, houtExact⟩

def wrongZeroCacheRow : Array RustM31 3#usize :=
  Array.make 3#usize [0#u32, 0#u32, 1#u32]

/-- A corrupted third entry is rejected even though its two source limbs are
the canonical zero pair. -/
theorem corrupted_cache_tooth :
    ¬ RepresentsCM31Row wrongZeroCacheRow ⟨0#u32, 0#u32⟩ := by
  norm_num [RepresentsCM31Row, wrongZeroCacheRow,
    AspisCoreCM31Multiplicative.field.M31.add,
    AspisCoreCM31Multiplicative.field.P, Std.lift, Array.make]

def toothRowC0 : Array RustM31 3#usize :=
  Array.make 3#usize [1#u32, 0#u32, 1#u32]

def toothRowC1 : Array RustM31 3#usize :=
  Array.make 3#usize [0#u32, 0#u32, 0#u32]

def toothLeft : RustQM31 :=
  ⟨⟨1#u32, 0#u32⟩, ⟨0#u32, 0#u32⟩⟩

def swappedToothPrepared : RustPrepared :=
  ⟨Array.make 3#usize [toothRowC1, toothRowC0, toothRowC0]⟩

/-- Swapping the distinct `c0` and `c1` cache rows violates the generated
constructor representation. -/
theorem swapped_rows_tooth :
    ¬ RepresentsPrepared swappedToothPrepared toothLeft := by
  rintro ⟨leftSum, row0, row1, row2, _hleftSum, _hleftSumCanonical,
    hrow0, _hrow1, _hrow2, hcomponents⟩
  rcases hrow0 with ⟨sum0, _hsum0, _hsum0Canonical, hrow0Val⟩
  have hcomponents' :
      [toothRowC1, toothRowC0, toothRowC0] = [row0, row1, row2] := by
    simpa [swappedToothPrepared, Array.make] using hcomponents
  have hfirst : toothRowC1 = row0 := by
    have hhead := congrArg List.head? hcomponents'
    simpa using hhead
  have hvalEq := congrArg
    (fun row : Array RustM31 3#usize => row.val) hfirst
  rw [hrow0Val] at hvalEq
  simp [toothRowC1, toothLeft, Array.make] at hvalEq

/-- The quantified source domain used by both capstones is inhabited. -/
theorem prepared_qm31_domain_nonempty :
    ∃ left : RustQM31,
    ∃ prepared : RustPrepared,
      CanonicalQM31 left ∧ RepresentsPrepared prepared left := by
  rcases canonical_qm31_nonempty with ⟨left, hleft⟩
  rcases extracted_prepared_new_establishes left hleft with
    ⟨prepared, _hnew, hrep⟩
  exact ⟨left, prepared, hleft, hrep⟩

#print axioms extracted_prepared_new_establishes
#print axioms extracted_prepared_mul_corresponds
#print axioms extracted_new_then_prepared_mul_corresponds
#print axioms corrupted_cache_tooth
#print axioms swapped_rows_tooth
#print axioms prepared_qm31_domain_nonempty

end AspisAeneasPreparedQM31

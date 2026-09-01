import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes

/-!
# Finite traces of literal Aeneas loops

This generic support lemma unfolds Aeneas' own partial fixpoint only along a
successful execution.  Its trace stores equations for the supplied generated
body verbatim; it does not define or replace a Rust loop.
-/

open Aeneas Aeneas.Std Result ControlFlow Error

set_option autoImplicit false
set_option maxRecDepth 50000

namespace AspisV7Tag73AeneasExactLoopTrace

universe u v

theorem bind_eq_ok_iff {A B : Type} (input : Result A)
    (next : A → Result B) (output : B) :
    Bind.bind input next = .ok output ↔
      ∃ value, input = .ok value ∧ next value = .ok output := by
  cases input <;> simp [Bind.bind, Aeneas.Std.bind]

/-- A finite sequence of equations for one actual generated loop body. -/
inductive ExactLoopTrace {State : Type u} {Output : Type v}
    (body : State → Result (ControlFlow State Output)) :
    State → Output → Type (max u v)
  | done {state output}
      (equation : body state = .ok (.done output)) :
      ExactLoopTrace body state output
  | cont {state next output}
      (equation : body state = .ok (.cont next))
      (tail : ExactLoopTrace body next output) :
      ExactLoopTrace body state output

def ExactLoopTrace.contCount
    {State : Type u} {Output : Type v}
    {body : State → Result (ControlFlow State Output)}
    {state : State} {output : Output} :
    ExactLoopTrace body state output → Nat
  | .done _ => 0
  | .cont _ tail => tail.contCount + 1

/-- Successful Aeneas loop execution plus a literal decreasing measure yields
a finite exact-body trace. -/
theorem loop_success_has_exact_trace
    {State Output : Type*}
    (body : State → Result (ControlFlow State Output))
    (measure : State → Nat)
    (decreases : ∀ state next,
      body state = .ok (.cont next) → measure next < measure state)
    (state : State) (output : Output)
    (run : loop body state = .ok output) :
    Nonempty (ExactLoopTrace body state output) := by
  rw [loop.eq_def] at run
  generalize bodyEquation : body state = bodyResult at run
  cases bodyResult with
  | fail error => simp [bodyEquation] at run
  | div => simp [bodyEquation] at run
  | ok flow =>
      cases flow with
      | done actualOutput =>
          simp only [bodyEquation, bind_tc_ok] at run
          injection run with outputEquation
          subst actualOutput
          exact ⟨.done bodyEquation⟩
      | cont next =>
          simp only [bodyEquation, bind_tc_ok] at run
          have smaller : measure next < measure state :=
            decreases state next bodyEquation
          obtain ⟨tail⟩ := loop_success_has_exact_trace
            body measure decreases next output run
          exact ⟨.cont bodyEquation tail⟩
termination_by measure state

/-- Ordered successful calls of a supplied generated result-valued reader. -/
inductive SuccessfulReadTrace
    {Reader Value ReadError : Type}
    (next : Reader → Result
      ((core.result.Result Value ReadError) × Reader)) :
    Reader → List Value → Reader → Prop
  | nil (reader : Reader) : SuccessfulReadTrace next reader [] reader
  | cons {before after final : Reader} {value : Value} {tail : List Value}
      (read : next before = .ok (.Ok value, after))
      (rest : SuccessfulReadTrace next after tail final) :
      SuccessfulReadTrace next before (value :: tail) final

theorem SuccessfulReadTrace.append
    {Reader Value ReadError : Type}
    {next : Reader → Result ((core.result.Result Value ReadError) × Reader)}
    {first middle final : Reader} {left right : List Value}
    (leftTrace : SuccessfulReadTrace next first left middle)
    (rightTrace : SuccessfulReadTrace next middle right final) :
    SuccessfulReadTrace next first (left ++ right) final := by
  induction leftTrace with
  | nil => simpa using rightTrace
  | cons read rest inductionHypothesis =>
      simpa using SuccessfulReadTrace.cons read
        (inductionHypothesis rightTrace)

theorem SuccessfulReadTrace.length_measure
    {Reader Value ReadError : Type}
    {next : Reader → Result ((core.result.Result Value ReadError) × Reader)}
    {measure : Reader → Nat}
    {first final : Reader} {values : List Value}
    (trace : SuccessfulReadTrace next first values final)
    (oneStep : ∀ before value after,
      next before = .ok (.Ok value, after) →
      measure after + 1 = measure before) :
    measure final + values.length = measure first := by
  induction trace with
  | nil => simp
  | cons read rest inductionHypothesis =>
      simp only [List.length_cons]
      have step := oneStep _ _ _ read
      omega

#print axioms bind_eq_ok_iff
#print axioms loop_success_has_exact_trace
#print axioms SuccessfulReadTrace.append
#print axioms SuccessfulReadTrace.length_measure

end AspisV7Tag73AeneasExactLoopTrace

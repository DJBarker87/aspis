import V7MerkleK12.Funs

open Aeneas Aeneas.Std Result ControlFlow Error

set_option autoImplicit false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

namespace AspisV7MerkleK12SourceBridge

open V7MerkleK12Generated

abbrev Byte := Fin 256
abbrev GeneratedHash :=
  Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)

def generatedU8ToByte (byte : Std.U8) : Byte :=
  ⟨byte.val, by
    have h := UScalar.hBounds byte
    norm_num at h ⊢
    exact h⟩

def generatedArrayBytes {n : Std.Usize} (bytes : Array Std.U8 n) : List Byte :=
  bytes.val.map generatedU8ToByte

def generatedSliceBytes (bytes : Slice Std.U8) : List Byte :=
  bytes.val.map generatedU8ToByte

def generatedHashInputBytes (inputs : Slice (Slice Std.U8)) : List Byte :=
  (inputs.val.flatMap fun input => input.val).map generatedU8ToByte

def HashCallbackEqualsSha256
    (sha256 : List Byte → List Byte) (hash : GeneratedHash) : Prop :=
  ∀ inputs output, hash inputs = .ok output →
    generatedArrayBytes output = sha256 (generatedHashInputBytes inputs)

theorem truncate_sha256_v7_exact
    (digest : Array Std.U8 32#usize) (output : Array Std.U8 26#usize)
    (hrun : v7_merkle208.truncate_sha256_v7 digest = .ok output) :
    generatedArrayBytes output = (generatedArrayBytes digest).take 26 := by
  simp [v7_merkle208.truncate_sha256_v7,
    v7_merkle208.V7_MERKLE_DIGEST_BYTES, generatedArrayBytes,
    core.array.Array.index, core.ops.index.IndexSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index,
    core.array.TryFromArrayCopySlice.try_from,
    core.result.Result.expect, Array.to_slice, List.slice] at hrun ⊢
  have hval := congrArg Subtype.val hrun
  simp only at hval
  rw [← hval, List.map_take]

theorem private_leaf_hash_v7_exact
    (sha256 : List Byte → List Byte) (hash : GeneratedHash)
    (hhash : HashCallbackEqualsSha256 sha256 hash)
    (treeTag : Std.U8) (value : Slice Std.U8)
    (salt : Array Std.U8 32#usize) (output : Array Std.U8 26#usize)
    (hrun : v7_merkle208.private_leaf_hash_v7
      hash treeTag value salt = .ok output) :
    generatedArrayBytes output =
      (sha256 ([⟨0x10, by norm_num⟩, generatedU8ToByte treeTag] ++
        generatedSliceBytes value ++ generatedArrayBytes salt)).take 26 := by
  unfold v7_merkle208.private_leaf_hash_v7 at hrun
  generalize hleaf :
      state_only_private_merkle.private_leaf_hash hash treeTag value salt =
        leafResult at hrun
  cases leafResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
  | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
  | ok digest =>
      have htruncate := truncate_sha256_v7_exact digest output hrun
      unfold state_only_private_merkle.private_leaf_hash at hleaf
      simp only [lift] at hleaf
      have hcallback := hhash
        (Array.to_slice (Array.make 3#usize [
          Array.to_slice (Array.make 2#usize [
            state_only_private_merkle.DOM_LEAF, treeTag ]),
          value, Array.to_slice salt ])) digest
      have hcall : hash
          (Array.to_slice (Array.make 3#usize [
            Array.to_slice (Array.make 2#usize [
              state_only_private_merkle.DOM_LEAF, treeTag ]),
            value, Array.to_slice salt ])) = .ok digest := by
        simpa using hleaf
      specialize hcallback hcall
      rw [htruncate]
      simpa [generatedArrayBytes, generatedSliceBytes,
        generatedHashInputBytes, generatedU8ToByte, Array.make,
        Array.val_to_slice, state_only_private_merkle.DOM_LEAF] using
          congrArg (List.take 26) hcallback

theorem node_hash_v7_exact
    (sha256 : List Byte → List Byte) (hash : GeneratedHash)
    (hhash : HashCallbackEqualsSha256 sha256 hash)
    (left right : Array Std.U8 26#usize)
    (output : Array Std.U8 26#usize)
    (hrun : v7_merkle208.node_hash_v7 hash left right = .ok output) :
    generatedArrayBytes output =
      (sha256 ([⟨0x11, by norm_num⟩] ++ generatedArrayBytes left ++
        generatedArrayBytes right)).take 26 := by
  have hleft := left.property
  have hright := right.property
  change left.val.length = 26 at hleft
  change right.val.length = 26 at hright
  have htakeLeft : List.take 26 (left.val.map generatedU8ToByte) =
      left.val.map generatedU8ToByte := by
    apply List.take_of_length_le
    simp [hleft]
  have htakeRight : List.take 26 (right.val.map generatedU8ToByte) =
      right.val.map generatedU8ToByte := by
    apply List.take_of_length_le
    simp [hright]
  have hindex : (1#usize + 26#usize : Result Std.Usize) =
      .ok 27#usize := by
    change UScalar.add 1#usize 26#usize = .ok 27#usize
    norm_num [UScalar.add, UScalar.tryMk, UScalar.tryMkOpt,
      UScalar.check_bounds, UScalar.inBounds, Result.ofOption]
    cases System.Platform.numBits_eq <;> simp_all
  unfold v7_merkle208.node_hash_v7 at hrun
  simp [Std.lift, Array.update, core.array.Array.index_mut,
    core.ops.index.IndexMutSlice, core.slice.index.Slice.index_mut,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut,
    core.slice.Slice.copy_from_slice, Array.to_slice, Array.from_slice,
    Array.index_usize, Array.make, Slice.len, Slice.length,
    v7_merkle208.DOM_NODE, v7_merkle208.V7_MERKLE_DIGEST_BYTES,
    hleft, hright, hindex] at hrun
  simp_lists at hrun
  simp [List.setSlice!, hleft, hright] at hrun
  let nodeInput : Slice Std.U8 :=
    ⟨17#u8 :: List.take 26 left.val ++ List.take 26 right.val, by
      simp [hleft, hright]
      exact Nat.le_trans (by norm_num) Usize.cMax_bound_concrete.1⟩
  let nodeInputs : Slice (Slice Std.U8) :=
    ⟨[nodeInput], by
      simp
      exact Nat.le_trans (by norm_num) Usize.cMax_bound_concrete.1⟩
  change (do
      let digest ← hash nodeInputs
      v7_merkle208.truncate_sha256_v7 digest) = .ok output at hrun
  generalize hcall : hash nodeInputs = hashResult at hrun
  cases hashResult with
  | fail error => simp [Bind.bind, Aeneas.Std.bind] at hrun
  | div => simp [Bind.bind, Aeneas.Std.bind] at hrun
  | ok digest =>
      have htruncate := truncate_sha256_v7_exact digest output hrun
      have hcallback := hhash nodeInputs digest hcall
      rw [htruncate]
      rw [hcallback]
      simp [nodeInputs, nodeInput, generatedArrayBytes,
        generatedHashInputBytes, generatedU8ToByte, List.map_take,
        htakeLeft, htakeRight]

abbrev GeneratedEntry :=
  Std.U32 × Array Std.U8 26#usize × Array Std.U8 26#usize
abbrev GeneratedLevel := alloc.vec.Vec GeneratedEntry

def pendingIsNotTrue : Option Bool → Prop
  | some true => False
  | _ => True

def resultDoneOptionTrue {α β γ : Type}
    (result : Result (ControlFlow α (β × γ × Option Bool))) : Bool :=
  match result with
  | .ok (.done (_, _, some true)) => true
  | _ => false

@[simp] theorem resultDoneOptionTrue_ok_cont {α β γ : Type}
    (state : α) :
    resultDoneOptionTrue
      (.ok (.cont state) : Result (ControlFlow α (β × γ × Option Bool))) =
        false := rfl

@[simp] theorem resultDoneOptionTrue_ok_done_none {α β γ : Type}
    (left : β) (middle : γ) :
    resultDoneOptionTrue
      (.ok (.done (left, middle, none)) :
        Result (ControlFlow α (β × γ × Option Bool))) = false := rfl

@[simp] theorem resultDoneOptionTrue_ok_done_false {α β γ : Type}
    (left : β) (middle : γ) :
    resultDoneOptionTrue
      (.ok (.done (left, middle, some false)) :
        Result (ControlFlow α (β × γ × Option Bool))) = false := rfl

@[simp] theorem resultDoneOptionTrue_fail {α β γ : Type}
    (error : Error) :
    resultDoneOptionTrue
      (.fail error : Result (ControlFlow α (β × γ × Option Bool))) = false := rfl

@[simp] theorem resultDoneOptionTrue_div {α β γ : Type} :
    resultDoneOptionTrue
      (.div : Result (ControlFlow α (β × γ × Option Bool))) = false := rfl

theorem resultDoneOptionTrue_bind {δ α β γ : Type}
    (computation : Result δ)
    (continuation : δ → Result (ControlFlow α (β × γ × Option Bool))) :
    resultDoneOptionTrue (Bind.bind computation continuation) =
      match computation with
      | .ok value => resultDoneOptionTrue (continuation value)
      | _ => false := by
  cases computation <;> rfl

theorem resultDoneOptionTrue_ite {α β γ : Type}
    (condition : Prop) [Decidable condition]
    (ifTrue ifFalse : Result (ControlFlow α (β × γ × Option Bool))) :
    resultDoneOptionTrue (if condition then ifTrue else ifFalse) =
      if condition then resultDoneOptionTrue ifTrue
      else resultDoneOptionTrue ifFalse := by
  by_cases condition <;> simp_all

theorem resultDoneOptionTrue_bind_eq_false {δ α β γ : Type}
    (computation : Result δ)
    (continuation : δ → Result (ControlFlow α (β × γ × Option Bool)))
    (continuationFalse : ∀ value,
      resultDoneOptionTrue (continuation value) = false) :
    resultDoneOptionTrue (Bind.bind computation continuation) = false := by
  cases computation <;> simp [Bind.bind, Aeneas.Std.bind, continuationFalse]

theorem resultDoneOptionTrue_bind_pair_eq_false
    {δ ε α β γ : Type} (computation : Result (δ × ε))
    (continuation : δ → ε →
      Result (ControlFlow α (β × γ × Option Bool)))
    (continuationFalse : ∀ left right,
      resultDoneOptionTrue (continuation left right) = false) :
    resultDoneOptionTrue
      (do let (left, right) ← computation; continuation left right) = false := by
  cases computation with
  | ok value =>
      rcases value with ⟨left, right⟩
      simpa [Bind.bind, Aeneas.Std.bind] using continuationFalse left right
  | fail error => rfl
  | div => rfl

theorem resultDoneOptionTrue_bind_triple_eq_false
    {δ ε ζ α β γ : Type}
    (computation : Result (δ × ε × ζ))
    (continuation : δ → ε → ζ →
      Result (ControlFlow α (β × γ × Option Bool)))
    (continuationFalse : ∀ first second third,
      resultDoneOptionTrue (continuation first second third) = false) :
    resultDoneOptionTrue
      (do let (first, second, third) ← computation
          continuation first second third) = false := by
  cases computation with
  | ok value =>
      rcases value with ⟨first, second, third⟩
      simpa [Bind.bind, Aeneas.Std.bind] using
        continuationFalse first second third
  | fail error => rfl
  | div => rfl

theorem resultDoneOptionTrue_ite_eq_false {α β γ : Type}
    (condition : Prop) [Decidable condition]
    (ifTrue ifFalse : Result (ControlFlow α (β × γ × Option Bool)))
    (trueFalse : resultDoneOptionTrue ifTrue = false)
    (falseFalse : resultDoneOptionTrue ifFalse = false) :
    resultDoneOptionTrue (if condition then ifTrue else ifFalse) = false := by
  by_cases condition <;> simp_all

theorem bind_eq_ok_iff_exists
    {α β : Type} (computation : Result α)
    (continuation : α → Result β) (output : β) :
    (do let value ← computation; continuation value) = .ok output ↔
      ∃ value, computation = .ok value ∧ continuation value = .ok output := by
  cases computation <;> simp [Bind.bind, Aeneas.Std.bind]

theorem bind_pair_eq_ok_iff_exists
    {α β γ : Type} (computation : Result (α × β))
    (continuation : α → β → Result γ) (output : γ) :
    (do let (left, right) ← computation; continuation left right) = .ok output ↔
      ∃ left right, computation = .ok (left, right) ∧
        continuation left right = .ok output := by
  cases computation with
  | ok value =>
      rcases value with ⟨left, right⟩
      simp [Bind.bind, Aeneas.Std.bind, Aeneas.Std.uncurry]
  | fail error => simp [Bind.bind, Aeneas.Std.bind, Aeneas.Std.uncurry]
  | div => simp [Bind.bind, Aeneas.Std.bind, Aeneas.Std.uncurry]

theorem bind_triple_eq_ok_iff_exists
    {α β γ δ : Type} (computation : Result (α × β × γ))
    (continuation : α → β → γ → Result δ) (output : δ) :
    (do let (first, second, third) ← computation
        continuation first second third) = .ok output ↔
      ∃ first second third,
        computation = .ok (first, second, third) ∧
          continuation first second third = .ok output := by
  cases computation with
  | ok value =>
      rcases value with ⟨first, second, third⟩
      simp [Bind.bind, Aeneas.Std.bind, Aeneas.Std.uncurry]
  | fail error => simp [Bind.bind, Aeneas.Std.bind, Aeneas.Std.uncurry]
  | div => simp [Bind.bind, Aeneas.Std.bind, Aeneas.Std.uncurry]

theorem inner_body_cannot_return_true
    (hash : GeneratedHash) (c1Nodes c2Nodes : Slice Std.U8)
    (level next outputNext : GeneratedLevel)
    (nodePos index outputNodePos : Std.Usize)
    (hrun :
      v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0.body
          hash c1Nodes c2Nodes level next nodePos index =
        .ok (.done (outputNext, outputNodePos, some true))) : False := by
  have projection := congrArg resultDoneOptionTrue hrun
  have bodyProjection :
      resultDoneOptionTrue
        (v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0.body
          hash c1Nodes c2Nodes level next nodePos index) = false := by
    unfold
      v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0.body
    repeat'
      first
      | apply resultDoneOptionTrue_bind_triple_eq_false
        intro first second third
      | apply resultDoneOptionTrue_bind_pair_eq_false
        intro left right
      | apply resultDoneOptionTrue_bind_eq_false
        intro value
      | apply resultDoneOptionTrue_ite_eq_false
      | rfl
  rw [bodyProjection] at projection
  exact Bool.noConfusion projection

def resultOptionTrue {β γ : Type}
    (result : Result (β × γ × Option Bool)) : Bool :=
  match result with
  | .ok (_, _, some true) => true
  | _ => false

/-- Generic partial-correctness fact for the exact Aeneas `loop`: if no body
step can terminate with `some true`, neither can a successful loop result.
Errors and divergence remain explicit in `Result`; no totality is assumed. -/
theorem loop_result_option_never_true
    {α β γ : Type}
    (body : α → Result (ControlFlow α (β × γ × Option Bool)))
    (bodyNeverTrue : ∀ state outputLeft outputMiddle,
      body state ≠ .ok (.done (outputLeft, outputMiddle, some true))) :
    ∀ state, resultOptionTrue (loop body state) = false := by
  apply loop.fixpoint_induct body
    (motive := fun recursive => ∀ state,
      resultOptionTrue (recursive state) = false)
  · apply Lean.Order.admissible_pi
    intro state
    apply Lean.Order.admissible_apply
      (fun _ result => resultOptionTrue result = false)
    apply Lean.Order.admissible_flatOrder
    rfl
  · intro recursive inductionHypothesis state
    simp only
    cases bodyEquation : body state with
    | fail error => rfl
    | div => rfl
    | ok flow =>
        cases flow with
        | cont nextState =>
            simpa [bodyEquation] using inductionHypothesis nextState
        | done output =>
            rcases output with ⟨outputLeft, outputMiddle, pending⟩
            cases pending with
            | none => rfl
            | some pendingValue =>
                cases pendingValue with
                | false => rfl
                | true =>
                    exact (bodyNeverTrue state outputLeft outputMiddle
                      bodyEquation).elim

theorem loop_success_excludes_bad_output
    {α β : Type} (body : α → Result (ControlFlow α β))
    (bad : β → Prop)
    (bodyExcludes : ∀ state output,
      bad output → body state ≠ .ok (.done output)) :
    ∀ state output, loop body state = .ok output → ¬ bad output := by
  apply loop.fixpoint_induct body
    (motive := fun recursive => ∀ state output,
      recursive state = .ok output → ¬ bad output)
  · apply Lean.Order.admissible_pi
    intro state
    apply Lean.Order.admissible_pi
    intro output
    apply Lean.Order.admissible_apply
      (fun _ result => result = Result.ok output → ¬ bad output)
    apply Lean.Order.admissible_flatOrder
    simp
  · intro recursive inductionHypothesis state output hrun outputBad
    simp only at hrun
    cases bodyEquation : body state with
    | fail error => simp [bodyEquation] at hrun
    | div => simp [bodyEquation] at hrun
    | ok flow =>
        cases flow with
        | cont nextState =>
            exact inductionHypothesis nextState output
              (by simpa [bodyEquation] using hrun) outputBad
        | done bodyOutput =>
            have outputEquation : bodyOutput = output := by
              simpa [bodyEquation] using hrun
            subst output
            exact bodyExcludes state bodyOutput outputBad bodyEquation

/-- A proof-relevant, finite trace of the exact body equations taken by an
Aeneas `loop`.  Unlike an invariant supplied by a caller, every constructor
stores an equation for the translated body itself. -/
inductive ExactLoopTrace {state output : Type}
    (body : state → Result (ControlFlow state output)) : state → output → Type
  | done {start result} :
      body start = .ok (.done result) → ExactLoopTrace body start result
  | cont {start next result} :
      body start = .ok (.cont next) → ExactLoopTrace body next result →
        ExactLoopTrace body start result

/-- Number of literal `continue` edges in the translated execution. -/
def ExactLoopTrace.contCount
    {state output : Type}
    {body : state → Result (ControlFlow state output)}
    {start : state} {result : output} :
    ExactLoopTrace body start result → Nat
  | .done _ => 0
  | .cont _ tail => tail.contCount + 1

theorem ExactLoopTrace.has_terminal_body_equation
    {state output : Type}
    {body : state → Result (ControlFlow state output)}
    {start : state} {result : output}
    (trace : ExactLoopTrace body start result) :
    ∃ terminal, body terminal = .ok (.done result) := by
  induction trace with
  | done equation => exact ⟨_, equation⟩
  | cont _ _ inductionHypothesis => exact inductionHypothesis

/-- Partial-correctness inversion for Aeneas's exact fixpoint interpreter.
A successful loop result has a finite chain of translated body equations; an
error or divergence cannot create such a chain. -/
theorem loop_success_yields_exact_trace
    {state output : Type}
    (body : state → Result (ControlFlow state output)) :
    ∀ start result, loop body start = .ok result →
      Nonempty (ExactLoopTrace body start result) := by
  apply loop.fixpoint_induct body
    (motive := fun recursive => ∀ start result,
      recursive start = .ok result →
        Nonempty (ExactLoopTrace body start result))
  · apply Lean.Order.admissible_pi
    intro start
    apply Lean.Order.admissible_pi
    intro result
    apply Lean.Order.admissible_apply
      (β := fun _ : state => Result output)
      (P := fun _ computation => computation = Result.ok result →
        Nonempty (ExactLoopTrace body start result))
      start
    apply Lean.Order.admissible_flatOrder
    simp
  · intro recursive inductionHypothesis start result hrun
    simp only at hrun
    cases bodyEquation : body start with
    | fail error => simp [bodyEquation] at hrun
    | div => simp [bodyEquation] at hrun
    | ok flow =>
        cases flow with
        | cont next =>
            have recursiveRun : recursive next = .ok result := by
              simpa [bodyEquation] using hrun
            let tail := Classical.choice
              (inductionHypothesis next result recursiveRun)
            exact ⟨ExactLoopTrace.cont bodyEquation tail⟩
        | done bodyResult =>
            have outputExact : bodyResult = result := by
              simpa [bodyEquation] using hrun
            subst result
            exact ⟨ExactLoopTrace.done bodyEquation⟩

abbrev InnerLoopState := GeneratedLevel × Std.Usize × Std.Usize
abbrev InnerLoopOutput := GeneratedLevel × Std.Usize × Option Bool

def exactInnerBody (hash : GeneratedHash) (c1Nodes c2Nodes : Slice Std.U8)
    (level : GeneratedLevel) :
    InnerLoopState → Result (ControlFlow InnerLoopState InnerLoopOutput) :=
  fun state =>
    v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0.body
      hash c1Nodes c2Nodes level state.1 state.2.1 state.2.2

/-- Every successful translated inner loop exposes every literal body edge.
Unfolding an edge selects exactly one of production's paired-child,
frontier-right, or frontier-left hash branches. -/
theorem inner_loop_success_yields_exact_control_flow_trace
    (hash : GeneratedHash) (c1Nodes c2Nodes : Slice Std.U8)
    (level next outputNext : GeneratedLevel)
    (nodePos index outputNodePos : Std.Usize)
    (pending : Option Bool)
    (hrun :
      v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0
        hash c1Nodes c2Nodes level next nodePos index =
          .ok (outputNext, outputNodePos, pending)) :
    Nonempty (ExactLoopTrace (exactInnerBody hash c1Nodes c2Nodes level)
      (next, nodePos, index) (outputNext, outputNodePos, pending)) := by
  unfold v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0 at hrun
  exact loop_success_yields_exact_trace
    (exactInnerBody hash c1Nodes c2Nodes level)
    (next, nodePos, index) (outputNext, outputNodePos, pending) hrun

abbrev OuterLoopState :=
  core.ops.range.Range Std.U32 × GeneratedLevel ×
    GeneratedLevel × Std.Usize
abbrev OuterLoopOutput :=
  GeneratedLevel × GeneratedLevel × Std.Usize × Option Bool

def exactOuterBody (hash : GeneratedHash) (c1Nodes c2Nodes : Slice Std.U8) :
    OuterLoopState → Result (ControlFlow OuterLoopState OuterLoopOutput) :=
  fun state =>
    v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0.body
      hash c1Nodes c2Nodes state.1 state.2.1 state.2.2.1 state.2.2.2

/-- Every successful translated outer loop exposes the exact range, clear,
inner-loop, and swap body equations for every executed tree level. -/
theorem outer_loop_success_yields_exact_control_flow_trace
    (hash : GeneratedHash) (c1Nodes c2Nodes : Slice Std.U8)
    (iter : core.ops.range.Range Std.U32)
    (level next outputLevel outputNext : GeneratedLevel)
    (nodePos outputNodePos : Std.Usize) (pending : Option Bool)
    (hrun : v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0
      iter hash c1Nodes c2Nodes level next nodePos =
        .ok (outputLevel, outputNext, outputNodePos, pending)) :
    Nonempty (ExactLoopTrace (exactOuterBody hash c1Nodes c2Nodes)
      (iter, level, next, nodePos)
      (outputLevel, outputNext, outputNodePos, pending)) := by
  unfold v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0 at hrun
  exact loop_success_yields_exact_trace (exactOuterBody hash c1Nodes c2Nodes)
    (iter, level, next, nodePos)
    (outputLevel, outputNext, outputNodePos, pending) hrun

theorem inner_loop_cannot_return_true
    (hash : GeneratedHash) (c1Nodes c2Nodes : Slice Std.U8)
    (level next outputNext : GeneratedLevel)
    (nodePos index outputNodePos : Std.Usize)
    (hrun :
      v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0
          hash c1Nodes c2Nodes level next nodePos index =
        .ok (outputNext, outputNodePos, some true)) : False := by
  unfold
    v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0 at hrun
  have loopProjection := loop_result_option_never_true
    (fun state : GeneratedLevel × Std.Usize × Std.Usize =>
      v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0.body
        hash c1Nodes c2Nodes level state.1 state.2.1 state.2.2)
    (fun state (outputLeft : GeneratedLevel)
        (outputMiddle : Std.Usize) impossible =>
      inner_body_cannot_return_true hash c1Nodes c2Nodes level state.1
        outputLeft state.2.1 state.2.2 outputMiddle impossible)
    (next, nodePos, index)
  have projectedRun := congrArg resultOptionTrue hrun
  rw [loopProjection] at projectedRun
  exact Bool.noConfusion projectedRun

theorem outer_body_cannot_return_true
    (hash : GeneratedHash) (c1Nodes c2Nodes : Slice Std.U8)
    (iter : core.ops.range.Range Std.U32)
    (level next outputLevel outputNext : GeneratedLevel)
    (nodePos outputNodePos : Std.Usize)
    (hrun :
      v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0.body
          hash c1Nodes c2Nodes iter level next nodePos =
        .ok (.done
          (outputLevel, outputNext, outputNodePos, some true))) : False := by
  unfold v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0.body at hrun
  generalize rangeEquation :
      core.iter.range.IteratorRange.next core.iter.range.StepU32 iter =
        rangeResult at hrun
  cases rangeResult with
  | fail error => simp [rangeEquation, Bind.bind, Aeneas.Std.bind] at hrun
  | div => simp [rangeEquation, Bind.bind, Aeneas.Std.bind] at hrun
  | ok rangeOutput =>
      rcases rangeOutput with ⟨ordinal, nextIter⟩
      simp only [rangeEquation, Aeneas.Std.bind_tc_ok] at hrun
      cases ordinal with
      | none => simp at hrun
      | some _ =>
          generalize clearEquation :
              alloc.vec.Vec.clear Global next = clearResult at hrun
          cases clearResult with
          | fail error =>
              simp [clearEquation, Bind.bind, Aeneas.Std.bind] at hrun
          | div => simp [clearEquation, Bind.bind, Aeneas.Std.bind] at hrun
          | ok clearedNext =>
              simp only [clearEquation, Aeneas.Std.bind_tc_ok] at hrun
              generalize innerEquation :
                  v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0_loop0
                    hash c1Nodes c2Nodes level clearedNext nodePos 0#usize =
                      innerResult at hrun
              cases innerResult with
              | fail error =>
                  simp [innerEquation, Bind.bind, Aeneas.Std.bind] at hrun
              | div =>
                  simp [innerEquation, Bind.bind, Aeneas.Std.bind] at hrun
              | ok innerOutput =>
                  rcases innerOutput with
                    ⟨innerNext, innerNodePos, pending⟩
                  simp only [innerEquation, Aeneas.Std.bind_tc_ok] at hrun
                  cases pending with
                  | none => simp at hrun
                  | some pendingValue =>
                      cases pendingValue with
                      | false => simp at hrun
                      | true =>
                          exact inner_loop_cannot_return_true
                            hash c1Nodes c2Nodes level clearedNext innerNext
                            nodePos 0#usize innerNodePos innerEquation

theorem outer_loop_cannot_return_true
    (hash : GeneratedHash) (c1Nodes c2Nodes : Slice Std.U8)
    (iter : core.ops.range.Range Std.U32)
    (level next outputLevel outputNext : GeneratedLevel)
    (nodePos outputNodePos : Std.Usize)
    (hrun :
      v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0
          iter hash c1Nodes c2Nodes level next nodePos =
        .ok (outputLevel, outputNext, outputNodePos, some true)) : False := by
  unfold v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0 at hrun
  have exclusion := loop_success_excludes_bad_output
    (fun state : core.ops.range.Range Std.U32 ×
        GeneratedLevel × GeneratedLevel × Std.Usize =>
      v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0.body
        hash c1Nodes c2Nodes state.1 state.2.1 state.2.2.1 state.2.2.2)
    (fun output : GeneratedLevel × GeneratedLevel ×
        Std.Usize × Option Bool => output.2.2.2 = some true)
    (fun state output outputBad impossible => by
      rcases output with ⟨bodyLevel, bodyNext, bodyNodePos, pending⟩
      simp only at outputBad
      subst pending
      exact outer_body_cannot_return_true hash c1Nodes c2Nodes state.1
        state.2.1 state.2.2.1 bodyLevel bodyNext state.2.2.2
        bodyNodePos impossible)
    (iter, level, next, nodePos)
    (outputLevel, outputNext, outputNodePos, some true)
    hrun
  exact exclusion rfl

theorem list_allM_u8_eq_true_implies_equal :
    ∀ (left right : List Std.U8),
      List.allM
          (fun pair : Std.U8 × Std.U8 =>
            Result.ok (decide (pair.1.val = pair.2.val)))
          (List.zip left right) = Result.ok true →
        left.length = right.length → left = right := by
  intro left
  induction left with
  | nil =>
      intro right allEqual sameLength
      cases right <;> simp_all
  | cons leftHead leftTail inductionHypothesis =>
      intro right allEqual sameLength
      cases right with
      | nil => simp at sameLength
      | cons rightHead rightTail =>
          by_cases headValuesEqual : leftHead.val = rightHead.val
          · simp [List.allM, headValuesEqual] at allEqual
            have headEqual : leftHead = rightHead := by
              exact UScalar.eq_of_val_eq headValuesEqual
            subst rightHead
            have tailLength : leftTail.length = rightTail.length := by
              simpa using sameLength
            exact congrArg (List.cons leftHead)
              (inductionHypothesis rightTail allEqual tailLength)
          · simp [List.allM, headValuesEqual, pure] at allEqual

theorem partial_eq_u8_array_true_implies_equal
    {n : Std.Usize} (left right : Array Std.U8 n)
    (hrun : core.array.equality.PartialEqArray.eq
      core.cmp.PartialEqU8 left right = .ok true) : left = right := by
  unfold core.array.equality.PartialEqArray.eq at hrun
  simp [core.cmp.PartialEqU8, core.cmp.impls.PartialEqU8.ne,
    Aeneas.Std.liftFun2] at hrun
  apply Subtype.ext
  exact list_allM_u8_eq_true_implies_equal left.val right.val hrun
    (by simpa using left.property.trans right.property.symm)

structure ExactPublicShapeChecks
    (depth : Std.U32) (entries : Slice GeneratedEntry)
    (c1Nodes c2Nodes : Slice Std.U8) where
  c1Remainder : Std.Usize
  c2Remainder : Std.Usize
  entriesNonempty : entries.val ≠ []
  depthBelowWordBits : depth.val < 32
  c1RemainderEquation :
    (Slice.len c1Nodes % v7_merkle208.V7_MERKLE_DIGEST_BYTES :
      Result Std.Usize) =
      .ok c1Remainder
  c1RemainderZero : c1Remainder.val = 0
  c2RemainderEquation :
    (Slice.len c2Nodes % v7_merkle208.V7_MERKLE_DIGEST_BYTES :
      Result Std.Usize) =
      .ok c2Remainder
  c2RemainderZero : c2Remainder.val = 0
  equalFrontierLengths : c1Nodes.val.length = c2Nodes.val.length

structure ExactSortedInRangeChecks
    (depth : Std.U32) (entries : Slice GeneratedEntry) where
  windows : core.slice.iter.Windows GeneratedEntry
  finalWindows : core.slice.iter.Windows GeneratedEntry
  lastOption : Option GeneratedEntry
  lastPosition : Std.U32
  lastC1 : Array Std.U8 26#usize
  lastC2 : Array Std.U8 26#usize
  domainSize : Std.U32
  windowsEquation : core.slice.Slice.windows entries 2#usize = .ok windows
  sortedWindowsEquation :
    core.iter.traits.iterator.Iterator.any.default
      (core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice
        GeneratedEntry)
      v7_merkle208.verify_two_minimal_subtrees_v7_bytes.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceTupleU32ArrayU826ArrayU826Bool
      windows () = .ok (false, finalWindows)
  lastEquation : core.slice.Slice.last entries = .ok lastOption
  lastUnwrapEquation : core.option.Option.unwrap lastOption =
    .ok (lastPosition, lastC1, lastC2)
  domainSizeEquation : 1#u32 <<< depth = .ok domainSize
  lastPositionInRange : lastPosition.val < domainSize.val

structure ExactTraversalInitialization
    (entries : Slice GeneratedEntry) (initialLevel : GeneratedLevel) where
  clearedLevel : GeneratedLevel
  seededLevel : GeneratedLevel
  clearEquation :
    alloc.vec.Vec.clear Global initialLevel = .ok clearedLevel
  seedEquation :
    alloc.vec.Vec.extend_from_slice
      (BuiltinClone GeneratedEntry) clearedLevel entries = .ok seededLevel

@[irreducible] def ExactTraversalRunEquation
    (hash : GeneratedHash) (depth : Std.U32)
    (c1Nodes c2Nodes : Slice Std.U8)
    (seededLevel initialNext outputLevel outputNext : GeneratedLevel) : Prop :=
    v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0
      { start := 0#u32, «end» := depth } hash c1Nodes c2Nodes
      seededLevel initialNext 0#usize =
        .ok (outputLevel, outputNext, Slice.len c1Nodes, none)

@[irreducible] def ExactTraversalControlFlowTrace
    (hash : GeneratedHash) (depth : Std.U32)
    (c1Nodes c2Nodes : Slice Std.U8)
    (seededLevel initialNext outputLevel outputNext : GeneratedLevel) : Type :=
    ExactLoopTrace (exactOuterBody hash c1Nodes c2Nodes)
      ({ start := 0#u32, «end» := depth }, seededLevel, initialNext,
        0#usize)
      (outputLevel, outputNext, Slice.len c1Nodes, none)

structure ExactTraversalRunEvidence
    (hash : GeneratedHash) (depth : Std.U32)
    (c1Nodes c2Nodes : Slice Std.U8)
    (seededLevel initialNext outputLevel outputNext : GeneratedLevel) where
  traversalEquation : ExactTraversalRunEquation hash depth c1Nodes c2Nodes
    seededLevel initialNext outputLevel outputNext
  traversalControlFlowTrace : ExactTraversalControlFlowTrace hash depth
    c1Nodes c2Nodes seededLevel initialNext outputLevel outputNext

structure ExactFinalRoot
    (c1Root c2Root : Array Std.U8 26#usize)
    (outputLevel : GeneratedLevel) where
  finalSingleton : alloc.vec.Vec.len outputLevel = 1#usize
  rootEntryEquation :
    alloc.vec.Vec.index
      (core.slice.index.SliceIndexUsizeSlice GeneratedEntry)
      outputLevel 0#usize = .ok (0#u32, c1Root, c2Root)

structure ExactAcceptedTwoTreeTraversal
    (hash : GeneratedHash)
    (c1Root c2Root : Array Std.U8 26#usize)
    (depth : Std.U32) (entries : Slice GeneratedEntry)
    (c1Nodes c2Nodes : Slice Std.U8)
    (initialLevel initialNext outputLevel outputNext : GeneratedLevel) where
  publicShape : ExactPublicShapeChecks depth entries c1Nodes c2Nodes
  sortedInRange : ExactSortedInRangeChecks depth entries
  initialization : ExactTraversalInitialization entries initialLevel
  traversal : ExactTraversalRunEvidence hash depth c1Nodes c2Nodes
    initialization.seededLevel initialNext outputLevel outputNext
  finalRoot : ExactFinalRoot c1Root c2Root outputLevel

/-- Inversion of the exact translated production verifier. Acceptance forces
the unique non-early-return path: all depth rounds execute, all paired
frontier bytes are consumed, the final level is a singleton at position zero,
and its two independently hashed roots equal the supplied roots. -/
theorem verify_two_subtrees_success_yields_exact_traversal
    (hash : GeneratedHash)
    (c1Root c2Root : Array Std.U8 26#usize)
    (depth : Std.U32) (entries : Slice GeneratedEntry)
    (c1Nodes c2Nodes : Slice Std.U8)
    (level next outputLevel outputNext : GeneratedLevel)
    (hrun : v7_merkle208.verify_two_minimal_subtrees_v7_bytes
      hash (c1Root, c2Root) depth entries (c1Nodes, c2Nodes) level next =
        .ok (true, outputLevel, outputNext)) :
    Nonempty (ExactAcceptedTwoTreeTraversal hash c1Root c2Root depth entries
      c1Nodes c2Nodes level next outputLevel outputNext) := by
  have entriesNonempty : entries.val ≠ [] := by
    intro hempty
    have emptyRun : core.slice.Slice.is_empty entries = .ok true := by
      simp [core.slice.Slice.is_empty, hempty]
    have impossibleRun := hrun
    unfold v7_merkle208.verify_two_minimal_subtrees_v7_bytes
      at impossibleRun
    rw [emptyRun] at impossibleRun
    have falseTrue : false = true := congrArg
      (fun result => match result with
        | .ok output => output.1
        | _ => false) impossibleRun
    exact Bool.noConfusion falseTrue
  have depthBelow : depth.val < 32 := by
    by_contra notBelow
    have depthHigh : depth ≥ 32#u32 := by scalar_tac
    have emptyRun : core.slice.Slice.is_empty entries = .ok false := by
      simp [core.slice.Slice.is_empty, entriesNonempty]
    have impossibleRun := hrun
    unfold v7_merkle208.verify_two_minimal_subtrees_v7_bytes
      at impossibleRun
    rw [emptyRun] at impossibleRun
    dsimp only at impossibleRun
    simp only [Aeneas.Std.bind_tc_ok, Bool.false_eq_true, ↓reduceIte]
      at impossibleRun
    simp only [if_pos depthHigh] at impossibleRun
    have falseTrue : false = true := congrArg
      (fun result => match result with
        | .ok output => output.1
        | _ => false) impossibleRun
    exact Bool.noConfusion falseTrue
  have emptyEquation : core.slice.Slice.is_empty entries = .ok false := by
    simp [core.slice.Slice.is_empty, entriesNonempty]
  have depthNotHigh : ¬ depth ≥ 32#u32 := by
    scalar_tac
  have depthNatNotHigh : ¬ 32 ≤ depth.val := not_le_of_gt depthBelow
  generalize c1RemainderEquation :
      Slice.len c1Nodes % v7_merkle208.V7_MERKLE_DIGEST_BYTES =
        c1RemainderResult
  cases c1RemainderResult with
  | fail error =>
      simp [v7_merkle208.verify_two_minimal_subtrees_v7_bytes,
        emptyEquation, if_neg depthNotHigh, c1RemainderEquation,
        Bind.bind, Aeneas.Std.bind] at hrun
      simp [entriesNonempty, depthNatNotHigh] at hrun
  | div =>
      simp [v7_merkle208.verify_two_minimal_subtrees_v7_bytes,
        emptyEquation, if_neg depthNotHigh, c1RemainderEquation,
        Bind.bind, Aeneas.Std.bind] at hrun
      simp [entriesNonempty, depthNatNotHigh] at hrun
  | ok c1Remainder =>
      by_cases c1Malformed : c1Remainder.val ≠ 0
      · simp [v7_merkle208.verify_two_minimal_subtrees_v7_bytes,
          entriesNonempty, depthNatNotHigh, c1RemainderEquation,
          c1Malformed, Bind.bind, Aeneas.Std.bind] at hrun
      · have c1Zero : c1Remainder.val = 0 := not_ne_iff.mp c1Malformed
        simp [v7_merkle208.verify_two_minimal_subtrees_v7_bytes,
          entriesNonempty, depthNatNotHigh, c1RemainderEquation,
          c1Zero, Bind.bind, Aeneas.Std.bind] at hrun
        generalize c2RemainderEquation :
            Slice.len c2Nodes % v7_merkle208.V7_MERKLE_DIGEST_BYTES =
              c2RemainderResult at hrun
        cases c2RemainderResult with
        | fail error =>
            simp [c2RemainderEquation, Bind.bind, Aeneas.Std.bind] at hrun
        | div =>
            simp [c2RemainderEquation, Bind.bind, Aeneas.Std.bind] at hrun
        | ok c2Remainder =>
            simp only [Aeneas.Std.bind_tc_ok] at hrun
            by_cases c2Malformed : c2Remainder.val ≠ 0
            · simp [if_neg c2Malformed] at hrun
            · have c2Zero : c2Remainder.val = 0 :=
                not_ne_iff.mp c2Malformed
              simp only [if_pos c2Zero] at hrun
              by_cases unequalLengths :
                  c1Nodes.val.length ≠ c2Nodes.val.length
              · simp [if_neg unequalLengths] at hrun
              · have equalLengths : c1Nodes.val.length =
                    c2Nodes.val.length := not_ne_iff.mp unequalLengths
                simp only [if_pos equalLengths] at hrun
                generalize windowsEquation :
                    core.slice.Slice.windows entries 2#usize = windowsResult
                      at hrun
                cases windowsResult with
                | fail error =>
                    simp [windowsEquation, Bind.bind, Aeneas.Std.bind] at hrun
                | div =>
                    simp [windowsEquation, Bind.bind, Aeneas.Std.bind] at hrun
                | ok windows =>
                    simp only [windowsEquation, Aeneas.Std.bind_tc_ok] at hrun
                    generalize sortedEquation :
                        core.iter.traits.iterator.Iterator.any.default
                          (core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice
                            GeneratedEntry)
                          v7_merkle208.verify_two_minimal_subtrees_v7_bytes.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceTupleU32ArrayU826ArrayU826Bool
                          windows () = sortedResult at hrun
                    cases sortedResult with
                    | fail error =>
                        simp [sortedEquation, Bind.bind, Aeneas.Std.bind] at hrun
                    | div =>
                        simp [sortedEquation, Bind.bind, Aeneas.Std.bind] at hrun
                    | ok sortedOutput =>
                        rcases sortedOutput with ⟨outOfOrder, finalWindows⟩
                        simp only [sortedEquation, Aeneas.Std.bind_tc_ok] at hrun
                        cases outOfOrder with
                        | true => simp at hrun
                        | false =>
                          generalize lastEquation :
                              core.slice.Slice.last entries = lastResult at hrun
                          cases lastResult with
                          | fail error =>
                              simp [lastEquation, Bind.bind, Aeneas.Std.bind]
                                at hrun
                          | div =>
                              simp [lastEquation, Bind.bind, Aeneas.Std.bind]
                                at hrun
                          | ok lastOption =>
                            simp only [lastEquation, Aeneas.Std.bind_tc_ok]
                              at hrun
                            generalize unwrapEquation :
                                core.option.Option.unwrap lastOption =
                                  unwrapResult at hrun
                            cases unwrapResult with
                            | fail error =>
                                simp [unwrapEquation, Bind.bind,
                                  Aeneas.Std.bind] at hrun
                            | div =>
                                simp [unwrapEquation, Bind.bind,
                                  Aeneas.Std.bind] at hrun
                            | ok lastEntry =>
                              rcases lastEntry with
                                ⟨lastPosition, lastC1, lastC2⟩
                              simp only [unwrapEquation,
                                Aeneas.Std.bind_tc_ok] at hrun
                              generalize shiftEquation :
                                  1#u32 <<< depth = shiftResult at hrun
                              cases shiftResult with
                              | fail error =>
                                  simp [shiftEquation, Bind.bind,
                                    Aeneas.Std.bind] at hrun
                              | div =>
                                  simp [shiftEquation, Bind.bind,
                                    Aeneas.Std.bind] at hrun
                              | ok domainSize =>
                                simp only [shiftEquation,
                                  Aeneas.Std.bind_tc_ok] at hrun
                                by_cases lastOutOfRange :
                                    domainSize.val ≤ lastPosition.val
                                · simp [if_pos lastOutOfRange] at hrun
                                · simp [lastOutOfRange] at hrun
                                  generalize clearEquation :
                                      alloc.vec.Vec.clear Global level =
                                        clearResult at hrun
                                  cases clearResult with
                                  | fail error =>
                                      simp [clearEquation, Bind.bind,
                                        Aeneas.Std.bind] at hrun
                                  | div =>
                                      simp [clearEquation, Bind.bind,
                                        Aeneas.Std.bind] at hrun
                                  | ok clearedLevel =>
                                    simp only [clearEquation,
                                      Aeneas.Std.bind_tc_ok] at hrun
                                    generalize seedEquation :
                                        alloc.vec.Vec.extend_from_slice
                                          (BuiltinClone GeneratedEntry)
                                          clearedLevel entries = seedResult
                                            at hrun
                                    cases seedResult with
                                    | fail error =>
                                        simp [seedEquation, Bind.bind,
                                          Aeneas.Std.bind] at hrun
                                    | div =>
                                        simp [seedEquation, Bind.bind,
                                          Aeneas.Std.bind] at hrun
                                    | ok seededLevel =>
                                      simp only [seedEquation,
                                        Aeneas.Std.bind_tc_ok] at hrun
                                      generalize traversalEquation :
                                          v7_merkle208.verify_two_minimal_subtrees_v7_bytes_loop0
                                            { start := 0#u32, «end» := depth }
                                            hash c1Nodes c2Nodes seededLevel
                                            next 0#usize = traversalResult
                                              at hrun
                                      cases traversalResult with
                                      | fail error =>
                                          simp [traversalEquation, Bind.bind,
                                            Aeneas.Std.bind] at hrun
                                      | div =>
                                          simp [traversalEquation, Bind.bind,
                                            Aeneas.Std.bind] at hrun
                                      | ok traversalOutput =>
                                        rcases traversalOutput with
                                          ⟨finalLevel, finalNext, nodePosition,
                                            pending⟩
                                        simp only [traversalEquation,
                                          Aeneas.Std.bind_tc_ok] at hrun
                                        cases pending with
                                        | some pendingValue =>
                                            cases pendingValue with
                                            | false => simp at hrun
                                            | true =>
                                                exact
                                                  (outer_loop_cannot_return_true
                                                    hash c1Nodes c2Nodes
                                                    { start := 0#u32,
                                                      «end» := depth }
                                                    seededLevel next finalLevel
                                                    finalNext 0#usize
                                                    nodePosition
                                                    traversalEquation).elim
                                        | none =>
                                          by_cases frontierConsumed :
                                              nodePosition = Slice.len c1Nodes
                                          · simp [frontierConsumed] at hrun
                                            by_cases singleton :
                                                alloc.vec.Vec.len finalLevel =
                                                  1#usize
                                            · simp only [if_pos singleton]
                                                at hrun
                                              generalize rootEntryEquation :
                                                  finalLevel.index_usize
                                                    0#usize =
                                                      rootEntryResult at hrun
                                              cases rootEntryResult with
                                              | fail error =>
                                                  cases hrun
                                              | div =>
                                                  cases hrun
                                              | ok rootEntry =>
                                                rcases rootEntry with
                                                  ⟨rootPosition, computedC1,
                                                    computedC2⟩
                                                by_cases rootAtZero :
                                                    rootPosition = 0#u32
                                                · simp [rootAtZero] at hrun
                                                  generalize c1EqualEquation :
                                                      core.array.equality.PartialEqArray.eq
                                                        core.cmp.PartialEqU8
                                                        computedC1 c1Root =
                                                          c1EqualResult at hrun
                                                  cases c1EqualResult with
                                                  | fail error =>
                                                      simp [c1EqualEquation,
                                                        Bind.bind,
                                                        Aeneas.Std.bind] at hrun
                                                  | div =>
                                                      simp [c1EqualEquation,
                                                        Bind.bind,
                                                        Aeneas.Std.bind] at hrun
                                                  | ok c1Equal =>
                                                    cases c1Equal with
                                                    | false => simp at hrun
                                                    | true =>
                                                      generalize c2EqualEquation :
                                                          core.array.equality.PartialEqArray.eq
                                                            core.cmp.PartialEqU8
                                                            computedC2 c2Root =
                                                              c2EqualResult at hrun
                                                      cases c2EqualResult with
                                                      | fail error =>
                                                          simp [c2EqualEquation,
                                                            Bind.bind,
                                                            Aeneas.Std.bind]
                                                              at hrun
                                                      | div =>
                                                          simp [c2EqualEquation,
                                                            Bind.bind,
                                                            Aeneas.Std.bind]
                                                              at hrun
                                                      | ok c2Equal =>
                                                        cases c2Equal with
                                                        | false => simp at hrun
                                                        | true =>
                                                          have c1Exact :=
                                                            partial_eq_u8_array_true_implies_equal
                                                              computedC1 c1Root
                                                              c1EqualEquation
                                                          have c2Exact :=
                                                            partial_eq_u8_array_true_implies_equal
                                                              computedC2 c2Root
                                                              c2EqualEquation
                                                          subst computedC1
                                                          subst computedC2
                                                          subst rootPosition
                                                          have outputsExact :
                                                              finalLevel = outputLevel ∧
                                                                finalNext = outputNext := by
                                                            simpa using hrun
                                                          rcases outputsExact with
                                                            ⟨finalLevelExact,
                                                              finalNextExact⟩
                                                          subst outputLevel
                                                          subst outputNext
                                                          refine ⟨{
                                                            publicShape := {
                                                              c1Remainder := c1Remainder
                                                              c2Remainder := c2Remainder
                                                              entriesNonempty := entriesNonempty
                                                              depthBelowWordBits := depthBelow
                                                              c1RemainderEquation := c1RemainderEquation
                                                              c1RemainderZero := c1Zero
                                                              c2RemainderEquation := c2RemainderEquation
                                                              c2RemainderZero := c2Zero
                                                              equalFrontierLengths := equalLengths }
                                                            sortedInRange := {
                                                              windows := windows
                                                              finalWindows := finalWindows
                                                              lastOption := lastOption
                                                              lastPosition := lastPosition
                                                              lastC1 := lastC1
                                                              lastC2 := lastC2
                                                              domainSize := domainSize
                                                              windowsEquation := windowsEquation
                                                              sortedWindowsEquation := sortedEquation
                                                              lastEquation := lastEquation
                                                              lastUnwrapEquation := unwrapEquation
                                                              domainSizeEquation := shiftEquation
                                                              lastPositionInRange := by omega }
                                                            initialization := {
                                                              clearedLevel := clearedLevel
                                                              seededLevel := seededLevel
                                                              clearEquation := clearEquation
                                                              seedEquation := seedEquation }
                                                            traversal := {
                                                              traversalEquation := ?_
                                                              traversalControlFlowTrace := ?_ }
                                                            finalRoot := {
                                                              finalSingleton := singleton
                                                              rootEntryEquation := rootEntryEquation } }⟩
                                                          · unfold ExactTraversalRunEquation
                                                            simpa [frontierConsumed]
                                                              using traversalEquation
                                                          · unfold ExactTraversalControlFlowTrace
                                                            exact Classical.choice
                                                              (outer_loop_success_yields_exact_control_flow_trace
                                                                hash c1Nodes c2Nodes
                                                                { start := 0#u32,
                                                                  «end» := depth }
                                                                seededLevel next finalLevel
                                                                finalNext 0#usize
                                                                (Slice.len c1Nodes) none
                                                                (by simpa [frontierConsumed]
                                                                  using traversalEquation))
                                                · simp [if_neg rootAtZero]
                                                    at hrun
                                            · simp [if_neg singleton] at hrun
                                          · simp [frontierConsumed] at hrun

/-- Acceptance by the exact generated two-tree verifier implies every
fail-closed public shape check made before traversal. -/
theorem verify_two_subtrees_success_implies_exact_shape
    (hash : GeneratedHash)
    (roots : Array Std.U8 26#usize × Array Std.U8 26#usize)
    (depth : Std.U32) (entries : Slice GeneratedEntry)
    (c1Nodes c2Nodes : Slice Std.U8)
    (level next outputLevel outputNext : GeneratedLevel)
    (hrun : v7_merkle208.verify_two_minimal_subtrees_v7_bytes
      hash roots depth entries (c1Nodes, c2Nodes) level next =
        .ok (true, outputLevel, outputNext)) :
    entries.val ≠ [] ∧ depth.val < 32 ∧
      ∃ c1Remainder c2Remainder : Std.Usize,
        (Slice.len c1Nodes % v7_merkle208.V7_MERKLE_DIGEST_BYTES :
          Result Std.Usize) =
            .ok c1Remainder ∧
          c1Remainder.val = 0 ∧
          (Slice.len c2Nodes % v7_merkle208.V7_MERKLE_DIGEST_BYTES :
            Result Std.Usize) =
            .ok c2Remainder ∧
          c2Remainder.val = 0 ∧
          c1Nodes.val.length = c2Nodes.val.length := by
  rcases roots with ⟨c1Root, c2Root⟩
  let traversal := Classical.choice
    (verify_two_subtrees_success_yields_exact_traversal hash c1Root c2Root
      depth entries c1Nodes c2Nodes level next outputLevel outputNext hrun)
  exact ⟨traversal.publicShape.entriesNonempty,
    traversal.publicShape.depthBelowWordBits,
    traversal.publicShape.c1Remainder,
    traversal.publicShape.c2Remainder,
    traversal.publicShape.c1RemainderEquation,
    traversal.publicShape.c1RemainderZero,
    traversal.publicShape.c2RemainderEquation,
    traversal.publicShape.c2RemainderZero,
    traversal.publicShape.equalFrontierLengths⟩

#print axioms truncate_sha256_v7_exact
#print axioms private_leaf_hash_v7_exact
#print axioms node_hash_v7_exact
#print axioms inner_body_cannot_return_true
#print axioms loop_result_option_never_true
#print axioms loop_success_excludes_bad_output
#print axioms loop_success_yields_exact_trace
#print axioms inner_loop_success_yields_exact_control_flow_trace
#print axioms outer_loop_success_yields_exact_control_flow_trace
#print axioms inner_loop_cannot_return_true
#print axioms outer_body_cannot_return_true
#print axioms outer_loop_cannot_return_true
#print axioms partial_eq_u8_array_true_implies_equal
#print axioms verify_two_subtrees_success_yields_exact_traversal
#print axioms verify_two_subtrees_success_implies_exact_shape

end AspisV7MerkleK12SourceBridge

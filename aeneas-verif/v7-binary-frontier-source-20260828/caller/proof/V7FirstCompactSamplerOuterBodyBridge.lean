import V7FirstCompactSamplerNativeBlockBridge

open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false

namespace V7FirstCompactSamplerOuterBodyBridge

open V7FirstCompactSamplerLoop16Bridge
open V7FirstCompactSamplerNativeBlockBridge

abbrev Transcript := V7FirstCompactSource.transcript.Transcript

def q16OuterContinuation
    (self : Transcript) (out : alloc.vec.Vec Std.U32)
    (draws : Std.Usize) (iter : core.slice.iter.ChunksExact Std.U8) :
    Result (ControlFlow (Transcript × alloc.vec.Vec Std.U32 × Std.Usize)
      (Transcript × alloc.vec.Vec Std.U32)) := do
  let (out1, draws1, marker) ←
    V7FirstCompactSource.transcript.Transcript.challenge_queries_without_replacement_loop0_loop0
      iter q16Count q16MaxDraws q16Mask out draws
  match marker with
  | 1#uscalar => ok (cont (self, out1, draws1))
  | _ => ok (done (self, out1))

/-- Kernel-level congruence endpoint: source chunks are replaced before the
generated outer continuation is exposed to tactic unification. -/
theorem source_chunks_bind_q16_continuation
    (block : SourceSqueezeBlock) (next : Transcript)
    (out : alloc.vec.Vec Std.U32) (draws : Std.Usize) :
    (do
      let iter ← core.slice.Slice.chunks_exact (Array.to_slice block) 4#usize
      q16OuterContinuation next out draws iter) =
    q16OuterContinuation next out draws
      (nativeBlockChunks (sourceSqueezeBytes block)) := by
  rw [sourceSqueeze_chunks_exact_is_nativeBlockChunks block]
  rfl

def nativeQ16OuterBody
    (self : Transcript) (out : alloc.vec.Vec Std.U32) (draws : Std.Usize) :
    Result (ControlFlow (Transcript × alloc.vec.Vec Std.U32 × Std.Usize)
      (Transcript × alloc.vec.Vec Std.U32)) := do
  if draws < q16MaxDraws then
    let (block, self1) ←
      V7FirstCompactSource.transcript.Transcript.squeeze_block self
    q16OuterContinuation self1 out draws
      (nativeBlockChunks (sourceSqueezeBytes block))
  else
    ok (done (self, out))

/-- The literal generated outer body equals a stable native refinement. The
only change is replacing source `chunks_exact(4)` by its proved exact result. -/
theorem current_outer_body_eq_native
    (self : Transcript) (out : alloc.vec.Vec Std.U32) (draws : Std.Usize) :
    V7FirstCompactSource.transcript.Transcript.challenge_queries_without_replacement_loop0.body
        q16Count q16MaxDraws q16Mask self out draws =
      nativeQ16OuterBody self out draws := by
  unfold
    V7FirstCompactSource.transcript.Transcript.challenge_queries_without_replacement_loop0.body
    nativeQ16OuterBody
  by_cases houter : draws < q16MaxDraws
  · rw [if_pos houter, if_pos houter]
    generalize hsqueeze :
      V7FirstCompactSource.transcript.Transcript.squeeze_block self = result
    cases result with
    | fail error => rfl
    | div => rfl
    | ok pair =>
        rcases pair with ⟨block, next⟩
        simp only [bind_tc_ok, lift]
        with_unfolding_all
          exact source_chunks_bind_q16_continuation block next out draws
  · rw [if_neg houter, if_neg houter]

def nativeQ16OuterLoop
    (self : Transcript) (out : alloc.vec.Vec Std.U32) (draws : Std.Usize) :
    Result (Transcript × alloc.vec.Vec Std.U32) := do
  loop
    (fun (self1, out1, draws1) =>
      nativeQ16OuterBody self1 out1 draws1)
    (self, out, draws)

/-- The complete translated recursive outer loop equals the stable native
refinement, not merely one generated loop body. -/
theorem current_outer_loop_eq_native
    (self : Transcript) (out : alloc.vec.Vec Std.U32) (draws : Std.Usize) :
    V7FirstCompactSource.transcript.Transcript.challenge_queries_without_replacement_loop0
        self q16Count q16MaxDraws q16Mask out draws =
      nativeQ16OuterLoop self out draws := by
  unfold
    V7FirstCompactSource.transcript.Transcript.challenge_queries_without_replacement_loop0
    nativeQ16OuterLoop
  apply congrArg (fun body => loop body (self, out, draws))
  funext state
  rcases state with ⟨current, values, currentDraws⟩
  exact current_outer_body_eq_native current values currentDraws

#print axioms source_chunks_bind_q16_continuation
#print axioms current_outer_body_eq_native
#print axioms current_outer_loop_eq_native

end V7FirstCompactSamplerOuterBodyBridge

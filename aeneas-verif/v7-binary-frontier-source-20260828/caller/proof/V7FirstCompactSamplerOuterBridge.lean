import V7FirstCompactSamplerLoop16Bridge

open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false

namespace V7FirstCompactSamplerOuterBridge

open V7FirstCompactSamplerLoop16Bridge
open AspisK1.V7Tag73SamplerDecoder

abbrev Transcript := V7FirstCompactSource.transcript.Transcript
abbrev QueryBlock := Array Std.U8 32#usize

/-- The literal successful current-source squeeze sequence.  This relation
records the exact translated `Result` calls and introduces no SHA semantics. -/
inductive ExactSqueezeTrace :
    Transcript → List QueryBlock → Transcript → Prop
  | nil (self : Transcript) : ExactSqueezeTrace self [] self
  | cons (self next final : Transcript) (block : QueryBlock)
      (blocks : List QueryBlock)
      (head :
        V7FirstCompactSource.transcript.Transcript.squeeze_block self =
          .ok (block, next))
      (tail : ExactSqueezeTrace next blocks final) :
      ExactSqueezeTrace self (block :: blocks) final

/-- Each literal source block is projected through the already proved exact
little-endian codec and 18-bit q16 mask into the K1.3 candidate vocabulary. -/
def generatedCandidateBlocks (blocks : List QueryBlock) : List (List Nat) :=
  blocks.map (fun block => (blockWords (sourceDigest block)).map q16Candidate)

@[simp] theorem generatedCandidateBlocks_nil :
    generatedCandidateBlocks [] = [] := rfl

@[simp] theorem generatedCandidateBlocks_cons
    (block : QueryBlock) (blocks : List QueryBlock) :
    generatedCandidateBlocks (block :: blocks) =
      (blockWords (sourceDigest block)).map q16Candidate ::
        generatedCandidateBlocks blocks := rfl

theorem exactSqueezeTrace_append_one
    {initial current next : Transcript}
    {blocks : List QueryBlock} {block : QueryBlock}
    (htrace : ExactSqueezeTrace initial blocks current)
    (hsqueeze :
      V7FirstCompactSource.transcript.Transcript.squeeze_block current =
        .ok (block, next)) :
    ExactSqueezeTrace initial (blocks ++ [block]) next := by
  induction htrace generalizing next block with
  | nil traceSelf =>
      simpa using ExactSqueezeTrace.cons traceSelf next next block [] hsqueeze
        (ExactSqueezeTrace.nil next)
  | cons self middle final headBlock priorBlocks head tail ih =>
      rw [List.cons_append]
      exact ExactSqueezeTrace.cons self middle next headBlock
        (priorBlocks ++ [block]) head (ih hsqueeze)

@[simp] theorem generatedCandidateBlocks_append
    (left right : List QueryBlock) :
    generatedCandidateBlocks (left ++ right) =
      generatedCandidateBlocks left ++ generatedCandidateBlocks right := by
  induction left with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.cons_append, generatedCandidateBlocks_cons, ih,
        List.cons_append]

/-- The exact source `chunks_exact(4)` iterator contains only four-byte words,
which is the structural premise consumed by the current inner-loop theorem. -/
theorem validWordIterator_blockChunks (block : QueryBlock) :
    ValidWordIterator
      (V5QuerySamplerGeneratedSemantics.blockChunks block) := by
  intro word hword
  simp only [V5QuerySamplerGeneratedSemantics.blockChunks,
    List.mem_ofFn] at hword
  rcases hword with ⟨index, rfl⟩
  simp [V5QuerySamplerGeneratedSemantics.wordSlice]

#print axioms exactSqueezeTrace_append_one
#print axioms generatedCandidateBlocks_append
#print axioms validWordIterator_blockChunks

end V7FirstCompactSamplerOuterBridge

import AspisFormal.V5TranscriptConnection

/-!
# Exact bounded query-sampler control model

This file isolates the deterministic part of the production query sampler.
It treats squeezed 32-byte blocks as inputs, decodes their eight little-endian
words, masks each word into the 17-bit query domain, rejects repeated values,
and stops after at most 64 candidate draws.

The production Rust method has the same visible control decisions, but pinned
Aeneas does not currently translate its `continue` from the inner
`chunks_exact` loop to the outer draw loop.  Nothing in this file assumes that
unproved Rust-to-Lean equality.  The equality is named at the end so that the
remaining boundary cannot be mistaken for a test result.
-/

namespace AspisV5QuerySamplerControl

open AspisV5TranscriptConnection

def keepIfNew (seen : List Nat) (value : Nat) : List Nat :=
  if value ∈ seen then seen else seen ++ [value]

/-- Scan candidates in source order, stopping before the first candidate that
would be examined after `count` values have already been accepted. -/
def scanUntil (count : Nat) (seen : List Nat) : List Nat → List Nat
  | [] => seen
  | value :: remaining =>
      if seen.length = count then seen
      else scanUntil count (keepIfNew seen value) remaining

theorem firstUniqueAux_eq_foldl_keepIfNew (seen values : List Nat) :
    firstUniqueAux seen values = values.foldl keepIfNew seen := by
  induction values generalizing seen with
  | nil => rfl
  | cons value remaining ih =>
      simp [firstUniqueAux, List.foldl, keepIfNew, ih]

theorem firstUnique_eq_foldl_keepIfNew (values : List Nat) :
    firstUnique values = values.foldl keepIfNew [] := by
  simp [firstUnique, firstUniqueAux_eq_foldl_keepIfNew]

theorem keepIfNew_length_le_succ (seen : List Nat) (value : Nat) :
    (keepIfNew seen value).length ≤ seen.length + 1 := by
  simp only [keepIfNew]
  split <;> simp

theorem keepIfNew_nodup (seen : List Nat) (value : Nat)
    (hseen : seen.Nodup) : (keepIfNew seen value).Nodup := by
  simp only [keepIfNew]
  split_ifs with hmem
  · exact hseen
  · simpa using hseen.append (by simp) (by simpa)

theorem seen_prefix_firstUniqueAux (seen values : List Nat) :
    seen <+: firstUniqueAux seen values := by
  induction values generalizing seen with
  | nil => simp [firstUniqueAux]
  | cons value remaining ih =>
      simp only [firstUniqueAux]
      split_ifs
      · exact ih seen
      · exact (List.prefix_append seen [value]).trans
          (ih (seen ++ [value]))

/-- Stopping once `count` first occurrences have been accepted returns exactly
the first `count` elements of a complete first-occurrence scan. -/
theorem scanUntil_eq_take_firstUniqueAux
    (count : Nat) (seen values : List Nat)
    (hlength : seen.length ≤ count) (hnodup : seen.Nodup) :
    scanUntil count seen values =
      (firstUniqueAux seen values).take count := by
  induction values generalizing seen with
  | nil =>
      simp only [scanUntil, firstUniqueAux]
      exact ((List.take_eq_self_iff seen).2 hlength).symm
  | cons value remaining ih =>
      simp only [scanUntil]
      split_ifs with hdone
      · have hprefix := seen_prefix_firstUniqueAux seen (value :: remaining)
        have heq := List.prefix_iff_eq_take.mp hprefix
        simpa [hdone] using heq
      · simp only [firstUniqueAux]
        apply ih (keepIfNew seen value)
        · have hlt : seen.length < count := Nat.lt_of_le_of_ne hlength hdone
          exact (keepIfNew_length_le_succ seen value).trans (by omega)
        · exact keepIfNew_nodup seen value hnodup

theorem scanUntil_eq_take_firstUnique (count : Nat) (values : List Nat) :
    scanUntil count [] values = (firstUnique values).take count := by
  simpa [firstUnique] using
    scanUntil_eq_take_firstUniqueAux count [] values (by simp) (by simp)

theorem scanUntil_length_le (count : Nat) (seen values : List Nat)
    (hseen : seen.length ≤ count) :
    (scanUntil count seen values).length ≤ count := by
  induction values generalizing seen with
  | nil => simpa [scanUntil] using hseen
  | cons value remaining ih =>
      simp only [scanUntil]
      split_ifs with hdone
      · exact hseen
      · apply ih
        have hlt : seen.length < count := Nat.lt_of_le_of_ne hseen hdone
        exact (keepIfNew_length_le_succ seen value).trans (by omega)

theorem scanUntil_nodup (count : Nat) (seen values : List Nat)
    (hseen : seen.Nodup) : (scanUntil count seen values).Nodup := by
  induction values generalizing seen with
  | nil => simpa [scanUntil] using hseen
  | cons value remaining ih =>
      simp only [scanUntil]
      split_ifs
      · exact hseen
      · exact ih (keepIfNew seen value) (keepIfNew_nodup seen value hseen)

theorem scanUntil_preserves_predicate
    (predicate : Nat → Prop) (count : Nat) (seen values : List Nat)
    (hseen : ∀ value ∈ seen, predicate value)
    (hvalues : ∀ value ∈ values, predicate value) :
    ∀ value ∈ scanUntil count seen values, predicate value := by
  induction values generalizing seen with
  | nil => simpa [scanUntil] using hseen
  | cons head tail ih =>
      simp only [scanUntil]
      split_ifs
      · exact hseen
      · apply ih
        · intro value hvalue
          simp only [keepIfNew] at hvalue
          split at hvalue
          · exact hseen value hvalue
          · rcases List.mem_append.mp hvalue with hvalue | hvalue
            · exact hseen value hvalue
            · simp only [List.mem_singleton] at hvalue
              subst value
              exact hvalues head (by simp)
        · intro value hvalue
          exact hvalues value (by simp [hvalue])

/-- Candidate list available to the deployed sampler: eight words per squeezed
block, with the global 64-draw limit applied before duplicate rejection. -/
def deployedCandidateBudget (blocks : List (FixedBytes 32)) : List Nat :=
  (blocks.flatMap blockQueryCandidates).take 64

/-- Deterministic returned value of the deployed fixed-parameter sampler,
separated from transcript state and error construction. -/
def scanDeployedQueries (blocks : List (FixedBytes 32)) : Option (List Nat) :=
  let accepted := scanUntil 18 [] (deployedCandidateBudget blocks)
  if accepted.length = 18 then some accepted else none

theorem deployedCandidateBudget_eq_boundedQueryCandidates
    (blocks : List (FixedBytes 32)) :
    deployedCandidateBudget blocks = boundedQueryCandidates blocks := by
  rfl

theorem scanDeployedQueries_eq_derive18Queries
    (blocks : List (FixedBytes 32)) :
    scanDeployedQueries blocks = derive18Queries blocks := by
  simp only [scanDeployedQueries, derive18Queries]
  rw [deployedCandidateBudget_eq_boundedQueryCandidates]
  rw [scanUntil_eq_take_firstUnique]
  by_cases henough : 18 ≤ (firstUnique (boundedQueryCandidates blocks)).length
  · have hlength :
        ((firstUnique (boundedQueryCandidates blocks)).take 18).length = 18 := by
      simp [List.length_take, min_eq_left henough]
    simp [henough, hlength]
  · have hshort :
        ((firstUnique (boundedQueryCandidates blocks)).take 18).length < 18 := by
      simp only [List.length_take]
      omega
    simp [henough]

theorem scanDeployedQueries_success_properties
    (blocks : List (FixedBytes 32)) (queries : List Nat)
    (hsuccess : scanDeployedQueries blocks = some queries) :
    queries.length = 18 ∧ queries.Nodup ∧
      (∀ query ∈ queries, query < 2 ^ 17) := by
  rw [scanDeployedQueries] at hsuccess
  split at hsuccess
  next hlength =>
    simp only [Option.some.injEq] at hsuccess
    subst queries
    refine ⟨hlength, scanUntil_nodup 18 [] _ (by simp), ?_⟩
    exact scanUntil_preserves_predicate
      (fun query => query < 2 ^ 17) 18 [] (deployedCandidateBudget blocks)
      (by simp) (by
        rw [deployedCandidateBudget_eq_boundedQueryCandidates]
        exact bounded_query_candidates_lt_bound blocks)
  next hlength => simp at hsuccess

/-! ## Exact squeeze-block control -/

structure BlockScanState where
  accepted : List Nat
  draws : Nat
  consumedBlocks : Nat
  deriving Repr, DecidableEq

structure WordScanResult where
  state : BlockScanState
  stopOuter : Bool
  deriving Repr, DecidableEq

/-- Process the eight candidates already obtained from one squeezed block.
The completion and draw-limit checks occur before the draw counter changes,
matching the order in the production inner loop. -/
def scanWords (count maxDraws : Nat) :
    BlockScanState → List Nat → WordScanResult
  | state, [] => ⟨state, false⟩
  | state, value :: remaining =>
      if state.accepted.length = count || state.draws = maxDraws then
        ⟨state, true⟩
      else
        scanWords count maxDraws
          { state with
              accepted := keepIfNew state.accepted value
              draws := state.draws + 1 }
          remaining

/-- Consume whole squeeze blocks until the draw cap is reached or the inner
word scan asks to leave the outer loop.  A block is counted when squeezed,
before its first word is examined. -/
def scanBlocks (count maxDraws : Nat) :
    BlockScanState → List (List Nat) → BlockScanState
  | state, [] => state
  | state, block :: remaining =>
      if state.draws < maxDraws then
        let scanned := scanWords count maxDraws
          { state with consumedBlocks := state.consumedBlocks + 1 } block
        if scanned.stopOuter then scanned.state
        else scanBlocks count maxDraws scanned.state remaining
      else state

def initialBlockScanState : BlockScanState :=
  ⟨[], 0, 0⟩

/-- Eight blocks suffice for the production cap of 64 candidates because each
32-byte block contains exactly eight four-byte words. -/
def runDeployedBlockSampler
    (blocks : Fin 8 → FixedBytes 32) : BlockScanState :=
  scanBlocks 18 64 initialBlockScanState
    (List.ofFn fun block => blockQueryCandidates (blocks block))

def blockSamplerOutput (state : BlockScanState) : Option (List Nat) :=
  if state.accepted.length = 18 then some state.accepted else none

def deployedBlockList (blocks : Fin 8 → FixedBytes 32) :
    List (FixedBytes 32) :=
  List.ofFn blocks

/-- Number of candidate words actually examined before completion or input
exhaustion.  Repeated candidates still count as draws. -/
def drawsUntil (count : Nat) (seen : List Nat) : List Nat → Nat
  | [] => 0
  | value :: remaining =>
      if seen.length = count then 0
      else 1 + drawsUntil count (keepIfNew seen value) remaining

theorem drawsUntil_le_length
    (count : Nat) (seen values : List Nat) :
    drawsUntil count seen values ≤ values.length := by
  induction values generalizing seen with
  | nil => rfl
  | cons value remaining ih =>
      simp only [drawsUntil, List.length_cons]
      split_ifs
      · omega
      · have hremaining := ih (keepIfNew seen value)
        omega

/-- `drawsUntil` identifies exactly the prefix examined by `scanUntil`; bytes
after that prefix cannot affect the returned positions. -/
theorem scanUntil_take_drawsUntil
    (count : Nat) (seen values : List Nat) :
    scanUntil count seen (values.take (drawsUntil count seen values)) =
      scanUntil count seen values := by
  induction values generalizing seen with
  | nil => rfl
  | cons value remaining ih =>
      simp only [drawsUntil, scanUntil]
      split_ifs with hcomplete
      · rfl
      · rw [show 1 + drawsUntil count (keepIfNew seen value) remaining =
            Nat.succ (drawsUntil count (keepIfNew seen value) remaining) by
              omega]
        rw [List.take_succ_cons]
        simp only [scanUntil, hcomplete, ↓reduceIte]
        exact ih (keepIfNew seen value)

theorem deployed_candidate_budget_has_64_words
    (blocks : Fin 8 → FixedBytes 32) :
    (deployedCandidateBudget (deployedBlockList blocks)).length = 64 := by
  simp [deployedCandidateBudget, deployedBlockList, blockQueryCandidates]

def deployedDrawCount (blocks : Fin 8 → FixedBytes 32) : Nat :=
  drawsUntil 18 []
    (deployedCandidateBudget (deployedBlockList blocks))

theorem deployedDrawCount_le_64
    (blocks : Fin 8 → FixedBytes 32) :
    deployedDrawCount blocks ≤ 64 := by
  unfold deployedDrawCount
  rw [← deployed_candidate_budget_has_64_words blocks]
  exact drawsUntil_le_length 18 [] _

/-- Exact number of squeeze blocks consumed by the fixed production control
flow.  If success occurs before draw 64, the verifier detects it before the
next candidate.  Therefore a success on word 8, 16, ..., or 56 squeezes one
additional block before stopping.  At draw 64 the outer draw cap stops first,
so no ninth block is squeezed. -/
def deployedConsumedBlockCount
    (blocks : Fin 8 → FixedBytes 32) : Nat :=
  let accepted := scanUntil 18 []
    (deployedCandidateBudget (deployedBlockList blocks))
  let draws := deployedDrawCount blocks
  if accepted.length = 18 ∧ draws < 64 then draws / 8 + 1 else 8

theorem deployed_consumed_blocks_of_success_before_cap
    (blocks : Fin 8 → FixedBytes 32)
    (hsuccess :
      (scanUntil 18 []
        (deployedCandidateBudget (deployedBlockList blocks))).length = 18)
    (hdraws : deployedDrawCount blocks < 64) :
    deployedConsumedBlockCount blocks = deployedDrawCount blocks / 8 + 1 := by
  simp [deployedConsumedBlockCount, hsuccess, hdraws]

theorem deployed_consumed_blocks_of_success_at_cap
    (blocks : Fin 8 → FixedBytes 32)
    (hsuccess :
      (scanUntil 18 []
        (deployedCandidateBudget (deployedBlockList blocks))).length = 18)
    (hdraws : deployedDrawCount blocks = 64) :
    deployedConsumedBlockCount blocks = 8 := by
  simp [deployedConsumedBlockCount, hsuccess, hdraws]

theorem deployed_consumed_blocks_of_failure
    (blocks : Fin 8 → FixedBytes 32)
    (hfailure :
      (scanUntil 18 []
        (deployedCandidateBudget (deployedBlockList blocks))).length ≠ 18) :
    deployedConsumedBlockCount blocks = 8 := by
  simp [deployedConsumedBlockCount, hfailure]

/-- The exact last-word case: when success happens after a whole number of
eight-word blocks and before the cap, one more block is squeezed solely to
notice completion. -/
theorem deployed_last_word_success_consumes_one_detection_block
    (blocks : Fin 8 → FixedBytes 32)
    (hsuccess :
      (scanUntil 18 []
        (deployedCandidateBudget (deployedBlockList blocks))).length = 18)
    (hdraws : deployedDrawCount blocks < 64)
    (hlast : deployedDrawCount blocks % 8 = 0) :
    deployedConsumedBlockCount blocks = deployedDrawCount blocks / 8 + 1 ∧
      deployedDrawCount blocks / 8 < deployedConsumedBlockCount blocks ∧
      8 * (deployedConsumedBlockCount blocks - 1) =
        deployedDrawCount blocks := by
  rw [deployed_consumed_blocks_of_success_before_cap blocks hsuccess hdraws]
  exact ⟨rfl, by omega, by omega⟩

theorem deployedConsumedBlockCount_le_8
    (blocks : Fin 8 → FixedBytes 32) :
    deployedConsumedBlockCount blocks ≤ 8 := by
  simp only [deployedConsumedBlockCount]
  split_ifs with hsuccess
  · have hdraws : deployedDrawCount blocks < 64 := hsuccess.2
    omega
  · omega

def exactDeployedQuerySamplerResult
    (blocks : Fin 8 → FixedBytes 32) : Option (List Nat) × Nat :=
  (scanDeployedQueries (deployedBlockList blocks),
    deployedConsumedBlockCount blocks)

theorem exact_deployed_result_returns_derive18Queries
    (blocks : Fin 8 → FixedBytes 32) :
    (exactDeployedQuerySamplerResult blocks).1 =
      derive18Queries (deployedBlockList blocks) := by
  exact scanDeployedQueries_eq_derive18Queries _

theorem scanWords_when_complete
    (count maxDraws : Nat) (state : BlockScanState) (words : List Nat)
    (hcomplete : state.accepted.length = count) :
    scanWords count maxDraws state words =
      if words.isEmpty then ⟨state, false⟩ else ⟨state, true⟩ := by
  cases words with
  | nil => rfl
  | cons value remaining => simp [scanWords, hcomplete]

/-- If completion happens on the last word of a block while draw budget
remains, the production loop squeezes the next block before noticing that it
is already complete.  The next block changes transcript state but contributes
no candidate. -/
theorem completed_at_boundary_consumes_one_more_block
    (count maxDraws : Nat) (state : BlockScanState)
    (block : List Nat) (remaining : List (List Nat))
    (hdraw : state.draws < maxDraws)
    (hcomplete : state.accepted.length = count)
    (hnonempty : block ≠ []) :
    scanBlocks count maxDraws state (block :: remaining) =
      { state with consumedBlocks := state.consumedBlocks + 1 } := by
  rw [scanBlocks]
  simp only [if_pos hdraw]
  have hbumped :
      ({ state with consumedBlocks := state.consumedBlocks + 1 } :
        BlockScanState).accepted.length = count := hcomplete
  rw [scanWords_when_complete count maxDraws _ block hbumped]
  simp [hnonempty]

theorem scanWords_preserves_consumedBlocks
    (count maxDraws : Nat) (state : BlockScanState) (words : List Nat) :
    (scanWords count maxDraws state words).state.consumedBlocks =
      state.consumedBlocks := by
  induction words generalizing state with
  | nil => rfl
  | cons value remaining ih =>
      simp only [scanWords]
      split_ifs
      · rfl
      · exact ih _

theorem scanWords_draws_le
    (count maxDraws : Nat) (state : BlockScanState) (words : List Nat)
    (hdraws : state.draws ≤ maxDraws) :
    (scanWords count maxDraws state words).state.draws ≤ maxDraws := by
  induction words generalizing state with
  | nil => simpa [scanWords] using hdraws
  | cons value remaining ih =>
      simp only [scanWords]
      split_ifs with hstop
      · exact hdraws
      · apply ih
        have hne : state.draws ≠ maxDraws := by
          intro heq
          apply hstop
          simp [heq]
        change state.draws + 1 ≤ maxDraws
        omega

theorem scanWords_accepted_length_le
    (count maxDraws : Nat) (state : BlockScanState) (words : List Nat)
    (hlength : state.accepted.length ≤ count) :
    (scanWords count maxDraws state words).state.accepted.length ≤ count := by
  induction words generalizing state with
  | nil => simpa [scanWords] using hlength
  | cons value remaining ih =>
      simp only [scanWords]
      split_ifs with hstop
      · exact hlength
      · apply ih
        have hne : state.accepted.length ≠ count := by
          intro heq
          apply hstop
          simp [heq]
        have hlt : state.accepted.length < count :=
          Nat.lt_of_le_of_ne hlength hne
        exact (keepIfNew_length_le_succ state.accepted value).trans (by omega)

theorem scanBlocks_draws_le
    (count maxDraws : Nat) (state : BlockScanState)
    (blocks : List (List Nat)) (hdraws : state.draws ≤ maxDraws) :
    (scanBlocks count maxDraws state blocks).draws ≤ maxDraws := by
  induction blocks generalizing state with
  | nil => simpa [scanBlocks] using hdraws
  | cons block remaining ih =>
      rw [scanBlocks]
      by_cases houter : state.draws < maxDraws
      · rw [if_pos houter]
        let bumped : BlockScanState :=
          { state with consumedBlocks := state.consumedBlocks + 1 }
        have hbumped : bumped.draws ≤ maxDraws := by
          simpa [bumped] using hdraws
        have hscanned := scanWords_draws_le count maxDraws bumped block hbumped
        by_cases hstop :
            (scanWords count maxDraws bumped block).stopOuter = true
        · rw [if_pos hstop]
          exact hscanned
        · rw [if_neg hstop]
          exact ih _ hscanned
      · rw [if_neg houter]
        exact hdraws

theorem scanBlocks_accepted_length_le
    (count maxDraws : Nat) (state : BlockScanState)
    (blocks : List (List Nat)) (hlength : state.accepted.length ≤ count) :
    (scanBlocks count maxDraws state blocks).accepted.length ≤ count := by
  induction blocks generalizing state with
  | nil => simpa [scanBlocks] using hlength
  | cons block remaining ih =>
      rw [scanBlocks]
      by_cases houter : state.draws < maxDraws
      · rw [if_pos houter]
        let bumped : BlockScanState :=
          { state with consumedBlocks := state.consumedBlocks + 1 }
        have hbumped : bumped.accepted.length ≤ count := by
          simpa [bumped] using hlength
        have hscanned :=
          scanWords_accepted_length_le count maxDraws bumped block hbumped
        by_cases hstop :
            (scanWords count maxDraws bumped block).stopOuter = true
        · rw [if_pos hstop]
          exact hscanned
        · rw [if_neg hstop]
          exact ih _ hscanned
      · rw [if_neg houter]
        exact hlength

theorem scanBlocks_consumedBlocks_le_add_length
    (count maxDraws : Nat) (state : BlockScanState)
    (blocks : List (List Nat)) :
    (scanBlocks count maxDraws state blocks).consumedBlocks ≤
      state.consumedBlocks + blocks.length := by
  induction blocks generalizing state with
  | nil => simp [scanBlocks]
  | cons block remaining ih =>
      rw [scanBlocks]
      by_cases houter : state.draws < maxDraws
      · rw [if_pos houter]
        let bumped : BlockScanState :=
          { state with consumedBlocks := state.consumedBlocks + 1 }
        have hblocks :
            (scanWords count maxDraws bumped block).state.consumedBlocks =
              state.consumedBlocks + 1 := by
          simpa [bumped] using
            scanWords_preserves_consumedBlocks count maxDraws bumped block
        by_cases hstop :
            (scanWords count maxDraws bumped block).stopOuter = true
        · rw [if_pos hstop, hblocks]
          simp
        · rw [if_neg hstop]
          calc
            (scanBlocks count maxDraws
                (scanWords count maxDraws bumped block).state
                remaining).consumedBlocks ≤
                (scanWords count maxDraws bumped block).state.consumedBlocks +
                  remaining.length := ih _
            _ = state.consumedBlocks + (block :: remaining).length := by
              rw [hblocks]
              simp
              omega
      · rw [if_neg houter]
        simp

theorem deployed_block_sampler_caps_draws_and_output
    (blocks : Fin 8 → FixedBytes 32) :
    (runDeployedBlockSampler blocks).draws ≤ 64 ∧
      (runDeployedBlockSampler blocks).accepted.length ≤ 18 := by
  exact ⟨scanBlocks_draws_le 18 64 initialBlockScanState _ (by simp
      [initialBlockScanState]),
    scanBlocks_accepted_length_le 18 64 initialBlockScanState _ (by simp
      [initialBlockScanState])⟩

theorem deployed_block_sampler_consumes_at_most_eight_blocks
    (blocks : Fin 8 → FixedBytes 32) :
    (runDeployedBlockSampler blocks).consumedBlocks ≤ 8 := by
  simpa [runDeployedBlockSampler, initialBlockScanState] using
    scanBlocks_consumedBlocks_le_add_length 18 64 initialBlockScanState
      (List.ofFn fun block => blockQueryCandidates (blocks block))

/-- Exact remaining implementation statement for the production fixed call.
It includes both the returned positions and how many squeeze blocks changed
the transcript state.  Output-only tests do not prove this proposition. -/
def ExactProductionQuerySamplerEquality
    {RustTranscript : Type*}
    (rustSampler : RustTranscript → Option (List Nat) × Nat)
    (blocks : RustTranscript → Fin 8 → FixedBytes 32) : Prop :=
  ∀ transcript,
    rustSampler transcript =
      exactDeployedQuerySamplerResult (blocks transcript)

theorem production_sampler_returns_derive18Queries_of_equality
    {RustTranscript : Type*}
    (rustSampler : RustTranscript → Option (List Nat) × Nat)
    (blocks : RustTranscript → Fin 8 → FixedBytes 32)
    (hequality : ExactProductionQuerySamplerEquality rustSampler blocks)
    (transcript : RustTranscript) :
    (rustSampler transcript).1 =
      derive18Queries (deployedBlockList (blocks transcript)) := by
  calc
    (rustSampler transcript).1 =
        (exactDeployedQuerySamplerResult (blocks transcript)).1 :=
      congrArg Prod.fst (hequality transcript)
    _ = derive18Queries (deployedBlockList (blocks transcript)) :=
      exact_deployed_result_returns_derive18Queries _

theorem production_sampler_consumes_at_most_eight_blocks_of_equality
    {RustTranscript : Type*}
    (rustSampler : RustTranscript → Option (List Nat) × Nat)
    (blocks : RustTranscript → Fin 8 → FixedBytes 32)
    (hequality : ExactProductionQuerySamplerEquality rustSampler blocks)
    (transcript : RustTranscript) :
    (rustSampler transcript).2 ≤ 8 := by
  rw [hequality transcript]
  exact deployedConsumedBlockCount_le_8 _

theorem production_sampler_last_word_state_advance_of_equality
    {RustTranscript : Type*}
    (rustSampler : RustTranscript → Option (List Nat) × Nat)
    (blocks : RustTranscript → Fin 8 → FixedBytes 32)
    (hequality : ExactProductionQuerySamplerEquality rustSampler blocks)
    (transcript : RustTranscript)
    (hsuccess :
      (scanUntil 18 []
        (deployedCandidateBudget
          (deployedBlockList (blocks transcript)))).length = 18)
    (hdraws : deployedDrawCount (blocks transcript) < 64)
    (hlast : deployedDrawCount (blocks transcript) % 8 = 0) :
    (rustSampler transcript).2 =
        deployedDrawCount (blocks transcript) / 8 + 1 ∧
      deployedDrawCount (blocks transcript) / 8 <
        (rustSampler transcript).2 := by
  have hmodel := deployed_last_word_success_consumes_one_detection_block
    (blocks transcript) hsuccess hdraws hlast
  rw [hequality transcript]
  exact ⟨hmodel.1, hmodel.2.1⟩

#print axioms firstUniqueAux_eq_foldl_keepIfNew
#print axioms firstUnique_eq_foldl_keepIfNew
#print axioms keepIfNew_nodup
#print axioms seen_prefix_firstUniqueAux
#print axioms scanUntil_eq_take_firstUniqueAux
#print axioms scanUntil_eq_take_firstUnique
#print axioms scanUntil_length_le
#print axioms scanUntil_nodup
#print axioms scanUntil_preserves_predicate
#print axioms deployedCandidateBudget_eq_boundedQueryCandidates
#print axioms scanDeployedQueries_eq_derive18Queries
#print axioms scanDeployedQueries_success_properties
#print axioms scanWords_when_complete
#print axioms drawsUntil_le_length
#print axioms scanUntil_take_drawsUntil
#print axioms deployed_candidate_budget_has_64_words
#print axioms deployedDrawCount_le_64
#print axioms deployed_consumed_blocks_of_success_before_cap
#print axioms deployed_consumed_blocks_of_success_at_cap
#print axioms deployed_consumed_blocks_of_failure
#print axioms deployed_last_word_success_consumes_one_detection_block
#print axioms deployedConsumedBlockCount_le_8
#print axioms exact_deployed_result_returns_derive18Queries
#print axioms completed_at_boundary_consumes_one_more_block
#print axioms scanWords_preserves_consumedBlocks
#print axioms scanWords_draws_le
#print axioms scanWords_accepted_length_le
#print axioms scanBlocks_draws_le
#print axioms scanBlocks_accepted_length_le
#print axioms scanBlocks_consumedBlocks_le_add_length
#print axioms deployed_block_sampler_caps_draws_and_output
#print axioms deployed_block_sampler_consumes_at_most_eight_blocks
#print axioms production_sampler_returns_derive18Queries_of_equality
#print axioms production_sampler_consumes_at_most_eight_blocks_of_equality
#print axioms production_sampler_last_word_state_advance_of_equality

end AspisV5QuerySamplerControl

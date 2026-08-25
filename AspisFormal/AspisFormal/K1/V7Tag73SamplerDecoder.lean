import AspisFormal.K1.V7Tag73DeterministicRefinement

/-!
# Exact bounded byte decoders for the deployed Tag-73 samplers

This module implements the bounded samplers in
`crates/aspis-core/src/transcript.rs` at the raw 32-byte-block level:

* each block is read as eight little-endian `u32` words;
* an M31 limb masks off bit 31, rejects `2^31 - 1`, and gets at most eight
  sequential word attempts;
* one QM31 value consists of four accepted limbs in `(c0.a,c0.b,c1.a,c1.b)`
  order;
* nonzero and secure-circle modes start a fresh ordinary QM31 sampler on each
  of at most three outer attempts, discarding unused words in the last block
  of the preceding attempt exactly as Rust does; and
* q16 masks to 18 bits, keeps first occurrences, consumes at most 64 words,
  and succeeds exactly when the sixteenth distinct position first appears in
  the last supplied block.

The secure-circle rational map is deliberately a parameter of type
`SecureCircleParameterMap`.  This file does not fake QM31 arithmetic.  The
parameter must eventually be instantiated by the exact map
`x=(1-t^2)/(1+t^2), y=2t/(1+t^2)` with singular and `t in CM31` rejection.
All byte sampling before that map is executable here.
-/

set_option autoImplicit false

namespace AspisK1.V7Tag73SamplerDecoder

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73DeterministicRefinement

/-! ## Little-endian block words -/

def m31Prime : Nat := 2 ^ 31 - 1
def m31MaskModulus : Nat := 2 ^ 31
def q16Bound : Nat := 2 ^ 18

/-- The word at slot `0..7` in the same byte order as
`u32::from_le_bytes(block[4*i..4*i+4])`. -/
def littleEndianWord (block : Digest256) (word : Fin 8) : Nat :=
  (block ⟨4 * word.val, by omega⟩).toNat +
  256 * (block ⟨4 * word.val + 1, by omega⟩).toNat +
  65536 * (block ⟨4 * word.val + 2, by omega⟩).toNat +
  16777216 * (block ⟨4 * word.val + 3, by omega⟩).toNat

/-- Four runtime bytes interpreted little endian always form one mathematical
`u32`; no larger natural number can enter either deployed mask. -/
theorem littleEndianWord_lt_two_pow_32
    (block : Digest256) (word : Fin 8) :
    littleEndianWord block word < 2 ^ 32 := by
  have h0 := UInt8.toNat_lt (block ⟨4 * word.val, by omega⟩)
  have h1 := UInt8.toNat_lt (block ⟨4 * word.val + 1, by omega⟩)
  have h2 := UInt8.toNat_lt (block ⟨4 * word.val + 2, by omega⟩)
  have h3 := UInt8.toNat_lt (block ⟨4 * word.val + 3, by omega⟩)
  unfold littleEndianWord
  norm_num at h0 h1 h2 h3 ⊢
  omega

def blockWords (block : Digest256) : List Nat :=
  List.ofFn (littleEndianWord block)

def flattenedWords (blocks : List Digest256) : List Nat :=
  blocks.flatMap blockWords

@[simp] theorem blockWords_length (block : Digest256) :
    (blockWords block).length = 8 := by
  simp [blockWords]

theorem flattenedWords_length (blocks : List Digest256) :
    (flattenedWords blocks).length = 8 * blocks.length := by
  simp [flattenedWords, blockWords, Nat.mul_comm]

/-- `word & 0x7fffffff`; for a 32-bit word this is reduction modulo `2^31`. -/
def maskedM31 (word : Nat) : Nat := word % m31MaskModulus

def q16Candidate (word : Nat) : Nat := word % q16Bound

theorem maskedM31_lt_modulus (word : Nat) : maskedM31 word < m31MaskModulus := by
  exact Nat.mod_lt _ (by norm_num [m31MaskModulus])

theorem q16Candidate_lt_bound (word : Nat) : q16Candidate word < q16Bound := by
  exact Nat.mod_lt _ (by norm_num [q16Bound])

/-! ## Four-limb QM31 decoder -/

structure LimbDecode where
  value : Nat
  restWords : List Nat
  attemptsUsed : Nat
  deriving DecidableEq, Repr

/-- Try the next masked word, consuming at most `fuel` words.  Production calls
this with fuel eight independently for each limb. -/
def decodeLimb : Nat → List Nat → Option LimbDecode
  | 0, _ => none
  | fuel + 1, [] => none
  | fuel + 1, word :: rest =>
      let candidate := maskedM31 word
      if candidate = m31Prime then
        match decodeLimb fuel rest with
        | none => none
        | some decoded =>
            some { decoded with attemptsUsed := decoded.attemptsUsed + 1 }
      else
        some { value := candidate, restWords := rest, attemptsUsed := 1 }

structure FourLimbDecode where
  limbs : List Nat
  restWords : List Nat
  wordsUsed : Nat
  deriving DecidableEq, Repr

def decodeLimbs : Nat → List Nat → Option FourLimbDecode
  | 0, words => some { limbs := [], restWords := words, wordsUsed := 0 }
  | count + 1, words => do
      let first ← decodeLimb 8 words
      let rest ← decodeLimbs count first.restWords
      pure
        { limbs := first.value :: rest.limbs
          restWords := rest.restWords
          wordsUsed := first.attemptsUsed + rest.wordsUsed }

def listValue (values : List Nat) (index : Nat) : Nat :=
  values.getD index 0

/-- Canonical 16-byte field encoding used by `QM31::write_le_bytes`. -/
def encodeQm31Limbs (limbs : List Nat) : Qm31Bytes := fun index =>
  let limb := listValue limbs (index.val / 4)
  let byte := index.val % 4
  UInt8.ofNat ((limb / (256 ^ byte)) % 256)

def blocksNeededForWords (wordsUsed : Nat) : Nat :=
  (wordsUsed + 7) / 8

structure OrdinaryPrefixDecode where
  value : Qm31Bytes
  limbs : List Nat
  wordsUsed : Nat
  blocksUsed : Nat
  remainingBlocks : List Digest256
  deriving DecidableEq

/-- Decode one ordinary QM31 call from the front of a block stream.  Unused
words in its final consumed block are discarded before `remainingBlocks`. -/
def decodeOrdinaryPrefix (blocks : List Digest256) : Option OrdinaryPrefixDecode := do
  match blocks with
  | [] => none
  | _ :: _ =>
      let decoded ← decodeLimbs 4 (flattenedWords blocks)
      let used := blocksNeededForWords decoded.wordsUsed
      if valid : 0 < used ∧ used ≤ 4 ∧ used ≤ blocks.length then
        pure
          { value := encodeQm31Limbs decoded.limbs
            limbs := decoded.limbs
            wordsUsed := decoded.wordsUsed
            blocksUsed := used
            remainingBlocks := blocks.drop used }
      else
        none

def decodeOrdinaryExact (blocks : List Digest256) : Option Qm31Bytes :=
  if blocks.length ≤ 4 then
    match decodeOrdinaryPrefix blocks with
    | some decoded =>
        if decoded.remainingBlocks = [] then some decoded.value else none
    | none => none
  else
    none

theorem decodeOrdinaryExact_functional (blocks : List Digest256)
    (first second : Qm31Bytes)
    (hfirst : decodeOrdinaryExact blocks = some first)
    (hsecond : decodeOrdinaryExact blocks = some second) :
    first = second := by
  rw [hfirst] at hsecond
  exact Option.some.inj hsecond

theorem decodeOrdinaryExact_block_cap (blocks : List Digest256)
    (value : Qm31Bytes) (run : decodeOrdinaryExact blocks = some value) :
    blocks.length ≤ 4 := by
  unfold decodeOrdinaryExact at run
  split at run
  · assumption
  · simp_all

/-! ## Nonzero and secure-circle outer retries -/

def decodeNonzeroPrefix : Nat → List Digest256 → Option OrdinaryPrefixDecode
  | 0, _ => none
  | attempts + 1, blocks => do
      let decoded ← decodeOrdinaryPrefix blocks
      if decoded.value = zeroBytes 16 then
        decodeNonzeroPrefix attempts decoded.remainingBlocks
      else
        pure decoded

def decodeNonzeroExact (blocks : List Digest256) : Option Qm31Bytes :=
  if blocks.length ≤ 12 then
    match decodeNonzeroPrefix 3 blocks with
    | some decoded =>
        if decoded.remainingBlocks = [] then some decoded.value else none
    | none => none
  else
    none

/-- The exact secure-circle algebra/admissibility function.  `none` covers
`1+t^2=0` and `t in CM31`; `some (x,y)` is the Rust return. -/
abbrev SecureCircleParameterMap :=
  Qm31Bytes → Option SecureCirclePointBytes

def decodeSecureCirclePrefix (circleMap : SecureCircleParameterMap) :
    Nat → List Digest256 → Option OrdinaryPrefixDecode
  | 0, _ => none
  | attempts + 1, blocks => do
      let decoded ← decodeOrdinaryPrefix blocks
      match circleMap decoded.value with
      | some _ => pure decoded
      | none => decodeSecureCirclePrefix circleMap attempts decoded.remainingBlocks

def decodeSecureCircleParameterExact (circleMap : SecureCircleParameterMap)
    (blocks : List Digest256) : Option Qm31Bytes :=
  if blocks.length ≤ 12 then
    match decodeSecureCirclePrefix circleMap 3 blocks with
    | some decoded =>
        if decoded.remainingBlocks = [] then some decoded.value else none
    | none => none
  else
    none

theorem decodeNonzeroExact_block_cap (blocks : List Digest256)
    (value : Qm31Bytes) (run : decodeNonzeroExact blocks = some value) :
    blocks.length ≤ 12 := by
  unfold decodeNonzeroExact at run
  split at run
  · assumption
  · simp_all

theorem decodeSecureCircleParameterExact_block_cap
    (circleMap : SecureCircleParameterMap) (blocks : List Digest256)
    (value : Qm31Bytes)
    (run : decodeSecureCircleParameterExact circleMap blocks = some value) :
    blocks.length ≤ 12 := by
  unfold decodeSecureCircleParameterExact at run
  split at run
  · assumption
  · simp_all

/-! ## Ordered q16 without replacement -/

/-- Preserve the first occurrence: an existing candidate does not move, and a
fresh candidate is appended after every earlier distinct candidate. -/
def keepFirst (seen : List Nat) (candidate : Nat) : List Nat :=
  if candidate ∈ seen then seen else seen ++ [candidate]

theorem keepFirst_existing {seen : List Nat} {candidate : Nat}
    (present : candidate ∈ seen) :
    keepFirst seen candidate = seen := by
  simp [keepFirst, present]

theorem keepFirst_fresh {seen : List Nat} {candidate : Nat}
    (fresh : candidate ∉ seen) :
    keepFirst seen candidate = seen ++ [candidate] := by
  simp [keepFirst, fresh]

theorem keepFirst_preserves_nodup {seen : List Nat} {candidate : Nat}
    (nodup : seen.Nodup) :
    (keepFirst seen candidate).Nodup := by
  by_cases present : candidate ∈ seen
  · simpa [keepFirst, present] using nodup
  · rw [keepFirst_fresh present]
    rw [List.nodup_append]
    refine ⟨nodup, by simp, ?_⟩
    intro member hmember singleton hsingleton
    simp only [List.mem_singleton] at hsingleton
    subst singleton
    intro heq
    apply present
    rw [← heq]
    exact hmember

def PositionsBounded (positions : List Nat) : Prop :=
  ∀ position ∈ positions, position < q16Bound

theorem keepFirst_q16_preserves_bounded (seen : List Nat) (word : Nat)
    (bounded : PositionsBounded seen) :
    PositionsBounded (keepFirst seen (q16Candidate word)) := by
  by_cases present : q16Candidate word ∈ seen
  · simpa [keepFirst, present] using bounded
  · intro position member
    simp [keepFirst, present] at member
    rcases member with member | equal
    · exact bounded position member
    · subst position
      exact q16Candidate_lt_bound word

structure UniqueScan where
  positions : List Nat
  drawsUsed : Nat
  deriving DecidableEq, Repr

/-- Consume at most `fuel` sequential words and stop before the first word
after `needed` distinct masked candidates have been accumulated. -/
def scanUniqueUntil (needed : Nat) :
    Nat → List Nat → List Nat → UniqueScan
  | 0, _, seen => { positions := seen, drawsUsed := 0 }
  | fuel + 1, [], seen => { positions := seen, drawsUsed := 0 }
  | fuel + 1, word :: rest, seen =>
      if needed ≤ seen.length then
        { positions := seen, drawsUsed := 0 }
      else
        let nextSeen := keepFirst seen (q16Candidate word)
        let tail := scanUniqueUntil needed fuel rest nextSeen
        { positions := tail.positions, drawsUsed := tail.drawsUsed + 1 }

def scanQ16 (blocks : List Digest256) : UniqueScan :=
  scanUniqueUntil 16 64 (flattenedWords blocks) []

theorem scanUniqueUntil_draw_cap (needed fuel : Nat)
    (words seen : List Nat) :
    (scanUniqueUntil needed fuel words seen).drawsUsed ≤ fuel := by
  induction fuel generalizing words seen with
  | zero => simp [scanUniqueUntil]
  | succ fuel ih =>
      cases words with
      | nil => simp [scanUniqueUntil]
      | cons word rest =>
          simp only [scanUniqueUntil]
          split
          · simp
          · dsimp
            have bound := ih rest (keepFirst seen (q16Candidate word))
            omega

theorem scanUniqueUntil_preserves_nodup (needed fuel : Nat)
    (words seen : List Nat) (nodup : seen.Nodup) :
    (scanUniqueUntil needed fuel words seen).positions.Nodup := by
  induction fuel generalizing words seen with
  | zero => simpa [scanUniqueUntil] using nodup
  | succ fuel ih =>
      cases words with
      | nil => simpa [scanUniqueUntil] using nodup
      | cons word rest =>
          simp only [scanUniqueUntil]
          split
          · exact nodup
          · simpa using ih rest (keepFirst seen (q16Candidate word))
              (keepFirst_preserves_nodup nodup)

theorem scanUniqueUntil_preserves_bounded (needed fuel : Nat)
    (words seen : List Nat) (bounded : PositionsBounded seen) :
    PositionsBounded (scanUniqueUntil needed fuel words seen).positions := by
  induction fuel generalizing words seen with
  | zero => simpa [scanUniqueUntil] using bounded
  | succ fuel ih =>
      cases words with
      | nil => simpa [scanUniqueUntil] using bounded
      | cons word rest =>
          simp only [scanUniqueUntil]
          split
          · exact bounded
          · simpa using ih rest (keepFirst seen (q16Candidate word))
              (keepFirst_q16_preserves_bounded seen word bounded)

theorem scanQ16_draw_cap (blocks : List Digest256) :
    (scanQ16 blocks).drawsUsed ≤ 64 :=
  scanUniqueUntil_draw_cap 16 64 (flattenedWords blocks) []

theorem scanQ16_positions_nodup (blocks : List Digest256) :
    (scanQ16 blocks).positions.Nodup := by
  exact scanUniqueUntil_preserves_nodup 16 64 (flattenedWords blocks) []
    (by simp)

theorem scanQ16_positions_bounded (blocks : List Digest256) :
    PositionsBounded (scanQ16 blocks).positions := by
  exact scanUniqueUntil_preserves_bounded 16 64 (flattenedWords blocks) []
    (by simp [PositionsBounded])

def positionIndex {positions : List Nat} (lengthExact : positions.length = 16)
    (index : Fin 16) : Fin positions.length :=
  Fin.cast lengthExact.symm index

def positionsEmbedding (positions : List Nat)
    (lengthExact : positions.length = 16)
    (nodup : positions.Nodup)
    (bounded : ∀ position ∈ positions, position < q16Bound) :
    Fin 16 ↪ Fin q16Bound where
  toFun index :=
    let source := positionIndex lengthExact index
    ⟨positions.get source, bounded _ (List.get_mem positions source)⟩
  inj' := by
    intro first second equal
    have valuesEqual :
        positions.get (positionIndex lengthExact first) =
          positions.get (positionIndex lengthExact second) := by
      exact congrArg Fin.val equal
    have indicesEqual := nodup.injective_get valuesEqual
    apply Fin.ext
    simpa [positionIndex] using congrArg Fin.val indicesEqual

/-- Exact block consumption relative to the supplied fixed-table block list. -/
def CandidateUsesExactBlocks (blocks : List Digest256) : CandidateOutcome → Prop
  | .samplerAbort => blocks.length = 8
  | .schedule schedule => schedule.blocksUsed = blocks.length

structure CandidateDecode (blocks : List Digest256) where
  outcome : CandidateOutcome
  exactBlocks : CandidateUsesExactBlocks blocks outcome

/-- Decode the exact blocks recorded for one cloned counter branch.  The
counter is already bound by the absorb query; byte decoding itself is counter
independent. -/
def decodeCandidateDetailed (_counter : Fin 64) (blocks : List Digest256) :
    Option (CandidateDecode blocks) :=
  if blockCap : blocks.length ≤ 8 then
    let scan := scanQ16 blocks
    if lengthExact : scan.positions.length = 16 then
      let nodup := scanQ16_positions_nodup blocks
      let bounded := scanQ16_positions_bounded blocks
      if exactUse : blocks.length = blocksNeededForWords scan.drawsUsed then
        if atLeastTwo : 2 ≤ blocks.length then
          let schedule : QuerySchedule :=
            { positions := positionsEmbedding scan.positions lengthExact nodup bounded
              blocksUsed := blocks.length
              atLeastTwoBlocks := atLeastTwo
              withinSixtyFourDraws := blockCap }
          some
            { outcome := .schedule schedule
              exactBlocks := rfl }
        else
          none
      else
        none
    else if abortExact : blocks.length = 8 ∧ scan.drawsUsed = 64 then
      some
        { outcome := .samplerAbort
          exactBlocks := abortExact.1 }
    else
      none
  else
    none

def decodeCandidateOutcome (counter : Fin 64) (blocks : List Digest256) :
    Option CandidateOutcome :=
  (decodeCandidateDetailed counter blocks).map CandidateDecode.outcome

theorem decodeCandidateOutcome_functional (counter : Fin 64)
    (blocks : List Digest256) (first second : CandidateOutcome)
    (hfirst : decodeCandidateOutcome counter blocks = some first)
    (hsecond : decodeCandidateOutcome counter blocks = some second) :
    first = second := by
  rw [hfirst] at hsecond
  exact Option.some.inj hsecond

theorem decodeCandidateOutcome_uses_exact_blocks (counter : Fin 64)
    (blocks : List Digest256) (outcome : CandidateOutcome)
    (run : decodeCandidateOutcome counter blocks = some outcome) :
    CandidateUsesExactBlocks blocks outcome := by
  unfold decodeCandidateOutcome at run
  cases detailed : decodeCandidateDetailed counter blocks with
  | none => simp [detailed] at run
  | some decoded =>
      simp [detailed] at run
      subst outcome
      exact decoded.exactBlocks

theorem every_query_schedule_has_exact_deployed_block_cap
    (schedule : QuerySchedule) :
    2 ≤ schedule.blocksUsed ∧ schedule.blocksUsed ≤ 8 :=
  ⟨schedule.atLeastTwoBlocks, schedule.withinSixtyFourDraws⟩

/-! ## Challenge-mode dispatch and deterministic-refinement integration -/

def decodeChallengeParameter (circleMap : SecureCircleParameterMap)
    (id : ChallengeId) (blocks : List Digest256) : Option Qm31Bytes :=
  match samplerMode id with
  | .ordinaryQm31 => decodeOrdinaryExact blocks
  | .nonzeroQm31 => decodeNonzeroExact blocks
  | .secureCirclePoint => decodeSecureCircleParameterExact circleMap blocks

theorem decodeChallengeParameter_functional
    (circleMap : SecureCircleParameterMap) (id : ChallengeId)
    (blocks : List Digest256) (first second : Qm31Bytes)
    (hfirst : decodeChallengeParameter circleMap id blocks = some first)
    (hsecond : decodeChallengeParameter circleMap id blocks = some second) :
    first = second := by
  rw [hfirst] at hsecond
  exact Option.some.inj hsecond

/-- A complete instantiation of the deterministic-refinement decoder record,
parameterized only by the separately formalized exact secure-circle map. -/
def deterministicDecoders (circleMap : SecureCircleParameterMap) :
    DeterministicDecoders where
  qm31Parameter := decodeChallengeParameter circleMap
  secureCirclePoint := circleMap
  candidate := decodeCandidateOutcome

@[simp] theorem deterministicDecoders_qm31Parameter
    (circleMap : SecureCircleParameterMap) (id : ChallengeId)
    (blocks : List Digest256) :
    (deterministicDecoders circleMap).qm31Parameter id blocks =
      decodeChallengeParameter circleMap id blocks := by
  rfl

@[simp] theorem deterministicDecoders_secureCirclePoint
    (circleMap : SecureCircleParameterMap) (parameter : Qm31Bytes) :
    (deterministicDecoders circleMap).secureCirclePoint parameter =
      circleMap parameter := by
  rfl

@[simp] theorem deterministicDecoders_candidate
    (circleMap : SecureCircleParameterMap) (counter : Fin 64)
    (blocks : List Digest256) :
    (deterministicDecoders circleMap).candidate counter blocks =
      decodeCandidateOutcome counter blocks := by
  rfl

#print axioms blockWords_length
#print axioms flattenedWords_length
#print axioms littleEndianWord_lt_two_pow_32
#print axioms maskedM31_lt_modulus
#print axioms q16Candidate_lt_bound
#print axioms decodeOrdinaryExact_functional
#print axioms decodeOrdinaryExact_block_cap
#print axioms decodeNonzeroExact_block_cap
#print axioms decodeSecureCircleParameterExact_block_cap
#print axioms keepFirst_existing
#print axioms keepFirst_fresh
#print axioms keepFirst_preserves_nodup
#print axioms keepFirst_q16_preserves_bounded
#print axioms scanUniqueUntil_draw_cap
#print axioms scanUniqueUntil_preserves_nodup
#print axioms scanUniqueUntil_preserves_bounded
#print axioms scanQ16_draw_cap
#print axioms scanQ16_positions_nodup
#print axioms scanQ16_positions_bounded
#print axioms decodeCandidateOutcome_functional
#print axioms decodeCandidateOutcome_uses_exact_blocks
#print axioms every_query_schedule_has_exact_deployed_block_cap
#print axioms decodeChallengeParameter_functional

end AspisK1.V7Tag73SamplerDecoder

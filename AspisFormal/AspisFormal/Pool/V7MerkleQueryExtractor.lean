import AspisFormal.Pool.V7MerkleQueryGrammar

/-!
# Executable Tag-73 two-tree Merkle query-graph extractor

This is the deterministic K1.2 committed-word extractor for the exact
deployed Tag-73 grammar. Success returns complete C1 and C2 words of length
`2^18`; their roots are recomputed independently from every extracted leaf.
The sixteen disclosed openings are then proved to be projections of those
complete words. Supplied authentication paths do not establish either part
of the success conclusion.

One ordered SHA-256 query log is shared by C1 and C2. Later repeats of an
identical raw input are removed while preserving first-query order. The
collision check includes malformed adversarial inputs and the extractor's
canonical-default subtree inputs. This module deliberately assigns no
numerical random-oracle bound: it exposes only the raw typed failure event.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace AspisPool.V7MerkleQueryExtractor

open V7MerkleQueryGrammar

abbrev Position := Fin (2 ^ treeDepth)
abbrev SiblingPath := Fin treeDepth → Digest208

structure Roots where
  c1 : Digest208
  c2 : Digest208
  deriving DecidableEq

structure PairedOpening where
  position : Position
  c1Value : C1Value
  c2Value : C2Value
  sharedSalt : Salt32
  /-- Bottom-up authentication paths define the independent accepted
  predicate, but are not used to derive the extractor's root conclusion. -/
  c1Siblings : SiblingPath
  c2Siblings : SiblingPath

abbrev TwoTreeOpeningProof := Fin disclosedQueryPairs → PairedOpening

def openingList (proof : TwoTreeOpeningProof) : List PairedOpening :=
  List.ofFn proof

/-! ## Exact raw-byte parser -/

def fixedOfListD {n : Nat} (bytes : List Byte) : Fin n → Byte :=
  fun index => bytes.getD index.val 0

/-- Parse exactly one of the 437-, 220-, or 53-byte preimages. Every other
raw input remains in the shared collision log but is not a typed vertex. -/
def parseTypedPreimage (input : RawHashInput) : Option TypedPreimage :=
  if input.length = 437 ∧ input.take 2 = [0x10, 0x71] then
    let tail := input.drop 2
    some (.c1Leaf
      (fixedOfListD (tail.take 403))
      (fixedOfListD (tail.drop 403)))
  else if input.length = 220 ∧ input.take 2 = [0x10, 0xf1] then
    let tail := input.drop 2
    some (.c2Leaf
      (fixedOfListD (tail.take 186))
      (fixedOfListD (tail.drop 186)))
  else if input.length = 53 ∧ input.take 1 = [0x11] then
    let tail := input.drop 1
    some (.node
      (fixedOfListD (tail.take 26))
      (fixedOfListD (tail.drop 26)))
  else
    none

theorem fixedBytes_fixedOfListD_of_length {n : Nat}
    (bytes : List Byte) (lengthExact : bytes.length = n) :
    fixedBytes (fixedOfListD bytes : Fin n → Byte) = bytes := by
  have pointwise :
      (fixedOfListD bytes : Fin n → Byte) =
    fun index => bytes.get (Fin.cast lengthExact.symm index) := by
    funext index
    exact List.getD_eq_get bytes 0 (Fin.cast lengthExact.symm index)
  rw [fixedBytes, pointwise,
    ← List.ofFn_congr lengthExact (List.get bytes), List.ofFn_get]

@[simp] theorem fixedOfListD_fixedBytes {n : Nat}
    (value : Fin n → Byte) :
    fixedOfListD (fixedBytes value) = value := by
  apply fixedBytes_injective
  exact fixedBytes_fixedOfListD_of_length
    (fixedBytes value) (fixedBytes_length value)

/-! ## Independent supplied-opening acceptance predicate -/

def foldPathAux (truncateSha256 : RawHashInput → Digest208) :
    Nat → Digest208 → List Digest208 → Digest208
  | _, accumulator, [] => accumulator
  | position, accumulator, sibling :: rest =>
      let parent :=
        if position.testBit 0 then
          truncateSha256 (serialize (.node sibling accumulator))
        else
          truncateSha256 (serialize (.node accumulator sibling))
      foldPathAux truncateSha256 (position / 2) parent rest

def foldPath (truncateSha256 : RawHashInput → Digest208)
    (position : Position) (leaf : Digest208)
    (siblings : SiblingPath) : Digest208 :=
  foldPathAux truncateSha256 position.val leaf (List.ofFn siblings)

def c1DisclosedLeafDigest (truncateSha256 : RawHashInput → Digest208)
    (opening : PairedOpening) : Digest208 :=
  truncateSha256 (serialize (.c1Leaf opening.c1Value opening.sharedSalt))

def c2DisclosedLeafDigest (truncateSha256 : RawHashInput → Digest208)
    (opening : PairedOpening) : Digest208 :=
  truncateSha256 (serialize (.c2Leaf opening.c2Value opening.sharedSalt))

def accepted_two_tree_openings
    (truncateSha256 : RawHashInput → Digest208)
    (roots : Roots) (proof : TwoTreeOpeningProof) : Prop :=
  ((openingList proof).map PairedOpening.position).Nodup ∧
    ∀ ordinal : Fin disclosedQueryPairs,
      foldPath truncateSha256 (proof ordinal).position
          (c1DisclosedLeafDigest truncateSha256 (proof ordinal))
          (proof ordinal).c1Siblings = roots.c1 ∧
        foldPath truncateSha256 (proof ordinal).position
          (c2DisclosedLeafDigest truncateSha256 (proof ordinal))
          (proof ordinal).c2Siblings = roots.c2

/-! ## Raw shared log and typed failures -/

inductive Failure where
  | missingRootQuery
  | missingPreimageQuery
  | guessedDigest
  | forwardReference
  | truncatedDigestCollision
  | malformedTypedPreimage
  | pairedSaltMismatch
  deriving DecidableEq, Repr

def deduplicateFirstAux : List RawHashInput → OrderedRawQueryLog → OrderedRawQueryLog
  | _, [] => []
  | seen, input :: rest =>
      if input ∈ seen then deduplicateFirstAux seen rest
      else input :: deduplicateFirstAux (input :: seen) rest

def deduplicateFirst (log : OrderedRawQueryLog) : OrderedRawQueryLog :=
  deduplicateFirstAux [] log

def hasRawTruncatedCollision
    (truncateSha256 : RawHashInput → Digest208) : OrderedRawQueryLog → Bool
  | [] => false
  | input :: rest =>
      rest.any (fun other =>
        decide (input ≠ other ∧ truncateSha256 input = truncateSha256 other)) ||
      hasRawTruncatedCollision truncateSha256 rest

/-! ## Complete words and independent commitment computation -/

structure C1Leaf where
  value : C1Value
  salt : Salt32
  deriving DecidableEq

structure C2Leaf where
  value : C2Value
  salt : Salt32
  deriving DecidableEq

def defaultC1Leaf : C1Leaf where
  value := fun _ => 0
  salt := fun _ => 0

def defaultC2Leaf : C2Leaf where
  value := fun _ => 0
  salt := fun _ => 0

def c1LeafDigest (truncateSha256 : RawHashInput → Digest208)
    (leaf : C1Leaf) : Digest208 :=
  truncateSha256 (serialize (.c1Leaf leaf.value leaf.salt))

def c2LeafDigest (truncateSha256 : RawHashInput → Digest208)
    (leaf : C2Leaf) : Digest208 :=
  truncateSha256 (serialize (.c2Leaf leaf.value leaf.salt))

def nodeDigest (truncateSha256 : RawHashInput → Digest208)
    (left right : Digest208) : Digest208 :=
  truncateSha256 (serialize (.node left right))

/-- Independently commit a complete list of leaves. A result is produced only
for exactly `2^height` leaves. -/
def commitTree {Leaf : Type*}
    (truncateSha256 : RawHashInput → Digest208)
    (leafDigest : Leaf → Digest208) : Nat → List Leaf → Option Digest208
  | 0, [leaf] => some (leafDigest leaf)
  | 0, _ => none
  | height + 1, leaves =>
      if leaves.length = 2 ^ (height + 1) then
        match commitTree truncateSha256 leafDigest height
              (leaves.take (2 ^ height)),
            commitTree truncateSha256 leafDigest height
              (leaves.drop (2 ^ height)) with
        | some left, some right => some (nodeDigest truncateSha256 left right)
        | _, _ => none
      else
        none

def commitC1Word (truncateSha256 : RawHashInput → Digest208)
    (leaves : List C1Leaf) : Option Digest208 :=
  commitTree truncateSha256 (c1LeafDigest truncateSha256) treeDepth leaves

def commitC2Word (truncateSha256 : RawHashInput → Digest208)
    (leaves : List C2Leaf) : Option Digest208 :=
  commitTree truncateSha256 (c2LeafDigest truncateSha256) treeDepth leaves

def defaultC1SubtreeDigest (truncateSha256 : RawHashInput → Digest208) :
    Nat → Digest208
  | 0 => c1LeafDigest truncateSha256 defaultC1Leaf
  | height + 1 =>
      let child := defaultC1SubtreeDigest truncateSha256 height
      nodeDigest truncateSha256 child child

def defaultC2SubtreeDigest (truncateSha256 : RawHashInput → Digest208) :
    Nat → Digest208
  | 0 => c2LeafDigest truncateSha256 defaultC2Leaf
  | height + 1 =>
      let child := defaultC2SubtreeDigest truncateSha256 height
      nodeDigest truncateSha256 child child

/-- Inputs queried by the extractor when checking canonical-default subtree
digests. They are included in the same collision universe as adversarial raw
queries; they are not inserted into the adversary's causal log. -/
def defaultC1SubtreeInputs (truncateSha256 : RawHashInput → Digest208) :
    Nat → List RawHashInput
  | 0 => [serialize (.c1Leaf defaultC1Leaf.value defaultC1Leaf.salt)]
  | height + 1 =>
      let child := defaultC1SubtreeDigest truncateSha256 height
      defaultC1SubtreeInputs truncateSha256 height ++
        [serialize (.node child child)]

def defaultC2SubtreeInputs (truncateSha256 : RawHashInput → Digest208) :
    Nat → List RawHashInput
  | 0 => [serialize (.c2Leaf defaultC2Leaf.value defaultC2Leaf.salt)]
  | height + 1 =>
      let child := defaultC2SubtreeDigest truncateSha256 height
      defaultC2SubtreeInputs truncateSha256 height ++
        [serialize (.node child child)]

def collisionUniverse
    (truncateSha256 : RawHashInput → Digest208)
    (adversaryLog : OrderedRawQueryLog) : OrderedRawQueryLog :=
  deduplicateFirst
    (adversaryLog ++
      defaultC1SubtreeInputs truncateSha256 treeDepth ++
      defaultC2SubtreeInputs truncateSha256 treeDepth)

inductive SubtreeResult (Leaf : Type*) where
  | leaves (values : List Leaf)
  | failure (reason : Failure)

/-! ## Full causal graph traversal -/

def extractC1Subtree
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) :
    Nat → Digest208 → Nat → SubtreeResult C1Leaf
  | 0, expectedDigest, queryIndex =>
      match log[queryIndex]? with
      | none => .failure .missingPreimageQuery
      | some input =>
          if truncateSha256 input = expectedDigest then
            match parseTypedPreimage input with
            | some (.c1Leaf value salt) => .leaves [⟨value, salt⟩]
            | _ => .failure .malformedTypedPreimage
          else
            .failure .guessedDigest
  | height + 1, expectedDigest, queryIndex =>
      match log[queryIndex]? with
      | none => .failure .missingPreimageQuery
      | some input =>
          if truncateSha256 input = expectedDigest then
            match parseTypedPreimage input with
            | some (.node left right) =>
                let extractChild := fun child =>
                  if child = defaultC1SubtreeDigest truncateSha256 height then
                    SubtreeResult.leaves
                      (List.replicate (2 ^ height) defaultC1Leaf)
                  else
                    match classifyReference truncateSha256 child queryIndex log with
                    | .earlier childIndex =>
                        extractC1Subtree truncateSha256 log
                          height child childIndex
                    | .forward _ => .failure .forwardReference
                    | .missing => .failure .missingPreimageQuery
                match extractChild left with
                | .failure reason => .failure reason
                | .leaves leftLeaves =>
                    match extractChild right with
                    | .failure reason => .failure reason
                    | .leaves rightLeaves =>
                        .leaves (leftLeaves ++ rightLeaves)
            | _ => .failure .malformedTypedPreimage
          else
            .failure .guessedDigest

def extractC2Subtree
    (truncateSha256 : RawHashInput → Digest208)
    (log : OrderedRawQueryLog) :
    Nat → Digest208 → Nat → SubtreeResult C2Leaf
  | 0, expectedDigest, queryIndex =>
      match log[queryIndex]? with
      | none => .failure .missingPreimageQuery
      | some input =>
          if truncateSha256 input = expectedDigest then
            match parseTypedPreimage input with
            | some (.c2Leaf value salt) => .leaves [⟨value, salt⟩]
            | _ => .failure .malformedTypedPreimage
          else
            .failure .guessedDigest
  | height + 1, expectedDigest, queryIndex =>
      match log[queryIndex]? with
      | none => .failure .missingPreimageQuery
      | some input =>
          if truncateSha256 input = expectedDigest then
            match parseTypedPreimage input with
            | some (.node left right) =>
                let extractChild := fun child =>
                  if child = defaultC2SubtreeDigest truncateSha256 height then
                    SubtreeResult.leaves
                      (List.replicate (2 ^ height) defaultC2Leaf)
                  else
                    match classifyReference truncateSha256 child queryIndex log with
                    | .earlier childIndex =>
                        extractC2Subtree truncateSha256 log
                          height child childIndex
                    | .forward _ => .failure .forwardReference
                    | .missing => .failure .missingPreimageQuery
                match extractChild left with
                | .failure reason => .failure reason
                | .leaves leftLeaves =>
                    match extractChild right with
                    | .failure reason => .failure reason
                    | .leaves rightLeaves =>
                        .leaves (leftLeaves ++ rightLeaves)
            | _ => .failure .malformedTypedPreimage
          else
            .failure .guessedDigest

structure ExtractedWords where
  c1 : List C1Leaf
  c2 : List C2Leaf

inductive CompleteWordsResult where
  | words (received : ExtractedWords)
  | failure (reason : Failure)

def extractCompleteWords
    (truncateSha256 : RawHashInput → Digest208)
    (roots : Roots) (log : OrderedRawQueryLog) : CompleteWordsResult :=
  match resolveFirst truncateSha256 roots.c1 log,
      resolveFirst truncateSha256 roots.c2 log with
  | some c1RootIndex, some c2RootIndex =>
      match extractC1Subtree truncateSha256 log treeDepth roots.c1 c1RootIndex with
      | .failure reason => .failure reason
      | .leaves c1Leaves =>
          match extractC2Subtree truncateSha256 log treeDepth roots.c2 c2RootIndex with
          | .failure reason => .failure reason
          | .leaves c2Leaves => .words ⟨c1Leaves, c2Leaves⟩
  | _, _ => .failure .missingRootQuery

/-! ## Complete-root and disclosure projection conclusion -/

def disclosuresAreProjections
    (words : ExtractedWords) (proof : TwoTreeOpeningProof) : Prop :=
  ∀ ordinal : Fin disclosedQueryPairs,
    words.c1[(proof ordinal).position.val]? = some
        ⟨(proof ordinal).c1Value, (proof ordinal).sharedSalt⟩ ∧
      words.c2[(proof ordinal).position.val]? = some
        ⟨(proof ordinal).c2Value, (proof ordinal).sharedSalt⟩

def openingIsProjection
    (words : ExtractedWords) (opening : PairedOpening) : Prop :=
  words.c1[opening.position.val]? = some
      ⟨opening.c1Value, opening.sharedSalt⟩ ∧
    words.c2[opening.position.val]? = some
      ⟨opening.c2Value, opening.sharedSalt⟩

def completeWordsMatchRoots
    (truncateSha256 : RawHashInput → Digest208)
    (words : ExtractedWords) (roots : Roots) : Prop :=
  words.c1.length = 2 ^ treeDepth ∧
    words.c2.length = 2 ^ treeDepth ∧
    commitC1Word truncateSha256 words.c1 = some roots.c1 ∧
    commitC2Word truncateSha256 words.c2 = some roots.c2

/-- This success predicate independently hashes the complete extracted words
and projects their sixteen disclosed coordinates. It contains no supplied
authentication-path equation and is not stored in `ExtractedWords`. -/
def wordsMatchRootsAndAllAcceptedOpenings
    (truncateSha256 : RawHashInput → Digest208)
    (words : ExtractedWords) (roots : Roots)
    (proof : TwoTreeOpeningProof) : Prop :=
  completeWordsMatchRoots truncateSha256 words roots ∧
    disclosuresAreProjections words proof

/-- Give salt mismatch its exact typed reason before the final independent
root/projection check. -/
def firstProjectionFailure (words : ExtractedWords) :
    List PairedOpening → Option Failure
  | [] => none
  | opening :: rest =>
      match words.c1[opening.position.val]?, words.c2[opening.position.val]? with
      | some c1Leaf, some c2Leaf =>
          if c1Leaf.salt = opening.sharedSalt ∧
              c2Leaf.salt = opening.sharedSalt then
            if c1Leaf.value = opening.c1Value ∧
                c2Leaf.value = opening.c2Value then
              firstProjectionFailure words rest
            else
              some .guessedDigest
          else
            some .pairedSaltMismatch
      | _, _ => some .guessedDigest

theorem firstProjectionFailure_none_iff
    (words : ExtractedWords) : ∀ openings : List PairedOpening,
    firstProjectionFailure words openings = none ↔
      ∀ opening ∈ openings, openingIsProjection words opening := by
  intro openings
  induction openings with
  | nil => simp [firstProjectionFailure]
  | cons opening rest inductionHypothesis =>
      cases c1Equation : words.c1[opening.position.val]? with
      | none =>
          simp [firstProjectionFailure, c1Equation, openingIsProjection]
      | some c1Leaf =>
          cases c2Equation : words.c2[opening.position.val]? with
          | none =>
              simp [firstProjectionFailure, c1Equation, c2Equation,
                openingIsProjection]
          | some c2Leaf =>
              rcases c1Leaf with ⟨c1Value, c1Salt⟩
              rcases c2Leaf with ⟨c2Value, c2Salt⟩
              by_cases c1SaltMatches : c1Salt = opening.sharedSalt
              <;> by_cases c2SaltMatches : c2Salt = opening.sharedSalt
              <;> by_cases c1ValueMatches : c1Value = opening.c1Value
              <;> by_cases c2ValueMatches : c2Value = opening.c2Value
              <;> simp [firstProjectionFailure, c1Equation, c2Equation,
                openingIsProjection, inductionHypothesis, c1SaltMatches,
                c2SaltMatches, c1ValueMatches, c2ValueMatches]

theorem firstProjectionFailure_none_yields_disclosures
    (words : ExtractedWords) (proof : TwoTreeOpeningProof)
    (noFailure :
      firstProjectionFailure words (openingList proof) = none) :
    disclosuresAreProjections words proof := by
  intro ordinal
  exact (firstProjectionFailure_none_iff words (openingList proof)).mp
    noFailure (proof ordinal) (by simp [openingList])

inductive ExtractionResult where
  | words (received : ExtractedWords)
  | failure (reason : Failure)

def completeWordsMatchRootsB
    (truncateSha256 : RawHashInput → Digest208)
    (words : ExtractedWords) (roots : Roots) : Bool :=
  decide (words.c1.length = 2 ^ treeDepth) &&
    decide (words.c2.length = 2 ^ treeDepth) &&
    decide (commitC1Word truncateSha256 words.c1 = some roots.c1) &&
    decide (commitC2Word truncateSha256 words.c2 = some roots.c2)

theorem completeWordsMatchRootsB_eq_true_iff
    (truncateSha256 : RawHashInput → Digest208)
    (words : ExtractedWords) (roots : Roots) :
    completeWordsMatchRootsB truncateSha256 words roots = true ↔
      completeWordsMatchRoots truncateSha256 words roots := by
  simp [completeWordsMatchRootsB, completeWordsMatchRoots]
  tauto

def finishExtraction
    (truncateSha256 : RawHashInput → Digest208)
    (roots : Roots) (proof : TwoTreeOpeningProof)
    (words : ExtractedWords) : ExtractionResult :=
  match firstProjectionFailure words (openingList proof) with
  | some reason => .failure reason
  | none =>
      if completeWordsMatchRootsB truncateSha256 words roots then
        .words words
      else
        .failure .guessedDigest

/-- Executable K1.2 extractor. Canonical-default hash inputs affect collision
accounting, while causal resolution uses only the deduplicated adversary log. -/
def extractV7Words
    (truncateSha256 : RawHashInput → Digest208)
    (roots : Roots) (proof : TwoTreeOpeningProof)
    (orderedQueries : OrderedRawQueryLog) : ExtractionResult :=
  if hasRawTruncatedCollision truncateSha256
      (collisionUniverse truncateSha256 (deduplicateFirst orderedQueries)) then
    .failure .truncatedDigestCollision
  else
    match extractCompleteWords truncateSha256 roots
        (deduplicateFirst orderedQueries) with
    | .failure reason => .failure reason
    | .words words => finishExtraction truncateSha256 roots proof words

theorem finishExtraction_success_yields_match
    (truncateSha256 : RawHashInput → Digest208)
    (roots : Roots) (proof : TwoTreeOpeningProof)
    (candidate output : ExtractedWords)
    (success : finishExtraction truncateSha256 roots proof candidate =
      .words output) :
    output = candidate ∧
    wordsMatchRootsAndAllAcceptedOpenings
      truncateSha256 output roots proof := by
  cases projectionFailure :
      firstProjectionFailure candidate (openingList proof) with
  | some reason =>
      simp [finishExtraction, projectionFailure] at success
  | none =>
      cases rootsEquation :
          completeWordsMatchRootsB truncateSha256 candidate roots with
      | false =>
          simp [finishExtraction, projectionFailure, rootsEquation] at success
      | true =>
        have outputEquals : output = candidate := by
          simpa [finishExtraction, projectionFailure, rootsEquation] using
            success.symm
        subst output
        have rootsMatch :=
          (completeWordsMatchRootsB_eq_true_iff
            truncateSha256 candidate roots).mp rootsEquation
        exact ⟨rfl, rootsMatch,
          firstProjectionFailure_none_yields_disclosures
            candidate proof projectionFailure⟩

theorem extractV7Words_success_yields_roots_and_openings_match
    (truncateSha256 : RawHashInput → Digest208)
    (roots : Roots) (proof : TwoTreeOpeningProof)
    (orderedQueries : OrderedRawQueryLog) (words : ExtractedWords)
    (success : extractV7Words truncateSha256 roots proof orderedQueries =
      .words words) :
    wordsMatchRootsAndAllAcceptedOpenings
      truncateSha256 words roots proof := by
  cases collision : hasRawTruncatedCollision truncateSha256
      (collisionUniverse truncateSha256 (deduplicateFirst orderedQueries)) with
  | true => simp [extractV7Words, collision] at success
  | false =>
      cases graph : extractCompleteWords truncateSha256 roots
          (deduplicateFirst orderedQueries) with
      | failure reason => simp [extractV7Words, collision, graph] at success
      | words graphWords =>
          have finishSuccess :
              finishExtraction truncateSha256 roots proof graphWords =
                .words words := by
            simpa [extractV7Words, collision, graph] using success
          exact (finishExtraction_success_yields_match
            truncateSha256 roots proof graphWords words finishSuccess).2

/-! ## Causal provenance for the raw probability reduction -/

/-- Explicit success provenance, separate from the root/output conclusion.
The two subtree equations are executable graph walks.  Inverting either
equation exposes every raw preimage, exact expected digest, and recursively
either an exact canonical-default child or a `classifyReference = .earlier`
edge; no supplied authentication path occurs here. -/
def SuccessfulCausalProvenance
    (truncateSha256 : RawHashInput → Digest208)
    (roots : Roots) (proof : TwoTreeOpeningProof)
    (orderedQueries : OrderedRawQueryLog)
    (words : ExtractedWords) : Prop :=
  let log := deduplicateFirst orderedQueries
  hasRawTruncatedCollision truncateSha256
      (collisionUniverse truncateSha256 log) = false ∧
    ∃ c1RootIndex c2RootIndex : Nat,
      resolveFirst truncateSha256 roots.c1 log = some c1RootIndex ∧
      resolveFirst truncateSha256 roots.c2 log = some c2RootIndex ∧
      extractC1Subtree truncateSha256 log treeDepth roots.c1 c1RootIndex =
        .leaves words.c1 ∧
      extractC2Subtree truncateSha256 log treeDepth roots.c2 c2RootIndex =
        .leaves words.c2 ∧
      firstProjectionFailure words (openingList proof) = none

theorem extractCompleteWords_success_yields_root_queries
    (truncateSha256 : RawHashInput → Digest208)
    (roots : Roots) (log : OrderedRawQueryLog) (words : ExtractedWords)
    (success : extractCompleteWords truncateSha256 roots log = .words words) :
    ∃ c1RootIndex c2RootIndex : Nat,
      resolveFirst truncateSha256 roots.c1 log = some c1RootIndex ∧
      resolveFirst truncateSha256 roots.c2 log = some c2RootIndex ∧
      extractC1Subtree truncateSha256 log treeDepth roots.c1 c1RootIndex =
        .leaves words.c1 ∧
      extractC2Subtree truncateSha256 log treeDepth roots.c2 c2RootIndex =
        .leaves words.c2 := by
  cases c1RootEquation : resolveFirst truncateSha256 roots.c1 log with
  | none => simp [extractCompleteWords, c1RootEquation] at success
  | some c1RootIndex =>
      cases c2RootEquation : resolveFirst truncateSha256 roots.c2 log with
      | none =>
          simp [extractCompleteWords, c1RootEquation, c2RootEquation] at success
      | some c2RootIndex =>
          cases c1Extraction : extractC1Subtree truncateSha256 log
              treeDepth roots.c1 c1RootIndex with
          | failure reason =>
              simp [extractCompleteWords, c1RootEquation, c2RootEquation,
                c1Extraction] at success
          | leaves c1Leaves =>
              cases c2Extraction : extractC2Subtree truncateSha256 log
                  treeDepth roots.c2 c2RootIndex with
              | failure reason =>
                  simp [extractCompleteWords, c1RootEquation, c2RootEquation,
                    c1Extraction, c2Extraction] at success
              | leaves c2Leaves =>
                  have wordsEquation :
                      words = ⟨c1Leaves, c2Leaves⟩ := by
                    simpa [extractCompleteWords, c1RootEquation, c2RootEquation,
                      c1Extraction, c2Extraction] using success.symm
                  subst words
                  exact ⟨c1RootIndex, c2RootIndex, rfl, rfl, c1Extraction,
                    c2Extraction⟩

theorem finishExtraction_success_has_no_projection_failure
    (truncateSha256 : RawHashInput → Digest208)
    (roots : Roots) (proof : TwoTreeOpeningProof)
    (candidate output : ExtractedWords)
    (success : finishExtraction truncateSha256 roots proof candidate =
      .words output) :
    firstProjectionFailure output (openingList proof) = none := by
  have outputEquation :=
    (finishExtraction_success_yields_match
      truncateSha256 roots proof candidate output success).1
  subst output
  cases projectionEquation :
      firstProjectionFailure candidate (openingList proof) with
  | none => exact rfl
  | some reason =>
      simp [finishExtraction, projectionEquation] at success

theorem extractV7Words_success_yields_causal_provenance
    (truncateSha256 : RawHashInput → Digest208)
    (roots : Roots) (proof : TwoTreeOpeningProof)
    (orderedQueries : OrderedRawQueryLog) (words : ExtractedWords)
    (success : extractV7Words truncateSha256 roots proof orderedQueries =
      .words words) :
    SuccessfulCausalProvenance
      truncateSha256 roots proof orderedQueries words := by
  cases collisionEquation : hasRawTruncatedCollision truncateSha256
      (collisionUniverse truncateSha256 (deduplicateFirst orderedQueries)) with
  | true => simp [extractV7Words, collisionEquation] at success
  | false =>
      cases graphEquation : extractCompleteWords truncateSha256 roots
          (deduplicateFirst orderedQueries) with
      | failure reason =>
          simp [extractV7Words, collisionEquation, graphEquation] at success
      | words graphWords =>
          have finishSuccess :
              finishExtraction truncateSha256 roots proof graphWords =
                .words words := by
            simpa [extractV7Words, collisionEquation, graphEquation] using success
          have outputEquation :=
            (finishExtraction_success_yields_match
              truncateSha256 roots proof graphWords words finishSuccess).1
          subst words
          obtain ⟨c1RootIndex, c2RootIndex, c1RootEquation,
              c2RootEquation, c1Extraction, c2Extraction⟩ :=
            extractCompleteWords_success_yields_root_queries
              truncateSha256 roots (deduplicateFirst orderedQueries)
              graphWords graphEquation
          exact ⟨collisionEquation, c1RootIndex, c2RootIndex,
            c1RootEquation, c2RootEquation, c1Extraction, c2Extraction,
            finishExtraction_success_has_no_projection_failure
              truncateSha256 roots proof graphWords graphWords finishSuccess⟩

/-- Raw, symbolic failure event. Later probability accounting must bound this
as a function of the total distinct shared-log and canonical-default queries. -/
def V7MerkleExtractionFailure
    (truncateSha256 : RawHashInput → Digest208)
    (roots : Roots) (proof : TwoTreeOpeningProof)
    (orderedQueries : OrderedRawQueryLog) : Prop :=
  ∃ reason : Failure,
    extractV7Words truncateSha256 roots proof orderedQueries =
      .failure reason

/-- The exact raw event whose random-oracle probability remains to be bounded.
No numerical estimate is asserted in K1.2. -/
def AcceptedRawMerkleExtractionFailure
    (truncateSha256 : RawHashInput → Digest208)
    (roots : Roots) (proof : TwoTreeOpeningProof)
    (orderedQueries : OrderedRawQueryLog) : Prop :=
  accepted_two_tree_openings truncateSha256 roots proof ∧
    V7MerkleExtractionFailure truncateSha256 roots proof orderedQueries

theorem accepted_two_tree_openings_extract_or_typed_failure
    (truncateSha256 : RawHashInput → Digest208)
    (roots : Roots) (proof : TwoTreeOpeningProof)
    (orderedQueries : OrderedRawQueryLog)
    (_accepted : accepted_two_tree_openings truncateSha256 roots proof) :
    (∃ words : ExtractedWords,
        extractV7Words truncateSha256 roots proof orderedQueries =
            .words words ∧
          wordsMatchRootsAndAllAcceptedOpenings
            truncateSha256 words roots proof) ∨
      V7MerkleExtractionFailure
        truncateSha256 roots proof orderedQueries := by
  cases resultEquation :
      extractV7Words truncateSha256 roots proof orderedQueries with
  | words words =>
      left
      exact ⟨words, rfl,
        extractV7Words_success_yields_roots_and_openings_match
          truncateSha256 roots proof orderedQueries words resultEquation⟩
  | failure reason =>
      right
      exact ⟨reason, resultEquation⟩

theorem exact_depth_roots_and_opening_count :
    treeDepth = 18 ∧ disclosedQueryPairs = 16 :=
  frozen_tree_parameters

#print axioms finishExtraction_success_yields_match
#print axioms extractV7Words_success_yields_roots_and_openings_match
#print axioms extractV7Words_success_yields_causal_provenance
#print axioms accepted_two_tree_openings_extract_or_typed_failure

end AspisPool.V7MerkleQueryExtractor

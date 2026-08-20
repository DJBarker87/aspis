import AspisFormal.V5AcceptedExecutionSecurityBridge
import AspisFormal.V5MerkleConsumedValueBridge

/-!
# Authenticated V5 openings determine the FRI words

The maintained accepted-execution bridge used to ask for a separately chosen
"reference forest" whose decoded leaves already agreed with the ideal FRI
transcript.  That is stronger than the Merkle fact actually needed and, for
layer zero, its decoder shape was inaccurate: production combines the C1 and
C2 leaves before the first fold.

This file states the exact commitment fact directly.  For a fixed Merkle root
and section index, choose the value of any accepted leaf at that index (or a
fixed default if no such leaf exists).  Outside an explicit hash collision,
every accepted opening at that index has that value.  Applying the production-
shaped paired C1/C2 decoder therefore constructs four complete FRI words from
the five roots, independently of the sampled query set, and every accepted
forest projects to those words.

This is a Merkle-binding and byte-projection result.  It does not identify the
root-defined words with an independently supplied Fiat--Shamir adversary
family; that separate experiment connection must use the roots absorbed by
the transcript driver rather than be hidden as a leaf-decoder premise.
-/

namespace AspisV5MerkleTranscriptProjection

open AspisV5AcceptedExecutionSecurityBridge
open AspisV5ComponentCConcreteFoldLinearity
open AspisV5FriCoherentCandidateExtraction
open AspisV5FriReleasedAdaptiveExtraction
open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleConsumedValueBridge
open AspisV5MerkleRustBridge

variable {K Digest : Type*}

/-! ## Production-shaped decoding -/

/-- Public name for the corrected production-shaped decoder maintained by the
accepted-execution bridge. -/
abbrev ProductionOpeningDecoder := OpeningFibreDecoder

/-- Pure field-value operations applied after the exact little-endian byte
decoders.  This separates byte layout (proved below) from the already
maintained field-arithmetic equations for gamma combination and FRI folding. -/
structure DecodedFibreOperations (K : Type*) where
  layer0 : (Fin 16 -> Option AspisV5ComponentCRejectionSampler.M31Value) ->
    (Fin 3 -> Option AspisV5ComponentCRejectionSampler.QM31Limbs) -> K
  c2 : (Fin 3 -> Option AspisV5ComponentCRejectionSampler.QM31Limbs) -> K
  later : Option AspisV5ComponentCRejectionSampler.QM31Limbs -> K

/-- The production-shaped decoder assembled directly from the exact C1, C2,
and later-layer byte offsets.  There is no caller equality in this definition:
the only inputs are the raw authenticated leaves and the field operations. -/
def exactByteOpeningDecoder (operations : DecodedFibreOperations K) :
    ProductionOpeningDecoder K where
  layer0 := fun c1 c2 slot => operations.layer0
    (fun column => decodeC1Entry c1 slot column)
    (fun helper => decodeC2Entry c2 slot helper)
  c2 := fun c2 slot => operations.c2
    (fun helper => decodeC2Entry c2 slot helper)
  later := fun _tree value slot => operations.later (decodeLaterSlot value slot)

@[simp] theorem exactByteOpeningDecoder_layer0
    (operations : DecodedFibreOperations K) (c1 c2 : List Byte)
    (slot : Fin 4) :
    (exactByteOpeningDecoder operations).layer0 c1 c2 slot =
      operations.layer0
        (fun column => decodeC1Entry c1 slot column)
        (fun helper => decodeC2Entry c2 slot helper) := rfl

@[simp] theorem exactByteOpeningDecoder_c2
    (operations : DecodedFibreOperations K) (c2 : List Byte)
    (slot : Fin 4) :
    (exactByteOpeningDecoder operations).c2 c2 slot =
      operations.c2 (fun helper => decodeC2Entry c2 slot helper) := rfl

@[simp] theorem exactByteOpeningDecoder_later
    (operations : DecodedFibreOperations K) (tree : V5PrivateSection)
    (value : List Byte) (slot : Fin 4) :
    (exactByteOpeningDecoder operations).later tree value slot =
      operations.later (decodeLaterSlot value slot) := rfl

/-- Decode the four values used for one section/query.  The `.c1` case is the
production gamma-combined layer-zero value and therefore reads both roots. -/
def productionDecodedFibre
    (decoder : ProductionOpeningDecoder K)
    (hashing : MerkleHashing Digest)
    {roots : V5PrivateRoots Digest} {querySet : Finset V5Query}
    (forest : AcceptedV5Forest hashing roots querySet)
    (tree : V5PrivateSection) (query : V5Query) (hq : query ∈ querySet) :
    Fin 4 -> K :=
  decodedFibre decoder hashing forest tree query hq

/-! ## Accepted leaves indexed by their actual tree position -/

def radixSlotsAtIndex (tree : V5PrivateSection) (index : Nat) :
    List (Fin 4) :=
  radixSlotsFromLevel index 0 (radixLevelCount tree)

def binaryCapIndexAtIndex (tree : V5PrivateSection) (index : Nat) : Nat :=
  indexAtRadixLevel index (radixLevelCount tree)

def topSideAtIndex (tree : V5PrivateSection) (index : Nat) : BinarySide :=
  if binaryCapIndexAtIndex tree index = 0 then .left else .right

/-- The Merkle statement depends on the section's actual leaf index.  Keeping
that index directly avoids treating two V5 queries that share a later-layer
leaf as different commitment positions. -/
structure AcceptedV5LeafAtIndex
    (hashing : MerkleHashing Digest) (tree : V5PrivateSection)
    (index : Nat) (root : Digest) where
  record : List Byte
  record_length : record.length = valueWidth tree + 32
  path : OddBinaryCapPath Digest (radixSlotsAtIndex tree index)
  root_eq : pathRoot hashing (topSideAtIndex tree index) path
      (hashing.privateLeaf (treeTag tree) record) = root

def openedValueAtIndex
    {hashing : MerkleHashing Digest} {tree : V5PrivateSection}
    {index : Nat} {root : Digest}
    (opening : AcceptedV5LeafAtIndex hashing tree index root) : List Byte :=
  opening.record.take (valueWidth tree)

/-- Forget the syntactic query and retain exactly the tree index which drives
the path topology. -/
def acceptedLeafAtIndex
    (hashing : MerkleHashing Digest)
    {tree : V5PrivateSection} {query : V5Query} {root : Digest}
    (leaf : AcceptedV5Leaf hashing tree query root) :
    AcceptedV5LeafAtIndex hashing tree (sectionIndex tree query) root where
  record := leaf.record
  record_length := leaf.record_length
  path := leaf.path
  root_eq := leaf.root_eq

@[simp] theorem openedValueAtIndex_acceptedLeafAtIndex
    (hashing : MerkleHashing Digest)
    {tree : V5PrivateSection} {query : V5Query} {root : Digest}
    (leaf : AcceptedV5Leaf hashing tree query root) :
    openedValueAtIndex (acceptedLeafAtIndex hashing leaf) = openedValue leaf :=
  rfl

/-- Distinct records accepted at one root/section/index exhibit an explicit
primitive Merkle-hash collision. -/
theorem acceptedV5LeafAtIndex_collision_of_record_ne
    (hashing : MerkleHashing Digest)
    {tree : V5PrivateSection} {index : Nat} {root : Digest}
    (left right : AcceptedV5LeafAtIndex hashing tree index root)
    (hne : left.record ≠ right.record) : HashCollision hashing := by
  let leftLeaf := hashing.privateLeaf (treeTag tree) left.record
  let rightLeaf := hashing.privateLeaf (treeTag tree) right.record
  by_cases hleaf : leftLeaf = rightLeaf
  · refine ⟨.privateLeaf (treeTag tree) left.record,
      .privateLeaf (treeTag tree) right.record, ?_, hleaf⟩
    intro hinput
    injection hinput with _htag hrecord
    exact hne hrecord
  · apply pathRoot_collision_of_leaf_ne hashing (topSideAtIndex tree index)
      left.path right.path hleaf
    rw [left.root_eq, right.root_eq]

theorem acceptedV5LeafAtIndex_value_unique
    (hashing : MerkleHashing Digest) (hfree : CollisionFree hashing)
    {tree : V5PrivateSection} {index : Nat} {root : Digest}
    (left right : AcceptedV5LeafAtIndex hashing tree index root) :
    openedValueAtIndex left = openedValueAtIndex right := by
  unfold openedValueAtIndex
  congr 1
  by_contra hne
  exact hfree
    (acceptedV5LeafAtIndex_collision_of_record_ne hashing left right hne)

/-! ## A query-independent value fixed by one root -/

/-- One fixed value for a root, section, and query index.  The choice is over
all accepted paths for that root and is therefore independent of which query
set the Fiat--Shamir verifier later samples. -/
noncomputable def committedValue
    (hashing : MerkleHashing Digest) (root : Digest)
    (tree : V5PrivateSection) (index : Nat) : List Byte := by
  classical
  exact if h : Nonempty (AcceptedV5LeafAtIndex hashing tree index root)
    then openedValueAtIndex (Classical.choice h)
    else List.replicate (valueWidth tree) 0

theorem committedValue_eq_openedValue
    (hashing : MerkleHashing Digest) (hfree : CollisionFree hashing)
    {root : Digest} {tree : V5PrivateSection} {query : V5Query}
    (leaf : AcceptedV5Leaf hashing tree query root) :
    committedValue hashing root tree (sectionIndex tree query) =
      openedValue leaf := by
  classical
  unfold committedValue
  split
  next h =>
    calc
      openedValueAtIndex (Classical.choice h) =
          openedValueAtIndex (acceptedLeafAtIndex hashing leaf) :=
        acceptedV5LeafAtIndex_value_unique hashing hfree
          (Classical.choice h) (acceptedLeafAtIndex hashing leaf)
      _ = openedValue leaf := openedValueAtIndex_acceptedLeafAtIndex hashing leaf
  next h => exact False.elim (h ⟨acceptedLeafAtIndex hashing leaf⟩)

/-! ## Canonical queries for the four word domains -/

def layer0Index (symbol : Fin 524288) : Nat := symbol.val / 4

def layer0Slot (symbol : Fin 524288) : Fin 4 :=
  ⟨symbol.val % 4, Nat.mod_lt _ (by decide)⟩

def line1Index (symbol : Fin 131072) : Nat := symbol.val / 4

def line1Slot (symbol : Fin 131072) : Fin 4 :=
  ⟨symbol.val % 4, Nat.mod_lt _ (by decide)⟩

def line2Index (symbol : Fin 32768) : Nat := symbol.val / 4

def line2Slot (symbol : Fin 32768) : Fin 4 :=
  ⟨symbol.val % 4, Nat.mod_lt _ (by decide)⟩

def line3Index (symbol : Fin 8192) : Nat := symbol.val / 4

def line3Slot (symbol : Fin 8192) : Fin 4 :=
  ⟨symbol.val % 4, Nat.mod_lt _ (by decide)⟩

/-! ## The transcript fixed by the five roots -/

/-- Complete ideal words selected by the five Merkle roots and the exact
production-shaped byte decoder.  The final polynomial is public proof data,
not part of the private-opening forest, and is therefore supplied separately. -/
noncomputable def committedTranscript
    (decoder : ProductionOpeningDecoder K)
    (hashing : MerkleHashing Digest) (roots : V5PrivateRoots Digest)
    (publishedFinal : Fin 4 -> K) : IdealTranscript K where
  layer0 := fun symbol =>
    decoder.layer0
      (committedValue hashing (roots.get .c1) .c1 (layer0Index symbol))
      (committedValue hashing (roots.get .c2) .c2 (layer0Index symbol))
      (layer0Slot symbol)
  layer1 := fun symbol =>
    decoder.later .line1
      (committedValue hashing (roots.get .line1) .line1 (line1Index symbol))
      (line1Slot symbol)
  layer2 := fun symbol =>
    decoder.later .line2
      (committedValue hashing (roots.get .line2) .line2 (line2Index symbol))
      (line2Slot symbol)
  layer3 := fun symbol =>
    decoder.later .line3
      (committedValue hashing (roots.get .line3) .line3 (line3Index symbol))
      (line3Slot symbol)
  publishedFinal := publishedFinal

/-- The C2 helper word selected by its root. -/
noncomputable def committedC2
    (decoder : ProductionOpeningDecoder K)
    (hashing : MerkleHashing Digest) (roots : V5PrivateRoots Digest) :
    V5Query -> Fin 4 -> K := fun query slot =>
  decoder.c2
    (committedValue hashing (roots.get .c2) .c2 (sectionIndex .c2 query)) slot

/-! ## Causally chosen commitment roots -/

/-- The commitment roots in the order allowed by the released FRI transcript.
C1 and C2 are fixed before the first fold challenge.  Each later root may
depend only on challenges sampled before that root was committed. -/
structure CausalMerkleRoots (K Digest : Type*) where
  c1 : Digest
  c2 : Digest
  line1 : K -> Digest
  line2 : K -> K -> Digest
  line3 : K -> K -> K -> Digest
  final : K -> K -> K -> K -> Fin 4 -> K

def CausalMerkleRoots.at
    (roots : CausalMerkleRoots K Digest) (z0 z1 z2 : K) :
    V5PrivateRoots Digest where
  c1 := roots.c1
  c2 := roots.c2
  line1 := roots.line1 z0
  line2 := roots.line2 z0 z1
  line3 := roots.line3 z0 z1 z2

/-- Root binding itself supplies the causal family of complete words.  This
is the commitment-level adversary object required by the adaptive FRI model;
it is defined before any query set is sampled. -/
noncomputable def committedCausalFamily
    (decoder : ProductionOpeningDecoder K)
    (hashing : MerkleHashing Digest)
    (roots : CausalMerkleRoots K Digest) : CausalTranscriptFamily K where
  layer0 := fun symbol => decoder.layer0
    (committedValue hashing roots.c1 .c1 (layer0Index symbol))
    (committedValue hashing roots.c2 .c2 (layer0Index symbol))
    (layer0Slot symbol)
  layer1 := fun z0 symbol => decoder.later .line1
    (committedValue hashing (roots.line1 z0) .line1 (line1Index symbol))
    (line1Slot symbol)
  layer2 := fun z0 z1 symbol => decoder.later .line2
    (committedValue hashing (roots.line2 z0 z1) .line2 (line2Index symbol))
    (line2Slot symbol)
  layer3 := fun z0 z1 z2 symbol => decoder.later .line3
    (committedValue hashing (roots.line3 z0 z1 z2) .line3 (line3Index symbol))
    (line3Slot symbol)
  final := roots.final

/-- At every challenge tuple, the causal root family gives exactly the full
root-defined transcript for the roots which existed on that execution path. -/
@[simp] theorem fullTranscript_committedCausalFamily
    (decoder : ProductionOpeningDecoder K)
    (hashing : MerkleHashing Digest)
    (roots : CausalMerkleRoots K Digest) (z0 z1 z2 z3 : K) :
    fullTranscript (committedCausalFamily decoder hashing roots) z0 z1 z2 z3 =
      committedTranscript decoder hashing (roots.at z0 z1 z2)
        (roots.final z0 z1 z2 z3) := by
  rfl

/-! ## Exact index identities -/

theorem layer0Index_childIndex (query : V5Query) (slot : Fin 4) :
    layer0Index (childIndex query slot) = sectionIndex .c1 query := by
  simp [layer0Index, childIndex, sectionIndex]
  omega

theorem layer0Slot_childIndex (query : V5Query) (slot : Fin 4) :
    layer0Slot (childIndex query slot) = slot := by
  apply Fin.ext
  simp [layer0Slot, childIndex]

theorem line1Index_childIndex_parent (query : V5Query) (slot : Fin 4) :
    line1Index (childIndex (queryParent1 query) slot) =
      sectionIndex .line1 query := by
  simp [line1Index, childIndex, queryParent1, sectionIndex]
  omega

theorem line1Slot_childIndex_parent (query : V5Query) (slot : Fin 4) :
    line1Slot (childIndex (queryParent1 query) slot) = slot := by
  apply Fin.ext
  simp [line1Slot, childIndex]

theorem line2Index_childIndex_parent (query : V5Query) (slot : Fin 4) :
    line2Index (childIndex (queryParent2 query) slot) =
      sectionIndex .line2 query := by
  simp [line2Index, childIndex, queryParent2, sectionIndex]
  omega

theorem line2Slot_childIndex_parent (query : V5Query) (slot : Fin 4) :
    line2Slot (childIndex (queryParent2 query) slot) = slot := by
  apply Fin.ext
  simp [line2Slot, childIndex]

theorem line3Index_childIndex_parent (query : V5Query) (slot : Fin 4) :
    line3Index (childIndex (queryParent3 query) slot) =
      sectionIndex .line3 query := by
  simp [line3Index, childIndex, queryParent3, sectionIndex]
  omega

theorem line3Slot_childIndex_parent (query : V5Query) (slot : Fin 4) :
    line3Slot (childIndex (queryParent3 query) slot) = slot := by
  apply Fin.ext
  simp [line3Slot, childIndex]

/-! ## Every accepted forest projects to the committed transcript -/

/-- Public name emphasizing the root-constructed specialization of the
maintained `ForestProjectsToTranscript` proposition. -/
abbrev ForestProjectsToCommittedTranscript
    (decoder : ProductionOpeningDecoder K)
    (hashing : MerkleHashing Digest)
    {roots : V5PrivateRoots Digest} {querySet : Finset V5Query}
    (forest : AcceptedV5Forest hashing roots querySet)
    (transcript : IdealTranscript K)
    (expectedC2 : V5Query -> Fin 4 -> K) : Prop :=
  ForestProjectsToTranscript decoder hashing forest transcript expectedC2

/-- Merkle binding constructs the former reference projection outright.  No
reference forest or transcript equality is assumed. -/
theorem forest_projects_to_committedTranscript
    (decoder : ProductionOpeningDecoder K)
    (hashing : MerkleHashing Digest) (hfree : CollisionFree hashing)
    {roots : V5PrivateRoots Digest} {querySet : Finset V5Query}
    (forest : AcceptedV5Forest hashing roots querySet)
    (publishedFinal : Fin 4 -> K) :
    ForestProjectsToCommittedTranscript decoder hashing forest
      (committedTranscript decoder hashing roots publishedFinal)
      (committedC2 decoder hashing roots) := by
  constructor
  · intro query hq slot
    simp only [decodedFibre, committedTranscript]
    rw [layer0Index_childIndex, layer0Slot_childIndex]
    rw [committedValue_eq_openedValue hashing hfree
      (forest.opening .c1 query hq)]
    rw [show sectionIndex .c1 query = sectionIndex .c2 query by rfl]
    rw [committedValue_eq_openedValue hashing hfree
      (forest.opening .c2 query hq)]
  · intro query hq slot
    simp only [decodedFibre, committedC2]
    rw [committedValue_eq_openedValue hashing hfree
      (forest.opening .c2 query hq)]
  · intro query hq slot
    simp only [decodedFibre, committedTranscript]
    rw [line1Index_childIndex_parent, line1Slot_childIndex_parent]
    rw [committedValue_eq_openedValue hashing hfree
      (forest.opening .line1 query hq)]
  · intro query hq slot
    simp only [decodedFibre, committedTranscript]
    rw [line2Index_childIndex_parent, line2Slot_childIndex_parent]
    rw [committedValue_eq_openedValue hashing hfree
      (forest.opening .line2 query hq)]
  · intro query hq slot
    simp only [decodedFibre, committedTranscript]
    rw [line3Index_childIndex_parent, line3Slot_childIndex_parent]
    rw [committedValue_eq_openedValue hashing hfree
      (forest.opening .line3 query hq)]

/-- The same result in the adaptive FRI model: a forest opened under the roots
present at one challenge tuple projects directly to the corresponding member
of the causally constructed transcript family. -/
theorem forest_projects_to_committedCausalFamily
    (decoder : ProductionOpeningDecoder K)
    (hashing : MerkleHashing Digest) (hfree : CollisionFree hashing)
    (roots : CausalMerkleRoots K Digest) (z0 z1 z2 z3 : K)
    {querySet : Finset V5Query}
    (forest : AcceptedV5Forest hashing (roots.at z0 z1 z2) querySet) :
    ForestProjectsToTranscript decoder hashing forest
      (fullTranscript (committedCausalFamily decoder hashing roots)
        z0 z1 z2 z3)
      (committedC2 decoder hashing (roots.at z0 z1 z2)) := by
  simpa only [fullTranscript_committedCausalFamily] using
    forest_projects_to_committedTranscript decoder hashing hfree forest
      (roots.final z0 z1 z2 z3)

/-! ## Join to the exact production observation -/

/-- A successful combined parser/FRI observation supplies an authenticated
forest which projects to the transcript fixed by its five roots.  The old
existential reference-forest premise is not used. -/
theorem exactObservation_projects_to_committedTranscript
    (sha256 : List Byte -> Digest32)
    (rustObservation : V5ProductionCall -> Option OpeningAndFriObservation)
    (hsource : ExactRustV5OpeningAndFriConsumerEquality sha256 rustObservation)
    (call : V5ProductionCall) (observation : OpeningAndFriObservation)
    (hrust : rustObservation call = some observation)
    (decoder : ProductionOpeningDecoder K)
    (publishedFinal : Fin 4 -> K)
    (hfree : CollisionFree (sha256MerkleHashing sha256)) :
    exists run : ExactV5Run sha256 call.roots call.queries,
      run.proofBytes = call.proofBytes /\
      observation = observationOfRun run /\
      ForestProjectsToCommittedTranscript decoder
        (sha256MerkleHashing sha256) run.forest
        (committedTranscript decoder (sha256MerkleHashing sha256)
          call.roots publishedFinal)
        (committedC2 decoder (sha256MerkleHashing sha256) call.roots) := by
  obtain ⟨run, hbytes, hobservation⟩ := hsource call observation hrust
  refine ⟨run, hbytes, hobservation, ?_⟩
  exact forest_projects_to_committedTranscript decoder
    (sha256MerkleHashing sha256) hfree run.forest publishedFinal

/-- Full byte-to-word join for one successful production observation.  It
simultaneously records:

* the exact parser run and all four FRI read lists;
* equality of Rust's M31/QM31 decoders with every maintained byte offset; and
* the root-defined ideal transcript to which the accepted forest projects.

No transcript equality or reference forest is a premise. -/
theorem exactObservation_binds_decoded_bytes_to_committedTranscript
    (sha256 : List Byte -> Digest32)
    (rustObservation : V5ProductionCall -> Option OpeningAndFriObservation)
    (hsource : ExactRustV5OpeningAndFriConsumerEquality sha256 rustObservation)
    (rustM31Decode : (Fin 4 -> Byte) ->
      Option AspisV5ComponentCRejectionSampler.M31Value)
    (rustQM31Decode : (Fin 16 -> Byte) ->
      Option AspisV5ComponentCRejectionSampler.QM31Limbs)
    (hdecode : ExactRustFriByteDecoderEquality rustM31Decode rustQM31Decode)
    (operations : DecodedFibreOperations K)
    (call : V5ProductionCall) (observation : OpeningAndFriObservation)
    (hrust : rustObservation call = some observation)
    (publishedFinal : Fin 4 -> K)
    (hfree : CollisionFree (sha256MerkleHashing sha256)) :
    exists run : ExactV5Run sha256 call.roots call.queries,
      run.proofBytes = call.proofBytes /\
      observation = observationOfRun run /\
      FriReadScheduleDecoderAgreement rustM31Decode rustQM31Decode
        observation.friReads /\
      ForestProjectsToCommittedTranscript
        (exactByteOpeningDecoder operations) (sha256MerkleHashing sha256)
        run.forest
        (committedTranscript (exactByteOpeningDecoder operations)
          (sha256MerkleHashing sha256) call.roots publishedFinal)
        (committedC2 (exactByteOpeningDecoder operations)
          (sha256MerkleHashing sha256) call.roots) := by
  obtain ⟨run, hbytes, hobservation⟩ := hsource call observation hrust
  have hagreement : FriReadScheduleDecoderAgreement rustM31Decode
      rustQM31Decode observation.friReads :=
    exactRustFriByteDecoders_agree_with_schedule rustM31Decode rustQM31Decode
      hdecode observation.friReads
  refine ⟨run, hbytes, hobservation, hagreement, ?_⟩
  exact forest_projects_to_committedTranscript
    (exactByteOpeningDecoder operations) (sha256MerkleHashing sha256)
    hfree run.forest publishedFinal

/-! ## Audit -/

#print axioms acceptedV5LeafAtIndex_value_unique
#print axioms committedValue_eq_openedValue
#print axioms forest_projects_to_committedTranscript
#print axioms forest_projects_to_committedCausalFamily
#print axioms exactObservation_projects_to_committedTranscript
#print axioms exactObservation_binds_decoded_bytes_to_committedTranscript

end AspisV5MerkleTranscriptProjection

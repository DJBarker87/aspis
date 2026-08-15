import Std

/-!
# Universal equivalence of the deployed Merkle loop and its extraction adapter

Charon/Aeneas cannot translate the deployed verifier's nested early returns.
The extraction-only source adapter therefore spells the same scan as three
recursive helpers: four children, all groups in one level, and all levels.

This file models both control-flow spellings independently.  It proves equality
of acceptance, successful buffers and frontier position, and the ordered list
of primitive hash calls.  A rejected run exposes only its hash-call prefix:
the production caller returns immediately and never reads its scratch vectors.

The proof is polymorphic in the digest type and hash function.  It therefore
applies in particular to the released SHA-256 specialization; it assumes no
cryptographic property of SHA-256.
-/

namespace AspisV5MerkleSourceAdapter

inductive HashCallInput (Digest : Type) where
  | radix4Node (children : Fin 4 → Digest)

structure MerkleHashing (Digest : Type) where
  radix4Node : (Fin 4 → Digest) → Digest

abbrev RadixMask := Fin 4 → Bool

structure FillState (Digest : Type) where
  valuePos : Nat
  frontierPos : Nat
  children : List Digest
  deriving Repr

structure LevelScanState (Digest : Type) where
  valuePos : Nat
  frontierPos : Nat
  next : List Digest
  calls : List (HashCallInput Digest)

structure RadixState (Digest : Type) where
  level : List Digest
  next : List Digest
  frontierPos : Nat
  calls : List (HashCallInput Digest)

/-- Observable result of the deployed helper.  Scratch buffers are observable
on success.  On rejection only the ordered calls made before the first error
are observable, because every production caller returns immediately. -/
inductive DeployedLoopResult (Digest : Type) where
  | rejected (calls : List (HashCallInput Digest))
  | accepted (level next : List Digest) (frontierPos : Nat)
      (calls : List (HashCallInput Digest))

abbrev RecursiveHelperResult := DeployedLoopResult

def readRadixChild {Digest : Type}
    (level frontier : List Digest) (present : RadixMask) (slot : Fin 4)
    (state : FillState Digest) : Option (FillState Digest) :=
  if present slot then
    match level[state.valuePos]? with
    | none => none
    | some child => some {
        valuePos := state.valuePos + 1
        frontierPos := state.frontierPos
        children := state.children ++ [child] }
  else
    match frontier[state.frontierPos]? with
    | none => none
    | some child => some {
        valuePos := state.valuePos
        frontierPos := state.frontierPos + 1
        children := state.children ++ [child] }

/-- Mathematical semantics of the deployed fixed four-iteration child loop. -/
def deployedFillChildren {Digest : Type}
    (level frontier : List Digest) (present : RadixMask)
    (state : FillState Digest) : Option (FillState Digest) :=
  match readRadixChild level frontier present 0 state with
  | none => none
  | some first =>
      match readRadixChild level frontier present 1 first with
      | none => none
      | some second =>
          match readRadixChild level frontier present 2 second with
          | none => none
          | some third =>
              readRadixChild level frontier present 3 third

/-- Mathematical semantics of the extraction adapter's `slot + 1` recursion. -/
def recursiveFillChildrenAux {Digest : Type}
    (level frontier : List Digest) (present : RadixMask) :
    (fuel slot : Nat) → FillState Digest → Option (FillState Digest)
  | 0, _, state => some state
  | fuel + 1, slot, state =>
      if hslot : slot < 4 then
        match readRadixChild level frontier present ⟨slot, hslot⟩ state with
        | none => none
        | some next => recursiveFillChildrenAux level frontier present
            fuel (slot + 1) next
      else
        some state

def recursiveFillChildren {Digest : Type}
    (level frontier : List Digest) (present : RadixMask)
    (state : FillState Digest) : Option (FillState Digest) :=
  recursiveFillChildrenAux level frontier present 4 0 state

/-- The recursive child helper consumes exactly the same source in the same
slot order and stops at the same first missing value as the deployed loop. -/
theorem deployedFillChildren_eq_recursiveFillChildren {Digest : Type}
    (level frontier : List Digest) (present : RadixMask)
    (state : FillState Digest) :
    deployedFillChildren level frontier present state =
      recursiveFillChildren level frontier present state := by
  cases hfirst : readRadixChild level frontier present 0 state with
  | none => simp [deployedFillChildren, recursiveFillChildren,
      recursiveFillChildrenAux, hfirst]
  | some first =>
      cases hsecond : readRadixChild level frontier present 1 first with
      | none => simp [deployedFillChildren, recursiveFillChildren,
          recursiveFillChildrenAux, hfirst, hsecond]
      | some second =>
          cases hthird : readRadixChild level frontier present 2 second with
          | none => simp [deployedFillChildren, recursiveFillChildren,
              recursiveFillChildrenAux, hfirst, hsecond, hthird]
          | some third =>
              cases hfourth : readRadixChild level frontier present 3 third <;>
                simp [deployedFillChildren, recursiveFillChildren,
                  recursiveFillChildrenAux, hfirst, hsecond, hthird, hfourth]

def childrenFunction {Digest : Type} [Inhabited Digest]
    (children : List Digest) : Fin 4 → Digest :=
  fun slot => children[slot.val]!

def processRadixGroup {Digest : Type} [Inhabited Digest]
    (hash : (Fin 4 → Digest) → Digest)
    (level frontier : List Digest) (present : RadixMask)
    (state : LevelScanState Digest) :
    Except (List (HashCallInput Digest)) (LevelScanState Digest) :=
  let initial : FillState Digest := {
    valuePos := state.valuePos
    frontierPos := state.frontierPos
    children := [] }
  match deployedFillChildren level frontier present initial with
  | none => .error state.calls
  | some filled =>
      let children := childrenFunction filled.children
      let call := HashCallInput.radix4Node children
      .ok {
        valuePos := filled.valuePos
        frontierPos := filled.frontierPos
        next := state.next ++ [hash children]
        calls := state.calls ++ [call] }

/-- The source `while mask_pos < masks.len()` loop. -/
def deployedHashGroups {Digest : Type} [Inhabited Digest]
    (hash : (Fin 4 → Digest) → Digest)
    (level frontier : List Digest) :
    List RadixMask → LevelScanState Digest →
      Except (List (HashCallInput Digest)) (LevelScanState Digest)
  | [], state => .ok state
  | present :: masks, state =>
      match processRadixGroup hash level frontier present state with
      | .error calls => .error calls
      | .ok next => deployedHashGroups hash level frontier masks next

/-- The extraction adapter's recursive group helper. -/
def recursiveHashGroups {Digest : Type} [Inhabited Digest]
    (hash : (Fin 4 → Digest) → Digest)
    (level frontier : List Digest) :
    List RadixMask → LevelScanState Digest →
      Except (List (HashCallInput Digest)) (LevelScanState Digest)
  | [], state => .ok state
  | present :: masks, state =>
      match processRadixGroup hash level frontier present state with
      | .error calls => .error calls
      | .ok next => recursiveHashGroups hash level frontier masks next

/-- Every group succeeds or fails at the same point, and successful groups
append the same digest and the same exact radix-four hash-call input. -/
theorem deployedHashGroups_eq_recursiveHashGroups {Digest : Type}
    [Inhabited Digest]
    (hash : (Fin 4 → Digest) → Digest)
    (level frontier : List Digest) (masks : List RadixMask)
    (state : LevelScanState Digest) :
    deployedHashGroups hash level frontier masks state =
      recursiveHashGroups hash level frontier masks state := by
  induction masks generalizing state with
  | nil => rfl
  | cons present masks ih =>
      cases hgroup : processRadixGroup hash level frontier present state with
      | error calls => simp [deployedHashGroups, recursiveHashGroups, hgroup]
      | ok next =>
          simp [deployedHashGroups, recursiveHashGroups, hgroup, ih]

def processRadixLevel {Digest : Type} [Inhabited Digest]
    (hash : (Fin 4 → Digest) → Digest) (frontier : List Digest)
    (masks : List RadixMask) (state : RadixState Digest) :
    Except (List (HashCallInput Digest)) (RadixState Digest) :=
  let initial : LevelScanState Digest := {
    valuePos := 0
    frontierPos := state.frontierPos
    next := []
    calls := state.calls }
  match deployedHashGroups hash state.level frontier masks initial with
  | .error calls => .error calls
  | .ok scanned =>
      if scanned.valuePos = state.level.length then
        .ok {
          level := scanned.next
          next := state.level
          frontierPos := scanned.frontierPos
          calls := scanned.calls }
      else
        .error scanned.calls

/-- The source outer level loop. -/
def deployedHashLevels {Digest : Type} [Inhabited Digest]
    (hash : (Fin 4 → Digest) → Digest) (frontier : List Digest)
    : List (List RadixMask) → RadixState Digest →
      Except (List (HashCallInput Digest)) (RadixState Digest)
  | [], state => .ok state
  | masks :: levels, state =>
      match processRadixLevel hash frontier masks state with
      | .error calls => .error calls
      | .ok next => deployedHashLevels hash frontier levels next

/-- The extraction adapter's recursive level helper. -/
def recursiveHashLevels {Digest : Type} [Inhabited Digest]
    (hash : (Fin 4 → Digest) → Digest) (frontier : List Digest) :
    List (List RadixMask) → RadixState Digest →
      Except (List (HashCallInput Digest)) (RadixState Digest)
  | [], state => .ok state
  | masks :: levels, state =>
      match processRadixLevel hash frontier masks state with
      | .error calls => .error calls
      | .ok next => recursiveHashLevels hash frontier levels next

/-- The complete radix-level scan is universally equal.  No sortedness or
18-query hypothesis is needed, so this theorem is stronger than the released
constructor-reachable case. -/
theorem deployedHashLevels_eq_recursiveHashLevels {Digest : Type}
    [Inhabited Digest]
    (hash : (Fin 4 → Digest) → Digest) (frontier : List Digest)
    (levels : List (List RadixMask)) (state : RadixState Digest) :
    deployedHashLevels hash frontier levels state =
      recursiveHashLevels hash frontier levels state := by
  induction levels generalizing state with
  | nil => rfl
  | cons masks levels ih =>
      cases hlevel : processRadixLevel hash frontier masks state with
      | error calls => simp [deployedHashLevels, recursiveHashLevels, hlevel]
      | ok next =>
          simp [deployedHashLevels, recursiveHashLevels, hlevel, ih]

def observeLoopResult {Digest : Type}
    (result : Except (List (HashCallInput Digest)) (RadixState Digest)) :
    DeployedLoopResult Digest :=
  match result with
  | .error calls => .rejected calls
  | .ok state =>
      .accepted state.level state.next state.frontierPos state.calls

def runDeployedLoop {Digest : Type} [Inhabited Digest]
    (hash : (Fin 4 → Digest) → Digest) (frontier : List Digest)
    (levels : List (List RadixMask)) (initialLevel initialNext : List Digest) :
    DeployedLoopResult Digest :=
  observeLoopResult <| deployedHashLevels hash frontier levels {
    level := initialLevel
    next := initialNext
    frontierPos := 0
    calls := [] }

def runRecursiveHelper {Digest : Type} [Inhabited Digest]
    (hash : (Fin 4 → Digest) → Digest) (frontier : List Digest)
    (levels : List (List RadixMask)) (initialLevel initialNext : List Digest) :
    RecursiveHelperResult Digest :=
  observeLoopResult <| recursiveHashLevels hash frontier levels {
    level := initialLevel
    next := initialNext
    frontierPos := 0
    calls := [] }

/-- Universal observable equivalence of the source loop and extraction
adapter.  Equality contains acceptance/rejection, exact first-failure hash
prefix, and on success both buffers, the frontier position, and all calls. -/
theorem deployedLoopResult_eq_recursiveHelperResult {Digest : Type}
    [Inhabited Digest]
    (hash : (Fin 4 → Digest) → Digest) (frontier : List Digest)
    (levels : List (List RadixMask)) (initialLevel initialNext : List Digest) :
    runDeployedLoop hash frontier levels initialLevel initialNext =
      runRecursiveHelper hash frontier levels initialLevel initialNext := by
  unfold runDeployedLoop runRecursiveHelper
  rw [deployedHashLevels_eq_recursiveHashLevels]

/-! ## Explicit source-code boundaries

The theorem above deliberately does not pretend that a handwritten semantics
is source extraction.  The following two propositions name the remaining code
connections.  The first must connect the original deployed loop/LLBC to
`runDeployedLoop`; the second must connect Aeneas's generated recursive helper
definitions to `runRecursiveHelper`.
-/

def OriginalDeployedLoopImplementsDeployedModel {Digest SourceInput : Type}
    [Inhabited Digest]
    (hash : (Fin 4 → Digest) → Digest)
    (sourceRun : SourceInput → DeployedLoopResult Digest)
    (frontierOf : SourceInput → List Digest)
    (levelsOf : SourceInput → List (List RadixMask))
    (initialLevelOf initialNextOf : SourceInput → List Digest) : Prop :=
  ∀ input,
    sourceRun input = runDeployedLoop hash (frontierOf input) (levelsOf input)
      (initialLevelOf input) (initialNextOf input)

def GeneratedRecursiveHelpersImplementRecursiveModel
    {Digest GeneratedInput : Type} [Inhabited Digest]
    (hash : (Fin 4 → Digest) → Digest)
    (generatedRun : GeneratedInput → RecursiveHelperResult Digest)
    (frontierOf : GeneratedInput → List Digest)
    (levelsOf : GeneratedInput → List (List RadixMask))
    (initialLevelOf initialNextOf : GeneratedInput → List Digest) : Prop :=
  ∀ input,
    generatedRun input = runRecursiveHelper hash (frontierOf input)
      (levelsOf input) (initialLevelOf input) (initialNextOf input)

/-- Once the two named source-code bridges are supplied for a common input,
the original deployed loop and generated recursive helper have identical
observable behavior. -/
theorem sourceBridges_imply_exact_observable_equality
    {Digest Input : Type} [Inhabited Digest]
    (hash : (Fin 4 → Digest) → Digest)
    (sourceRun generatedRun : Input → DeployedLoopResult Digest)
    (frontierOf : Input → List Digest)
    (levelsOf : Input → List (List RadixMask))
    (initialLevelOf initialNextOf : Input → List Digest)
    (hsource : OriginalDeployedLoopImplementsDeployedModel hash sourceRun
      frontierOf levelsOf initialLevelOf initialNextOf)
    (hgenerated : GeneratedRecursiveHelpersImplementRecursiveModel hash
      generatedRun frontierOf levelsOf initialLevelOf initialNextOf) :
    ∀ input, sourceRun input = generatedRun input := by
  intro input
  rw [hsource input, hgenerated input]
  exact deployedLoopResult_eq_recursiveHelperResult hash (frontierOf input)
    (levelsOf input) (initialLevelOf input) (initialNextOf input)

/-- Released constructor bounds are not needed for equivalence.  This named
corollary exposes the exact premises available in V5: sorted/deduplicated at
most 18 initial indices and at most eight radix-four levels. -/
theorem releasedConstructorReachable_loop_equivalence {Digest : Type}
    [Inhabited Digest]
    (hash : (Fin 4 → Digest) → Digest) (frontier : List Digest)
    (levels : List (List RadixMask)) (initialLevel initialNext : List Digest)
    (indices : List Nat)
    (_hsorted : indices.Pairwise (· < ·)) (_hnodup : indices.Nodup)
    (_hqueries : indices.length ≤ 18) (_hlevels : levels.length ≤ 8) :
    runDeployedLoop hash frontier levels initialLevel initialNext =
      runRecursiveHelper hash frontier levels initialLevel initialNext :=
  deployedLoopResult_eq_recursiveHelperResult hash frontier levels
    initialLevel initialNext

/-- The theorem is parametric in the hash oracle.  In particular, replacing
the adapter's opaque fixed hash by the released Merkle radix-four function
does not add a mathematical or cryptographic assumption to the control-flow
equivalence. -/
theorem fixedHash_specialization {Digest : Type} [Inhabited Digest]
    (hashing : MerkleHashing Digest) (frontier : List Digest)
    (levels : List (List RadixMask)) (initialLevel initialNext : List Digest) :
    runDeployedLoop hashing.radix4Node frontier levels initialLevel initialNext =
      runRecursiveHelper hashing.radix4Node frontier levels initialLevel
        initialNext :=
  deployedLoopResult_eq_recursiveHelperResult hashing.radix4Node frontier
    levels initialLevel initialNext

#print axioms deployedFillChildren_eq_recursiveFillChildren
#print axioms deployedHashGroups_eq_recursiveHashGroups
#print axioms deployedHashLevels_eq_recursiveHashLevels
#print axioms deployedLoopResult_eq_recursiveHelperResult
#print axioms sourceBridges_imply_exact_observable_equality
#print axioms releasedConstructorReachable_loop_equivalence
#print axioms fixedHash_specialization

end AspisV5MerkleSourceAdapter

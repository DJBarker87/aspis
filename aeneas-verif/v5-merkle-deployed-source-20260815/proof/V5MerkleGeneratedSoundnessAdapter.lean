import V5MerkleGeneratedDriverInversion
import V5MerkleGeneratedRadixBridge
import AspisFormal.V5TopologyConstruction

/-!
# One-way V5 Merkle soundness composition

The theft-resistance argument only needs the direction from successful Rust
acceptance to an `ExactSectionTrace`.  It does not need a proof that every
mathematically valid trace is accepted by Rust.  This file records and proves
that smaller composition target so the remaining source work is not inflated
into an unnecessary equivalence proof.
-/

namespace AspisV5MerkleGeneratedSoundnessAdapter

open AspisV5MerkleAuthenticationBinding
open AspisV5MerkleRustBridge
open AspisV5TopologyConstruction

/-- One-way released helper obligation: a successful Rust helper call with
the released eighteen queries yields the exact parsed and authenticated
section model. -/
def ReleasedHelperSoundness
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32)
    (rustHelperAccepts : StateOnlyTopologyHelperCall → Prop) : Prop :=
  ∀ call, call.queries.card = 18 → rustHelperAccepts call →
    ExactStateOnlyTopologyHelperAcceptance sha256 call

/-- One-way residual obligation for the parser and authentication execution
after the exact released topology has been constructed. -/
def ParserAndAuthenticationSoundness
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32)
    (rustAuthenticates : StateOnlyTopologyHelperCall →
      TopologyObservation → Prop) : Prop :=
  ∀ call, call.queries.card = 18 →
    rustAuthenticates call (exactTopologyObservation call.queries) →
      ExactStateOnlyTopologyHelperAcceptance sha256 call

/-- Exact topology construction plus one-way parser/authentication soundness
is sufficient for one-way helper soundness. -/
theorem constructor_and_authentication_imply_helper_soundness
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32)
    (rustConstructs : Finset V5Query → Option TopologyObservation)
    (rustAuthenticates : StateOnlyTopologyHelperCall →
      TopologyObservation → Prop)
    (hconstructor : Radix4BinaryCapTopologyNewSourceEquality rustConstructs)
    (hauthentication : ParserAndAuthenticationSoundness
      sha256 rustAuthenticates) :
    ReleasedHelperSoundness sha256
      (HelperUsingTopologyConstructor rustConstructs rustAuthenticates) := by
  intro call hcount
  rintro ⟨topology, htopology, haccept⟩
  have hexact := hconstructor call.queries hcount
  have htopologyExact :
      topology = exactTopologyObservation call.queries := by
    rw [htopology] at hexact
    exact Option.some.inj hexact
  subst topology
  exact hauthentication call hcount haccept

/-- One-way driver theorem.  Five sound helper calls, threaded through their
literal returned remainders, construct one exact five-section run. -/
theorem released_helpers_imply_exact_v5_acceptance
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32)
    (rustHelperAccepts : StateOnlyTopologyHelperCall → Prop)
    (hhelper : ReleasedHelperSoundness sha256 rustHelperAccepts)
    (call : V5ProductionCall)
    (hdriver : V5DriverUsingStateOnlyHelper rustHelperAccepts call) :
    ExactV5PrivateOpeningAcceptance sha256 call := by
  rcases hdriver with ⟨hcount, afterC1, afterC2, afterLine1, afterLine2,
    hc1, hc2, hline1, hline2, hline3⟩
  obtain ⟨c1, hc1bytes⟩ := hhelper _ hcount hc1
  obtain ⟨c2, hc2bytes⟩ := hhelper _ hcount hc2
  obtain ⟨line1, hline1bytes⟩ := hhelper _ hcount hline1
  obtain ⟨line2, hline2bytes⟩ := hhelper _ hcount hline2
  obtain ⟨line3, hline3bytes⟩ := hhelper _ hcount hline3
  change call.proofBytes = c1.wire ++ afterC1 at hc1bytes
  change afterC1 = c2.wire ++ afterC2 at hc2bytes
  change afterC2 = line1.wire ++ afterLine1 at hline1bytes
  change afterLine1 = line2.wire ++ afterLine2 at hline2bytes
  change afterLine2 = line3.wire ++ [] at hline3bytes
  let sections : ∀ tree,
      ExactSectionTrace sha256 tree (call.roots.get tree) call.queries :=
    fun tree => match tree with
      | .c1 => c1
      | .c2 => c2
      | .line1 => line1
      | .line2 => line2
      | .line3 => line3
  refine ⟨{
    proofBytes := call.proofBytes
    query_count := hcount
    sections := sections
    proof_eq := ?_ }, rfl⟩
  change call.proofBytes =
    c1.wire ++ c2.wire ++ line1.wire ++ line2.wire ++ line3.wire
  rw [hc1bytes, hc2bytes, hline1bytes, hline2bytes, hline3bytes]
  simp only [List.append_assoc, List.append_nil]

/-- One-way source obligation for the public five-call Rust driver. -/
def DriverSoundness
    (rustAccepts : V5ProductionCall → Prop)
    (rustHelperAccepts : StateOnlyTopologyHelperCall → Prop) : Prop :=
  ∀ call, rustAccepts call →
    V5DriverUsingStateOnlyHelper rustHelperAccepts call

/-- The exact implication needed downstream: deployed acceptance yields the
maintained five-section model.  No reverse/completeness claim is required. -/
theorem helper_and_driver_soundness_imply_exact_acceptance
    (sha256 : List AspisV5MerkleAuthenticationBinding.Byte → Digest32)
    (rustAccepts : V5ProductionCall → Prop)
    (rustHelperAccepts : StateOnlyTopologyHelperCall → Prop)
    (hhelper : ReleasedHelperSoundness sha256 rustHelperAccepts)
    (hdriver : DriverSoundness rustAccepts rustHelperAccepts)
    (call : V5ProductionCall) (haccept : rustAccepts call) :
    ExactV5PrivateOpeningAcceptance sha256 call :=
  released_helpers_imply_exact_v5_acceptance sha256 rustHelperAccepts hhelper
    call (hdriver call haccept)

#print axioms constructor_and_authentication_imply_helper_soundness
#print axioms released_helpers_imply_exact_v5_acceptance
#print axioms helper_and_driver_soundness_imply_exact_acceptance

end AspisV5MerkleGeneratedSoundnessAdapter

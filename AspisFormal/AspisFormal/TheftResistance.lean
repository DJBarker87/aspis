import Mathlib

/-!
# Reduction for an extracted wrong secret

This file proves a reduction.  Fix one note with secret `kν`, randomness
`rin`, and public nullifier `Hnul kν rin`.  Fix an adversary and its random
coins.  If the adversary makes an accepted spend and the extractor returns a
different secret, then at least one of these events happened:

1. the knowledge extractor failed to return a valid witness; or
2. the extracted witness gives a different input with the same nullifier.

The second event is a **target second-preimage event for this adversary**.  It
is not the false statement that a compressing hash is globally injective.  The
main theorem proves inclusion of the wrong-secret event in the union of those
two bad events.  A measure-theoretic corollary gives the corresponding union
bound.

This is not, by itself, a complete theft game.  It does not model how the note
is sampled, which information the adversary receives, or which algorithms are
efficient.  It also does not connect the abstract `Accepts` and `R` below to
the deployed verifier.  A deployed theft-resistance claim needs those links in
addition to this reduction.

What this file does not prove:

* knowledge soundness of the proof system;
* simulation extractability after observing other proofs; or
* target second-preimage resistance of the deployed Poseidon2 nullifier.

Those are cryptographic inputs.  `KnowledgeExtractor` and `SimExtractor`
record their ideal successful branches, while the general reduction keeps an
extractor-failure event explicit.
-/

namespace Aspis.TheftResistance

/-! ## 1. Abstract objects

Protocol-logic typing, not the concrete circuit.  A spend statement `x`, a
witness `w`, an execution record `e`, the spending secret `k` and its
randomness `r`, and the nullifier space.  The execution record may contain the
proof bytes, prover description, random-oracle query transcript, and fixed
extractor coins required by a straight-line extractor; it is not assumed to be
the public proof alone.
Everything downstream is abstract over these. -/

variable {Statement Witness Execution Secret Randomness Nullifier : Type*}

/- `Hnul k r` is the nullifier map `H_nul(k_ν, r_in)` (`eq:nullifier`,
`derive_nullifier` in `spend.rs`). -/
variable (Hnul : Secret → Randomness → Nullifier)

/- `nul x` is the public nullifier `ν` pinned in statement `x`.  The reduction
below fixes this field because it routes a spend to the victim's nullifier
marker.  Other public statement fields may also depend on the witness, and
this fixed-nullifier reduction does not cover opening the same semantic note
under a different nullifier. -/
variable (nul : Statement → Nullifier)

/- `wSecret w` is the spending secret carried by a witness
(`SpendWitness.nullifier_key`). -/
variable (wSecret : Witness → Secret)

/- `wRand w` is the input randomness carried by a witness
(`SpendWitness.input_salt`). -/
variable (wRand : Witness → Randomness)

/- The spend relation `R_spend`.  `R x w` means `w` satisfies the pinned spend
relation for statement `x` (`RProfile(x,w)=1`). -/
variable (R : Statement → Witness → Prop)

/-! ## 2. The BCS knowledge extractor — CITED interface (not proved)

`thm:argument-of-knowledge` / `ass:sr-knowledge` / `lem:generic-extraction`,
i.e. the Fiat–Shamir-of-IOP extractor of Ben-Sasson–Chiesa–Spooner 2016.  We do
**not** re-prove knowledge soundness; it is imported as this structure.  The
field `extract_sound` is exactly the extractor's guarantee, stated in the
idealized success event (see the file header). -/

/-- A straight-line knowledge extractor for accepting predicate `Acc` and
relation `R`: a deterministic map from a statement and complete execution
record to a witness.  The record may include the prover and its random-oracle
query transcript; this is not a claim that public proof bytes reveal the
witness.  This is the CITED interface — named, never proved here. -/
structure KnowledgeExtractor
    {Statement Witness Execution : Type*}
    (Acc : Statement → Execution → Prop)
    (R : Statement → Witness → Prop) where
  /-- The straight-line extractor `E = Φ ∘ Ext₀`. -/
  extract : Statement → Execution → Witness
  /-- BCS knowledge soundness (idealized-success event): every accepting
      execution record extracts to a witness in the relation. -/
  extract_sound : ∀ {x : Statement} {e : Execution}, Acc x e → R x (extract x e)

/-! ## 3. Single-spend reduction -/

/-- A candidate is a target second preimage when it differs from the fixed note
input but produces the same nullifier.  This predicate is about one target and
one candidate.  It makes no global injectivity claim. -/
def TargetSecondPreimageAt
    (kν : Secret) (rin : Randomness) (candidate : Secret × Randomness) : Prop :=
  candidate ≠ (kν, rin) ∧
    Hnul candidate.1 candidate.2 = Hnul kν rin

/-- The event that an adversary's accepted execution record extracts to a
different secret.  `Coins` is the adversary's random tape and `A` produces the
complete record supplied to the extractor. -/
def WrongSecretEvent
    {Coins : Type*}
    (Accepts : Statement → Execution → Prop)
    (extract : Statement → Execution → Witness)
    (x : Statement) (kν : Secret)
    (A : Coins → Execution) (coins : Coins) : Prop :=
  Accepts x (A coins) ∧ wSecret (extract x (A coins)) ≠ kν

/-- The event that the extractor fails on this adversary run. -/
def ExtractionFailureEvent
    {Coins : Type*}
    (Accepts : Statement → Execution → Prop)
    (extract : Statement → Execution → Witness)
    (x : Statement) (A : Coins → Execution) (coins : Coins) : Prop :=
  Accepts x (A coins) ∧ ¬ R x (extract x (A coins))

/-- The target second-preimage event produced from this adversary run. -/
def TargetSecondPreimageEvent
    {Coins : Type*}
    (extract : Statement → Execution → Witness)
    (x : Statement) (kν : Secret) (rin : Randomness)
    (A : Coins → Execution) (coins : Coins) : Prop :=
  TargetSecondPreimageAt Hnul kν rin
    (wSecret (extract x (A coins)), wRand (extract x (A coins)))

/-- A valid extracted witness with a different secret is a target second
preimage.  The relation supplies the nullifier equality; `hnote` identifies the
fixed target. -/
theorem relation_witness_gives_target_second_preimage
    (Rbinds : ∀ x w, R x w → Hnul (wSecret w) (wRand w) = nul x)
    {x : Statement} {kν : Secret} {rin : Randomness}
    (hnote : nul x = Hnul kν rin)
    {w : Witness} (hR : R x w) (hdifferent : wSecret w ≠ kν) :
    TargetSecondPreimageAt Hnul kν rin (wSecret w, wRand w) := by
  constructor
  · intro hp
    exact hdifferent (congrArg Prod.fst hp)
  · exact (Rbinds x w hR).trans hnote

/-- **Wrong-secret reduction.**

For each random tape of a fixed adversary, an accepted execution whose
extracted secret differs from the note secret implies either extractor failure
or a target second preimage.  No hash injectivity assumption is used. -/
theorem wrong_secret_reduction
    {Coins : Type*}
    (Accepts : Statement → Execution → Prop)
    (extract : Statement → Execution → Witness)
    (Rbinds : ∀ x w, R x w → Hnul (wSecret w) (wRand w) = nul x)
    {x : Statement} {kν : Secret} {rin : Randomness}
    (hnote : nul x = Hnul kν rin)
    (A : Coins → Execution) (coins : Coins) :
    WrongSecretEvent wSecret Accepts extract x kν A coins →
      ExtractionFailureEvent R Accepts extract x A coins ∨
      TargetSecondPreimageEvent Hnul wSecret wRand extract x kν rin A coins := by
  rintro ⟨hacc, hdifferent⟩
  by_cases hR : R x (extract x (A coins))
  · right
    exact relation_witness_gives_target_second_preimage
      Hnul nul wSecret wRand R Rbinds hnote hR hdifferent
  · exact Or.inl ⟨hacc, hR⟩

/-- Set form of `wrong_secret_reduction`, suitable for applying a probability
measure to the adversary's random coins. -/
theorem wrong_secret_event_subset_bad_events
    {Coins : Type*}
    (Accepts : Statement → Execution → Prop)
    (extract : Statement → Execution → Witness)
    (Rbinds : ∀ x w, R x w → Hnul (wSecret w) (wRand w) = nul x)
    {x : Statement} {kν : Secret} {rin : Randomness}
    (hnote : nul x = Hnul kν rin)
    (A : Coins → Execution) :
    {coins | WrongSecretEvent wSecret Accepts extract x kν A coins} ⊆
      {coins | ExtractionFailureEvent R Accepts extract x A coins} ∪
      {coins | TargetSecondPreimageEvent Hnul wSecret wRand
        extract x kν rin A coins} := by
  intro coins htheft
  exact wrong_secret_reduction Hnul nul wSecret wRand R Accepts extract Rbinds
    hnote A coins htheft

/-- Measure form of the reduction.  When `μ` is a probability distribution on
the adversary's coins, this says

`Pr[accepted execution extracts a wrong secret]`
`≤ Pr[extractor failure] + Pr[target second preimage]`.

Concrete bounds for the two terms are cryptographic results outside this
file. -/
theorem wrong_secret_measure_le_bad_events
    {Coins : Type*} [MeasurableSpace Coins]
    (μ : MeasureTheory.Measure Coins)
    (Accepts : Statement → Execution → Prop)
    (extract : Statement → Execution → Witness)
    (Rbinds : ∀ x w, R x w → Hnul (wSecret w) (wRand w) = nul x)
    {x : Statement} {kν : Secret} {rin : Randomness}
    (hnote : nul x = Hnul kν rin)
    (A : Coins → Execution) :
    μ {coins | WrongSecretEvent wSecret Accepts extract x kν A coins} ≤
      μ {coins | ExtractionFailureEvent R Accepts extract x A coins} +
      μ {coins | TargetSecondPreimageEvent Hnul wSecret wRand
        extract x kν rin A coins} := by
  calc
    μ {coins | WrongSecretEvent wSecret Accepts extract x kν A coins} ≤
        μ ({coins | ExtractionFailureEvent R Accepts extract x A coins} ∪
          {coins | TargetSecondPreimageEvent Hnul wSecret wRand
            extract x kν rin A coins}) :=
      MeasureTheory.measure_mono (wrong_secret_event_subset_bad_events
        Hnul nul wSecret wRand R Accepts extract Rbinds hnote A)
    _ ≤ μ {coins | ExtractionFailureEvent R Accepts extract x A coins} +
        μ {coins | TargetSecondPreimageEvent Hnul wSecret wRand
          extract x kν rin A coins} := MeasureTheory.measure_union_le _ _

/-- If the cited knowledge extractor is in its successful branch, the first
bad event is absent, so an accepted execution extracting a wrong secret yields
a target second preimage for the same adversary run. -/
theorem wrong_secret_under_successful_extraction
    {Coins : Type*}
    (Accepts : Statement → Execution → Prop)
    (E : KnowledgeExtractor Accepts R)
    (Rbinds : ∀ x w, R x w → Hnul (wSecret w) (wRand w) = nul x)
    {x : Statement} {kν : Secret} {rin : Randomness}
    (hnote : nul x = Hnul kν rin)
    (A : Coins → Execution) (coins : Coins) :
    WrongSecretEvent wSecret Accepts E.extract x kν A coins →
      TargetSecondPreimageEvent Hnul wSecret wRand
        E.extract x kν rin A coins := by
  rintro ⟨hacc, hdifferent⟩
  exact relation_witness_gives_target_second_preimage
    Hnul nul wSecret wRand R Rbinds hnote (E.extract_sound hacc) hdifferent

/-! ## 4. Deployed-pool extension — CITED sim-extractability interface

In the deployed setting the adversary may observe honest spends.  Handling
that setting needs simulation extractability.  We record it as an interface
and prove what follows from it.  We do **not** prove that the deployed protocol
has simulation extractability, nor derive it from weak unique response here. -/

/-- Weak unique response (`lem:quasi-unique-response`), represented only by its
ideal successful branch.  The computational error and the claim that the
deployed transcript has this property are not proved here. -/
structure WeakUniqueResponse
    {Statement Proof : Type*}
    (Accepts : Statement → Proof → Prop)
    (SharesFixedPrefix : Proof → Proof → Prop) where
  /-- Two accepting proofs with the same fixed transcript prefix are equal
      (in the idealized no-second-preimage event). -/
  unique : ∀ {x : Statement} {π π' : Proof},
      Accepts x π → Accepts x π' → SharesFixedPrefix π π' → π = π'

/-- The Fiat–Shamir simulation extractor (`thm:sim-extractability`), as a cited
interface.  `AcceptsSim` must encode the relevant observation game.  The
existence, efficiency, error bound, and deployed applicability of this
extractor are not proved here. -/
structure SimExtractor
    {Statement Witness Execution : Type*}
    (AcceptsSim : Statement → Execution → Prop)
    (R : Statement → Witness → Prop) where
  /-- The straight-line simulation-sound extractor. -/
  extract : Statement → Execution → Witness
  /-- Simulation-extractability (idealized-success event): a fresh accepting
      execution, even in the presence of simulated proofs, extracts to a
      witness in the relation. -/
  extract_sound : ∀ {x : Statement} {e : Execution},
    AcceptsSim x e → R x (extract x e)

/-- **Deployed-pool reduction.**

On the successful branch of the cited simulation extractor, an accepted spend
whose extracted secret differs from the note secret produces a target second
preimage.  The theorem does not claim that such a second preimage is
impossible; a computational Poseidon2 assumption must bound this exact event. -/
theorem deployed_wrong_secret_reduction
    {Coins : Type*}
    (AcceptsSim : Statement → Execution → Prop)
    (S : SimExtractor AcceptsSim R)
    (Rbinds : ∀ x w, R x w → Hnul (wSecret w) (wRand w) = nul x)
    {x : Statement} {kν : Secret} {rin : Randomness}
    (hnote : nul x = Hnul kν rin)
    (A : Coins → Execution) (coins : Coins) :
    WrongSecretEvent wSecret AcceptsSim S.extract x kν A coins →
      TargetSecondPreimageEvent Hnul wSecret wRand
        S.extract x kν rin A coins := by
  rintro ⟨hacc, hdifferent⟩
  exact relation_witness_gives_target_second_preimage
    Hnul nul wSecret wRand R Rbinds hnote (S.extract_sound hacc) hdifferent

end Aspis.TheftResistance

-- Kernel axiom audit: mathlib's standard set only (propext, Classical.choice,
-- Quot.sound), sorry-free.
#print axioms Aspis.TheftResistance.relation_witness_gives_target_second_preimage
#print axioms Aspis.TheftResistance.wrong_secret_reduction
#print axioms Aspis.TheftResistance.wrong_secret_event_subset_bad_events
#print axioms Aspis.TheftResistance.wrong_secret_measure_le_bad_events
#print axioms Aspis.TheftResistance.wrong_secret_under_successful_extraction
#print axioms Aspis.TheftResistance.deployed_wrong_secret_reduction

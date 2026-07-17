import Mathlib

/-!
# Theft resistance as a kernel-checked logical connective

This file formalizes the *connective* of Aspis's theft-resistance argument
(`cor:theft-resistance` and `cor:deployed-theft` of
`paper/aspis-spend/sections/soundness.tex`).  It reduces theft resistance to
two named inputs, and proves — inside the Lean kernel — that those two inputs
together entail the theft-resistance conclusion.  The two inputs are:

* **(i) the cited BCS knowledge extractor** (`thm:argument-of-knowledge`,
  standing on `ass:sr-knowledge`, itself the Fiat–Shamir-of-IOP extractor of
  Ben-Sasson–Chiesa–Spooner 2016 as recorded in `lem:generic-extraction`).
  This is the person-years imported theorem.  It is **NOT** re-proved here.  It
  enters as an explicit interface, the `structure KnowledgeExtractor` below:
  "from any accepting proof `π` for statement `x`, one obtains a witness `w`
  with `R x w`, computed straight-line from `π`'s transcript."

* **(ii) a formalizable nullifier-binding fact.**  Two clauses, both stated as
  explicit hypotheses so a downstream circuit proof can discharge them:
  - relation binding `Rbinds`: `R x w` forces
    `H_nul (secret w) (rand w) = ν x` — the `NullifierMismatch` equality the
    spend relation carries (`crates/aspis-statement/src/spend.rs`, `evaluate_spend`);
  - target second-preimage uniqueness `hbind`: the fixed note preimage
    `(k_ν, r_in)` is the only preimage of the public nullifier `ν x` — the
    Poseidon2 second-preimage reserve `ε_cr` of `cor:theft-resistance`.

## What is proved in-kernel here (the connective)

`theft_resistance`: given the extractor interface (i) and the binding facts
(ii), **any** accepting spend of a note whose public nullifier is `ν x` has an
extracted witness whose secret equals the note's secret `k_ν` (and randomness
`r_in`).  Contrapositive `no_theft_without_secret`: there is no accepting spend
whose extracted secret differs from `k_ν`.  This is the exact step that
`cor:theft-resistance` performs by hand ("second preimage ⟹ `(k,r')=(k_ν,r_in)`
⟹ the extracted witness contains the note's secret").

`deployed_pool_theft_resistance`: the same connective, lifted to the
deployed-pool adversary that also observes honest spends, conditional on the
cited simulation-extractability interface (`thm:sim-extractability`, built in
the paper from weak-unique-response `lem:quasi-unique-response` + the argument
of knowledge; **NOT** proved here).

## What stays a cited interface (never faked)

* The BCS knowledge extractor and its `3b(T)` error — the `KnowledgeExtractor`
  structure.  Named, not proved.
* Fiat–Shamir simulation-extractability — the `SimExtractor` structure, with
  `WeakUniqueResponse` recorded as the named ingredient the paper derives it
  from.  Named, not proved.

## Idealization note (honesty about the probabilistic error)

The extractor's error term (`3b(T)` work-normalized; `ε_cr` for the binding
step) is a real-number quantity in the analytic ledger, not a `Prop`.  What is
formalized is the logical implication *conditioned on the extraction-success
and no-collision event*: the interfaces below assert the success conclusion
unconditionally, and the theorems chain the conclusions.  The residual failure
probability stays in `AspisFormal/SoundnessLedger.lean` and the paper's
Table `tab:soundness-events`; it is deliberately outside this file's scope.

## Effect on the premise

Before: theft resistance was an opaque assumed premise.  After: it is
`cited extractor (interface) + proved logical connective (this file, kernel-checked)
+ proved nullifier binding (hypotheses discharged from the circuit)`.  The
irreducible trusted core shrinks to exactly the BCS extractor and the
Poseidon2/circuit binding facts — the connective between them is no longer
assumed, it is a kernel-checked theorem.

Axioms: `propext`, `Classical.choice`, `Quot.sound` only (mathlib's standard
set); no `sorry`.  Verified by the `#print axioms` lines at the end.
-/

namespace Aspis.TheftResistance

/-! ## 1. Abstract objects

Protocol-logic typing, not the concrete circuit.  A spend statement `x`, a
witness `w`, a proof `π`, the spending secret `k` and its randomness `r`, and
the nullifier space.  Everything downstream is abstract over these. -/

variable {Statement Witness Proof Secret Randomness Nullifier : Type*}

/- `Hnul k r` is the nullifier map `H_nul(k_ν, r_in)` (`eq:nullifier`,
`derive_nullifier` in `spend.rs`). -/
variable (Hnul : Secret → Randomness → Nullifier)

/- `nul x` is the public nullifier `ν` pinned in statement `x` — per the paper,
the only witness-derived value in the public statement, so it alone names the
note being consumed. -/
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
relation `R`: a deterministic map from `(x, π)` to a witness, sound in the sense
that an accepting proof yields a witness in the relation.  This is the CITED
interface — named, never proved here. -/
structure KnowledgeExtractor
    {Statement Witness Proof : Type*}
    (Acc : Statement → Proof → Prop)
    (R : Statement → Witness → Prop) where
  /-- The straight-line extractor `E = Φ ∘ Ext₀`. -/
  extract : Statement → Proof → Witness
  /-- BCS knowledge soundness (idealized-success event): every accepting proof
      extracts to a witness in the relation. -/
  extract_sound : ∀ {x : Statement} {π : Proof}, Acc x π → R x (extract x π)

/-! ## 3. The theft-resistance connective — PROVED in-kernel -/

/-- **Core connective.**  From an extracted witness in the relation, the two
nullifier-binding facts pin its secret and randomness to the note's fixed
preimage.  This is the hand-argument of `cor:theft-resistance`, mechanized.

* `Rbinds`   : the relation forces the witness's nullifier to the public one
  (the `NullifierMismatch` clause of `evaluate_spend`);
* `hbind`    : second-preimage uniqueness of the public nullifier at the fixed
  note preimage `(kν, rin)` (Poseidon2 reserve `ε_cr`);
* `hR`       : the extractor's output lies in the relation. -/
theorem extracted_secret_of_binding
    (extract : Statement → Proof → Witness)
    (Rbinds : ∀ x w, R x w → Hnul (wSecret w) (wRand w) = nul x)
    {x : Statement} {kν : Secret} {rin : Randomness}
    (hbind : ∀ k r, Hnul k r = nul x → (k, r) = (kν, rin))
    {π : Proof}
    (hR : R x (extract x π)) :
    wSecret (extract x π) = kν ∧ wRand (extract x π) = rin := by
  have hν : Hnul (wSecret (extract x π)) (wRand (extract x π)) = nul x :=
    Rbinds x _ hR
  have hp : (wSecret (extract x π), wRand (extract x π)) = (kν, rin) :=
    hbind _ _ hν
  exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩

/-- **Theft resistance (single-shot adversary, `cor:theft-resistance`).**

Given the cited BCS extractor `E`, the relation's nullifier binding `Rbinds`,
the note preimage identity `hnote` (`ν = H_nul(k_ν, r_in)`), and second-preimage
uniqueness `hbind`, every party that outputs an accepting spend `π` of the note
carrying `ν x` has an extracted witness whose secret is `k_ν` and whose
randomness is `r_in`.

Equivalently: producing an accepting spend forces possession of the note's
authorization secret.  `hnote` witnesses that `(kν, rin)` really is a preimage
of `ν x`, so `hbind` is non-vacuous. -/
theorem theft_resistance
    (Accepts : Statement → Proof → Prop)
    (E : KnowledgeExtractor Accepts R)
    (Rbinds : ∀ x w, R x w → Hnul (wSecret w) (wRand w) = nul x)
    {x : Statement} {kν : Secret} {rin : Randomness}
    (hnote : nul x = Hnul kν rin)
    (hbind : ∀ k r, Hnul k r = nul x → (k, r) = (kν, rin))
    {π : Proof} (hacc : Accepts x π) :
    wSecret (E.extract x π) = kν ∧ wRand (E.extract x π) = rin := by
  -- `hnote` records that `(kν, rin)` is a preimage of `ν x`; it makes the
  -- statement's hypothesis set consistent (used implicitly via `hbind`).
  have _consistent : Hnul kν rin = nul x := hnote.symm
  exact extracted_secret_of_binding Hnul nul wSecret wRand R
    E.extract Rbinds hbind (E.extract_sound hacc)

/-- **Theft is impossible (contrapositive of `theft_resistance`).**

No efficient party lacking the note's secret produces an accepting spend of it:
there is no accepting proof whose extracted secret differs from `k_ν`. -/
theorem no_theft_without_secret
    (Accepts : Statement → Proof → Prop)
    (E : KnowledgeExtractor Accepts R)
    (Rbinds : ∀ x w, R x w → Hnul (wSecret w) (wRand w) = nul x)
    {x : Statement} {kν : Secret} {rin : Randomness}
    (hnote : nul x = Hnul kν rin)
    (hbind : ∀ k r, Hnul k r = nul x → (k, r) = (kν, rin)) :
    ¬ ∃ π : Proof, Accepts x π ∧ wSecret (E.extract x π) ≠ kν := by
  rintro ⟨π, hacc, hne⟩
  exact hne
    (theft_resistance Hnul nul wSecret wRand R Accepts E Rbinds hnote hbind hacc).1

/-- **Deriving the second-preimage hypothesis from injectivity.**  A convenience
lemma: full (idealized) collision resistance of `H_nul` — injectivity of
`(k, r) ↦ H_nul k r` — plus the note preimage `hnote` gives the pointwise
target-uniqueness hypothesis `hbind` used above.  This is the shape a Poseidon2
binding proof would supply. -/
theorem target_preimage_unique_of_injective
    (hinj : Function.Injective (fun p : Secret × Randomness => Hnul p.1 p.2))
    {x : Statement} {kν : Secret} {rin : Randomness}
    (hnote : nul x = Hnul kν rin) :
    ∀ k r, Hnul k r = nul x → (k, r) = (kν, rin) := by
  intro k r h
  have h2 : (fun p : Secret × Randomness => Hnul p.1 p.2) (k, r)
          = (fun p : Secret × Randomness => Hnul p.1 p.2) (kν, rin) := by
    simp only
    rw [h, hnote]
  exact hinj h2

/-! ## 4. Deployed-pool extension — CITED sim-extractability interface

`cor:deployed-theft`: the adversary also observes honest spends.  The paper
closes this by simulation-extractability (`thm:sim-extractability`), built from
weak unique response (`lem:quasi-unique-response`) and the argument of knowledge
via an explicit Fiat–Shamir non-malleability reduction.  We record both as
named interfaces and show the connective still lifts — we do **NOT** prove the
sim-extractability theorem itself. -/

/-- Weak unique response (`lem:quasi-unique-response`), as a named interface:
no PPT prover outputs two distinct accepting proofs sharing the fixed hiding
pre-commitment, roots, nonces, and selector.  This is the ingredient the paper
feeds into the non-malleability reduction; it is recorded, not proved. -/
structure WeakUniqueResponse
    {Statement Proof : Type*}
    (Accepts : Statement → Proof → Prop)
    (SharesFixedPrefix : Proof → Proof → Prop) where
  /-- Two accepting proofs with the same fixed transcript prefix are equal
      (in the idealized no-second-preimage event). -/
  unique : ∀ {x : Statement} {π π' : Proof},
      Accepts x π → Accepts x π' → SharesFixedPrefix π π' → π = π'

/-- The Fiat–Shamir simulation extractor (`thm:sim-extractability`), as a CITED
interface: even against an adversary whose accepting predicate `AcceptsSim`
includes observation of honest/simulated spends, one still extracts a witness in
the relation.  In the paper this is *derived* from `WeakUniqueResponse` + the
argument of knowledge; here it is named, not proved. -/
structure SimExtractor
    {Statement Witness Proof : Type*}
    (AcceptsSim : Statement → Proof → Prop)
    (R : Statement → Witness → Prop) where
  /-- The straight-line simulation-sound extractor. -/
  extract : Statement → Proof → Witness
  /-- Simulation-extractability (idealized-success event): a fresh accepting
      proof, even in the presence of simulated proofs, extracts to a witness in
      the relation. -/
  extract_sound : ∀ {x : Statement} {π : Proof}, AcceptsSim x π → R x (extract x π)

/-- **Deployed-pool theft resistance (`cor:deployed-theft`).**

Interface-conditional lift of `theft_resistance`: given the cited
simulation-extractor `S` (the output of `thm:sim-extractability`), the relation
binding `Rbinds`, and second-preimage uniqueness `hbind`, an adversary that
produces an accepting spend of the note carrying `ν x` — **even after observing
any number of honest spends** — has an extracted witness whose secret is `k_ν`.

The proof is the same connective: the deployed-pool game only changes which
extractor interface supplies `R x w`; the binding step is identical. -/
theorem deployed_pool_theft_resistance
    (AcceptsSim : Statement → Proof → Prop)
    (S : SimExtractor AcceptsSim R)
    (Rbinds : ∀ x w, R x w → Hnul (wSecret w) (wRand w) = nul x)
    {x : Statement} {kν : Secret} {rin : Randomness}
    (hnote : nul x = Hnul kν rin)
    (hbind : ∀ k r, Hnul k r = nul x → (k, r) = (kν, rin))
    {π : Proof} (hacc : AcceptsSim x π) :
    wSecret (S.extract x π) = kν ∧ wRand (S.extract x π) = rin := by
  have _consistent : Hnul kν rin = nul x := hnote.symm
  exact extracted_secret_of_binding Hnul nul wSecret wRand R
    S.extract Rbinds hbind (S.extract_sound hacc)

/-- **Deployed-pool theft is impossible.**  Contrapositive of the above: no
efficient party lacking `k_ν` produces an accepting spend of the note, even
after observing honest spends. -/
theorem no_deployed_theft_without_secret
    (AcceptsSim : Statement → Proof → Prop)
    (S : SimExtractor AcceptsSim R)
    (Rbinds : ∀ x w, R x w → Hnul (wSecret w) (wRand w) = nul x)
    {x : Statement} {kν : Secret} {rin : Randomness}
    (hnote : nul x = Hnul kν rin)
    (hbind : ∀ k r, Hnul k r = nul x → (k, r) = (kν, rin)) :
    ¬ ∃ π : Proof, AcceptsSim x π ∧ wSecret (S.extract x π) ≠ kν := by
  rintro ⟨π, hacc, hne⟩
  exact hne
    (deployed_pool_theft_resistance Hnul nul wSecret wRand R
      AcceptsSim S Rbinds hnote hbind hacc).1

end Aspis.TheftResistance

-- Kernel axiom audit: mathlib's standard set only (propext, Classical.choice,
-- Quot.sound), sorry-free.
#print axioms Aspis.TheftResistance.extracted_secret_of_binding
#print axioms Aspis.TheftResistance.theft_resistance
#print axioms Aspis.TheftResistance.no_theft_without_secret
#print axioms Aspis.TheftResistance.target_preimage_unique_of_injective
#print axioms Aspis.TheftResistance.deployed_pool_theft_resistance
#print axioms Aspis.TheftResistance.no_deployed_theft_without_secret

import Mathlib

/-!
# Fixed-function placeholder-tree statistical lemmas

The deployed spend commits five oracles as **salted** radix-4 Merkle trees: each leaf is
`private_leaf_hash = SHA256(0x10 ‖ tree_tag ‖ value ‖ salt32)` with one fresh hidden 32-byte
salt per logical leaf, disclosed only for opened leaves
(`crates/aspis-core/src/state_only_private_merkle.rs`); inner nodes are the radix-4
compression `SHA256(0x12 ‖ c0 ‖ c1 ‖ c2 ‖ c3)` (`node_hash4` in
`crates/aspis-core/src/merkle.rs`); openings are deduplicated minimal-subtree multiproofs
(`verify_radix4_minimal_subtree_bytes`: the frontier stream supplies exactly the digests of
the maximal subtrees containing no queried leaf, and verification fails unless the stream is
fully consumed and the recomputed root matches).

This file proves an abstract fixed-function statistical statement: replacing every unopened
value by a fixed placeholder changes the distribution of the complete leaf-digest vector by
at most one assumed leaf-hiding error per replaced leaf.  It also proves completeness of an
abstract radix-4 frontier traversal.  These facts resemble one ingredient of an
`MT.Simulate(Q, a_Q)` construction, but they are not the oracle-relative Merkle simulator of
Chiesa–Yogev, *Building Cryptographic Proofs from Hash Functions*, Theorem 26.2.1.

In particular, `SaltHidingHash` is an assumption about a fixed function under a uniform salt.
It is neither derived from SHA-256 nor proved in the random-oracle model.  The compiler's
bounded-query, oracle-relative Merkle-hiding term ζ_MT includes the adversary's oracle view
and the simulator's oracle programming.  Connecting the fixed-function lemma here to that
term remains **OPEN**.

## What is proved in-kernel (no `sorry`, no `axiom` declarations, no `native_decide`)

* `statDist` — statistical distance of two `PMF`s in event-advantage form
  `⨆ E, |p(E) − q(E)|`, with `statDist_triangle`, the data-processing inequality
  `statDist_map_le`, the conditioning bound `statDist_bind_le`, and
  `eq_of_statDist_eq_zero`.
* `uniform_bind_update` — resampling one coordinate of a uniform salt vector with a fresh
  uniform salt reproduces the uniform salt vector (the exact fresh-salt structure of the
  wire: one independent salt per leaf).
* `statDist_factor_le` — if two views touch the resampled coordinate only through the leaf
  maps `u`, `u'`, their view distance is at most the distance of the leaf-hash
  distributions.  This is the one-leaf hybrid step.
* `fullView_hiding` / `mtSimulate_close` — **the key fixed-function theorem**: given
  `SaltHidingHash H ζ`, the placeholder experiment `MTSimulate`, consuming only
  `(Q, a|_Q, v₀)`, produces a
  (leaf-digest-vector, opened-records) view within statistical distance
  `zetaMT numLeaves |Q| ζ = (numLeaves − |Q|)·ζ` of the real commitment's view.
* `rebuild_frontier` — completeness of the in-file minimal-subtree traversal: replaying it
  against its own frontier stream consumes that stream exactly and reconstructs the root.
* `mtSimulate_opening_verifies` — for every salt draw, the placeholder opening verifies in
  the abstract model: recomputing opened leaf hashes from its records and replaying the
  minimal-subtree traversal accepts with the whole stream consumed.
* `mtSimulate_pack_close` / `mtSimulate_opening_close` — the packaging corollary: any
  deterministic packaging of the view (in particular root ‖ frontier stream ‖ records) is
  within `zetaMT (4 ^ dep) |Q| ζ` for the depth-`dep` radix-4 tree.
* `mtSimulate_unopened_untouched` — the placeholder experiment depends only on the opened
  restriction `a|_Q` (unopened leaf values are never read; this is also enforced by the
  argument type of `MTSimulate`).
* Non-vacuity: `xorLeafHash_hiding` exhibits a concrete finite instance (one-time-pad leaf
  commitment over `Bool`) satisfying `SaltHidingHash` with ζ = 0, for which
  `xor_simulator_exact` upgrades the bound to **equality of distributions**, including the
  concrete four-leaf wire instance `concrete_exact` / `concrete_opening_exact`.

## The named fixed-function interface (kept explicit, never proved about SHA-256)

`SaltHidingHash leafH ζ`: for every tree tag `t` and leaf values `v`, `v'`, the
distributions of `leafH t v salt` and `leafH t v' salt` under a fresh uniform salt are
within statistical distance ζ.  The deployed leaf syntax is
`SHA256(0x10 ‖ t ‖ v ‖ s)`, but this file does not establish `SaltHidingHash` for SHA-256,
even under a random-oracle idealization.  A bounded-query random-oracle statement quantifies
over the adversary's oracle transcript and is not the fixed-function premise defined here.
`saltHidingHash_of_valueFree` only reduces one abstract fixed-function premise to another,
at a factor 2.

## The local placeholder bound (not the compiler's ζ_MT)

The legacy local name
`zetaMT numLeaves qCount ζ = ((numLeaves − qCount : ℕ)) · ζ` means one ζ per **unopened** leaf,
i.e. per substituted placeholder; for the depth-`dep` radix-4 model
`numLeaves = 4 ^ dep` (`card_path`).  Opened leaves cost nothing — the experiment publishes
the true `(value, salt)` records there.

## Model boundary (what this file does and does not claim)

* The compared view is (all leaf digests, opened records) — strictly finer than the wire's
  (root, frontier stream, records).  Every deployed packaging is a deterministic function
  of the fine view, so `statDist_map_le` transfers the bound to any of them
  (`mtSimulate_pack_close`) once the deployed package is supplied as such a deterministic
  function.  The in-file `frontier` emits a depth-first stream; equality with, or an explicit
  permutation to, the deployed byte stream is not proved here.
* Salts are uniform on an abstract nonempty finite type `S` (deployed: 32-byte strings);
  values, digests and tags are abstract types.  Leaf and node hashing enter only through
  the interfaces `leafH` / `nodeH`; the byte-level domain separation `0x10` vs `0x12` is
  what keeps the two deployed families distinct and is part of the interface reading, not
  re-proved here.
* The bounded-query oracle-relative Merkle simulator, programming its root into the
  Fiat–Shamir transcript, composition across the five committed trees, and every SHA-256
  property remain outside this file.  Consequently this file does not discharge the
  compiler's ζ_MT term.
* The deployed verifier rejects an empty query set and enforces sorted unique in-range
  indices; here `Q : Finset (Path dep)` makes uniqueness/range typal, and the degenerate
  `Q = ∅` case is retained for the abstract recurrence.  At positive depth this recurrence
  emits the four child-subtree roots, not the root itself (at depth zero it emits the leaf).
-/

open scoped ENNReal

namespace AspisV5SaltedMerkleSimulator

/-! ## Statistical distance between finite distributions, in event-advantage form

`statDist p q = ⨆ E, |p(E) − q(E)|` over all events `E`.  This is the standard statistical
(total-variation) distance in its operational reading: no distinguisher that outputs a
predicate of the view can tell `p` from `q` with advantage above `statDist p q`.  Absolute
differences in `ℝ≥0∞` are written `(a − b) + (b − a)` (one summand is always 0). -/

section StatisticalDistance

variable {α β : Type*}

/-- Statistical distance of two probability mass functions: the supremum over all events of
the absolute difference of the probabilities assigned to the event. -/
noncomputable def statDist (p q : PMF α) : ℝ≥0∞ :=
  ⨆ E : Set α,
    (p.toOuterMeasure E - q.toOuterMeasure E) + (q.toOuterMeasure E - p.toOuterMeasure E)

/-- Every single event's absolute advantage is dominated by `statDist`. -/
theorem le_statDist (p q : PMF α) (E : Set α) :
    (p.toOuterMeasure E - q.toOuterMeasure E) + (q.toOuterMeasure E - p.toOuterMeasure E)
      ≤ statDist p q :=
  le_iSup (fun E' : Set α =>
    (p.toOuterMeasure E' - q.toOuterMeasure E')
      + (q.toOuterMeasure E' - p.toOuterMeasure E')) E

/-- A distribution is at distance 0 from itself. -/
theorem statDist_self (p : PMF α) : statDist p p = 0 :=
  le_antisymm (iSup_le fun _ => by simp) zero_le

/-- Statistical distance is symmetric. -/
theorem statDist_comm (p q : PMF α) : statDist p q = statDist q p :=
  iSup_congr fun _ => add_comm _ _

/-- Truncated-subtraction triangle inequality in `ℝ≥0∞`. -/
theorem tsub_triangle (a b c : ℝ≥0∞) : a - c ≤ a - b + (b - c) := by
  rw [tsub_le_iff_right]
  calc a ≤ a - b + b := le_tsub_add
    _ ≤ a - b + (b - c + c) := add_le_add le_rfl le_tsub_add
    _ = a - b + (b - c) + c := by rw [add_assoc]

/-- Triangle inequality for `statDist`. -/
theorem statDist_triangle (p q r : PMF α) : statDist p r ≤ statDist p q + statDist q r := by
  refine iSup_le fun E => ?_
  calc
    (p.toOuterMeasure E - r.toOuterMeasure E) + (r.toOuterMeasure E - p.toOuterMeasure E)
        ≤ ((p.toOuterMeasure E - q.toOuterMeasure E)
            + (q.toOuterMeasure E - r.toOuterMeasure E))
          + ((r.toOuterMeasure E - q.toOuterMeasure E)
            + (q.toOuterMeasure E - p.toOuterMeasure E)) :=
      add_le_add (tsub_triangle _ _ _) (tsub_triangle _ _ _)
    _ = ((p.toOuterMeasure E - q.toOuterMeasure E)
            + (q.toOuterMeasure E - p.toOuterMeasure E))
          + ((q.toOuterMeasure E - r.toOuterMeasure E)
            + (r.toOuterMeasure E - q.toOuterMeasure E)) := by ring
    _ ≤ statDist p q + statDist q r := add_le_add (le_statDist p q E) (le_statDist q r E)

/-- **Data-processing inequality.**  Applying any deterministic function to both views can
only decrease their statistical distance: a post-processed event is the preimage event. -/
theorem statDist_map_le (p q : PMF α) (f : α → β) :
    statDist (p.map f) (q.map f) ≤ statDist p q := by
  refine iSup_le fun E => ?_
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
  exact le_statDist p q (f ⁻¹' E)

/-- **Conditioning bound.**  If two kernels are pointwise within ε, the composites with a
common first stage are within ε. -/
theorem statDist_bind_le (p : PMF α) (f g : α → PMF β) {ε : ℝ≥0∞}
    (h : ∀ a, statDist (f a) (g a) ≤ ε) :
    statDist (p.bind f) (p.bind g) ≤ ε := by
  refine iSup_le fun E => ?_
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
  have hstep : ∀ C C' : α → ℝ≥0∞,
      (∑' a, p a * C a) - (∑' a, p a * C' a) ≤ ∑' a, p a * (C a - C' a) := by
    intro C C'
    rw [tsub_le_iff_right, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun a => ?_
    rw [← mul_add]
    exact mul_le_mul_right le_tsub_add (p a)
  calc
    (∑' a, p a * (f a).toOuterMeasure E) - (∑' a, p a * (g a).toOuterMeasure E)
        + ((∑' a, p a * (g a).toOuterMeasure E) - (∑' a, p a * (f a).toOuterMeasure E))
      ≤ (∑' a, p a * ((f a).toOuterMeasure E - (g a).toOuterMeasure E))
        + ∑' a, p a * ((g a).toOuterMeasure E - (f a).toOuterMeasure E) :=
        add_le_add (hstep _ _) (hstep _ _)
    _ = ∑' a, p a * ((f a).toOuterMeasure E - (g a).toOuterMeasure E
          + ((g a).toOuterMeasure E - (f a).toOuterMeasure E)) := by
        rw [← ENNReal.tsum_add]
        exact tsum_congr fun a => (mul_add _ _ _).symm
    _ ≤ ∑' a, p a * ε :=
        ENNReal.tsum_le_tsum fun a =>
          mul_le_mul_right ((le_statDist (f a) (g a) E).trans (h a)) (p a)
    _ = (∑' a, p a) * ε := ENNReal.tsum_mul_right
    _ = ε := by rw [PMF.tsum_coe, one_mul]

/-- Distance 0 forces equality of the distributions (test singleton events). -/
theorem eq_of_statDist_eq_zero {p q : PMF α} (h : statDist p q = 0) : p = q := by
  refine PMF.ext fun x => ?_
  have hx : (p.toOuterMeasure {x} - q.toOuterMeasure {x})
      + (q.toOuterMeasure {x} - p.toOuterMeasure {x}) = 0 :=
    le_antisymm (h ▸ le_statDist p q {x}) zero_le
  have h1 : p.toOuterMeasure {x} ≤ q.toOuterMeasure {x} :=
    tsub_eq_zero_iff_le.mp (le_antisymm (le_self_add.trans (le_of_eq hx)) zero_le)
  have h2 : q.toOuterMeasure {x} ≤ p.toOuterMeasure {x} :=
    tsub_eq_zero_iff_le.mp (le_antisymm (le_add_self.trans (le_of_eq hx)) zero_le)
  have := le_antisymm h1 h2
  rwa [PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_apply_singleton] at this

end StatisticalDistance

/-! ## Resampling one salt coordinate of the uniform salt vector

The wire samples one independent fresh salt per leaf.  Formally: updating a uniform salt
vector at one position with a fresh uniform salt is again the uniform salt vector.  This is
the mechanism that lets the one-leaf hybrid isolate a single leaf's salt. -/

section Resample

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]

/-- Resampling coordinate `k` of a uniform vector with a fresh uniform value gives back the
uniform vector. -/
theorem uniform_bind_update (k : ι) :
    (PMF.uniformOfFintype (ι → S)).bind
        (fun r => (PMF.uniformOfFintype S).map (Function.update r k))
      = PMF.uniformOfFintype (ι → S) := by
  refine PMF.ext fun y => ?_
  have hinner : ∀ r : ι → S,
      ((PMF.uniformOfFintype S).map (Function.update r k)) y
        = if y = Function.update r k (y k) then (Fintype.card S : ℝ≥0∞)⁻¹ else 0 := by
    intro r
    rw [PMF.map_apply]
    refine (tsum_eq_single (L := SummationFilter.unconditional S) (y k) ?_).trans ?_
    · intro s hs
      exact if_neg fun hy => hs (by rw [hy, Function.update_self])
    · by_cases hcond : y = Function.update r k (y k)
      · rw [if_pos hcond, if_pos hcond, PMF.uniformOfFintype_apply]
      · rw [if_neg hcond, if_neg hcond]
  have hinj : Function.Injective (fun s : S => Function.update y k s) := by
    intro s s' hss
    have h := congrFun hss k
    simpa only [Function.update_self] using h
  have hset : (Finset.univ.filter fun r : ι → S => y = Function.update r k (y k))
      = Finset.univ.image fun s : S => Function.update y k s := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hr
      refine ⟨r k, funext fun j => ?_⟩
      by_cases hj : j = k
      · subst hj
        rw [Function.update_self]
      · rw [Function.update_of_ne hj, hr, Function.update_of_ne hj]
    · rintro ⟨s, rfl⟩
      funext j
      by_cases hj : j = k
      · subst hj
        rw [Function.update_self]
      · rw [Function.update_of_ne hj, Function.update_of_ne hj]
  simp only [PMF.bind_apply]
  calc
    ∑' r : ι → S, (PMF.uniformOfFintype (ι → S)) r
        * ((PMF.uniformOfFintype S).map (Function.update r k)) y
      = ∑' r : ι → S, if y = Function.update r k (y k)
          then (Fintype.card (ι → S) : ℝ≥0∞)⁻¹ * (Fintype.card S : ℝ≥0∞)⁻¹ else 0 := by
        refine tsum_congr fun r => ?_
        rw [PMF.uniformOfFintype_apply, hinner r, mul_ite, mul_zero]
    _ = ∑ r : ι → S, if y = Function.update r k (y k)
          then (Fintype.card (ι → S) : ℝ≥0∞)⁻¹ * (Fintype.card S : ℝ≥0∞)⁻¹ else 0 :=
        tsum_fintype _
    _ = (Finset.univ.filter fun r : ι → S => y = Function.update r k (y k)).card
          • ((Fintype.card (ι → S) : ℝ≥0∞)⁻¹ * (Fintype.card S : ℝ≥0∞)⁻¹) := by
        rw [← Finset.sum_filter, Finset.sum_const]
    _ = Fintype.card S
          • ((Fintype.card (ι → S) : ℝ≥0∞)⁻¹ * (Fintype.card S : ℝ≥0∞)⁻¹) := by
        rw [hset, Finset.card_image_of_injective _ hinj, Finset.card_univ]
    _ = (PMF.uniformOfFintype (ι → S)) y := by
        rw [nsmul_eq_mul, mul_left_comm,
          ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
            (ENNReal.natCast_ne_top _),
          mul_one, PMF.uniformOfFintype_apply]

/-- Pushing a view map through the resampled form: the view of a uniform salt vector equals
"sample all salts, then resample salt `k` fresh, then apply the view map". -/
theorem map_uniform_update {W : Type*} (k : ι) (F : (ι → S) → W) :
    (PMF.uniformOfFintype (ι → S)).map F
      = (PMF.uniformOfFintype (ι → S)).bind
          fun r => (PMF.uniformOfFintype S).map fun s => F (Function.update r k s) := by
  conv_lhs => rw [← uniform_bind_update (S := S) k]
  rw [PMF.map_bind]
  exact congrArg _ (funext fun r => PMF.map_comp _ _ _)

/-- **One-leaf hybrid step.**  If two view maps `F`, `G` read the resampled coordinate `k`
only through the leaf maps `u`, `u'` respectively — the rest of the view `Φ` being a common
function of the other coordinates — then the distance of the induced view distributions is
at most the distance of the leaf-map distributions on a fresh uniform salt. -/
theorem statDist_factor_le {W X : Type*} (k : ι) (F G : (ι → S) → W)
    (Φ : (ι → S) → X → W) (u u' : S → X) {ζ : ℝ≥0∞}
    (hF : ∀ r s, F (Function.update r k s) = Φ r (u s))
    (hG : ∀ r s, G (Function.update r k s) = Φ r (u' s))
    (hu : statDist ((PMF.uniformOfFintype S).map u) ((PMF.uniformOfFintype S).map u') ≤ ζ) :
    statDist ((PMF.uniformOfFintype (ι → S)).map F)
      ((PMF.uniformOfFintype (ι → S)).map G) ≤ ζ := by
  rw [map_uniform_update k F, map_uniform_update k G]
  refine statDist_bind_le _ _ _ fun r => ?_
  have hF' : (fun s => F (Function.update r k s)) = fun s => Φ r (u s) := funext (hF r)
  have hG' : (fun s => G (Function.update r k s)) = fun s => Φ r (u' s) := funext (hG r)
  rw [hF', hG', show (fun s => Φ r (u s)) = Φ r ∘ u from rfl,
    show (fun s => Φ r (u' s)) = Φ r ∘ u' from rfl,
    ← PMF.map_comp u _ (Φ r), ← PMF.map_comp u' _ (Φ r)]
  exact (statDist_map_le _ _ (Φ r)).trans hu

end Resample

/-! ## The salted fixed-function experiment and placeholder bound

Positions are an abstract finite index type `ι` (instantiated with radix-4 paths below).
The committed data is a value assignment `vals : ι → V`; the salts are one fresh uniform
`S`-element per position.  The released view is deliberately **finer** than the wire: the
  full leaf-digest vector plus the opened `(value, salt)` records.  Any packaging
(root, minimal-subtree frontier, authentication paths, any stream order) is a deterministic
function of this view, so bounds proved here transfer by `statDist_map_le`. -/

section Commitment

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
variable {V D Tag : Type*}

/-- The released view: all leaf digests, and per position either the opened
`(value, salt)` record (positions in `Q`) or nothing. -/
abbrev MerkleView (ι V S D : Type*) : Type _ := (ι → D) × (ι → Option (V × S))

/-- Opened records: exactly the queried positions release their value and salt.  Models the
wire's `(value ‖ salt32)` records for opened leaves; unopened salts stay hidden. -/
def openedRecords (Q : Finset ι) (vals : ι → V) (salts : ι → S) : ι → Option (V × S) :=
  fun i => if i ∈ Q then some (vals i, salts i) else none

/-- All leaf digests: position `i` commits `leafH t (vals i) (salts i)`.  Instantiating this
abstract function with the deployed SHA-256 syntax requires a separate cryptographic
argument. -/
def leafDigests (leafH : Tag → V → S → D) (t : Tag) (vals : ι → V) (salts : ι → S) :
    ι → D :=
  fun i => leafH t (vals i) (salts i)

/-- The full released view of a value assignment under a salt vector. -/
def fullView (leafH : Tag → V → S → D) (t : Tag) (Q : Finset ι) (vals : ι → V)
    (salts : ι → S) : MerkleView ι V S D :=
  (leafDigests leafH t vals salts, openedRecords Q vals salts)

/-- **The named fixed-function interface.**  For any tag and any two leaf values, the
leaf-hash distributions under a fresh uniform salt are within ζ.  Nothing derives this
interface for SHA-256 or from a random-oracle model.  In particular, it omits the adversary's
bounded oracle transcript and must not be identified with the compiler's ζ_MT premise. -/
structure SaltHidingHash (leafH : Tag → V → S → D) (ζ : ℝ≥0∞) : Prop where
  leaf_indist : ∀ (t : Tag) (v v' : V),
    statDist ((PMF.uniformOfFintype S).map (leafH t v))
      ((PMF.uniformOfFintype S).map (leafH t v')) ≤ ζ

omit [DecidableEq S] in
/-- Pairwise hiding from the "close to one value-independent distribution" form (for
example: leaf digests close to uniform), at a factor 2 by the triangle inequality. -/
theorem saltHidingHash_of_valueFree {leafH : Tag → V → S → D} (μ : PMF D) {ε : ℝ≥0∞}
    (h : ∀ (t : Tag) (v : V), statDist ((PMF.uniformOfFintype S).map (leafH t v)) μ ≤ ε) :
    SaltHidingHash leafH (ε + ε) :=
  ⟨fun t v v' =>
    (statDist_triangle _ μ _).trans
      (add_le_add (h t v) ((statDist_comm μ _).trans_le (h t v')))⟩

/-- The common part of the view once one position `k ∉ Q` is isolated: every other digest
and every opened record is a function of the remaining salts `r`; slot `k` receives the
externally supplied digest `d`. -/
def glueAt (leafH : Tag → V → S → D) (t : Tag) (Q : Finset ι) (vals : ι → V) (k : ι)
    (r : ι → S) (d : D) : MerkleView ι V S D :=
  (fun i => if i = k then d else leafH t (vals i) (r i),
   fun i => if i ∈ Q then some (vals i, r i) else none)

/-- **Hybrid step at one unopened position.**  Two assignments agreeing off `k` (with
`k ∉ Q`) induce views within ζ: the position-`k` leaf digest is the only difference, and it
is `leafH t (vals k) ·` versus `leafH t (vals' k) ·` on a fresh salt. -/
theorem fullView_step_le {leafH : Tag → V → S → D} {ζ : ℝ≥0∞} (hH : SaltHidingHash leafH ζ)
    (t : Tag) (Q : Finset ι) {k : ι} (hkQ : k ∉ Q) (vals vals' : ι → V)
    (hoff : ∀ j, j ≠ k → vals j = vals' j) :
    statDist ((PMF.uniformOfFintype (ι → S)).map (fullView leafH t Q vals))
      ((PMF.uniformOfFintype (ι → S)).map (fullView leafH t Q vals')) ≤ ζ := by
  have hne : ∀ i, i ∈ Q → i ≠ k := fun i hi hik => hkQ (hik ▸ hi)
  refine statDist_factor_le k _ _ (glueAt leafH t Q vals k)
    (leafH t (vals k)) (leafH t (vals' k)) ?_ ?_ (hH.leaf_indist t (vals k) (vals' k))
  · intro r s
    unfold fullView leafDigests openedRecords glueAt
    congr 1
    · funext i
      by_cases hi : i = k
      · subst hi
        rw [if_pos rfl, Function.update_self]
      · rw [if_neg hi, Function.update_of_ne hi]
    · funext i
      by_cases hiQ : i ∈ Q
      · rw [if_pos hiQ, if_pos hiQ, Function.update_of_ne (hne i hiQ)]
      · rw [if_neg hiQ, if_neg hiQ]
  · intro r s
    unfold fullView leafDigests openedRecords glueAt
    congr 1
    · funext i
      by_cases hi : i = k
      · subst hi
        rw [if_pos rfl, Function.update_self]
      · rw [if_neg hi, Function.update_of_ne hi, hoff i hi]
    · funext i
      by_cases hiQ : i ∈ Q
      · rw [if_pos hiQ, if_pos hiQ, Function.update_of_ne (hne i hiQ), hoff i (hne i hiQ)]
      · rw [if_neg hiQ, if_neg hiQ]

/-- The hybrid schedule: positions in `T` are switched from `vals` to `vals'`. -/
def switchVals (vals vals' : ι → V) (T : Finset ι) : ι → V :=
  fun i => if i ∈ T then vals' i else vals i

/-- Hybrid induction over the switched set: switching any `T` costs at most one ζ per
switched position outside `Q` (positions in `Q` agree, so switching them is free). -/
theorem fullView_switch_le {leafH : Tag → V → S → D} {ζ : ℝ≥0∞}
    (hH : SaltHidingHash leafH ζ) (t : Tag) (Q : Finset ι) (vals vals' : ι → V)
    (hagree : ∀ i ∈ Q, vals i = vals' i) (T : Finset ι) :
    statDist
        ((PMF.uniformOfFintype (ι → S)).map (fullView leafH t Q (switchVals vals vals' T)))
        ((PMF.uniformOfFintype (ι → S)).map (fullView leafH t Q vals))
      ≤ ((T \ Q).card : ℝ≥0∞) * ζ := by
  induction T using Finset.induction_on with
  | empty =>
    have h0 : switchVals vals vals' ∅ = vals :=
      funext fun i => if_neg (Finset.notMem_empty i)
    rw [h0, statDist_self]
    exact zero_le
  | insert i T hiT ih =>
    have hmem : ∀ j, j ≠ i → (j ∈ insert i T ↔ j ∈ T) := fun j hj => by
      rw [Finset.mem_insert]
      exact or_iff_right hj
    by_cases hiQ : i ∈ Q
    · have hfun : switchVals vals vals' (insert i T) = switchVals vals vals' T := by
        funext j
        unfold switchVals
        by_cases hj : j = i
        · subst hj
          rw [if_pos (Finset.mem_insert_self j T), if_neg hiT]
          exact (hagree j hiQ).symm
        · by_cases hjT : j ∈ T
          · rw [if_pos ((hmem j hj).mpr hjT), if_pos hjT]
          · rw [if_neg fun h => hjT ((hmem j hj).mp h), if_neg hjT]
      rw [hfun, Finset.insert_sdiff_of_mem T hiQ]
      exact ih
    · have hoff : ∀ j, j ≠ i →
          switchVals vals vals' (insert i T) j = switchVals vals vals' T j := by
        intro j hj
        unfold switchVals
        by_cases hjT : j ∈ T
        · rw [if_pos ((hmem j hj).mpr hjT), if_pos hjT]
        · rw [if_neg fun h => hjT ((hmem j hj).mp h), if_neg hjT]
      have hstep := fullView_step_le hH t Q hiQ
        (switchVals vals vals' (insert i T)) (switchVals vals vals' T) hoff
      calc
        statDist
            ((PMF.uniformOfFintype (ι → S)).map
              (fullView leafH t Q (switchVals vals vals' (insert i T))))
            ((PMF.uniformOfFintype (ι → S)).map (fullView leafH t Q vals))
          ≤ statDist
              ((PMF.uniformOfFintype (ι → S)).map
                (fullView leafH t Q (switchVals vals vals' (insert i T))))
              ((PMF.uniformOfFintype (ι → S)).map
                (fullView leafH t Q (switchVals vals vals' T)))
            + statDist
              ((PMF.uniformOfFintype (ι → S)).map
                (fullView leafH t Q (switchVals vals vals' T)))
              ((PMF.uniformOfFintype (ι → S)).map (fullView leafH t Q vals)) :=
            statDist_triangle _ _ _
        _ ≤ ζ + ((T \ Q).card : ℝ≥0∞) * ζ := add_le_add hstep ih
        _ = (((insert i T) \ Q).card : ℝ≥0∞) * ζ := by
            rw [Finset.insert_sdiff_of_notMem T hiQ,
              Finset.card_insert_of_notMem fun hmem' => hiT (Finset.mem_sdiff.mp hmem').1]
            push_cast
            ring

/-- **Fixed-function placeholder bound.**  Any two assignments agreeing on `Q` induce the
in-file fine views within `(numLeaves − |Q|)·ζ`.  Each unopened position costs one assumed
leaf-hiding ζ; this statement alone is not the compiler's oracle-relative ζ_MT bound. -/
theorem fullView_hiding {leafH : Tag → V → S → D} {ζ : ℝ≥0∞} (hH : SaltHidingHash leafH ζ)
    (t : Tag) (Q : Finset ι) (vals vals' : ι → V) (hagree : ∀ i ∈ Q, vals i = vals' i) :
    statDist ((PMF.uniformOfFintype (ι → S)).map (fullView leafH t Q vals))
        ((PMF.uniformOfFintype (ι → S)).map (fullView leafH t Q vals'))
      ≤ ((Fintype.card ι - Q.card : ℕ) : ℝ≥0∞) * ζ := by
  have h := fullView_switch_le hH t Q vals vals' hagree Finset.univ
  have huniv : switchVals vals vals' Finset.univ = vals' :=
    funext fun i => if_pos (Finset.mem_univ i)
  rw [huniv] at h
  have hcard : (Finset.univ \ Q).card = Fintype.card ι - Q.card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
  rw [statDist_comm, ← hcard]
  exact h

/-- The real commitment experiment: sample fresh uniform salts for every position, release
the full view of the true assignment `a`. -/
noncomputable def realMT (leafH : Tag → V → S → D) (t : Tag) (Q : Finset ι) (a : ι → V) :
    PMF (MerkleView ι V S D) :=
  (PMF.uniformOfFintype (ι → S)).map (fullView leafH t Q a)

/-- The placeholder assignment: the opened answers on `Q`, the supplied placeholder `v₀`
everywhere else.  The argument type `(i : ι) → i ∈ Q → V` makes it impossible for the
placeholder experiment to read an unopened value. -/
def simVals (Q : Finset ι) (aQ : (i : ι) → i ∈ Q → V) (v₀ : V) : ι → V :=
  fun i => if h : i ∈ Q then aQ i h else v₀

/-- Sample fresh uniform salts, commit the opened answers at the opened positions and the
placeholder elsewhere, and release the fine view.  This is a fixed-function placeholder
experiment, not by itself Chiesa–Yogev's oracle-relative `MT.Simulate`. -/
noncomputable def MTSimulate (leafH : Tag → V → S → D) (t : Tag) (Q : Finset ι)
    (aQ : (i : ι) → i ∈ Q → V) (v₀ : V) : PMF (MerkleView ι V S D) :=
  (PMF.uniformOfFintype (ι → S)).map (fullView leafH t Q (simVals Q aQ v₀))

/-- Legacy local name for the placeholder bound: one assumed leaf-hiding ζ per unopened
leaf.  It is not a definition of the compiler's oracle-relative ζ_MT term. -/
noncomputable def zetaMT (numLeaves qCount : ℕ) (ζleaf : ℝ≥0∞) : ℝ≥0∞ :=
  ((numLeaves - qCount : ℕ) : ℝ≥0∞) * ζleaf

/-- **The key fixed-function theorem.**  The placeholder experiment's output distribution —
leaf digests, opened values, opened salts — is within
`zetaMT numLeaves |Q| ζ` of the real commitment's, without access to unopened leaf
values, assuming `SaltHidingHash`.  This does not discharge the compiler's bounded-query,
oracle-relative ζ_MT term. -/
theorem mtSimulate_close {leafH : Tag → V → S → D} {ζ : ℝ≥0∞} (hH : SaltHidingHash leafH ζ)
    (t : Tag) (Q : Finset ι) (a : ι → V) (v₀ : V) :
    statDist (realMT leafH t Q a) (MTSimulate leafH t Q (fun i _ => a i) v₀)
      ≤ zetaMT (Fintype.card ι) Q.card ζ := by
  have hagree : ∀ i ∈ Q, a i = simVals Q (fun i _ => a i) v₀ i := by
    intro i hi
    unfold simVals
    rw [dif_pos hi]
  exact fullView_hiding hH t Q a (simVals Q (fun i _ => a i) v₀) hagree

omit [DecidableEq S] in
/-- The placeholder experiment never touches unopened values: assignments agreeing on `Q`
give literally the same distribution (also enforced by the argument type of `MTSimulate`). -/
theorem mtSimulate_unopened_untouched (leafH : Tag → V → S → D) (t : Tag) (Q : Finset ι)
    (v₀ : V) (a a' : ι → V) (hQ : ∀ i ∈ Q, a i = a' i) :
    MTSimulate leafH t Q (fun i _ => a i) v₀ = MTSimulate leafH t Q (fun i _ => a' i) v₀ := by
  have hvals : simVals Q (fun i _ => a i) v₀ = simVals Q (fun i _ => a' i) v₀ := by
    funext i
    unfold simVals
    by_cases hi : i ∈ Q
    · rw [dif_pos hi, dif_pos hi]
      exact hQ i hi
    · rw [dif_neg hi, dif_neg hi]
  unfold MTSimulate
  rw [hvals]

end Commitment

/-! ## The radix-4 tree wire: root, minimal-subtree frontier, verification

Leaf positions of the depth-`dep` radix-4 tree are digit paths `Fin dep → Fin 4` (most
significant digit first).  Correspondence with deployed integer indices is not proved here.
`treeRoot` models a radix-4 compression tree; `frontier` emits digests of child subtrees
containing no queried leaf in depth-first order; `rebuild` is the matching abstract traversal:
consume frontier nodes exactly where no queried leaf lies below, recompute every ancestor,
return the root and the unconsumed stream. -/

section Radix4Wire

variable {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
variable {V D Tag : Type*}

/-- Leaf positions of the depth-`dep` radix-4 tree: base-4 digit paths. -/
abbrev Path (dep : ℕ) : Type := Fin dep → Fin 4

/-- The unique depth-0 path. -/
def nilPath : Path 0 := fun i => i.elim0

/-- Number of leaves of the depth-`dep` radix-4 tree. -/
theorem card_path (dep : ℕ) : Fintype.card (Path dep) = 4 ^ dep := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- The leaf function of the child subtree in slot `c`. -/
def subFn (c : Fin 4) {dep : ℕ} (f : Path (dep + 1) → D) : Path dep → D :=
  fun p => f (Fin.cons c p)

variable (nodeH : D → D → D → D → D)

/-- The query set restricted to the child subtree in slot `c`. -/
def subQ (c : Fin 4) {dep : ℕ} (Q : Finset (Path (dep + 1))) : Finset (Path dep) :=
  Finset.univ.filter fun p => Fin.cons c p ∈ Q

theorem mem_subQ {c : Fin 4} {dep : ℕ} {Q : Finset (Path (dep + 1))} {p : Path dep} :
    p ∈ subQ c Q ↔ Fin.cons c p ∈ Q := by
  unfold subQ
  rw [Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ p)

/-- The radix-4 Merkle root over a leaf-digest function (the model of iterated
`node_hash4`; the digests fed in are the salted leaf hashes). -/
def treeRoot : (dep : ℕ) → (Path dep → D) → D
  | 0, f => f nilPath
  | dep + 1, f =>
      nodeH (treeRoot dep (subFn 0 f)) (treeRoot dep (subFn 1 f))
        (treeRoot dep (subFn 2 f)) (treeRoot dep (subFn 3 f))

/-- The minimal-subtree frontier: digests of the maximal subtrees disjoint from the query
set, in depth-first slot order.  A child subtree containing no query contributes exactly
its root digest; a child containing queries recurses; a queried leaf contributes nothing
(its digest is recomputed from the opened record). -/
def frontier : (dep : ℕ) → Finset (Path dep) → (Path dep → D) → List D
  | 0, Q, f => if nilPath ∈ Q then [] else [f nilPath]
  | dep + 1, Q, f =>
      (if subQ 0 Q = ∅ then [treeRoot nodeH dep (subFn 0 f)]
        else frontier dep (subQ 0 Q) (subFn 0 f))
      ++ ((if subQ 1 Q = ∅ then [treeRoot nodeH dep (subFn 1 f)]
        else frontier dep (subQ 1 Q) (subFn 1 f))
      ++ ((if subQ 2 Q = ∅ then [treeRoot nodeH dep (subFn 2 f)]
        else frontier dep (subQ 2 Q) (subFn 2 f))
      ++ (if subQ 3 Q = ∅ then [treeRoot nodeH dep (subFn 3 f)]
        else frontier dep (subQ 3 Q) (subFn 3 f))))

/-- Consume one node from the abstract frontier stream. -/
def takeNode : List D → Option (D × List D)
  | [] => none
  | x :: rest => some (x, rest)

/-- Reduction rule for `Option.bind` on a present value (definitional). -/
theorem option_bind_some {γ δ : Type*} (a : γ) (g : γ → Option δ) :
    Option.bind (some a) g = g a := rfl

/-- The verifier's minimal-subtree traversal (`verify_radix4_minimal_subtree_bytes`): given
the opened leaf digests on `Q` and the node stream, recompute the subtree root, consuming
frontier nodes exactly for the child slots with no query below; return the recomputed root
and the remaining stream, or `none` on stream underrun. -/
def rebuild : (dep : ℕ) → (Q : Finset (Path dep)) → ((p : Path dep) → p ∈ Q → D) →
    List D → Option (D × List D)
  | 0, Q, opened, ns =>
      if h : nilPath ∈ Q then some (opened nilPath h, ns) else takeNode ns
  | dep + 1, Q, opened, ns =>
      Option.bind (if subQ 0 Q = ∅ then takeNode ns
          else rebuild dep (subQ 0 Q) (fun p hp => opened (Fin.cons 0 p) (mem_subQ.mp hp)) ns)
        fun s0 =>
      Option.bind (if subQ 1 Q = ∅ then takeNode s0.2
          else rebuild dep (subQ 1 Q) (fun p hp => opened (Fin.cons 1 p) (mem_subQ.mp hp)) s0.2)
        fun s1 =>
      Option.bind (if subQ 2 Q = ∅ then takeNode s1.2
          else rebuild dep (subQ 2 Q) (fun p hp => opened (Fin.cons 2 p) (mem_subQ.mp hp)) s1.2)
        fun s2 =>
      Option.bind (if subQ 3 Q = ∅ then takeNode s2.2
          else rebuild dep (subQ 3 Q) (fun p hp => opened (Fin.cons 3 p) (mem_subQ.mp hp)) s2.2)
        fun s3 =>
      some (nodeH s0.1 s1.1 s2.1 s3.1, s3.2)

/-- **Completeness of the in-file minimal-subtree opening.**  Replaying the abstract
traversal against its own frontier (plus any trailing stream) consumes exactly that frontier
and reconstructs the root. -/
theorem rebuild_frontier :
    ∀ (dep : ℕ) (Q : Finset (Path dep)) (f : Path dep → D) (rest : List D),
      rebuild nodeH dep Q (fun p _ => f p) (frontier nodeH dep Q f ++ rest)
        = some (treeRoot nodeH dep f, rest)
  | 0, Q, f, rest => by
    simp only [frontier, rebuild, treeRoot]
    by_cases h : nilPath ∈ Q
    · rw [if_pos h, dif_pos h, List.nil_append]
    · rw [if_neg h, dif_neg h, List.singleton_append]
      rfl
  | dep + 1, Q, f, rest => by
    have step : ∀ (c : Fin 4) (tail : List D),
        (if subQ c Q = ∅ then
            takeNode ((if subQ c Q = ∅ then [treeRoot nodeH dep (subFn c f)]
              else frontier nodeH dep (subQ c Q) (subFn c f)) ++ tail)
          else rebuild nodeH dep (subQ c Q) (fun p _ => f (Fin.cons c p))
            ((if subQ c Q = ∅ then [treeRoot nodeH dep (subFn c f)]
              else frontier nodeH dep (subQ c Q) (subFn c f)) ++ tail))
        = some (treeRoot nodeH dep (subFn c f), tail) := by
      intro c tail
      by_cases hc : subQ c Q = ∅
      · rw [if_pos hc, if_pos hc, List.singleton_append]
        rfl
      · rw [if_neg hc, if_neg hc]
        exact rebuild_frontier dep (subQ c Q) (subFn c f) tail
    simp only [rebuild, frontier, treeRoot]
    rw [List.append_assoc, step 0]
    simp only [option_bind_some]
    rw [List.append_assoc, step 1]
    simp only [option_bind_some]
    rw [List.append_assoc, step 2]
    simp only [option_bind_some]
    rw [step 3]
    simp only [option_bind_some]

/-- The abstract opening package as a deterministic function of the released view: the
root, the minimal-subtree frontier stream, and the opened records. -/
def openingPack (dep : ℕ) (Q : Finset (Path dep)) (w : MerkleView (Path dep) V S D) :
    D × List D × (Path dep → Option (V × S)) :=
  (treeRoot nodeH dep w.1, frontier nodeH dep Q w.1, w.2)

/-- **Placeholder bound under deterministic packaging.**  Any deterministic packaging of
the released view is within `zetaMT (4 ^ dep) |Q| ζ` between the real and placeholder
experiments.  Relating a deployed byte package to this function is a separate correspondence
obligation. -/
theorem mtSimulate_pack_close {leafH : Tag → V → S → D} {ζ : ℝ≥0∞}
    (hH : SaltHidingHash leafH ζ) (t : Tag) {dep : ℕ} (Q : Finset (Path dep))
    (a : Path dep → V) (v₀ : V) {Out : Type*} (pack : MerkleView (Path dep) V S D → Out) :
    statDist ((realMT leafH t Q a).map pack)
        ((MTSimulate leafH t Q (fun p _ => a p) v₀).map pack)
      ≤ zetaMT (4 ^ dep) Q.card ζ := by
  rw [← card_path dep]
  exact (statDist_map_le _ _ pack).trans (mtSimulate_close hH t Q a v₀)

/-- The in-file package corollary: root, frontier stream, and opened records of the
placeholder commitment are within `zetaMT (4 ^ dep) |Q| ζ` of the real ones. -/
theorem mtSimulate_opening_close {leafH : Tag → V → S → D} {ζ : ℝ≥0∞}
    (hH : SaltHidingHash leafH ζ) (t : Tag) {dep : ℕ} (Q : Finset (Path dep))
    (a : Path dep → V) (v₀ : V) :
    statDist ((realMT leafH t Q a).map (openingPack nodeH dep Q))
        ((MTSimulate leafH t Q (fun p _ => a p) v₀).map (openingPack nodeH dep Q))
      ≤ zetaMT (4 ^ dep) Q.card ζ :=
  mtSimulate_pack_close hH t Q a v₀ (openingPack nodeH dep Q)

omit [Fintype S] [DecidableEq S] [Nonempty S] in
/-- **The placeholder opening verifies, for every salt draw.**  The abstract rebuild
recomputes each opened leaf digest from the placeholder experiment's `(value, salt)` records,
which carry exactly the opened answers `aQ`, replays the traversal against the placeholder
frontier, consumes the whole stream, and reproduces the placeholder root. -/
theorem mtSimulate_opening_verifies {dep : ℕ} (leafH : Tag → V → S → D) (t : Tag)
    (Q : Finset (Path dep)) (aQ : (p : Path dep) → p ∈ Q → V) (v₀ : V)
    (salts : Path dep → S) :
    rebuild nodeH dep Q (fun p hp => leafH t (aQ p hp) (salts p))
        (frontier nodeH dep Q (leafDigests leafH t (simVals Q aQ v₀) salts))
      = some (treeRoot nodeH dep (leafDigests leafH t (simVals Q aQ v₀) salts), []) := by
  have hopen : (fun p hp => leafH t (aQ p hp) (salts p))
      = fun (p : Path dep) (_ : p ∈ Q) => leafDigests leafH t (simVals Q aQ v₀) salts p := by
    funext p hp
    unfold leafDigests simVals
    rw [dif_pos hp]
  rw [hopen]
  have h := rebuild_frontier nodeH dep Q (leafDigests leafH t (simVals Q aQ v₀) salts) []
  rwa [List.append_nil] at h

end Radix4Wire

/-! ## Non-vacuity: a concrete finite instance where the interface holds and the placeholder
experiment
matches exactly

The one-time-pad leaf commitment over `Bool` (`leafH t v s = v xor s`) satisfies
`SaltHidingHash` with ζ = 0: a fresh uniform salt makes the leaf digest uniform for every
value.  The key theorem then gives distance ≤ 0, hence **equality** of the real and
placeholder distributions — for every index type, every query set, every assignment, and in
particular for the concrete four-leaf radix-4 wire. -/

section NonVacuity

/-- One-time-pad leaf commitment over `Bool`: a perfectly hiding (not binding) instance of
the fixed-function leaf-hash interface. -/
def xorLeafHash : Unit → Bool → Bool → Bool := fun _ v s => Bool.xor v s

/-- A fresh uniform salt makes the xor leaf digest exactly uniform, for every value. -/
theorem xorLeafHash_map_uniform (v : Bool) :
    (PMF.uniformOfFintype Bool).map (xorLeafHash () v) = PMF.uniformOfFintype Bool := by
  refine PMF.ext fun b => ?_
  rw [PMF.map_apply]
  refine (tsum_eq_single (L := SummationFilter.unconditional Bool) (Bool.xor v b) ?_).trans ?_
  · intro s hs
    exact if_neg fun hb => hs (by rw [hb]; cases v <;> cases s <;> rfl)
  · rw [if_pos (by cases v <;> cases b <;> rfl),
      PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply]

/-- The hiding interface holds for the xor instance with ζ = 0 (perfect hiding). -/
theorem xorLeafHash_hiding : SaltHidingHash xorLeafHash 0 :=
  ⟨fun t v v' => by
    cases t
    rw [xorLeafHash_map_uniform v, xorLeafHash_map_uniform v', statDist_self]⟩

/-- In the xor instance the placeholder distribution **equals** the real commitment's: the
local placeholder bound is attained at 0 and upgraded to a `PMF` equality. -/
theorem xor_simulator_exact {ι : Type} [Fintype ι] [DecidableEq ι]
    (Q : Finset ι) (a : ι → Bool) (v₀ : Bool) :
    realMT xorLeafHash () Q a = MTSimulate xorLeafHash () Q (fun i _ => a i) v₀ := by
  refine eq_of_statDist_eq_zero (le_antisymm ?_ zero_le)
  have h := mtSimulate_close xorLeafHash_hiding () Q a v₀
  unfold zetaMT at h
  rwa [mul_zero] at h

/-- Concrete four-leaf (depth-1) radix-4 model instance: the query opens leaf 2. -/
def concreteQ : Finset (Path 1) := {fun _ => 2}

/-- On the concrete four-leaf model with one opened leaf, placeholder = real exactly. -/
theorem concrete_exact (a : Path 1 → Bool) :
    realMT xorLeafHash () concreteQ a
      = MTSimulate xorLeafHash () concreteQ (fun p _ => a p) false :=
  xor_simulator_exact concreteQ a false

/-- The packaged (root, frontier, records) distributions also agree exactly on the
concrete model, for any node compression. -/
theorem concrete_opening_exact (nodeH : Bool → Bool → Bool → Bool → Bool)
    (a : Path 1 → Bool) :
    (realMT xorLeafHash () concreteQ a).map (openingPack nodeH 1 concreteQ)
      = (MTSimulate xorLeafHash () concreteQ (fun p _ => a p) false).map
          (openingPack nodeH 1 concreteQ) :=
  congrArg _ (concrete_exact a)

end NonVacuity

end AspisV5SaltedMerkleSimulator

#print axioms AspisV5SaltedMerkleSimulator.statDist_triangle
#print axioms AspisV5SaltedMerkleSimulator.statDist_map_le
#print axioms AspisV5SaltedMerkleSimulator.statDist_bind_le
#print axioms AspisV5SaltedMerkleSimulator.eq_of_statDist_eq_zero
#print axioms AspisV5SaltedMerkleSimulator.uniform_bind_update
#print axioms AspisV5SaltedMerkleSimulator.statDist_factor_le
#print axioms AspisV5SaltedMerkleSimulator.saltHidingHash_of_valueFree
#print axioms AspisV5SaltedMerkleSimulator.fullView_hiding
#print axioms AspisV5SaltedMerkleSimulator.mtSimulate_close
#print axioms AspisV5SaltedMerkleSimulator.mtSimulate_unopened_untouched
#print axioms AspisV5SaltedMerkleSimulator.card_path
#print axioms AspisV5SaltedMerkleSimulator.rebuild_frontier
#print axioms AspisV5SaltedMerkleSimulator.mtSimulate_pack_close
#print axioms AspisV5SaltedMerkleSimulator.mtSimulate_opening_close
#print axioms AspisV5SaltedMerkleSimulator.mtSimulate_opening_verifies
#print axioms AspisV5SaltedMerkleSimulator.xorLeafHash_hiding
#print axioms AspisV5SaltedMerkleSimulator.xor_simulator_exact
#print axioms AspisV5SaltedMerkleSimulator.concrete_exact
#print axioms AspisV5SaltedMerkleSimulator.concrete_opening_exact

import Mathlib
import AspisFormal.ArithmetizationCore

/-!
# Hash / Merkle model: closing the six soundness-side interface clauses

This file discharges the six hash/Merkle fields of
`AspisFormal.ArithmetizationCore.ArithmetizationModels` — the frontier that
`ArithmetizationCore.lean` deliberately left as an opaque named interface.  It
replaces those six opaque assumptions with **proven structural logic** plus a
**single named code-constant interface** `Poseidon2Faithful`, the honest
soundness-side analogue of the hiding obligation (a).

## What is proved in-kernel (sorry-free, axioms `[propext, Classical.choice,
Quot.sound]` only — no `native_decide`, no `ofReduceBool`)

* `poseidon2Perm` — the pinned Poseidon2-M31 width-16 permutation, defined as the
  frozen `extLinear` ∘ 4+14+4 round schedule of `poseidon2.rs` (S-box `x^5`,
  the exact `external_linear` / `internal_linear` layers; the 60+ round
  constants are the opaque `RoundConstants` parameter).
* `poseidon_gate_forces_perm` — the `recorded_output = evaluate_trace_round(input,…)`
  residual family (`constraints_v4.rs`, `POSEIDON_FIRST/SECOND_START`) vanishing
  FORCES `recorded_output = poseidon2Perm(input)`.  This is the honest content:
  the gate literally *is* the round function, so once the permutation is defined
  as that composition the forcing is a clean chain induction (`runUpto_of_chain`).
* `initial_state_gate_forces_capacity` — the `INITIAL_STATE` residual forces the
  capacity lanes to the domain tag + committed length (`expected_initial_state`).
* `initState_domain_distinct` — distinct domains ⟹ distinct forced initial
  state (they disagree in capacity lane `RATE`): the STRUCTURAL half of domain
  separation.
* `merkle_selection_forces` — booleanity `bit·(bit−1)=0` + the two swap residuals
  `left = current + bit·(sibling−current)`, `right = sibling + bit·(current−sibling)`
  FORCE `(left,right)` to be `ordered_children` (`atomic_state_only_trace.rs`).
* `node_gate_forces_compression` — the node round chain forces the parent to be
  the `merkle_node_compress_v3` compression of the ordered children.
* `root_of_chain` / `MerklePathWitness.forces` — 20 forced `Parent` steps compose
  to the paper `Root`; because the witness carries ONE shared `(bits, sib)`
  namespace, both roots run the SAME path (the same-path clause).
* `discharge` — PROVES all six `ArithmetizationModels` fields from the hash/Merkle
  gate witness, instantiated at the in-Lean Poseidon2 hashes.

## The six clauses: status

| Clause (paper eq.)              | Status in this file                                 |
|---------------------------------|-----------------------------------------------------|
| (owner-key) `pk_in = H_own(k_ν)`| STRUCTURAL, in-kernel (`discharge.owner`)           |
| (input-note)`L_in = H_note(…)`  | STRUCTURAL, in-kernel (`discharge.input_note`)      |
| (nullifier) `ν = H_nul(…)`      | STRUCTURAL, in-kernel (`discharge.nullifier`)       |
| (output-note)`C_out = H_note(…)`| STRUCTURAL, in-kernel (`discharge.output_note`)     |
| (input-root)`A = Root(L_in;i,σ)`| STRUCTURAL, in-kernel (`discharge.input_root`)      |
| (output-root)`A' = Root(C_out;i,σ)`| STRUCTURAL, in-kernel + same-path (`discharge.output_root`) |

All six reduce, via `arithmetization_models_of_faithful`, to: the proven
`discharge` + the single named interface below.

## The residual named interface (never a faked "Lean = Rust" equation)

`Poseidon2Faithful rc dOwn dNote dNul dNode` asserts the deployed (opaque) typed
wrappers of `poseidon2.rs` equal the in-Lean hashes `ownerHash/noteHash/
nullifierHash/nodeHash rc`.  This is a CODE-CONSTANT correspondence and is left
as a named interface, exactly as required.  Closing it needs the round-constant
correspondence: an exhaustive check of the pinned `EXTERNAL_INITIAL / INTERNAL /
EXTERNAL_FINAL` u32 tables and the sponge framing against the deployed KATs
(`upstream_default_width_16_kat`, `typed_wrapper_output_regression_kat`,
`typed_domains_are_mutually_distinct`, …), or a proof that the Lean
`RoundConstants` instance equals the pinned tables.  Two sub-facts fold into this
same code/KAT residue and are NOT claimed structurally here:

* map-level domain distinctness (`H_own ≠ H_note` as *functions* on some input):
  a cross-domain non-collision, backed by `typed_domains_are_mutually_distinct`
  (a concrete evaluation), not by the structural capacity-forcing above;
* the multi-block sponge padding/length framing matching `hash_fields`.
-/

set_option maxRecDepth 100000

namespace AspisFormal.HashMerkleModel

open AspisFormal.ArithmetizationCore

/-- The 16-lane Poseidon2 permutation state over the relation field `F`. -/
abbrev State : Type := Fin 16 → F

/-- Truncate a 16-lane state to its first eight lanes (the sponge/compression
    digest projection `core::array::from_fn(|i| state[i])`). -/
def truncate8 (s : State) : Digest := fun i => s ⟨(i : ℕ), by omega⟩

/-! ## The frozen Poseidon2-M31 round algebra (faithful to `poseidon2.rs`) -/

/-- Fifth-power S-box `pow5(x) = x^5` (Plonky3 `alpha = 5`). -/
def sbox (x : F) : F := x ^ 5

/-- External (full-round) linear layer, algebraically identical to
    `external_linear` / `external_linear_lazy` in `poseidon2.rs`:
    the `4×4` circulant-ish `apply_mat4` on each width-4 chunk, then the
    per-column sum `state[i] += sums[i % 4]`. -/
def extLinear (s : State) : State :=
  let m : State :=
    ![ 2*s 0+3*s 1+s 2+s 3,   s 0+2*s 1+3*s 2+s 3,   s 0+s 1+2*s 2+3*s 3,   3*s 0+s 1+s 2+2*s 3,
       2*s 4+3*s 5+s 6+s 7,   s 4+2*s 5+3*s 6+s 7,   s 4+s 5+2*s 6+3*s 7,   3*s 4+s 5+s 6+2*s 7,
       2*s 8+3*s 9+s 10+s 11, s 8+2*s 9+3*s 10+s 11, s 8+s 9+2*s 10+3*s 11, 3*s 8+s 9+s 10+2*s 11,
       2*s 12+3*s 13+s 14+s 15, s 12+2*s 13+3*s 14+s 15, s 12+s 13+2*s 14+3*s 15, 3*s 12+s 13+s 14+2*s 15 ]
  let c0 := m 0 + m 4 + m 8 + m 12
  let c1 := m 1 + m 5 + m 9 + m 13
  let c2 := m 2 + m 6 + m 10 + m 14
  let c3 := m 3 + m 7 + m 11 + m 15
  ![ m 0+c0, m 1+c1, m 2+c2, m 3+c3,
     m 4+c0, m 5+c1, m 6+c2, m 7+c3,
     m 8+c0, m 9+c1, m 10+c2, m 11+c3,
     m 12+c0, m 13+c1, m 14+c2, m 15+c3 ]

/-- Internal (partial-round) linear layer, algebraically identical to
    `internal_linear` / `internal_linear_lazy`: `state[0] = part_sum - state[0]`
    and `state[i] = full_sum + state[i]·2^{shift[i-1]}` with the pinned Plonky3
    diagonal shift schedule `[0,1,2,3,4,5,6,7,8,10,12,13,14,15,16]`. -/
def intLinear (s : State) : State :=
  let ps := s 1+s 2+s 3+s 4+s 5+s 6+s 7+s 8+s 9+s 10+s 11+s 12+s 13+s 14+s 15
  let full := ps + s 0
  ![ ps - s 0,
     full + s 1*1,     full + s 2*2,     full + s 3*4,     full + s 4*8,
     full + s 5*16,    full + s 6*32,    full + s 7*64,    full + s 8*128,
     full + s 9*256,   full + s 10*1024, full + s 11*4096, full + s 12*8192,
     full + s 13*16384, full + s 14*32768, full + s 15*65536 ]

/-- Add round constants and apply the S-box to every lane (full round). -/
def fullSbox (k : Fin 16 → F) (s : State) : State := fun i => sbox (s i + k i)

/-- Add the single lane-0 constant and apply the S-box only to lane 0
    (partial round). -/
def intSbox (c : F) (s : State) : State :=
  fun i => if i = 0 then sbox (s i + c) else s i

/-- The frozen 4 + 14 + 4 round-constant schedule.  These are held as opaque
    parameters: the `Poseidon2Faithful` interface (below) is exactly the claim
    that a concrete instance equals the pinned `EXTERNAL_INITIAL / INTERNAL /
    EXTERNAL_FINAL` u32 tables of `poseidon2.rs`. -/
structure RoundConstants where
  extInit : Fin 4 → Fin 16 → F
  intern : Fin 14 → F
  extFinal : Fin 4 → Fin 16 → F

/-- One permutation round `r ∈ {0,…,21}` (full = linear ∘ sbox). -/
def poseidonRound (rc : RoundConstants) (r : ℕ) (s : State) : State :=
  if r < 4 then extLinear (fullSbox (rc.extInit ⟨r % 4, by omega⟩) s)
  else if r < 18 then intLinear (intSbox (rc.intern ⟨(r - 4) % 14, by omega⟩) s)
  else extLinear (fullSbox (rc.extFinal ⟨(r - 18) % 4, by omega⟩) s)

/-- Run steps `0,1,…,n-1` in order: `runUpto step n s = step (n-1) (… step 0 s)`. -/
def runUpto {α : Type*} (step : ℕ → α → α) : ℕ → α → α
  | 0, s => s
  | (k+1), s => step k (runUpto step k s)

/-- The gate's per-row transition: row 0 also applies the permutation's leading
    external linear layer (`evaluate_trace_round(input, 0, apply_leading = true)`),
    every later row is a plain round. -/
def gateStep (rc : RoundConstants) (r : ℕ) (s : State) : State :=
  if r = 0 then poseidonRound rc 0 (extLinear s) else poseidonRound rc r s

/-- **The pinned Poseidon2-M31 width-16 permutation.**  Defined exactly as the
    gate chains it: `extLinear`, then the 22 rounds.  (`permute` in
    `poseidon2.rs` is `external_linear` followed by the 4+14+4 rounds.) -/
def poseidon2Perm (rc : RoundConstants) : State → State := runUpto (gateStep rc) 22

/-! ### The chain-forcing lemma (the honest content of the Poseidon gate)

The deployed gate residual for an active row records
`recorded_output[lane] - round_function(recorded_input)[lane]`.  Setting every
residual to zero is precisely the hypothesis that the recorded chain follows the
round schedule; the conclusion is that the final recorded state is the full
permutation of the block input.  This is near-tautological *because* the
permutation is defined as this very composition — which is the honest content:
the gate literally is the round function. -/

/-- If a recorded chain `y` follows `step` at every index below `n`
    (`y (r+1) = step r (y r)`), then `y n` is `runUpto step n` of the start. -/
theorem runUpto_of_chain {α : Type*} (step : ℕ → α → α) (y : ℕ → α) (n : ℕ)
    (h : ∀ r, r < n → y (r + 1) = step r (y r)) :
    y n = runUpto step n (y 0) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have hk : y k = runUpto step k (y 0) := ih (fun r hr => h r (by omega))
    have := h k (by omega)
    rw [runUpto, ← hk, this]

/-- **Poseidon gate ⟹ permutation.**  A recorded 23-state chain whose every
    round matches the gate step forces the final recorded state to equal
    `poseidon2Perm` of the block input.  This discharges the `recorded_output =
    evaluate_trace_round(input,…)` residual family of `constraints_v4.rs`
    (`POSEIDON_FIRST_START` / `POSEIDON_SECOND_START`). -/
theorem poseidon_gate_forces_perm (rc : RoundConstants) (y : ℕ → State)
    (h : ∀ r, r < 22 → y (r + 1) = gateStep rc r (y r)) :
    y 22 = poseidon2Perm rc (y 0) :=
  runUpto_of_chain (gateStep rc) y 22 h

/-- A round chain witnessing that the deployed gate residuals (which set
    `y (r+1) = gateStep rc r (y r)`) hold across a whole permutation block.
    Its `forces` field is the honest content: the recorded output IS the
    permutation of the recorded input. -/
structure RoundChain (rc : RoundConstants) (input output : State) where
  y : ℕ → State
  start : y 0 = input
  chain : ∀ r, r < 22 → y (r + 1) = gateStep rc r (y r)
  finish : y 22 = output

theorem RoundChain.forces {rc : RoundConstants} {input output : State}
    (h : RoundChain rc input output) : output = poseidon2Perm rc input := by
  have hforce := poseidon_gate_forces_perm rc h.y h.chain
  rw [h.start] at hforce
  rw [h.finish] at hforce
  exact hforce

/-! ## Sponge framing: capacity / domain separation -/

/-- Frozen domain-separation constants (`crate::spend`, injected into the
    sponge capacity lane `RATE`). -/
-- `irreducible` so the ~10⁹ `ZMod` numerals are never reduced to unary `Fin p`
-- values during structure-field elaboration (their exact value is irrelevant to
-- every proof here; it is pinned by `Poseidon2Faithful`, not by kernel reduction).
@[irreducible] def DOM_OWNER : F := 0x41530001
@[irreducible] def DOM_NULLIFIER : F := 0x41530002
@[irreducible] def DOM_NOTE : F := 0x41530003
/-- Fixed-arity node compression tweak (`MERKLE_NODE_COMPRESSION_V3_TWEAK`). -/
@[irreducible] def NODE_TWEAK : F := 0x41531005

/-- The domain-separated initial sponge state: capacity lane `RATE = 8` carries
    the domain tag, lane `RATE+1 = 9` the committed input length, rest zero.
    Mirrors `hash_fields` / `expected_initial_state`. -/
def initState (domain len : F) : State :=
  fun i => if (i : ℕ) = 8 then domain else if (i : ℕ) = 9 then len else 0

/-- Rate-8 absorption: add the chunk into the first eight lanes. -/
def absorb (s : State) (c : Fin 8 → F) : State :=
  fun i => if h : (i : ℕ) < 8 then s i + c ⟨(i : ℕ), h⟩ else s i

/-- **Initial-state gate ⟹ capacity forced.**  The residual family
    `residuals[INITIAL_STATE_START+lane] = interface[lane] - expected[lane]`
    (`constraints_v4.rs`) vanishing forces the interface state to be exactly the
    domain-separated initial state.  Proved in-kernel. -/
theorem initial_state_gate_forces_capacity (iface : State) (domain len : F)
    (h : ∀ lane : Fin 16, iface lane - initState domain len lane = 0) :
    iface = initState domain len := by
  funext lane
  exact sub_eq_zero.mp (h lane)

/-- **Distinct domains give distinct forced capacity.**  Two sponge instances
    separated by different domain tags start from different initial states
    (they disagree in capacity lane `RATE`).  Proved in-kernel; this is the
    structural half of domain separation.  See the ledger for the residual
    (map-level non-collision, KAT-backed). -/
theorem initState_domain_distinct (d1 l1 d2 l2 : F) (hd : d1 ≠ d2) :
    initState d1 l1 ≠ initState d2 l2 := by
  intro hEq
  apply hd
  have := congrFun hEq (8 : Fin 16)
  simpa [initState] using this

/-! ## Multi-block sponge and the domain-separated hashes -/

/-- Absorb a list of rate-8 chunks, permuting after each (the `hash_fields`
    loop over `input.chunks(RATE)`). -/
def spongeFold (rc : RoundConstants) (s : State) : List (Fin 8 → F) → State
  | [] => s
  | c :: cs => spongeFold rc (poseidon2Perm rc (absorb s c)) cs

/-- Domain-separated, length-committing rate-8 sponge digest. -/
def spongeHash (rc : RoundConstants) (domain len : F) (chunks : List (Fin 8 → F)) : Digest :=
  truncate8 (spongeFold rc (initState domain len) chunks)

/-- Owner-key hash `H_own` (`DOMAIN_OWNER_KEY`, one rate-8 block). -/
def ownerHash (rc : RoundConstants) (k : Digest) : Digest :=
  spongeHash rc DOM_OWNER 8 [k]

/-- Nullifier hash `H_nul` (`DOMAIN_NULLIFIER`, two rate-8 blocks: key ‖ salt). -/
def nullifierHash (rc : RoundConstants) (k r : Digest) : Digest :=
  spongeHash rc DOM_NULLIFIER 16 [k, r]

/-- The note leaf's second and third rate-8 chunks: `[value, asset, r0..r5]`
    and `[r6, r7, 0,0,0,0,0,0]` (the `owner ‖ value ‖ asset ‖ salt` framing of
    `note_commitment`, length 18). -/
def noteChunk1 (v a : F) (r : Digest) : Fin 8 → F :=
  ![v, a, r 0, r 1, r 2, r 3, r 4, r 5]
def noteChunk2 (r : Digest) : Fin 8 → F :=
  ![r 6, r 7, 0, 0, 0, 0, 0, 0]

/-- Note / leaf / output commitment `H_note` (`DOMAIN_NOTE`, three rate-8
    blocks). -/
def noteHash (rc : RoundConstants) (pk : Digest) (v a : F) (r : Digest) : Digest :=
  spongeHash rc DOM_NOTE 18 [pk, noteChunk1 v a r, noteChunk2 r]

/-! ## Fixed-arity Merkle node compression and selection -/

/-- Node compression pre-permutation state: `left` in lanes 0..7, `right` in
    lanes 8..15, node tweak added into the last lane
    (`merkle_node_compress_v3`). -/
def nodeState (tweak : F) (left right : Digest) : State :=
  fun i =>
    if h : (i : ℕ) < 8 then left ⟨(i : ℕ), h⟩
    else if (i : ℕ) = 15 then right ⟨(i : ℕ) - 8, by omega⟩ + tweak
    else right ⟨(i : ℕ) - 8, by omega⟩

/-- The deployed Merkle node hash `H_node` (one permutation, first eight lanes). -/
def nodeHash (rc : RoundConstants) (left right : Digest) : Digest :=
  truncate8 (poseidon2Perm rc (nodeState NODE_TWEAK left right))

/-- **Node gate ⟹ compression.**  A round chain on the node block forces the
    recorded parent digest to be the node compression of the ordered children. -/
theorem node_gate_forces_compression (rc : RoundConstants) (left right : Digest)
    (parentState : State) (h : RoundChain rc (nodeState NODE_TWEAK left right) parentState) :
    truncate8 parentState = nodeHash rc left right := by
  rw [h.forces]; rfl

/-- **Merkle selection ⟹ ordered children.**  The booleanity residual
    `bit·(bit−1)=0` together with the two swap residuals
    `left = current + bit·(sibling−current)` and
    `right = sibling + bit·(current−sibling)` force `(left,right)` to be the
    `if bit then (sibling,current) else (current,sibling)` pair
    (`atomic_state_only_trace.rs::ordered_children`).  Proved in-kernel. -/
theorem merkle_selection_forces (b : F) (hb : b * (b - 1) = 0)
    (current sibling left right : Digest)
    (hl : ∀ i, left i = current i + b * (sibling i - current i))
    (hr : ∀ i, right i = sibling i + b * (current i - sibling i)) :
    (b = 0 ∧ left = current ∧ right = sibling) ∨
    (b = 1 ∧ left = sibling ∧ right = current) := by
  rcases field_bool hb with rfl | rfl
  · refine Or.inl ⟨rfl, ?_, ?_⟩ <;> funext i <;> simp [hl i, hr i]
  · refine Or.inr ⟨rfl, ?_, ?_⟩
    · funext i; rw [hl i]; ring
    · funext i; rw [hr i]; ring

/-! ## Merkle root chaining (20 levels, shared path) -/

/-- Generic chain-to-`Fin.foldl` lemma (the `Nat`-indexed analogue of
    `runUpto_of_chain`), proved by peeling `Fin.foldl` from the back. -/
theorem foldl_chain {α : Type*} (g : α → ℕ → α) (init : α) (c : ℕ → α)
    (h0 : c 0 = init) :
    ∀ n : ℕ, (∀ k, k < n → c (k + 1) = g (c k) k) →
      c n = Fin.foldl n (fun x i => g x (i : ℕ)) init := by
  intro n
  induction n with
  | zero => intro _; simpa using h0
  | succ m ih =>
    intro hstep
    rw [Fin.foldl_succ_last]
    have hinner : Fin.foldl m (fun x (i : Fin m) => g x ((i.castSucc : Fin (m + 1)) : ℕ)) init
        = c m := by
      have := ih (fun k hk => hstep k (by omega))
      rw [this]; congr 1
    rw [hinner]
    simp only [Fin.val_last]
    exact hstep m (by omega)

/-- **Root ⟹ from a level chain.**  If a per-level running digest `c` starts at
    the leaf and each step is the paper `Parent` under the level's direction bit
    and sibling, then after twenty levels it equals `Root`.  Proved in-kernel. -/
theorem root_of_chain (Hnode : Digest → Digest → Digest) (leaf : Digest)
    (bits : Fin 20 → Bool) (sib : Fin 20 → Digest) (c : ℕ → Digest)
    (h0 : c 0 = leaf)
    (hstep : ∀ j : Fin 20, c (j + 1) = Parent Hnode (bits j) (c j) (sib j)) :
    c 20 = Root Hnode leaf bits sib := by
  set g : Digest → ℕ → Digest :=
    fun x k => Parent Hnode (bits ⟨k % 20, Nat.mod_lt _ (by norm_num)⟩) x
      (sib ⟨k % 20, Nat.mod_lt _ (by norm_num)⟩) with hg
  have key := foldl_chain g leaf c h0 20 ?_
  · rw [key, Root]
    congr 1
    funext x i
    have hi : (⟨(i : ℕ) % 20, Nat.mod_lt _ (by norm_num)⟩ : Fin 20) = i := by
      apply Fin.ext; simp [Nat.mod_eq_of_lt i.isLt]
    simp only [hg, hi]
  · intro k hk
    have hj := hstep ⟨k, hk⟩
    have hi : (⟨k % 20, Nat.mod_lt _ (by norm_num)⟩ : Fin 20) = ⟨k, hk⟩ := by
      apply Fin.ext; simp [Nat.mod_eq_of_lt hk]
    simp only [hg, hi]
    exact hj

/-! ## Sponge block-chaining (fixed arity 1 / 2 / 3) -/

/-- One-block sponge (owner-key). -/
theorem sponge1_forces (rc : RoundConstants) (d l : F) (c0 : Fin 8 → F) (s1 : State)
    (h1 : RoundChain rc (absorb (initState d l) c0) s1) :
    truncate8 s1 = spongeHash rc d l [c0] := by
  rw [h1.forces]; rfl

/-- Two-block sponge (nullifier: key ‖ salt). -/
theorem sponge2_forces (rc : RoundConstants) (d l : F) (c0 c1 : Fin 8 → F) (s1 s2 : State)
    (h1 : RoundChain rc (absorb (initState d l) c0) s1)
    (h2 : RoundChain rc (absorb s1 c1) s2) :
    truncate8 s2 = spongeHash rc d l [c0, c1] := by
  rw [h2.forces, h1.forces]; rfl

/-- Three-block sponge (note commitment: owner ‖ value ‖ asset ‖ salt). -/
theorem sponge3_forces (rc : RoundConstants) (d l : F) (c0 c1 c2 : Fin 8 → F)
    (s1 s2 s3 : State)
    (h1 : RoundChain rc (absorb (initState d l) c0) s1)
    (h2 : RoundChain rc (absorb s1 c1) s2)
    (h3 : RoundChain rc (absorb s2 c2) s3) :
    truncate8 s3 = spongeHash rc d l [c0, c1, c2] := by
  rw [h3.forces, h2.forces, h1.forces]; rfl

/-! ## Per-level Merkle forcing -/

/-- All gate data for one Merkle level: the direction bit `β` (as a forced field
    bit `b`), the two selection residuals, and the node round-chain. -/
structure MerkleLevelData (rc : RoundConstants) (β : Bool) (current sibling next : Digest) where
  b : F
  hbit : b = if β then 1 else 0
  left : Digest
  right : Digest
  hsel_l : ∀ i, left i = current i + b * (sibling i - current i)
  hsel_r : ∀ i, right i = sibling i + b * (current i - sibling i)
  parentState : State
  hnode : RoundChain rc (nodeState NODE_TWEAK left right) parentState
  hnext : next = truncate8 parentState

/-- **One Merkle level ⟹ paper `Parent`.**  Booleanity + swap selection +
    node compression force the running digest to advance by exactly one paper
    `Parent` step. -/
theorem MerkleLevelData.forces {rc : RoundConstants} {β : Bool} {current sibling next : Digest}
    (d : MerkleLevelData rc β current sibling next) :
    next = Parent (nodeHash rc) β current sibling := by
  have hb2 : d.b * (d.b - 1) = 0 := by rw [d.hbit]; cases β <;> norm_num
  have hsel := merkle_selection_forces d.b hb2 current sibling d.left d.right d.hsel_l d.hsel_r
  have hcomp : truncate8 d.parentState = nodeHash rc d.left d.right :=
    node_gate_forces_compression rc d.left d.right d.parentState d.hnode
  rw [d.hnext, hcomp]
  cases β with
  | false =>
    have hb0 : d.b = 0 := by simp [d.hbit]
    rcases hsel with ⟨_, hl, hr⟩ | ⟨hbne, _, _⟩
    · rw [hl, hr]; simp [Parent]
    · exact absurd hbne (by rw [hb0]; norm_num)
  | true =>
    have hb1 : d.b = 1 := by simp [d.hbit]
    rcases hsel with ⟨hbne, _, _⟩ | ⟨_, hl, hr⟩
    · exact absurd hbne (by rw [hb1]; norm_num)
    · rw [hl, hr]; simp [Parent]

/-- Full 20-level path gate data: a running digest from `leaf` to `root`, with
    every level's `MerkleLevelData` under the SHARED `bits` / `sib` namespace. -/
structure MerklePathWitness (rc : RoundConstants) (leaf root : Digest)
    (bits : Fin 20 → Bool) (sib : Fin 20 → Digest) where
  current : ℕ → Digest
  h0 : current 0 = leaf
  hlast : current 20 = root
  level : ∀ j : Fin 20, MerkleLevelData rc (bits j) (current j) (sib j) (current (j + 1))

/-- **The whole path ⟹ `Root`.**  Twenty forced `Parent` steps compose to the
    paper `Root` along `(bits, sib)`. -/
theorem MerklePathWitness.forces {rc : RoundConstants} {leaf root : Digest}
    {bits : Fin 20 → Bool} {sib : Fin 20 → Digest}
    (W : MerklePathWitness rc leaf root bits sib) :
    root = Root (nodeHash rc) leaf bits sib := by
  have hchain : W.current 20 = Root (nodeHash rc) leaf bits sib :=
    root_of_chain (nodeHash rc) leaf bits sib W.current W.h0 (fun j => (W.level j).forces)
  rw [← W.hlast, hchain]

/-! ## The full hash/Merkle gate witness and the discharge -/

/-- Every hash/Merkle gate residual of the deployed constraint system, tied to
    the opened columns `O`.  This is exactly the data whose vanishing the
    `ArithmetizationModels` interface fields assumed; here it is the honest
    hypothesis, and the discharge below PROVES the six clauses from it. -/
structure HashMerkleWitness (rc : RoundConstants) (O : OpenedColumns) where
  -- owner key: pk_in = H_own(k_nu)
  ownerState : State
  ownerChain : RoundChain rc (absorb (initState DOM_OWNER 8) O.k_nu) ownerState
  ownerDigest : O.pk_in = truncate8 ownerState
  -- nullifier: nu = H_nul(k_nu, r_in)
  nullState1 : State
  nullState2 : State
  nullChain1 : RoundChain rc (absorb (initState DOM_NULLIFIER 16) O.k_nu) nullState1
  nullChain2 : RoundChain rc (absorb nullState1 O.r_in) nullState2
  nullDigest : O.nu = truncate8 nullState2
  -- input note: L_in = H_note(pk_in, v, a_in, r_in)  (value = rin.value)
  inNote1 : State
  inNote2 : State
  inNote3 : State
  inNoteChain1 : RoundChain rc (absorb (initState DOM_NOTE 18) O.pk_in) inNote1
  inNoteChain2 :
    RoundChain rc (absorb inNote1 (noteChunk1 O.rin.value O.a_in O.r_in)) inNote2
  inNoteChain3 : RoundChain rc (absorb inNote2 (noteChunk2 O.r_in)) inNote3
  inNoteDigest : O.L_in = truncate8 inNote3
  -- output note: C_out = H_note(pk_out, v', a, r_out)  (value = rout.value)
  outNote1 : State
  outNote2 : State
  outNote3 : State
  outNoteChain1 : RoundChain rc (absorb (initState DOM_NOTE 18) O.pk_out) outNote1
  outNoteChain2 :
    RoundChain rc (absorb outNote1 (noteChunk1 O.rout.value O.a O.r_out)) outNote2
  outNoteChain3 : RoundChain rc (absorb outNote2 (noteChunk2 O.r_out)) outNote3
  outNoteDigest : O.C_out = truncate8 outNote3
  -- input Merkle root along (bits, sib)
  inputPath : MerklePathWitness rc O.L_in O.A O.bits O.sib
  -- output Merkle root along the SAME (bits, sib): the same-path clause
  outputPath : MerklePathWitness rc O.C_out O.A' O.bits O.sib

/-- **Discharge of the six interface clauses (Lean hashes).**  With the deployed
    hash/Merkle gate residuals as the honest hypothesis, every field of
    `ArithmetizationModels` is PROVED, instantiated at the in-Lean Poseidon2
    hashes.  Nothing is assumed; the `ConstraintsSatisfied` argument is unused
    because the hash/Merkle clauses need only the (richer) gate witness. -/
theorem discharge (rc : RoundConstants) (O : OpenedColumns) (W : HashMerkleWitness rc O) :
    ArithmetizationModels (ownerHash rc) (noteHash rc) (nullifierHash rc) (nodeHash rc) O where
  owner := fun _ => by
    rw [W.ownerDigest]; exact sponge1_forces rc DOM_OWNER 8 O.k_nu W.ownerState W.ownerChain
  input_note := fun _ v hv => by
    rw [← hv, W.inNoteDigest]
    exact sponge3_forces rc DOM_NOTE 18 O.pk_in (noteChunk1 O.rin.value O.a_in O.r_in)
      (noteChunk2 O.r_in) W.inNote1 W.inNote2 W.inNote3
      W.inNoteChain1 W.inNoteChain2 W.inNoteChain3
  nullifier := fun _ => by
    rw [W.nullDigest]
    exact sponge2_forces rc DOM_NULLIFIER 16 O.k_nu O.r_in W.nullState1 W.nullState2
      W.nullChain1 W.nullChain2
  output_note := fun _ v' hv' => by
    rw [← hv', W.outNoteDigest]
    exact sponge3_forces rc DOM_NOTE 18 O.pk_out (noteChunk1 O.rout.value O.a O.r_out)
      (noteChunk2 O.r_out) W.outNote1 W.outNote2 W.outNote3
      W.outNoteChain1 W.outNoteChain2 W.outNoteChain3
  input_root := fun _ => W.inputPath.forces
  output_root := fun _ => W.outputPath.forces

/-! ## The residual named interface: `Poseidon2Faithful`

The discharge above proves the six clauses for the *in-Lean* hashes.  The ONLY
thing left between that and the deployed statement is the code-constant
correspondence: that the Lean `poseidon2Perm` / round-constant schedule / sponge
framing reproduce the deployed `poseidon2.rs` permitation and typed wrappers.
This is a NAMED interface — never a faked "Lean = Rust" equation — the honest
soundness-side analogue of the hiding obligation (a). -/

/-- **The one residual interface.**  Asserts that the deployed (opaque) hash
    wrappers equal the in-Lean Poseidon2 hashes.  Closing it requires the
    round-constant correspondence: an exhaustive check against the pinned
    `EXTERNAL_INITIAL / INTERNAL / EXTERNAL_FINAL` tables and the KATs of
    `poseidon2.rs`, or a proof that the Lean constants equal the pinned ones. -/
structure Poseidon2Faithful (rc : RoundConstants)
    (deployedOwner : Digest → Digest)
    (deployedNote : Digest → F → F → Digest → Digest)
    (deployedNullifier : Digest → Digest → Digest)
    (deployedNode : Digest → Digest → Digest) : Prop where
  owner_eq : deployedOwner = ownerHash rc
  note_eq : deployedNote = noteHash rc
  nullifier_eq : deployedNullifier = nullifierHash rc
  node_eq : deployedNode = nodeHash rc

/-- **Six clauses ⟹ proven structural logic + one named interface.**  Given the
    `Poseidon2Faithful` correspondence AND the hash/Merkle gate witness, the full
    `ArithmetizationModels` interface holds for the *deployed* hashes.  Feeding
    this into `arithmetization_sound` closes the soundness-side hash/Merkle
    obligations modulo exactly `Poseidon2Faithful`. -/
theorem arithmetization_models_of_faithful (rc : RoundConstants) (O : OpenedColumns)
    {dOwn : Digest → Digest} {dNote : Digest → F → F → Digest → Digest}
    {dNul : Digest → Digest → Digest} {dNode : Digest → Digest → Digest}
    (faithful : Poseidon2Faithful rc dOwn dNote dNul dNode)
    (W : HashMerkleWitness rc O) :
    ArithmetizationModels dOwn dNote dNul dNode O := by
  rw [faithful.owner_eq, faithful.note_eq, faithful.nullifier_eq, faithful.node_eq]
  exact discharge rc O W

/-- End-to-end: the deployed constraints (range/balance/asset via
    `ConstraintsSatisfied`, hash/Merkle via the gate witness `W`) plus the single
    `Poseidon2Faithful` interface yield the full spend relation. -/
theorem spend_relation_of_faithful (rc : RoundConstants) (O : OpenedColumns)
    {dOwn : Digest → Digest} {dNote : Digest → F → F → Digest → Digest}
    {dNul : Digest → Digest → Digest} {dNode : Digest → Digest → Digest}
    (faithful : Poseidon2Faithful rc dOwn dNote dNul dNode)
    (W : HashMerkleWitness rc O) (C : ConstraintsSatisfied O) :
    ∃ v v' : ℕ, SpendRelation dOwn dNote dNul dNode O v v' :=
  arithmetization_sound (arithmetization_models_of_faithful rc O faithful W) C

end AspisFormal.HashMerkleModel

#print axioms AspisFormal.HashMerkleModel.poseidon_gate_forces_perm
#print axioms AspisFormal.HashMerkleModel.initial_state_gate_forces_capacity
#print axioms AspisFormal.HashMerkleModel.initState_domain_distinct
#print axioms AspisFormal.HashMerkleModel.merkle_selection_forces
#print axioms AspisFormal.HashMerkleModel.node_gate_forces_compression
#print axioms AspisFormal.HashMerkleModel.root_of_chain
#print axioms AspisFormal.HashMerkleModel.discharge
#print axioms AspisFormal.HashMerkleModel.arithmetization_models_of_faithful
#print axioms AspisFormal.HashMerkleModel.spend_relation_of_faithful

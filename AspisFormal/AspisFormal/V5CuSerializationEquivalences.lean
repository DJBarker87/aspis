import Mathlib

/-!
# Serialization equivalences for the retained v5 CU rewrites

This leaf module records byte-level serialization facts behind four retained
v5 CU rewrites.  Every statement is about the honest byte models defined in
this file: bytes are natural numbers constrained by explicit `< 256`
hypotheses, buffers are functions out of `Fin`, words are natural numbers
shown `< 2 ^ 64`.

* zero-scanning the post-salt 400-byte tail as 50 little-endian-packed
  64-bit words is equivalent to scanning all 400 bytes;
* the direct index-formula fill of the 129-byte Merkle child buffer is
  byte-for-byte equal to the domain byte `0x12` followed by the four
  appended 32-byte children;
* fixed-width record access by `(record, offset)` pairs and flat ordinal
  access select identical bytes in identical order; and
* a matched-topology token constructor succeeds exactly on suffix equality,
  and consuming a constructed token re-yields exactly that equality.

Nothing in this file mentions, models, or proves anything about Rust code,
the deployed serializer, hashes, or any on-chain artifact.  Identifying the
deployed byte layouts and token flow with these models is a separate
executable-correspondence obligation; the four obligations are named
explicitly at the end of the file.
-/

open scoped BigOperators

namespace AspisV5CuSerializationEquivalences

/-! ## Little-endian 8-byte word packing

The zero-scan rewrite reads the 400-byte tail after the five 32-byte public
salt slots as 50 aligned 8-byte little-endian words and compares each word
against zero. -/

/-- Little-endian packing of 8 bytes into one natural number: byte `i`
contributes `b i * 256 ^ i`. -/
def packLE8 (b : Fin 8 → ℕ) : ℕ :=
  ∑ i : Fin 8, b i * 256 ^ (i : ℕ)

/-- A packed little-endian word is zero exactly when all eight bytes are
zero.  Stated under the byte bound of the model. -/
theorem packLE8_eq_zero_iff (b : Fin 8 → ℕ) (_hb : ∀ i, b i < 256) :
    packLE8 b = 0 ↔ ∀ i, b i = 0 := by
  constructor
  · intro h i
    have hterm : b i * 256 ^ (i : ℕ) ≤ packLE8 b := by
      unfold packLE8
      exact Finset.single_le_sum (f := fun j => b j * 256 ^ (j : ℕ))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have hzero : b i * 256 ^ (i : ℕ) = 0 := by omega
    have hpow : (256 : ℕ) ^ (i : ℕ) ≠ 0 := pow_ne_zero _ (by norm_num)
    exact (Nat.mul_eq_zero.mp hzero).resolve_right hpow
  · intro h
    unfold packLE8
    exact Finset.sum_eq_zero fun i _ => by rw [h i, zero_mul]

/-- Under the byte bound, a packed word fits in an unsigned 64-bit
integer. -/
theorem packLE8_lt_two_pow_64 (b : Fin 8 → ℕ) (hb : ∀ i, b i < 256) :
    packLE8 b < 2 ^ 64 := by
  have hle : packLE8 b ≤ ∑ i : Fin 8, 255 * 256 ^ (i : ℕ) := by
    unfold packLE8
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_left (by have := hb i; omega) _
  have hsum : (∑ i : Fin 8, 255 * 256 ^ (i : ℕ)) = 2 ^ 64 - 1 := by
    rw [Fin.sum_univ_eight]
    norm_num
  omega

/-- Shape pin for the scanned region: 400 bytes are exactly 50 aligned
8-byte words. -/
theorem region_bytes_eq_words_times_width : (400 : ℕ) = 50 * 8 := by
  norm_num

/-- The byte index of offset `j` inside word `w` of the 400-byte region. -/
def wordIndex (w : Fin 50) (j : Fin 8) : Fin 400 :=
  ⟨(w : ℕ) * 8 + (j : ℕ), by omega⟩

/-- Word `w` of the region, packed little-endian. -/
def packedWord (b : Fin 400 → ℕ) (w : Fin 50) : ℕ :=
  packLE8 fun j => b (wordIndex w j)

/-- Every packed word of a byte-bounded region fits in `u64`. -/
theorem packedWord_lt_two_pow_64 (b : Fin 400 → ℕ) (hb : ∀ i, b i < 256)
    (w : Fin 50) : packedWord b w < 2 ^ 64 :=
  packLE8_lt_two_pow_64 _ fun _ => hb _

/-- Checking that all 50 packed words are zero is equivalent to checking
that all 400 post-salt tail bytes are zero. -/
theorem packedWords_all_zero_iff_bytes_all_zero (b : Fin 400 → ℕ)
    (hb : ∀ i, b i < 256) :
    (∀ w : Fin 50, packedWord b w = 0) ↔ ∀ i : Fin 400, b i = 0 := by
  constructor
  · intro h i
    have hw : (i : ℕ) / 8 < 50 := by omega
    have hj : (i : ℕ) % 8 < 8 := by omega
    have h0 := (packLE8_eq_zero_iff _ fun _ => hb _).mp
      (h ⟨(i : ℕ) / 8, hw⟩) ⟨(i : ℕ) % 8, hj⟩
    have hidx : wordIndex ⟨(i : ℕ) / 8, hw⟩ ⟨(i : ℕ) % 8, hj⟩ = i := by
      apply Fin.ext
      show (i : ℕ) / 8 * 8 + (i : ℕ) % 8 = (i : ℕ)
      omega
    rwa [hidx] at h0
  · intro h w
    exact (packLE8_eq_zero_iff _ fun _ => hb _).mpr fun _ => h _

/-- Non-vacuity: the byte-bound hypothesis is satisfiable by a nonzero
vector that `packLE8` separates from zero. -/
theorem packLE8_bound_hypothesis_nonvacuous :
    ∃ b : Fin 8 → ℕ, (∀ i, b i < 256) ∧ packLE8 b ≠ 0 := by
  refine ⟨fun _ => 1, fun _ => by norm_num, fun hcontr => ?_⟩
  have h1 := (packLE8_eq_zero_iff (fun _ => 1) fun _ => by norm_num).mp hcontr 0
  norm_num at h1

/-! ## The 129-byte Merkle child buffer

Two syntactically different constructions of the same buffer: a direct
index formula with explicit range tests, and the domain byte `0x12`
followed by the four appended children. -/

/-- Evaluate `Fin.append` at an arbitrary index by comparing the raw index
against the left length. -/
theorem append_apply_val {α : Type*} {m n : ℕ} (a : Fin m → α) (b : Fin n → α)
    (i : Fin (m + n)) :
    Fin.append a b i =
      if h : (i : ℕ) < m then a ⟨(i : ℕ), h⟩ else b ⟨(i : ℕ) - m, by omega⟩ := by
  by_cases h : (i : ℕ) < m
  · rw [dif_pos h]
    have hc : i = Fin.castAdd n ⟨(i : ℕ), h⟩ := Fin.ext rfl
    calc Fin.append a b i
        = Fin.append a b (Fin.castAdd n ⟨(i : ℕ), h⟩) := by rw [← hc]
      _ = a ⟨(i : ℕ), h⟩ := Fin.append_left a b _
  · rw [dif_neg h]
    have hn : (i : ℕ) - m < n := by omega
    have hc : i = Fin.natAdd m ⟨(i : ℕ) - m, hn⟩ := by
      apply Fin.ext
      show (i : ℕ) = m + ((i : ℕ) - m)
      omega
    calc Fin.append a b i
        = Fin.append a b (Fin.natAdd m ⟨(i : ℕ) - m, hn⟩) := by rw [← hc]
      _ = b ⟨(i : ℕ) - m, hn⟩ := Fin.append_right a b _

/-- Direct index-formula fill of the 129-byte child-hash buffer: domain
byte `0x12` at index 0, then the four 32-byte children at explicit
offsets. -/
def merkleChildBufferDirect (c0 c1 c2 c3 : Fin 32 → ℕ) : Fin 129 → ℕ :=
  fun i =>
    if (i : ℕ) = 0 then 0x12
    else if h1 : (i : ℕ) < 33 then c0 ⟨(i : ℕ) - 1, by omega⟩
    else if h2 : (i : ℕ) < 65 then c1 ⟨(i : ℕ) - 33, by omega⟩
    else if h3 : (i : ℕ) < 97 then c2 ⟨(i : ℕ) - 65, by omega⟩
    else c3 ⟨(i : ℕ) - 97, by omega⟩

/-- The same buffer as a length-1 constant `0x12` prefix followed by the
four appended children. -/
def merkleChildBufferAppend (c0 c1 c2 c3 : Fin 32 → ℕ) : Fin 129 → ℕ :=
  Fin.append (fun _ : Fin 1 => 0x12)
    (Fin.append (Fin.append (Fin.append c0 c1) c2) c3)

/-- Shape pin for the buffer: one domain byte plus four 32-byte children. -/
theorem buffer_bytes_eq_one_add_four_children : (129 : ℕ) = 1 + 4 * 32 := by
  norm_num

/-- The direct fill places the domain byte at index 0. -/
theorem merkleChildBufferDirect_apply_zero (c0 c1 c2 c3 : Fin 32 → ℕ) :
    merkleChildBufferDirect c0 c1 c2 c3 0 = 0x12 := rfl

/-- The direct index-formula fill is byte-for-byte equal to the appended
form.  The two sides are syntactically different constructions; the proof
is a full case split over the index ranges, not a definitional `rfl`. -/
theorem merkleChildBufferDirect_eq_append (c0 c1 c2 c3 : Fin 32 → ℕ) :
    merkleChildBufferDirect c0 c1 c2 c3 = merkleChildBufferAppend c0 c1 c2 c3 := by
  funext i
  simp only [merkleChildBufferDirect, merkleChildBufferAppend, append_apply_val]
  split_ifs <;>
    first
      | rfl
      | (exfalso; omega)

/-- Byte-model preservation: if the children are byte-bounded then so is
every byte of the direct buffer (the domain byte `0x12` is a byte). -/
theorem merkleChildBufferDirect_lt_256 (c0 c1 c2 c3 : Fin 32 → ℕ)
    (h0 : ∀ j, c0 j < 256) (h1 : ∀ j, c1 j < 256)
    (h2 : ∀ j, c2 j < 256) (h3 : ∀ j, c3 j < 256) :
    ∀ i, merkleChildBufferDirect c0 c1 c2 c3 i < 256 := by
  intro i
  unfold merkleChildBufferDirect
  split_ifs
  · norm_num
  · exact h0 _
  · exact h1 _
  · exact h2 _
  · exact h3 _

/-- Non-vacuity: the child byte-bound bundle is satisfiable, and the
bounded buffer carries the domain byte at index 0. -/
theorem merkleChildBuffer_bound_hypothesis_nonvacuous :
    ∃ c : Fin 32 → ℕ, (∀ j, c j < 256) ∧
      merkleChildBufferDirect c c c c 0 = 0x12 :=
  ⟨fun _ => 0xAB, fun _ => by norm_num, rfl⟩

/-! ## Fixed-width record traversal

A buffer of `count` records of `width` bytes each has total length
`count * width`.  Access by `(record, offset)` and access by flat ordinal
are the same bytes in the same order. -/

/-- The ordinal of offset `o` in record `r` lies inside the buffer. -/
theorem recordIndex_lt {count width r o : ℕ} (hr : r < count) (ho : o < width) :
    r * width + o < count * width := by
  have h1 : (r + 1) * width ≤ count * width :=
    mul_le_mul_left (by omega) width
  have h2 : (r + 1) * width = r * width + width := by ring
  omega

/-- Fin-typed form of `recordIndex_lt`. -/
theorem sliceIndex_lt {count width : ℕ} (r : Fin count) (o : Fin width) :
    (r : ℕ) * width + (o : ℕ) < count * width :=
  recordIndex_lt r.isLt o.isLt

/-- Ordinal slicing: the byte of record `r` at offset `o`. -/
def recordSlice {count width : ℕ} (buf : Fin (count * width) → ℕ)
    (r : Fin count) (o : Fin width) : ℕ :=
  buf ⟨(r : ℕ) * width + (o : ℕ), sliceIndex_lt r o⟩

/-- Interface pin (definitional): the record-`r`, offset-`o` byte is the
buffer byte at flat ordinal `r * width + o`. -/
theorem recordSlice_eq_buffer_at {count width : ℕ}
    (buf : Fin (count * width) → ℕ) (r : Fin count) (o : Fin width) :
    recordSlice buf r o =
      buf ⟨(r : ℕ) * width + (o : ℕ), sliceIndex_lt r o⟩ := rfl

/-- The `(record, offset)`-to-flat-ordinal map. -/
def pairToFlat {count width : ℕ} (p : Fin count × Fin width) :
    Fin (count * width) :=
  ⟨(p.1 : ℕ) * width + (p.2 : ℕ), sliceIndex_lt p.1 p.2⟩

/-- The flat-ordinal-to-`(record, offset)` map, by Euclidean division. -/
def flatToPair {count width : ℕ} (hw : 0 < width) (k : Fin (count * width)) :
    Fin count × Fin width :=
  (⟨(k : ℕ) / width, (Nat.div_lt_iff_lt_mul hw).mpr k.isLt⟩,
   ⟨(k : ℕ) % width, Nat.mod_lt _ hw⟩)

/-- The two access patterns index the same byte set bijectively:
`(record, offset)` pairs and flat ordinals are equivalent. -/
def recordIndexEquiv (count width : ℕ) (hw : 0 < width) :
    Fin count × Fin width ≃ Fin (count * width) where
  toFun := pairToFlat
  invFun := flatToPair hw
  left_inv := by
    rintro ⟨r, o⟩
    unfold pairToFlat flatToPair
    simp only [Prod.mk.injEq]
    constructor
    · apply Fin.ext
      show ((r : ℕ) * width + (o : ℕ)) / width = (r : ℕ)
      rw [Nat.mul_comm (r : ℕ) width, Nat.mul_add_div hw,
        Nat.div_eq_of_lt o.isLt, Nat.add_zero]
    · apply Fin.ext
      show ((r : ℕ) * width + (o : ℕ)) % width = (o : ℕ)
      rw [Nat.mul_add_mod', Nat.mod_eq_of_lt o.isLt]
  right_inv := by
    intro k
    unfold pairToFlat flatToPair
    apply Fin.ext
    show (k : ℕ) / width * width + (k : ℕ) % width = (k : ℕ)
    exact Nat.div_add_mod' _ _

/-- Interface pin (definitional): slicing is buffer access through the
equivalence. -/
theorem recordSlice_eq_buffer_comp_equiv {count width : ℕ} (hw : 0 < width)
    (buf : Fin (count * width) → ℕ) (r : Fin count) (o : Fin width) :
    recordSlice buf r o = buf (recordIndexEquiv count width hw (r, o)) := rfl

/-- Flat access is recovered from ordinal slicing by Euclidean division:
the byte at flat ordinal `k` is the byte of record `k / width` at offset
`k % width`. -/
theorem flat_eq_recordSlice {count width : ℕ} (hw : 0 < width)
    (buf : Fin (count * width) → ℕ) (k : Fin (count * width)) :
    buf k = recordSlice buf
      ⟨(k : ℕ) / width, (Nat.div_lt_iff_lt_mul hw).mpr k.isLt⟩
      ⟨(k : ℕ) % width, Nat.mod_lt _ hw⟩ := by
  unfold recordSlice
  congr 1
  apply Fin.ext
  show (k : ℕ) = (k : ℕ) / width * width + (k : ℕ) % width
  exact (Nat.div_add_mod' _ _).symm

/-- Order preservation, arithmetic form: flat ordinals compare exactly as
`(record, offset)` pairs compare lexicographically. -/
theorem recordIndex_lt_iff_lex {width r₁ o₁ r₂ o₂ : ℕ}
    (ho₁ : o₁ < width) (ho₂ : o₂ < width) :
    r₁ * width + o₁ < r₂ * width + o₂ ↔
      r₁ < r₂ ∨ (r₁ = r₂ ∧ o₁ < o₂) := by
  constructor
  · intro h
    rcases Nat.lt_trichotomy r₁ r₂ with hr | hr | hr
    · exact Or.inl hr
    · subst hr
      exact Or.inr ⟨rfl, by omega⟩
    · exfalso
      have h1 : (r₂ + 1) * width ≤ r₁ * width :=
        mul_le_mul_left (by omega) width
      have h2 : (r₂ + 1) * width = r₂ * width + width := by ring
      omega
  · rintro (hr | ⟨rfl, ho⟩)
    · have h1 : (r₁ + 1) * width ≤ r₂ * width :=
        mul_le_mul_left (by omega) width
      have h2 : (r₁ + 1) * width = r₁ * width + width := by ring
      omega
    · omega

/-- Order preservation through the bijection: the equivalence maps the
lexicographic order on `(record, offset)` pairs to the flat order. -/
theorem recordIndexEquiv_lt_iff {count width : ℕ} (hw : 0 < width)
    (p q : Fin count × Fin width) :
    recordIndexEquiv count width hw p < recordIndexEquiv count width hw q ↔
      p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2) := by
  obtain ⟨r₁, o₁⟩ := p
  obtain ⟨r₂, o₂⟩ := q
  simpa only [recordIndexEquiv, Equiv.coe_fn_mk, pairToFlat, Fin.lt_def,
    Fin.ext_iff, Fin.val_mk] using
    recordIndex_lt_iff_lex o₁.isLt o₂.isLt

/-- The bytes of record `r`, in offset order, out of the flat stream `f`. -/
def recordBytes (f : ℕ → ℕ) (width r : ℕ) : List ℕ :=
  (List.range width).map fun o => f (r * width + o)

/-- All records in record order, each as its byte chunk. -/
def recordChunks (f : ℕ → ℕ) (count width : ℕ) : List (List ℕ) :=
  (List.range count).map (recordBytes f width)

/-- The flat contiguous traversal of the whole `count * width`-byte
buffer. -/
def flatTraversal (f : ℕ → ℕ) (count width : ℕ) : List ℕ :=
  (List.range (count * width)).map f

/-- Chunked record traversal and flat contiguous traversal produce the
same byte list: identical bytes in identical order. -/
theorem recordChunks_flatten_eq_flatTraversal (f : ℕ → ℕ)
    (count width : ℕ) :
    (recordChunks f count width).flatten = flatTraversal f count width := by
  induction count with
  | zero => simp [recordChunks, flatTraversal]
  | succ c ih =>
    have hmul : (c + 1) * width = c * width + width := by ring
    unfold recordChunks flatTraversal at ih ⊢
    rw [List.range_succ, List.map_append, List.flatten_append, ih, hmul,
      List.range_add, List.map_append, List.map_map]
    simp only [List.map_cons, List.map_nil, List.flatten_cons,
      List.flatten_nil, List.append_nil]
    congr 1

/-- Total length pin: the flat traversal has length `count * width`. -/
theorem flatTraversal_length (f : ℕ → ℕ) (count width : ℕ) :
    (flatTraversal f count width).length = count * width := by
  simp [flatTraversal]

/-- Total length pin: the chunked traversal also has length
`count * width`. -/
theorem recordChunks_flatten_length (f : ℕ → ℕ) (count width : ℕ) :
    ((recordChunks f count width).flatten).length = count * width := by
  rw [recordChunks_flatten_eq_flatTraversal, flatTraversal_length]

/-- Chunk access: offset `o` of record `r` reads byte `r * width + o`. -/
theorem recordBytes_getElem (f : ℕ → ℕ) (width r o : ℕ) (ho : o < width) :
    (recordBytes f width r)[o]'(by simpa [recordBytes] using ho) =
      f (r * width + o) := by
  simp [recordBytes]

/-- Flat access: ordinal `k` of the flat traversal reads byte `k`. -/
theorem flatTraversal_getElem (f : ℕ → ℕ) (count width k : ℕ)
    (hk : k < count * width) :
    (flatTraversal f count width)[k]'(by simpa [flatTraversal] using hk) =
      f k := by
  simp [flatTraversal]

/-- Cross-pattern slicing equality: chunk access at `(r, o)` and flat
access at ordinal `r * width + o` read the same byte. -/
theorem recordBytes_getElem_eq_flatTraversal_getElem (f : ℕ → ℕ)
    (count width r o : ℕ) (hr : r < count) (ho : o < width) :
    (recordBytes f width r)[o]'(by simpa [recordBytes] using ho) =
      (flatTraversal f count width)[r * width + o]'
        (by simpa [flatTraversal] using recordIndex_lt hr ho) := by
  rw [recordBytes_getElem f width r o ho,
    flatTraversal_getElem f count width _ (recordIndex_lt hr ho)]

/-- Non-vacuity: a concrete instance of the bijection, `3` records of
width `5`, record `1`, offset `2`, flat ordinal `7`. -/
theorem recordIndexEquiv_three_five_example :
    recordIndexEquiv 3 5 (by norm_num)
      (⟨1, by norm_num⟩, ⟨2, by norm_num⟩) = ⟨7, by norm_num⟩ := rfl

/-! ## Matched-topology token, opaque and honest

The derived suffix is an opaque parameter of the model.  Nothing is
claimed about how it is derived; the only content is the construct-then-
consume equivalence. -/

section Token

variable {α : Type*}

/-- A matched-topology token over an opaque derived suffix: it carries the
supplied suffix together with the fact that it equals the derived one. -/
structure MatchedToken (derived : α) where
  /-- The suffix supplied at construction time. -/
  supplied : α
  /-- The recorded match against the derived suffix. -/
  matched : supplied = derived

/-- Tokens over the same derived suffix are equal when their supplied
suffixes are. -/
theorem MatchedToken.ext {derived : α} {t₁ t₂ : MatchedToken derived}
    (h : t₁.supplied = t₂.supplied) : t₁ = t₂ := by
  cases t₁
  cases t₂
  cases h
  rfl

/-- The checked token constructor: succeeds exactly when the supplied
suffix equals the derived suffix. -/
def mkToken [DecidableEq α] (derived supplied : α) :
    Option (MatchedToken derived) :=
  if h : supplied = derived then some ⟨supplied, h⟩ else none

/-- Consuming a token yields its supplied suffix. -/
def consumeToken {derived : α} (t : MatchedToken derived) : α :=
  t.supplied

/-- Consumption yields the equality: any token consumes to the derived
suffix. -/
theorem consumeToken_eq_derived {derived : α} (t : MatchedToken derived) :
    consumeToken t = derived := t.matched

/-- The constructor succeeds exactly when the supplied suffix equals the
derived suffix. -/
theorem mkToken_isSome_iff [DecidableEq α] (derived supplied : α) :
    (mkToken derived supplied).isSome ↔ supplied = derived := by
  unfold mkToken
  by_cases hc : supplied = derived
  · rw [dif_pos hc]
    simpa using hc
  · rw [dif_neg hc]
    simpa using hc

/-- The constructor fails exactly when the supplied suffix differs from
the derived suffix. -/
theorem mkToken_eq_none_iff [DecidableEq α] (derived supplied : α) :
    mkToken derived supplied = none ↔ supplied ≠ derived := by
  unfold mkToken
  by_cases hc : supplied = derived
  · rw [dif_pos hc]
    simpa using hc
  · rw [dif_neg hc]
    simpa using hc

/-- Successful construction characterized: the constructor returns `t`
exactly when the supplied suffix matches the derived one and `t` consumes
back to the supplied suffix. -/
theorem mkToken_eq_some_iff [DecidableEq α] (derived supplied : α)
    (t : MatchedToken derived) :
    mkToken derived supplied = some t ↔
      supplied = derived ∧ consumeToken t = supplied := by
  constructor
  · intro h
    unfold mkToken at h
    split at h
    · next hc =>
        obtain rfl := Option.some.inj h
        exact ⟨hc, rfl⟩
    · simp at h
  · rintro ⟨hc, hs⟩
    unfold mkToken
    rw [dif_pos hc]
    congr 1
    exact MatchedToken.ext hs.symm

/-- Consuming a successfully-constructed token yields the checked
equality back: the consumed value is the supplied suffix, and the supplied
suffix equals the derived one. -/
theorem consume_constructed_yields_check [DecidableEq α]
    {derived supplied : α} {t : MatchedToken derived}
    (h : mkToken derived supplied = some t) :
    consumeToken t = supplied ∧ supplied = derived := by
  obtain ⟨hc, hs⟩ := (mkToken_eq_some_iff derived supplied t).mp h
  exact ⟨hs, hc⟩

/-- Construct-then-consume is equivalent to re-checking the equality: the
composite returns `some derived` under exactly the same condition as the
plain equality test. -/
theorem construct_then_consume_eq_recheck [DecidableEq α]
    (derived supplied : α) :
    (mkToken derived supplied).map consumeToken =
      if supplied = derived then some derived else none := by
  unfold mkToken
  by_cases hc : supplied = derived
  · rw [dif_pos hc, if_pos hc]
    subst hc
    rfl
  · rw [dif_neg hc, if_neg hc]
    rfl

end Token

/-- Non-vacuity: construction succeeds on a matched pair. -/
theorem mkToken_nat_matched_isSome : (mkToken (7 : ℕ) 7).isSome := rfl

/-- Non-vacuity: construction fails on a mismatched pair. -/
theorem mkToken_nat_mismatched_eq_none : mkToken (7 : ℕ) 5 = none := rfl

/-- Non-vacuity at the byte-suffix instantiation: for any 32-byte suffix,
supplying the derived suffix itself constructs a token. -/
theorem mkToken_byteSuffix_self_isSome (s : Fin 32 → ℕ) :
    (mkToken (α := Fin 32 → ℕ) s s).isSome := by
  rw [mkToken_isSome_iff]

/-! ## Named, unproved correspondence obligations

Everything above is a fact about the models in this file only.  The
following interfaces are *not* proved here and are not claimed:

1. `serializer-zero-scan-layout`: that the deployed serializer's zero scan
   starts after the five 32-byte public-salt slots and reads exactly this
   400-byte tail as exactly these 50 aligned words, with `u64` loads decoding
   as `packLE8` of those bytes.
2. `merkle-child-buffer-layout`: that the deployed child-hash builder
   writes exactly `0x12 ++ c0 ++ c1 ++ c2 ++ c3` into its 129-byte buffer.
3. `record-iterator-layout`: that the deployed record iterator visits
   exactly `count` records of exactly `width` bytes over a buffer of
   exactly `count * width` bytes at these offsets.
4. `token-construct-consume-correspondence`: that the deployed token
   type's constructor and consumer implement `mkToken`/`consumeToken`,
   and anything at all about how the derived suffix is computed.

Rust `u8`/`u64` arithmetic is likewise identified with `ℕ` plus explicit
bounds only through these obligations. -/

#print axioms packLE8
#print axioms packLE8_eq_zero_iff
#print axioms packLE8_lt_two_pow_64
#print axioms region_bytes_eq_words_times_width
#print axioms wordIndex
#print axioms packedWord
#print axioms packedWord_lt_two_pow_64
#print axioms packedWords_all_zero_iff_bytes_all_zero
#print axioms packLE8_bound_hypothesis_nonvacuous
#print axioms append_apply_val
#print axioms merkleChildBufferDirect
#print axioms merkleChildBufferAppend
#print axioms buffer_bytes_eq_one_add_four_children
#print axioms merkleChildBufferDirect_apply_zero
#print axioms merkleChildBufferDirect_eq_append
#print axioms merkleChildBufferDirect_lt_256
#print axioms merkleChildBuffer_bound_hypothesis_nonvacuous
#print axioms recordIndex_lt
#print axioms sliceIndex_lt
#print axioms recordSlice
#print axioms recordSlice_eq_buffer_at
#print axioms pairToFlat
#print axioms flatToPair
#print axioms recordIndexEquiv
#print axioms recordSlice_eq_buffer_comp_equiv
#print axioms flat_eq_recordSlice
#print axioms recordIndex_lt_iff_lex
#print axioms recordIndexEquiv_lt_iff
#print axioms recordBytes
#print axioms recordChunks
#print axioms flatTraversal
#print axioms recordChunks_flatten_eq_flatTraversal
#print axioms flatTraversal_length
#print axioms recordChunks_flatten_length
#print axioms recordBytes_getElem
#print axioms flatTraversal_getElem
#print axioms recordBytes_getElem_eq_flatTraversal_getElem
#print axioms recordIndexEquiv_three_five_example
#print axioms MatchedToken.ext
#print axioms mkToken
#print axioms consumeToken
#print axioms consumeToken_eq_derived
#print axioms mkToken_isSome_iff
#print axioms mkToken_eq_none_iff
#print axioms mkToken_eq_some_iff
#print axioms consume_constructed_yields_check
#print axioms construct_then_consume_eq_recheck
#print axioms mkToken_nat_matched_isSome
#print axioms mkToken_nat_mismatched_eq_none
#print axioms mkToken_byteSuffix_self_isSome

end AspisV5CuSerializationEquivalences

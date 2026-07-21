import AspisFormal.V5M31RawMulReduction

/-!
# Exact four-product batching for the v5 Good-gate dot products

The verifier's `qm31_m31_dot` kernel processes one output limb in blocks of
four canonical M31 products.  It reduces every four-product `u64` subtotal,
accumulates the six canonical subtotals, and reduces once more.  This leaf
proves that exact 24-term graph is the ordinary M31 dot product.

The overflow argument is kept at the deployed arity: `4 * (P - 1)^2 < 2^64`.
Nothing is approximated, and the theorem is universal in all 48 canonical
input limbs.
-/

namespace AspisV5GoodGateDotBatching

open AspisV5ComponentCRejectionSampler
open AspisV5ComponentCQM31TowerExact
open AspisV5ComponentCQM31RustFormulaSeam
open AspisV5M31RawMulReduction

/-- The deployed flattening of block `0..5` and slot `0..3` into `0..23`. -/
def blockIndex (block : Fin 6) (slot : Fin 4) : Fin 24 :=
  ⟨4 * block + slot, by omega⟩

/-- One unreduced four-product `u64` subtotal. -/
def blockRaw (left right : Fin 24 → Nat) (block : Fin 6) : Nat :=
  ∑ slot : Fin 4, left (blockIndex block slot) * right (blockIndex block slot)

/-- One canonical subtotal, exactly `M31::reduce_u64(raw)` in the Rust loop. -/
def blockReduced (left right : Fin 24 → Nat) (block : Fin 6) : Nat :=
  rawReduceU64 (blockRaw left right block)

/-- The six canonical block results accumulated in the outer `u64`. -/
def outerRaw (left right : Fin 24 → Nat) : Nat :=
  ∑ block : Fin 6, blockReduced left right block

/-- The final output limb of the deployed 24-entry batched dot kernel. -/
def batchedDot24 (left right : Fin 24 → Nat) : Nat :=
  rawReduceU64 (outerRaw left right)

/-- The ordinary unreduced 24-term dot product. -/
def ordinaryDot24 (left right : Fin 24 → Nat) : Nat :=
  ∑ index : Fin 24, left index * right index

theorem blockIndex_eq_finProdFinEquiv (block : Fin 6) (slot : Fin 4) :
    blockIndex block slot = finProdFinEquiv (block, slot) := by
  apply Fin.ext
  simp [blockIndex, finProdFinEquiv]
  omega

/-- The six-by-four loop nest visits each of the 24 dot coordinates exactly
once and in the same flattening used by Rust. -/
theorem blockRaw_partition (left right : Fin 24 → Nat) :
    (∑ block : Fin 6, blockRaw left right block) = ordinaryDot24 left right := by
  unfold ordinaryDot24 blockRaw
  calc
    (∑ block : Fin 6, ∑ slot : Fin 4,
        left (blockIndex block slot) * right (blockIndex block slot)) =
        ∑ pair : Fin 6 × Fin 4,
          left (blockIndex pair.1 pair.2) * right (blockIndex pair.1 pair.2) :=
      (Fintype.sum_prod_type
        (fun pair : Fin 6 × Fin 4 =>
          left (blockIndex pair.1 pair.2) * right (blockIndex pair.1 pair.2))).symm
    _ = ∑ pair : Fin 6 × Fin 4,
        left (finProdFinEquiv pair) * right (finProdFinEquiv pair) := by
      apply Finset.sum_congr rfl
      intro pair _
      rw [blockIndex_eq_finProdFinEquiv]
    _ = ∑ index : Fin 24, left index * right index :=
      (finProdFinEquiv : Fin 6 × Fin 4 ≃ Fin 24).sum_comp
        (fun index => left index * right index)

theorem ordinaryDot24_cast (left right : Fin 24 → Nat) :
    ((ordinaryDot24 left right : Nat) : M31Exact) =
      ∑ index : Fin 24, (left index : M31Exact) * (right index : M31Exact) := by
  rw [ordinaryDot24, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [Nat.cast_mul]

/-- Four maximal canonical products fit in one `u64`, exactly the bound cited
beside `qm31_m31_dot` in `field.rs`. -/
theorem four_max_products_lt_u64 : 4 * (P - 1) ^ 2 < 2 ^ 64 := by
  norm_num [P]

private theorem canonical_product_le_max {x y : Nat} (hx : x < P) (hy : y < P) :
    x * y ≤ (P - 1) ^ 2 := by
  have hx' : x ≤ P - 1 := Nat.le_pred_of_lt hx
  have hy' : y ≤ P - 1 := Nat.le_pred_of_lt hy
  simpa [pow_two] using Nat.mul_le_mul hx' hy'

/-- Every deployed four-product subtotal fits in `u64`. -/
theorem blockRaw_lt_u64 (left right : Fin 24 → Nat)
    (hleft : ∀ i, left i < P) (hright : ∀ i, right i < P) (block : Fin 6) :
    blockRaw left right block < 2 ^ 64 := by
  have h0 := canonical_product_le_max (hleft (blockIndex block 0))
    (hright (blockIndex block 0))
  have h1 := canonical_product_le_max (hleft (blockIndex block 1))
    (hright (blockIndex block 1))
  have h2 := canonical_product_le_max (hleft (blockIndex block 2))
    (hright (blockIndex block 2))
  have h3 := canonical_product_le_max (hleft (blockIndex block 3))
    (hright (blockIndex block 3))
  rw [blockRaw, Fin.sum_univ_four]
  have hmax := four_max_products_lt_u64
  omega

/-- Every reduced block is a canonical M31 limb. -/
theorem blockReduced_lt_P (left right : Fin 24 → Nat)
    (hleft : ∀ i, left i < P) (hright : ∀ i, right i < P) (block : Fin 6) :
    blockReduced left right block < P := by
  exact rawReduceU64_canonical _ (blockRaw_lt_u64 left right hleft hright block)

/-- Six canonical block results fit in the final outer `u64` accumulator. -/
theorem outerRaw_lt_u64 (left right : Fin 24 → Nat)
    (hleft : ∀ i, left i < P) (hright : ∀ i, right i < P) :
    outerRaw left right < 2 ^ 64 := by
  calc
    outerRaw left right ≤ ∑ _block : Fin 6, (P - 1) := by
      apply Finset.sum_le_sum
      intro block _
      exact Nat.le_pred_of_lt (blockReduced_lt_P left right hleft hright block)
    _ = 6 * (P - 1) := by simp
    _ < 2 ^ 64 := by norm_num [P]

/-- Reducing the six four-product chunks and then reducing their sum gives
exactly the ordinary 24-term field dot product. -/
theorem batchedDot24_cast_eq_ordinary (left right : Fin 24 → Nat)
    (hleft : ∀ i, left i < P) (hright : ∀ i, right i < P) :
    ((batchedDot24 left right : Nat) : M31Exact) =
      ∑ index : Fin 24, (left index : M31Exact) * (right index : M31Exact) := by
  rw [batchedDot24, rawReduceU64_residue _ (outerRaw_lt_u64 left right hleft hright)]
  rw [outerRaw, Nat.cast_sum]
  calc
    (∑ block : Fin 6, (blockReduced left right block : M31Exact)) =
        ∑ block : Fin 6, (blockRaw left right block : M31Exact) := by
      apply Finset.sum_congr rfl
      intro block _
      exact rawReduceU64_residue _ (blockRaw_lt_u64 left right hleft hright block)
    _ = ∑ index : Fin 24,
        (left index : M31Exact) * (right index : M31Exact) := by
      rw [← ordinaryDot24_cast, ← Nat.cast_sum, blockRaw_partition]

/-- Nat-level form of the same result: the deployed output word is the
canonical residue of the ordinary 24-product sum. -/
theorem batchedDot24_eq_ordinary_mod (left right : Fin 24 → Nat)
    (hleft : ∀ i, left i < P) (hright : ∀ i, right i < P) :
    batchedDot24 left right = ordinaryDot24 left right % P := by
  have hcast := batchedDot24_cast_eq_ordinary left right hleft hright
  have hcanon : batchedDot24 left right < P :=
    rawReduceU64_canonical _ (outerRaw_lt_u64 left right hleft hright)
  have hcast' : ((batchedDot24 left right : Nat) : M31Exact) =
      ((ordinaryDot24 left right : Nat) : M31Exact) := by
    rw [ordinaryDot24_cast]
    exact hcast
  rw [ZMod.natCast_eq_natCast_iff] at hcast'
  change batchedDot24 left right % P = ordinaryDot24 left right % P at hcast'
  rw [Nat.mod_eq_of_lt hcanon] at hcast'
  exact hcast'

/-- Load-bearing maximal-input tooth: every inner block reaches the audited
four-product bound, and the universal theorem still returns the correct field
dot. -/
theorem maximal_inputs_tooth :
    batchedDot24 (fun _ => P - 1) (fun _ => P - 1) =
      ordinaryDot24 (fun _ => P - 1) (fun _ => P - 1) % P := by
  apply batchedDot24_eq_ordinary_mod
  · intro; norm_num [P]
  · intro; norm_num [P]

/-! ## Exact deployed variable support and paired base/xor output

For shift `s = 0..11`, the parity-strided Rust loop visits exactly
`19 + s / 2` logical products.  Thus the live arity ranges from 19 through 24.
The definitions below zero-pad that prefix to the already-audited 24-entry
kernel.  They also model the paired base/xor loop with two independent raw
accumulators and the same per-four-product reduction boundaries.  The suffix
xor mask is supplied by the caller; in the deployed factored suffix it is six
(`0b000110`), corresponding to xor 12 before the low row bit is factored.
-/

/-- Number of parity-supported products at one deployed shift. -/
def deployedSupportCount (shift : Fin 12) : Nat := 19 + shift / 2

/-- The logical product at position `logical` reads this natural coordinate. -/
def deployedSupportIndex (shift : Fin 12) (logical : Nat) : Nat :=
  shift % 2 + 2 * logical

/-- The exclusive natural-coordinate endpoint used by the Rust loop. -/
def deployedSupportEnd (shift : Fin 12) : Nat := 37 + shift

/-- Every deployed shift has between 19 and 24 live products. -/
theorem deployedSupportCount_bounds (shift : Fin 12) :
    19 ≤ deployedSupportCount shift ∧ deployedSupportCount shift ≤ 24 := by
  unfold deployedSupportCount
  constructor
  · omega
  · have hshift := shift.isLt
    omega

/-- The endpoint arities are attained: shift zero has 19 products and shift
eleven has 24. -/
theorem deployedSupportCount_endpoints :
    deployedSupportCount (0 : Fin 12) = 19 ∧
      deployedSupportCount (11 : Fin 12) = 24 := by
  norm_num [deployedSupportCount]

/-- Every logical position below the exact support count is visited before the
Rust loop's exclusive endpoint. -/
theorem deployedSupportIndex_lt_end (shift : Fin 12) (logical : Nat)
    (hlogical : logical < deployedSupportCount shift) :
    deployedSupportIndex shift logical < deployedSupportEnd shift := by
  have hshift := shift.isLt
  unfold deployedSupportCount deployedSupportIndex deployedSupportEnd at *
  omega

/-- The strided traversal preserves the shift parity. -/
theorem deployedSupportIndex_mod_two (shift : Fin 12) (logical : Nat) :
    deployedSupportIndex shift logical % 2 = shift % 2 := by
  unfold deployedSupportIndex
  omega

/-- Conversely, every coordinate below the endpoint with the deployed parity
has a logical index below the exact support count. -/
theorem deployedSupportIndex_complete (shift : Fin 12) (index : Nat)
    (hindex : index < deployedSupportEnd shift)
    (hparity : index % 2 = shift % 2) :
    ∃ logical, logical < deployedSupportCount shift ∧
      index = deployedSupportIndex shift logical := by
  refine ⟨index / 2, ?_, ?_⟩
  · have hshift := shift.isLt
    unfold deployedSupportCount deployedSupportEnd at *
    omega
  · unfold deployedSupportIndex
    omega

/-- Zero-pad a natural-number prefix to the fixed 24-entry batching shape. -/
def zeroPad24 (count : Nat) (values : Nat → Nat) (index : Fin 24) : Nat :=
  if index < count then values index else 0

theorem zeroPad24_active (count : Nat) (values : Nat → Nat) (index : Fin 24)
    (hindex : (index : Nat) < count) :
    zeroPad24 count values index = values index := by
  simp [zeroPad24, hindex]

theorem zeroPad24_inactive (count : Nat) (values : Nat → Nat) (index : Fin 24)
    (hindex : count ≤ (index : Nat)) :
    zeroPad24 count values index = 0 := by
  simp [zeroPad24, Nat.not_lt.mpr hindex]

/-- Canonical live prefix values yield a canonical zero-padded array. -/
theorem zeroPad24_canonical (count : Nat) (values : Nat → Nat)
    (hvalues : ∀ index, index < count → values index < P) :
    ∀ index, zeroPad24 count values index < P := by
  intro index
  by_cases hindex : (index : Nat) < count
  · rw [zeroPad24_active count values index hindex]
    exact hvalues index hindex
  · rw [zeroPad24_inactive count values index (Nat.le_of_not_gt hindex)]
    norm_num [P]

/-- Ordinary dot product of two padded arrays is exactly the live prefix dot;
the absent tail, including the absent sixth block at arities 19 and 20, is
provably zero. -/
theorem ordinaryDot24_zeroPad_eq_prefix (count : Nat) (hcount : count ≤ 24)
    (left right : Nat → Nat) :
    ordinaryDot24 (zeroPad24 count left) (zeroPad24 count right) =
      ∑ index ∈ Finset.range count, left index * right index := by
  have hfilter :
      (Finset.range 24).filter (fun index => index < count) =
        Finset.range count := by
    ext index
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  unfold ordinaryDot24
  calc
    (∑ index : Fin 24,
        zeroPad24 count left index * zeroPad24 count right index) =
        ∑ index : Fin 24,
          if (index : Nat) < count then left index * right index else 0 := by
      apply Finset.sum_congr rfl
      intro index _
      by_cases hindex : (index : Nat) < count <;>
        simp [zeroPad24, hindex]
    _ = ∑ index ∈ Finset.range 24,
        if index < count then left index * right index else 0 := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro index hindex
      have hindex24 := Finset.mem_range.mp hindex
      simp [hindex24]
    _ = ∑ index ∈ (Finset.range 24).filter (fun index => index < count),
        left index * right index := by
      rw [Finset.sum_filter]
    _ = ∑ index ∈ Finset.range count, left index * right index := by
      rw [hfilter]

/-- One paired block has independent base and xor raw accumulators. -/
def pairedBlockReduced (left baseWeights xorWeights : Fin 24 → Nat) (block : Fin 6) :
    Nat × Nat :=
  (blockReduced left baseWeights block, blockReduced left xorWeights block)

/-- The paired loop accumulates the six canonical subtotals independently. -/
def pairedOuterRaw (left baseWeights xorWeights : Fin 24 → Nat) : Nat × Nat :=
  (∑ block : Fin 6, (pairedBlockReduced left baseWeights xorWeights block).1,
    ∑ block : Fin 6, (pairedBlockReduced left baseWeights xorWeights block).2)

/-- Ordered paired output: lane zero is base and lane one is the factored xor
suffix. -/
def pairedBatchedDot24 (left baseWeights xorWeights : Fin 24 → Nat) : Nat × Nat :=
  (rawReduceU64 (pairedOuterRaw left baseWeights xorWeights).1,
    rawReduceU64 (pairedOuterRaw left baseWeights xorWeights).2)

/-- Sharing the traversal changes neither output nor their `[base, xor]`
ordering. -/
theorem pairedBatchedDot24_eq_separate
    (left baseWeights xorWeights : Fin 24 → Nat) :
    pairedBatchedDot24 left baseWeights xorWeights =
      (batchedDot24 left baseWeights, batchedDot24 left xorWeights) := by
  rfl

/-- Both paired output lanes are the corresponding ordinary field dot. -/
theorem pairedBatchedDot24_cast_eq_ordinary
    (left baseWeights xorWeights : Fin 24 → Nat)
    (hleft : ∀ index, left index < P)
    (hbase : ∀ index, baseWeights index < P)
    (hxor : ∀ index, xorWeights index < P) :
    (((pairedBatchedDot24 left baseWeights xorWeights).1 : Nat) : M31Exact) =
        ∑ index : Fin 24, (left index : M31Exact) * (baseWeights index : M31Exact) ∧
      (((pairedBatchedDot24 left baseWeights xorWeights).2 : Nat) : M31Exact) =
        ∑ index : Fin 24, (left index : M31Exact) * (xorWeights index : M31Exact) := by
  rw [pairedBatchedDot24_eq_separate]
  exact ⟨batchedDot24_cast_eq_ordinary left baseWeights hleft hbase,
    batchedDot24_cast_eq_ordinary left xorWeights hleft hxor⟩

/-- Exact Nat-level semantics of the live 19-to-24-product paired traversal,
including zero padding of every partial tail block. -/
theorem pairedDeployedDot_eq_prefix_mod (shift : Fin 12)
    (left baseWeights xorWeights : Nat → Nat)
    (hleft : ∀ index, index < deployedSupportCount shift → left index < P)
    (hbase : ∀ index, index < deployedSupportCount shift → baseWeights index < P)
    (hxor : ∀ index, index < deployedSupportCount shift → xorWeights index < P) :
    pairedBatchedDot24
        (zeroPad24 (deployedSupportCount shift) left)
        (zeroPad24 (deployedSupportCount shift) baseWeights)
        (zeroPad24 (deployedSupportCount shift) xorWeights) =
      ((∑ index ∈ Finset.range (deployedSupportCount shift),
          left index * baseWeights index) % P,
        (∑ index ∈ Finset.range (deployedSupportCount shift),
          left index * xorWeights index) % P) := by
  rw [pairedBatchedDot24_eq_separate]
  have hcount := (deployedSupportCount_bounds shift).2
  have hleftPad := zeroPad24_canonical (deployedSupportCount shift) left hleft
  have hbasePad := zeroPad24_canonical (deployedSupportCount shift) baseWeights hbase
  have hxorPad := zeroPad24_canonical (deployedSupportCount shift) xorWeights hxor
  rw [batchedDot24_eq_ordinary_mod _ _ hleftPad hbasePad,
    batchedDot24_eq_ordinary_mod _ _ hleftPad hxorPad,
    ordinaryDot24_zeroPad_eq_prefix _ hcount,
    ordinaryDot24_zeroPad_eq_prefix _ hcount]

/-- Exact scalar-limb projection used by the deployed paired base/xor
traversal.  Logical position `i` reads natural coordinate
`shift % 2 + 2*i`; the second weight lane reads the six-coordinate suffix at
the factored XOR-12 index `coordinate XOR 6`.  This theorem pins the pure
arithmetic and ordering, while equality with the Rust arrays remains an
executable-correspondence obligation. -/
theorem pairedDeployedBaseXorProjection_eq_mod (shift : Fin 12)
    (natural suffixWeights : Nat → Nat)
    (hnatural : ∀ index, natural index < P)
    (hsuffix : ∀ index, suffixWeights index < P) :
    pairedBatchedDot24
        (zeroPad24 (deployedSupportCount shift)
          (fun logical => natural (deployedSupportIndex shift logical)))
        (zeroPad24 (deployedSupportCount shift)
          (fun logical => suffixWeights (deployedSupportIndex shift logical)))
        (zeroPad24 (deployedSupportCount shift)
          (fun logical => suffixWeights (Nat.xor (deployedSupportIndex shift logical) 6))) =
      ((∑ logical ∈ Finset.range (deployedSupportCount shift),
          natural (deployedSupportIndex shift logical) *
            suffixWeights (deployedSupportIndex shift logical)) % P,
        (∑ logical ∈ Finset.range (deployedSupportCount shift),
          natural (deployedSupportIndex shift logical) *
            suffixWeights (Nat.xor (deployedSupportIndex shift logical) 6)) % P) := by
  exact pairedDeployedDot_eq_prefix_mod shift
    (fun logical => natural (deployedSupportIndex shift logical))
    (fun logical => suffixWeights (deployedSupportIndex shift logical))
    (fun logical => suffixWeights (Nat.xor (deployedSupportIndex shift logical) 6))
    (fun _ _ => hnatural _)
    (fun _ _ => hsuffix _)
    (fun _ _ => hsuffix _)

/-! ## Shared deployed three-bit prefixes -/

/-- The optimized shared-middle formulas are exactly the literal MLE prefixes
`111` and `010`.  The second equality is the load-bearing expansion
`(1-p0)(1-p2) = 1-p0-p2+p0*p2`. -/
theorem deployedThreeBitPrefixes_eq_literal
    {R : Type*} [CommRing R] (p0 p1 p2 : R) :
    p1 * (p0 * p2) = p0 * p1 * p2 ∧
      p1 * (((1 : R) - p0) - p2 + p0 * p2) =
        ((1 : R) - p0) * p1 * ((1 : R) - p2) := by
  constructor <;> ring

/-- Omitting the cross term from the shared `010` prefix is concretely wrong
away from Boolean points. -/
theorem deployedThreeBitPrefixes_cross_term_tooth :
    (3 : M31Exact) * (((1 : M31Exact) - 2) - 5) ≠
      ((1 : M31Exact) - 2) * 3 * ((1 : M31Exact) - 5) := by
  intro h
  norm_num at h
  have hmod : (-18 : Int) % 2147483647 = 12 % 2147483647 :=
    (ZMod.intCast_eq_intCast_iff' (-18) 12 2147483647).mp h
  norm_num at hmod

/-! ## Fused query-kernel M31 multiply-add -/

/-- Raw nonnegative input to the reducer for `left * right + addend`. -/
def fusedMulAddRaw (left right addend : Nat) : Nat := left * right + addend

/-- One-reduction model of the query-kernel multiply-add. -/
def fusedMulAdd (left right addend : Nat) : Nat :=
  rawReduceU64 (fusedMulAddRaw left right addend)

/-- Exact maximal raw fused multiply-add over canonical M31 words. -/
def fusedMulAddMaxRaw : Nat := (P - 1) ^ 2 + (P - 1)

theorem fusedMulAddMaxRaw_value : fusedMulAddMaxRaw = 4611686011984936962 := by
  norm_num [fusedMulAddMaxRaw, P]

/-- The symbolic maximum used by Rust's compile-time bound is exact. -/
theorem fusedMulAddRaw_le_max (left right addend : Nat)
    (hleft : left < P) (hright : right < P) (haddend : addend < P) :
    fusedMulAddRaw left right addend ≤ fusedMulAddMaxRaw := by
  have hproduct := canonical_product_le_max hleft hright
  have haddend' := Nat.le_pred_of_lt haddend
  unfold fusedMulAddRaw fusedMulAddMaxRaw
  omega

/-- Every canonical fused multiply-add lies strictly below `2^62`. -/
theorem fusedMulAddRaw_lt_two_pow62 (left right addend : Nat)
    (hleft : left < P) (hright : right < P) (haddend : addend < P) :
    fusedMulAddRaw left right addend < 2 ^ 62 := by
  exact lt_of_le_of_lt (fusedMulAddRaw_le_max left right addend hleft hright haddend)
    (by norm_num [fusedMulAddMaxRaw, P])

/-- The one-reduction fused multiply-add returns a canonical M31 word. -/
theorem fusedMulAdd_canonical (left right addend : Nat)
    (hleft : left < P) (hright : right < P) (haddend : addend < P) :
    fusedMulAdd left right addend < P := by
  exact rawReduceU64_canonical _
    (lt_trans (fusedMulAddRaw_lt_two_pow62 left right addend hleft hright haddend)
      (by norm_num))

/-- The fused reducer has the intended multiply-add residue. -/
theorem fusedMulAdd_cast (left right addend : Nat)
    (hleft : left < P) (hright : right < P) (haddend : addend < P) :
    ((fusedMulAdd left right addend : Nat) : M31Exact) =
      (left : M31Exact) * (right : M31Exact) + (addend : M31Exact) := by
  rw [fusedMulAdd, rawReduceU64_residue _
    (lt_trans (fusedMulAddRaw_lt_two_pow62 left right addend hleft hright haddend)
      (by norm_num))]
  simp [fusedMulAddRaw]

/-- At the canonical-word level the fused operation is exactly the predecessor
`addend.add(left.mul(right))`, including its canonical representative. -/
theorem fusedMulAdd_eq_mul_then_add (left right addend : Nat)
    (hleft : left < P) (hright : right < P) (haddend : addend < P) :
    fusedMulAdd left right addend = rawM31Add addend (rawM31Mul left right) := by
  rw [fusedMulAdd, rawReduceU64_eq_mod _
    (lt_trans (fusedMulAddRaw_lt_two_pow62 left right addend hleft hright haddend)
      (by norm_num))]
  rw [rawM31Add_eq_mod haddend (rawM31Mul_canonical hleft hright)]
  rw [rawM31Mul, rawReduceU64_eq_mod _ (canonicalMul_lt_two_pow64 hleft hright)]
  simp [fusedMulAddRaw, Nat.add_mod, Nat.add_comm]

/-- Maximal canonical inputs attain the audited raw bound and reduce to zero. -/
theorem fusedMulAdd_max_tooth :
    fusedMulAddRaw (P - 1) (P - 1) (P - 1) = 4611686011984936962 ∧
      fusedMulAdd (P - 1) (P - 1) (P - 1) = 0 := by
  constructor
  · norm_num [fusedMulAddRaw, P]
  · rw [fusedMulAdd, rawReduceU64_eq_mod _ (by norm_num [fusedMulAddRaw, P])]
    norm_num [fusedMulAddRaw, P]

/-! ## Fused fraction-free M31 update

The verifier's M31 elimination kernel fuses one fraction-free update into one
call to the existing `u64` reducer.  This section models only that arithmetic
expression.  It neither identifies the model with Rust nor proves the
surrounding elimination algorithm correct.
-/

/-- Exact lower endpoint of the fused raw numerator over four canonical M31
inputs. -/
def fractionFreeMinRaw : Nat := P ^ 2 - (P - 1) ^ 2

/-- Exact upper endpoint of the fused raw numerator over four canonical M31
inputs. -/
def fractionFreeMaxRaw : Nat := P ^ 2 + (P - 1) ^ 2

/-- The nonnegative raw numerator passed to `reduce_u64`. -/
def fractionFreeRaw
    (value pivot leading pivotRowValue : Nat) : Nat :=
  value * pivot + P ^ 2 - leading * pivotRowValue

/-- The mathematical model of the fused M31 fraction-free update. -/
def fusedFractionFreeUpdate
    (value pivot leading pivotRowValue : Nat) : Nat :=
  rawReduceU64 (fractionFreeRaw value pivot leading pivotRowValue)

theorem fractionFreeMinRaw_value : fractionFreeMinRaw = 4294967293 := by
  norm_num [fractionFreeMinRaw, P]

theorem fractionFreeMaxRaw_value :
    fractionFreeMaxRaw = 9223372023969873925 := by
  norm_num [fractionFreeMaxRaw, P]

/-- Adding `P^2` makes the natural-number subtraction exact for every four
canonical inputs. -/
theorem fractionFree_negative_le_positive
    (value pivot leading pivotRowValue : Nat)
    (hleading : leading < P) (hpivotRow : pivotRowValue < P) :
    leading * pivotRowValue ≤ value * pivot + P ^ 2 := by
  have hnegative := canonical_product_le_max hleading hpivotRow
  have hstrict : (P - 1) ^ 2 < P ^ 2 := by norm_num [P]
  omega

/-- The raw numerator lies in the exact closed interval used by the verifier's
compile-time bounds. -/
theorem fractionFreeRaw_bounds
    (value pivot leading pivotRowValue : Nat)
    (hvalue : value < P) (hpivot : pivot < P)
    (hleading : leading < P) (hpivotRow : pivotRowValue < P) :
    fractionFreeMinRaw ≤
        fractionFreeRaw value pivot leading pivotRowValue ∧
      fractionFreeRaw value pivot leading pivotRowValue ≤ fractionFreeMaxRaw := by
  have hpositive := canonical_product_le_max hvalue hpivot
  have hnegative := canonical_product_le_max hleading hpivotRow
  have hsub := fractionFree_negative_le_positive value pivot leading pivotRowValue
    hleading hpivotRow
  unfold fractionFreeMinRaw fractionFreeMaxRaw fractionFreeRaw
  omega

/-- Both interval endpoints are attained by canonical inputs, so the bounds
are exact rather than merely conservative. -/
theorem fractionFreeRaw_endpoints_attained :
    fractionFreeRaw 0 0 (P - 1) (P - 1) = fractionFreeMinRaw ∧
      fractionFreeRaw (P - 1) (P - 1) 0 0 = fractionFreeMaxRaw := by
  constructor
  · simp [fractionFreeRaw, fractionFreeMinRaw]
  · simp [fractionFreeRaw, fractionFreeMaxRaw, Nat.add_comm]

theorem fractionFreeMaxRaw_lt_two_pow63 : fractionFreeMaxRaw < 2 ^ 63 := by
  norm_num [fractionFreeMaxRaw, P]

theorem fractionFreeMaxRaw_lt_two_pow64 : fractionFreeMaxRaw < 2 ^ 64 := by
  norm_num [fractionFreeMaxRaw, P]

/-- Every canonical fused numerator fits below `2^63`, hence in `u64`. -/
theorem fractionFreeRaw_lt_two_pow63
    (value pivot leading pivotRowValue : Nat)
    (hvalue : value < P) (hpivot : pivot < P)
    (hleading : leading < P) (hpivotRow : pivotRowValue < P) :
    fractionFreeRaw value pivot leading pivotRowValue < 2 ^ 63 := by
  exact lt_of_le_of_lt
    (fractionFreeRaw_bounds value pivot leading pivotRowValue
      hvalue hpivot hleading hpivotRow).2
    fractionFreeMaxRaw_lt_two_pow63

theorem fractionFreeRaw_lt_two_pow64
    (value pivot leading pivotRowValue : Nat)
    (hvalue : value < P) (hpivot : pivot < P)
    (hleading : leading < P) (hpivotRow : pivotRowValue < P) :
    fractionFreeRaw value pivot leading pivotRowValue < 2 ^ 64 := by
  exact lt_trans
    (fractionFreeRaw_lt_two_pow63 value pivot leading pivotRowValue
      hvalue hpivot hleading hpivotRow)
    (by norm_num)

/-- The fused reducer returns a canonical M31 word for all canonical inputs. -/
theorem fusedFractionFreeUpdate_canonical
    (value pivot leading pivotRowValue : Nat)
    (hvalue : value < P) (hpivot : pivot < P)
    (hleading : leading < P) (hpivotRow : pivotRowValue < P) :
    fusedFractionFreeUpdate value pivot leading pivotRowValue < P := by
  exact rawReduceU64_canonical _
    (fractionFreeRaw_lt_two_pow64 value pivot leading pivotRowValue
      hvalue hpivot hleading hpivotRow)

/-- In the exact M31 field, adding `P^2` disappears and the fused reducer is
the intended fraction-free update `value*pivot - leading*pivotRowValue`. -/
theorem fusedFractionFreeUpdate_cast
    (value pivot leading pivotRowValue : Nat)
    (hvalue : value < P) (hpivot : pivot < P)
    (hleading : leading < P) (hpivotRow : pivotRowValue < P) :
    ((fusedFractionFreeUpdate value pivot leading pivotRowValue : Nat) : M31Exact) =
      (value : M31Exact) * (pivot : M31Exact) -
        (leading : M31Exact) * (pivotRowValue : M31Exact) := by
  rw [fusedFractionFreeUpdate, rawReduceU64_residue _
    (fractionFreeRaw_lt_two_pow64 value pivot leading pivotRowValue
      hvalue hpivot hleading hpivotRow)]
  unfold fractionFreeRaw
  rw [Nat.cast_sub (fractionFree_negative_le_positive
    value pivot leading pivotRowValue hleading hpivotRow)]
  have hmodulus : (2147483647 : M31Exact) = 0 := by
    exact ZMod.natCast_self 2147483647
  push_cast
  rw [hmodulus]
  ring

/-- Lower-endpoint tooth: zero positive product and maximal negative product
reduce to the canonical representative `P - 1` of minus one. -/
theorem fusedFractionFreeUpdate_min_tooth :
    fractionFreeRaw 0 0 (P - 1) (P - 1) = 4294967293 ∧
      fusedFractionFreeUpdate 0 0 (P - 1) (P - 1) = P - 1 := by
  constructor
  · rw [fractionFreeRaw_endpoints_attained.1, fractionFreeMinRaw_value]
  · unfold fusedFractionFreeUpdate
    rw [fractionFreeRaw_endpoints_attained.1, fractionFreeMinRaw_value,
      rawReduceU64_eq_mod 4294967293 (by norm_num)]
    norm_num [P]

/-- Upper-endpoint tooth: maximal positive product and zero negative product
reduce to one. -/
theorem fusedFractionFreeUpdate_max_tooth :
    fractionFreeRaw (P - 1) (P - 1) 0 0 = 9223372023969873925 ∧
      fusedFractionFreeUpdate (P - 1) (P - 1) 0 0 = 1 := by
  constructor
  · rw [fractionFreeRaw_endpoints_attained.2, fractionFreeMaxRaw_value]
  · unfold fusedFractionFreeUpdate
    rw [fractionFreeRaw_endpoints_attained.2, fractionFreeMaxRaw_value,
      rawReduceU64_eq_mod 9223372023969873925 (by norm_num)]
    norm_num [P]

#print axioms AspisV5GoodGateDotBatching.blockIndex_eq_finProdFinEquiv
#print axioms AspisV5GoodGateDotBatching.blockRaw_partition
#print axioms AspisV5GoodGateDotBatching.ordinaryDot24_cast
#print axioms AspisV5GoodGateDotBatching.four_max_products_lt_u64
#print axioms AspisV5GoodGateDotBatching.blockRaw_lt_u64
#print axioms AspisV5GoodGateDotBatching.blockReduced_lt_P
#print axioms AspisV5GoodGateDotBatching.outerRaw_lt_u64
#print axioms AspisV5GoodGateDotBatching.batchedDot24_cast_eq_ordinary
#print axioms AspisV5GoodGateDotBatching.batchedDot24_eq_ordinary_mod
#print axioms AspisV5GoodGateDotBatching.maximal_inputs_tooth
#print axioms AspisV5GoodGateDotBatching.deployedSupportCount_bounds
#print axioms AspisV5GoodGateDotBatching.deployedSupportCount_endpoints
#print axioms AspisV5GoodGateDotBatching.deployedSupportIndex_lt_end
#print axioms AspisV5GoodGateDotBatching.deployedSupportIndex_mod_two
#print axioms AspisV5GoodGateDotBatching.deployedSupportIndex_complete
#print axioms AspisV5GoodGateDotBatching.zeroPad24_active
#print axioms AspisV5GoodGateDotBatching.zeroPad24_inactive
#print axioms AspisV5GoodGateDotBatching.zeroPad24_canonical
#print axioms AspisV5GoodGateDotBatching.ordinaryDot24_zeroPad_eq_prefix
#print axioms AspisV5GoodGateDotBatching.pairedBatchedDot24_eq_separate
#print axioms AspisV5GoodGateDotBatching.pairedBatchedDot24_cast_eq_ordinary
#print axioms AspisV5GoodGateDotBatching.pairedDeployedDot_eq_prefix_mod
#print axioms AspisV5GoodGateDotBatching.pairedDeployedBaseXorProjection_eq_mod
#print axioms AspisV5GoodGateDotBatching.deployedThreeBitPrefixes_eq_literal
#print axioms AspisV5GoodGateDotBatching.deployedThreeBitPrefixes_cross_term_tooth
#print axioms AspisV5GoodGateDotBatching.fusedMulAddMaxRaw_value
#print axioms AspisV5GoodGateDotBatching.fusedMulAddRaw_le_max
#print axioms AspisV5GoodGateDotBatching.fusedMulAddRaw_lt_two_pow62
#print axioms AspisV5GoodGateDotBatching.fusedMulAdd_canonical
#print axioms AspisV5GoodGateDotBatching.fusedMulAdd_cast
#print axioms AspisV5GoodGateDotBatching.fusedMulAdd_eq_mul_then_add
#print axioms AspisV5GoodGateDotBatching.fusedMulAdd_max_tooth
#print axioms AspisV5GoodGateDotBatching.fractionFreeMinRaw_value
#print axioms AspisV5GoodGateDotBatching.fractionFreeMaxRaw_value
#print axioms AspisV5GoodGateDotBatching.fractionFree_negative_le_positive
#print axioms AspisV5GoodGateDotBatching.fractionFreeRaw_bounds
#print axioms AspisV5GoodGateDotBatching.fractionFreeRaw_endpoints_attained
#print axioms AspisV5GoodGateDotBatching.fractionFreeMaxRaw_lt_two_pow63
#print axioms AspisV5GoodGateDotBatching.fractionFreeMaxRaw_lt_two_pow64
#print axioms AspisV5GoodGateDotBatching.fractionFreeRaw_lt_two_pow63
#print axioms AspisV5GoodGateDotBatching.fractionFreeRaw_lt_two_pow64
#print axioms AspisV5GoodGateDotBatching.fusedFractionFreeUpdate_canonical
#print axioms AspisV5GoodGateDotBatching.fusedFractionFreeUpdate_cast
#print axioms AspisV5GoodGateDotBatching.fusedFractionFreeUpdate_min_tooth
#print axioms AspisV5GoodGateDotBatching.fusedFractionFreeUpdate_max_tooth

end AspisV5GoodGateDotBatching

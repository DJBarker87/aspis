# AspisFormal — Lean 4 formalization

Kernel-checked lemmas for the Aspis construction. The point is to move
security-relevant claims off "an AI/script proved it" and onto the Lean kernel.
Build: `lake exe cache get && lake build` (Lean 4, mathlib). CI:
`.github/workflows/lean.yml` (builds/kernel-checks this project) and
`.github/workflows/param-binding.yml` (fails if Rust/Python/Lean disagree on the
deployed parameters).

**Every theorem below depends only on `[propext, Classical.choice, Quot.sound]`
(mathlib's standard base), with no `sorry`, custom axioms, `native_decide`, or
compiled evaluation. The Poseidon2 KATs use kernel `decide` on pinned one-round
transitions, then an ordinary induction folds the transitions into each full
permutation result.**

## Proof-status table — read this honestly

### Hiding
| Statement | File | Status |
|---|---|---|
| Surjective mask map ⟹ witness-independent fibre **counts** | `CoreHiding.lean` | **Proved** (counting, not `PMF`) |
| Same, upgraded to a **`PMF` distribution** equality over a finite field | `CoreHidingPMF.lean` | **Proved** |
| `det M ≠ 0` ⟹ surjective ⟹ hidden, for a square matrix `M` | `MaskingHiding.lean` | **Proved** (arbitrary `M`) |
| Schwartz–Zippel liveness bridge; b=2 to `2/|K|`; b=4 `det≠0` | `CircleVandermonde.lean` | **Proved** |
| Circle liveness at arbitrary even `b` (free coords `K^{2b}`); b=128 ⟹ `≤8192/|K|` | `CircleVandermondeGeneral.lean` | **Proved** |
| Circle liveness over independent rationally parameterised field points (`t`-param, poles handled); b=96 ⟹ `≤9408/|K|`, b=128 ⟹ `≤16640/|K|` | `CirclePointLiveness.lean` | **Proved for that distribution**; the current wire samples discrete domain indices and still needs its own availability argument |
| Hiding for the **concrete circle mask matrix** (not arbitrary `M`) + view interface | `AspisViewBinding.lean` | **Proved** + named interface |
| Byte-exact released-view model; view completeness arithmetic; sampler uniformity ⟹ `PMF`-level perfect hiding; (a) closure spec | `ViewModel.lean` | **Proved** + named interface |
| Hiding for a row-rescaled circle matrix `D·circleTMatrix` | `CircleTMatrixHiding.lean` | **Proved for the model** (`∏ dᵢ ≠ 0 ∧ det circleTMatrix ≠ 0 ⟹ det ≠ 0`); no concrete-wire claim in this module |
| Aligned reserve geometry (`896..991`), exact tensor factorisation `B_(896+j)=B_896·B_j`, monomial-to-natural conversion, and the exact rational rescale `diag(B)·V = diag(B/Qᵐ)·circleTMatrix` | `CircleTensorBinding.lean` | **Proved for the algebraic encoder model**, including conditional fibre-count hiding; Rust/table, nonzero-factor availability, and v5-wire correspondence remain explicit obligations |
| Degree-preserving chained sumcheck mask: uniform zero-boundary sampler, exact round boundaries and Boolean sum, conditional full-round hiding; a false sum accepts for at most one mixing challenge | `SumcheckMasking.lean` | **Proved** per round and for the algebraic self-reduction; adaptive transcript composition and every correlated commitment/PCS observation remain named wire obligations |

### Soundness
| Statement | File | Status |
|---|---|---|
| No field-wraparound `v'+f=v` over ℤ (no inflation) | `ValueConservation.lean` | **Proved** |
| Range (both) + balance + asset **from the constraint residuals** | `ArithmetizationCore.lean` | **Proved** |
| The Poseidon2/Merkle clauses (gate ⟹ `output=perm(input)`, domain separation, Merkle same-path) → **closes the whole `SpendRelation`** end-to-end | `HashMerkleModel.lean` | **Proved** (modulo the `Poseidon2Faithful` interface) |
| Johnson threshold `ρ≤α²`; agreement cap `A=⌊αN⌋=6082` (manifest-bound) | `SoundnessParams.lean` | **Proved** |
| Constants, regime `ρ<√ρ≤α`, every ledger degree, per-event SZ bits, fold/coarse unions, ×3 inflation (`≤2⁻¹⁰⁴`) | `SoundnessLedger.lean` | **Proved** (floor bounds) |
| Circle fibre-root distinctness / root≠1 (structural, no brute force) | `CircleFibreRoots.lean` | **Proved** (modulo the group-order interface) |
| Circle group `g` has order exactly `2³¹`; same-x criterion `X(gᵃ)=X(gᵇ) ↔ a≡±b [2³¹]` — **discharges** `CircleFibreRoots`'s `SameXCoord` interface | `CircleGroupOrder.lean` | **Proved** (kernel `decide`, 31-fold squaring) |
| Poseidon2 KATs: the in-Lean permutation / node / owner / note+nullifier sponges equal the deployed `poseidon2.rs` constants on fixed inputs | `Poseidon2Kat.lean` | **Proved** (kernel `decide` on each pinned round transition) |

### Knowledge / theft resistance
| Statement | File | Status |
|---|---|---|
| Cited extractor + nullifier-binding ⟹ any accepting spend's extracted secret = the note's secret (single-shot and deployed-pool) | `TheftResistance.lean` | **Proved** (axiom-free connective; BCS extractor & sim-ext are cited interfaces) |

## What is NOT (yet) proved — the honest gaps

Substantial progress, but these remain and a reviewer will ask for them:

- **Obligation (a): actual encoder mask map = proved circle matrix.** The first
  draft's rows `928..1023` were not one tensor block and have been rejected.
  `CircleTensorBinding.lean` proves that corrected rows `896..991` share the
  factor `B_896`, that the lower natural Chebyshev basis is degree-triangular,
  that its canonical coefficient conversion gives ordinary Vandermonde
  evaluation, and that the exact rational-parametrised rescale is
  `B_896(p_i)/(1+t_i²)^m` rather than the clearing factor itself. The
  feature-gated Rust module now performs that conversion and
  compares all 96 resulting columns with sparse basis images from the real
  `CircleEncoder` at representative codeword positions. It also reconstructs
  all 48 ordinary monomials coefficient-by-coefficient from the concrete
  conversion table. These are the algebraic pieces of the construction, but
  tests are not a universal code proof. Remaining
  obligations are the Rust↔Lean conversion-table correspondence, the exact v5
  serialized view, the M31/QM31 lane-width split, and an availability argument
  proving both matrix nonsingularity and `B_896(p_i) ≠ 0` for the wire's actual
  discrete query-index distribution.
- **Sumcheck-mask joint view.** `SumcheckMasking.lean` first proves the finite
  translation lemma for a mask uniform over the entire represented vector. It
  explicitly rules out applying that lemma to a 1024-value multilinear mask:
  such a mask cannot hide the higher coefficients of a degree-27 sumcheck
  message. The degree-preserving construction instead uses ten independent
  zero-boundary degree-27 polynomials linked by a half-claim carrier. Lean proves
  the tail sampler is exactly uniform, every boundary chains, the global Boolean
  sum is the initial mask claim, and each complete round's conditional `PMF` is
  independent of the real round polynomial. What remains is the adaptive
  transcript composition and its joint distribution with the commitment root,
  correlated PCS openings, and component-(A) evaluations. Those need the fixed
  v5 wire and a published-simulator composition argument; the elementary
  translation lemma does not supply them.
- **The `Poseidon2Faithful` interface.** The six Poseidon2/Merkle clauses are
  now *structurally proved* (`HashMerkleModel.lean`) — the whole `SpendRelation`
  closes in-kernel from a gate-residual witness — leaving one code-correspondence
  residue: that the in-Lean Poseidon2 permutation and round constants equal the
  deployed `poseidon2.rs`. `Poseidon2Kat.lean` now **pins this on fixed inputs**
  (the permutation, node, owner, and note/nullifier sponges all match the deployed
  constants), and `tools/check_poseidon_binding.py` guards the constant tables in
  CI. That is KAT-strength, not universal function equality — closing the *all
  inputs* gap needs a Rust-side verifier (Verus/Creusot) on the straight-line
  permutation, not more Lean.
- **Theft resistance** is now a kernel-checked (axiom-free) inference
  (`TheftResistance.lean`); what stays cited is the BCS knowledge extractor and
  the simulation-extractability theorem, plus the nullifier-binding hypotheses
  (dischargeable from `HashMerkleModel`'s nullifier hash).
- **The BCS work-normalized endpoint** (~100.16 bit) needs `Real.logb` + additive
  `2⁻²⁵⁶` terms; we kernel-check the coarse union `≤2⁻¹⁰⁶` and its ×3 `≤2⁻¹⁰⁴`,
  and the endpoint erosion stays Python-verified.
- **Serialization faithfulness.** The byte-exact view model matches the paper's
  wire table by `decide`; that it matches the *deployed serializer bytes* is the
  `serialization_complete` interface field.
- ~~**The circle-group order** (`g` has order exactly `2³¹`)~~ **Now proved**
  (`CircleGroupOrder.lean`, kernel `decide`): `orderOf g = 2³¹` and the same-x
  criterion, which discharges `CircleFibreRoots`'s `SameXCoord` interface. The two
  files are not yet textually merged, but the fact `CircleFibreRoots` assumed is
  now a kernel theorem.
- **The published theorems** (Johnson/MCA/WHIR/BCS list decoding, the ZK
  simulator template) are **cited, not formalized**. Intentional and normal, but
  it means the hiding/soundness *arguments* are not end-to-end formal.

## What has been closed since the first draft

- Parameters are now **manifest-bound and CI-enforced** across Rust, Python, and
  Lean (was: "Lean is about intended, not deployed, params").
- Hiding is now a **distribution-level** statement (was: fibre counts only).
- The liveness bound now holds over an independent rational circle-parameter
  distribution (was: free coordinates only). Binding that distribution to the
  wire's discrete query indices remains open.
- The soundness ledger arithmetic and fibre-root distinctness are **in the
  kernel** (were: Python-only).
- The value-conservation core is proven **from the constraints up** (was:
  abstract).
- The frontier (items 4–6) is reduced to a **short list of named, human-readable
  obligations**, several with their tractable halves already proved and a
  runnable closure spec for the rest.

The honest bottom line: the finite mathematics is increasingly in the kernel;
what remains is (i) code-correspondence obligations that need the v5
implementation or a Poseidon2/Merkle model, and (ii) the cited published
theorems. None of it is faked; all of it is named.

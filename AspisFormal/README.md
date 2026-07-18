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
| Exact pre-C residual projection: semantic lanes use `gamma^0..gamma^15`, Hcopy uses `gamma^16`, B uses `gamma^17`; the deployed interface exposes one combined inactive scalar plus eighteen 76-coordinate `E` views | `V5ComponentCPreCProjection.lean`, `V5ComponentCPreCProjectionMixed.lean`, `V5ComponentCPreProjectionDeployed.lean` | **Proved for the mathematical projection and numerically pinned deployed layout** (`72+4`, fibre-major layer zero, point-major `4x19` claims, and the structured `58 -> 36` relation projection); exact Rust parser/evaluator equality remains one named premise |
| Component-C fixed-schedule evaluator: four exact arity-4 folds, coefficient folds, 36 relation rows, schedule-sized deduplicated output, and the physical 58-field relation-tail extraction | `V5ComponentCConcreteFoldLinearity.lean`, `V5ComponentCRelationRowLinearity.lean`, `V5ComponentCConcreteDownstream.lean`, `V5ComponentCDownstreamDeployed.lean` | **Proved linear and composed for arbitrary supplied schedule records**, including the canonical schedule-sized deduplicated layout; the frozen 256-row layout is proved to be only the `(18,18,18)` no-dedup corner under runtime count bounds. Transcript-to-schedule derivation and exact Rust evaluator refinement remain explicit interfaces |
| Component-C sampler: 1023 free field coordinates map bijectively to `ker ell`; both the preallocated 4092×16 experiment and the literal shared-stream, first-success, variable-consumption parser give the exact joint-uniform law after conditioning once on whole-run success | `V5ComponentCSamplerKernel.lean`, `V5ComponentCRejectionSampler.lean`, `V5ComponentCStoppingTimeSampler.lean` | **Proved for both finite ideal experiments**; the exact abort ratio is proved for the preallocated experiment, while the production CSPRNG and Rust-control-flow equality remain named interfaces |
| Component-C encoder: Rust-shaped off-pivot row enumeration, least-inactive pivot, inactive-row functional, pivot correction, kernel landing, and two-sided inverse | `V5ComponentCEncoderCorrespondence.lean` | **Algebraic encoder seam proved unconditionally**; executable Rust transcription, the atomic-v3 mask-table-to-set identification, and QM31 representation remain explicit code/model interfaces |
| Component-C `u32`/QM31 representation: `word & 0x7fffffff = word mod 2^31`, canonical M31 rejection, the exact `M31 -> CM31 -> QM31` tower, and the 16-byte little-endian `(c0.a,c0.b,c1.a,c1.b)` codec | `V5ComponentCQM31Representation.lean`, `V5ComponentCQM31TowerExact.lean`, `V5ComponentCExactTowerDeployment.lean`, `V5ComponentCQM31RustFormulaSeam.lean` | **Proved for the exact mathematical tower, codec, Rust-shaped Karatsuba/square/inversion formula graph, and stopping-time sampler specialization**; subtraction and optimized square are load-bearing. Executable Rust equalities, including the totalized adapter for panicking nonzero-domain inversion, remain explicit source-correspondence interfaces |
| Component-C physical relation tail: `58` QM31 fields, `16` bytes each, exact field/byte flattening, pinned four-limb codec, and the non-contiguous `58 -> 36` witness-dependent projection | `V5ComponentCRelationTailCodec.lean` | **Proved for the exact mathematical serializer/decoder**, with Rust serializer equality and semantic artifact-to-schedule equality kept as two separate named premises |
| Complete direct Component-C joint-view equality using that literal conditioned-`u32` law and pivot encoder | `V5ComponentCDirectHiding.lean`, `V5ComponentCBlockSamplerDirectHiding.lean` | **Proved conditionally on A/H/B hiding and the deployed-shaped residual correspondences**; no C-DEC, rank certificate, or circle-to-GRS/FRI transport premise |
| Component-C deployment ledger: decoded fixed-schedule runtime laws and the adaptive FS/RO transcript compiler boundary | `V5ComponentCDeploymentLedger.lean` | **Kernel-checked conditional composition**; Rust/code-model edges, both production-entropy hybrids (the C stream and joint A/H/B/C source), PCS/serialization correspondences, and the compiler-supplied hash/RO/FS assumptions are explicit and load-bearing, so this does not assert deployed ZK |

### Soundness
| Statement | File | Status |
|---|---|---|
| No field-wraparound `v'+f=v` over ℤ (no inflation) | `ValueConservation.lean` | **Proved** |
| Range (both) + balance + asset **from the constraint residuals** | `ArithmetizationCore.lean` | **Proved** |
| The Poseidon2/Merkle clauses (gate ⟹ `output=perm(input)`, domain separation, Merkle same-path) → **closes the whole `SpendRelation`** end-to-end | `HashMerkleModel.lean` | **Proved** (modulo the `Poseidon2Faithful` interface) |
| Johnson threshold `ρ≤α²`; agreement cap `A=⌊αN⌋=6082` (manifest-bound) | `SoundnessParams.lean` | **Proved** |
| Constants, regime `ρ<√ρ≤α`, every ledger degree, per-event SZ bits, fold/coarse unions, ×3 inflation (`≤2⁻¹⁰⁴`) | `SoundnessLedger.lean` | **Proved** (floor bounds) |
| Work-normalized BCS endpoint: for `T` in `[1,2^128]`, `R≤32`, and capacity error `≤2⁻²⁵⁶`, the tight union gives final error `≤2⁻¹⁰⁰` | `SoundnessWorkNormalizedEndpoint.lean` | **Proved**, conditional on the explicitly stated cited BCS error formula; also proves the coarse floors are insufficient |
| Circle fibre-root distinctness / root≠1 (structural, no brute force) | `CircleFibreRoots.lean` | **Proved** (modulo the group-order interface) |
| Circle group `g` has order exactly `2³¹`; same-x criterion `X(gᵃ)=X(gᵇ) ↔ a≡±b [2³¹]` — **discharges** `CircleFibreRoots`'s `SameXCoord` interface | `CircleGroupOrder.lean` | **Proved** (kernel `decide`, 31-fold squaring) |
| Poseidon2 KATs: the in-Lean permutation / node / owner / note+nullifier sponges equal the deployed `poseidon2.rs` constants on fixed inputs | `Poseidon2Kat.lean` | **Proved** (kernel `decide` on each pinned round transition) |

### Knowledge / theft resistance
| Statement | File | Status |
|---|---|---|
| Cited extractor + nullifier-binding ⟹ any accepting spend's extracted secret = the note's secret (single-shot and deployed-pool) | `TheftResistance.lean` | **Proved** (axiom-free connective; BCS extractor & sim-ext are cited interfaces) |

## What is NOT (yet) proved — the honest gaps

Substantial progress, but these remain and a reviewer will ask for them:

- **Component C is closed as finite direct algebra, not as deployed ZK.** The
  direct route samples uniformly on `ker ell` and translates by the exact
  `(gamma^18)^-1`-scaled pre-C difference. This proves the joint law for every
  fixed linear downstream map and therefore does not need the rejected C-DEC
  rank-certificate path or a circle-to-GRS fold transport theorem. Deployment
  still requires universal Rust-to-Lean correspondence for the combined
  inactive scalar, all eighteen 76-coordinate views, encoder tables, the
  schedule-sized fold/relation evaluator, physical byte order, and terminal
  PCS opening. The finite sampler theorem now covers the literal first-success,
  variable-consumption control flow over one shared iid-`u32` prefix and proves
  its conditioned output law equals the earlier preallocated experiment. It
  also proves the low-31 bit operation and mathematical little-endian four-limb
  codec. The concrete field isomorphism is no longer a cardinality placeholder:
  the literal `M31 -> CM31 -> QM31` tower, limb equivalence, codec, and deployed
  algebraic formulae are kernel-checked. Deployment still needs the exact Rust
  parser equality, executable base-primitive and optimized-entry-point
  correspondence, and the computational 256-bit expander-to-iid hybrid. The
  physical `928`-byte relation-tail codec and `58 -> 36` projection are likewise
  pinned mathematically, while equality to the Rust serializer and real host
  artifact remains explicit. Joint independence from A/H/B coins requires its
  own production-source hybrid; serialization, Fiat--Shamir/RO compiler, and
  salted-Merkle/hash assumptions also remain explicit interfaces. The
  deployment ledger consumes each edge but does not prove it. A frozen-schedule
  KAT is regression evidence, not universal correspondence.

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
- **The cited BCS work-normalization theorem.**
  `SoundnessWorkNormalizedEndpoint.lean` now keeps the additive `2⁻²⁵⁶`
  terms, re-derives a tight `≤2^(-106.72)` round-error bound, and kernel-checks
  the release endpoint `≤2⁻¹⁰⁰`. It also proves that the older coarse floors
  cannot establish 100 bits after work normalization. The functional BCS
  error formula and constants are still a cited interface; the more precise
  ~100.16-bit figure remains an external calculation rather than the release
  claim.
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

The honest bottom line: Component C's finite direct hiding construction is now
in the kernel and composes with the existing A and B mathematics; this is not a
restart and it does not certify deployed v5 as zero-knowledge. What remains is
(i) the named implementation, entropy, transcript, PCS, serialization, and
hash correspondences, and (ii) the cited published compiler/extractor results.
None of those edges is silently promoted to a theorem.

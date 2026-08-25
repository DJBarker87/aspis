# Aspis V7: staged split-tensor front end + frozen V6 one-fold back end

**Status:** research and implementation plan. This document is deliberately not
a security claim.

**Baseline:** V6 is assumed to be complete, frozen, reproducibly built, and
accepted as the back-end proof system before production V7 integration. The
repository baseline is commit
`a6fa6d817e3cf343c8639684e4ab2ce289c40355` on `main`, whose selected profile
has 26 M31 C1 lanes, three QM31 C2 lanes, one committed arity-four fold, 256
disclosed final coefficients, q16 queries, and an exact 33,336-byte body.

**Repository status, 25 August 2026:** V6 source, reproducible SBF, complete
adversarial record and finalized devnet execution are frozen at that commit.
The canonical 1,151,632-byte SBF has SHA-256
`53ff6c8da29646bb8fc78f37656e42bf1c53bbe10026df13eea77624b66f1d4d`
and the atomic devnet execution used 1,247,328 CU. Two final long-running
formal release certificates were still completing on the NUC when the V7
branch was cut. Pure Phase-1 algebra and the theorem audit may proceed; no V7
production integration may consume the V6 release interface until that final
bundle is frozen.

**V7 goal:** reduce the selected 26+3 V6 proof to roughly 28–30 KiB, preferably
with lower prover memory, while preserving the V6 semantic relation, one-fold
terminal, atomic Solana state transition, transparent setup, and the same
honest/deployed assurance chain.

---

## 1. Executive decision

V7 should not replace V6's one-fold endpoint.

V7 should add a **staged split-tensor commitment and code-switch front end**,
whose sole job is to compress the 29 wide initial lanes into one ordinary
1,024-coefficient QM31 row message. Once that row message is committed, V7
hands control to a frozen V6 back end:

```text
26 M31 C1 lanes ┐
                 ├─ split-tensor restriction / code switch ─> G_gamma[1024]
3 QM31 C2 lanes ┘

G_gamma[1024]
   ── frozen V6 one-fold backend ──> final256
   ── frozen V6 relation tail ─────> final4
   ── frozen V6 semantic terminal ─> atomic state transition
```

This division is fundamental:

- **V6 remains the stable security and deployment base.**
- **V7 contains one new research-cryptography seam.**
- A failed V7 experiment does not threaten V6.
- The final V7 theorem should be a composition theorem, not a rewritten proof
  of the entire spend protocol.

The preferred production candidate is a staged, multi-root
**Circle-WHIR/BaseFold-style partial-evaluation code switch**. A simpler
random-point identity proof is retained as a formal and implementation
fallback.

---

# Part I — prerequisites and design freeze

## 2. V6 must cross a freeze gate first

Do not start production V7 integration merely because the V6 branch is
promising. Freeze V6 only when all of the following hold.

### 2.1 Functional freeze

- A complete host prover emits the selected 26+3 proof.
- The complete SBF verifier consumes exactly that proof.
- The same accepted execution performs the semantic check and atomic state
  transition.
- Failure rolls back all state changes.
- Proof-account lifecycle and rent recovery are complete.

### 2.2 Compute freeze

- The full verifier, not an isolated slice, is measured on the pinned local
  validator.
- The intended release gate is met with real headroom.
- The result is deterministic over at least three identical runs.
- A phase-by-phase CU ledger identifies every material cost.
- The exact SBF bytes and hash are frozen.

Recommended target:

```text
target full verifier: <= 1.30M CU
hard release gate:    <= 1.35M CU
```

### 2.3 Mathematical freeze

- The exact one-fold published-theorem predicates are stated.
- Every finite parameter substitution is kernel-checked.
- The compact-query conditioned probability is connected to the exact
  sampler.
- The V6 event ledger is complete rather than copied provisionally from V5.
- The selected 26+3 hiding theorem is complete for the full public view.
- The work-normalized Fiat–Shamir conclusion is assembled.

### 2.4 Source/deployment freeze

- The accepted Rust path is translated and replayed.
- One successful top-level execution supplies one common evidence record.
- The evidence record is connected to the pure V6 security theorem.
- A clean checkout reproduces the exact SBF.
- The proof, SBF, RPC record, account deltas, cleanup and release manifest are
  archived.

Tag this state, for example:

```text
v6-onefold-research-freeze
```

V7 branches from that exact tag. V6 files are thereafter changed only by
explicitly reviewed generic refactors.

---

## 3. V7 non-goals

V7 is not the place to add:

- multi-input/multi-output notes;
- parallel pool shards;
- a new hash function;
- recursion;
- digest truncation by default;
- a new semantic AIR;
- a new nullifier structure;
- a different masking construction unless the V7 view forces it;
- a generic WHIR library for all fields;
- production wallet work.

Those are independent projects. V7 succeeds if it compresses the initial PCS
layer and preserves the frozen V6 back end.

---

# Part II — exact algebraic architecture

## 4. Fields and lane inventory

Let

\[
F=\mathbb F_{2^{31}-1}
\]

be M31 and let

\[
K=\mathrm{QM31}
 =F[i,u]/(i^2+1,\ u^2-(2+i)).
\]

Use the fixed \(F\)-basis

\[
e_0=1,\qquad e_1=i,\qquad e_2=u,\qquad e_3=iu.
\]

The selected V6 profile contains:

- 26 C1 messages \(c_0,\ldots,c_{25}\), each in \(F^{2^{10}}\);
- three C2 messages \(h_0,h_1,h_2\), each in \(K^{2^{10}}\).

Every V7 theorem and serializer is parameterized by a profile fingerprint.
There must be no theorem that silently applies a 16+3 byte calculation to the
26+3 security profile.

---

## 5. Stage-A tensor

Pad the 26 C1 lanes to 32 lanes.

For row variable \(X\in\{0,1\}^{10}\) and lane variable
\(Y\in\{0,1\}^{5}\), define the monomial-lane polynomial

\[
A(X,Y)
 =\sum_{\ell=0}^{25} c_\ell(X)
   \prod_{j=0}^{4}Y_j^{b_j(\ell)},
\]

where \(b_j(\ell)\) is bit \(j\) of \(\ell\). Lanes 26–31 are exactly zero.

The committed Boolean table is the lane-wise zeta transform:

\[
\widehat A(X,B)
 = \sum_{\ell\subseteq B} c_\ell(X).
\]

Its multilinear extension is exactly the monomial polynomial \(A\).

Define

\[
y_A(\gamma)
 =(\gamma,\gamma^2,\gamma^4,\gamma^8,\gamma^{16}).
\]

Then

\[
A(X,y_A(\gamma))
 =\sum_{\ell=0}^{25}\gamma^\ell c_\ell(X).
\]

**Stage-A root must be committed before every challenge on which C2 depends and
before \(\gamma\).**

---

## 6. Stage-B tensor

Write each C2 lane in the fixed tower basis:

\[
h_j(X)=\sum_{r=0}^{3}h_{j,r}(X)e_r,
\qquad h_{j,r}(X)\in F.
\]

There are twelve M31 limb lanes. Pad them to sixteen.

Use low lane bits for the basis index \(r\) and high lane bits for the C2
index \(j\). Define

\[
B(X,U_0,U_1,V_0,V_1)
 =\sum_{j=0}^{2}\sum_{r=0}^{3}
   h_{j,r}(X)
   U_0^{b_0(r)}U_1^{b_1(r)}
   V_0^{b_0(j)}V_1^{b_1(j)}.
\]

Let

\[
y_B(\gamma)=(i,u,\gamma,\gamma^2).
\]

Then

\[
\gamma^{26}B(X,y_B(\gamma))
 =\sum_{j=0}^{2}\gamma^{26+j}h_j(X).
\]

**Stage-B root is committed after the C2-generating challenges
\(\lambda,\chi,\ldots\), but before \(\gamma\).**

The baseline formal model keeps B as a 14-variable tensor. A padded
15-variable B is an implementation simplification to test, not the default
mathematical profile.

---

## 7. Exact combined row message

Define

\[
G_\gamma(X)
 =
 A(X,y_A(\gamma))
 +\gamma^{26}B(X,y_B(\gamma)).
\]

Therefore

\[
\boxed{
G_\gamma(X)
 =\sum_{\ell=0}^{28}\gamma^\ell C_\ell(X)
}
\]

for the exact selected V6 lane order.

This identity has three important consequences.

1. The current width-29 degree-28 gamma-batching argument remains relevant.
2. The tensor transform changes representation, not the batched polynomial.
3. The V6 back end can consume \(G_\gamma\) without knowing how the 29 lanes
   were packed.

The zeta transform and the basis decomposition must be fully invertible in
Lean. Zero padding must be part of the statement, not an implementation
convention.

---

# Part III — the new V7 proof seam

## 8. The object to prove

After \(\gamma\) is sampled, the prover computes the 1,024-element row message

\[
g=(G_\gamma(X))_{X\in\{0,1\}^{10}}
\]

and commits to its ordinary V6-compatible circle-code encoding:

\[
R_G=\operatorname{Commit}(\operatorname{Enc}_{V6}(g)).
\]

V7 must prove that \(R_G\) is a correct re-encoding of the restrictions of the
two earlier staged tensor commitments.

The proof must remain sound even though:

- \(R_G\) is chosen after \(\gamma\);
- Stage A and Stage B were committed at different transcript times;
- the two source tensors have different lane arities;
- the target lives over QM31 while source leaves are M31;
- the V6 proof later treats \(R_G\) as its own authenticated initial object.

---

## 9. Preferred construction: local partial-evaluation code switch

The preferred design is a Circle-WHIR/BaseFold-style code switch.

For each verifier-derived source query position:

1. open the corresponding row block of Stage A;
2. open the corresponding row block of Stage B;
3. locally evaluate the lane restrictions at \(y_A(\gamma)\) and
   \(y_B(\gamma)\);
4. reconstruct the expected \(G_\gamma\) value;
5. open the corresponding value under \(R_G\);
6. require equality;
7. use a shared proximity/code-switch reduction to show that dense local
   consistency yields one globally valid restricted message.

The code-switch proof must establish a deterministic statement of the form:

```text
accepted local checks
and no small-consistency-set query miss
and no published reduction failure
and no list overflow

=> there exist source messages a,b and target message g such that
   StageA is close to EncA(a),
   StageB is close to EncB(b),
   RG is close to EncG(g), and
   g = restrictA_gamma(a) + gamma^26 * restrictB_gamma(b).
```

The word “close” is deliberate. The initial Merkle tables are received words,
not assumed codewords. The extraction theorem must use the same proximity/list
logic as V6 rather than smuggling exact encoding into the premise.

---

## 10. Query-sharing optimisation

The target production format should try to share the V6 q16 fibre schedule.

For each V6 fibre query \(q_i\), derive a two-bit slot \(s_i\). The V6 back end
opens all four \(G\) values in the fibre. The V7 front end opens Stage-A and
Stage-B data only for the selected full-domain position

\[
x_i=4q_i+s_i.
\]

The code-switch equality is checked at \(x_i\); the ordinary V6 one-fold
equality is checked over the whole fibre \(q_i\).

This is potentially the difference between a useful and useless V7:

- opening one A/B row per fibre is small;
- opening all four A/B rows per fibre largely destroys the compression.

This optimisation is not accepted until two facts are proved:

1. the derived \(x_i\) values have the exact intended distribution;
2. the joint first-compact sampler remains sound when compactness depends on
   the A, B and G tree frontiers.

The first reference prototype should use separate query streams. Shared
queries are a later optimisation.

---

## 11. Fallback construction: random-point identity link

If the published code-switch theorem cannot be matched cleanly, use a modular
fallback.

After \(R_G\), sample a fresh random row point \(r\in K^{10}\). Batch-open:

\[
A(r,y_A(\gamma)),\qquad
B(r,y_B(\gamma)),\qquad
G(r)
\]

and check

\[
G(r)=A(r,y_A(\gamma))+\gamma^{26}B(r,y_B(\gamma)).
\]

Provided all three commitments are bound to low-degree polynomials, a
nonzero row-polynomial discrepancy is caught by a Schwartz–Zippel term.

This fallback is mathematically clean but may cost more proof bytes and SBF
arithmetic. It is valuable because it separates two questions:

- whether split-tensor compression is useful;
- whether the specialised local code-switch theorem can be made to fit.

The fallback must use a real PCS multi-opening. Sending the three values
without binding them to their commitments is not a protocol.

---

## 12. Rejected shortcuts

The following are explicitly forbidden.

### 12.1 Independent post-gamma root

Do not merely commit an arbitrary \(G_\gamma\) root after \(\gamma\) and run
V6. That root is unrelated to Stage A/B without a link proof.

### 12.2 Four-point interpolation

Matching the semantic point claims at four points does not prove a global
degree-1-per-row-variable identity. A malicious prover can interpolate a
different low-degree object through those points.

### 12.3 Arbitrary compact retry counter

The prover may not present any compact counter it likes. The verifier derives
and checks the first compact candidate.

### 12.4 “WHIR applies”

No theorem or paper may be cited by name alone. The exact predicate, domain,
rate, list threshold, challenge count and staged commitment order must be
stated in Lean.

### 12.5 Assuming source words are codewords

Merkle commitments bind received words. Low-degree/codeword conclusions are
outputs of the proximity reduction, not premises.

---

# Part IV — quantitative target and kill budget

## 13. V6 baseline

The selected V6 body is:

\[
33{,}336\text{ bytes}.
\]

Its per-query record is:

\[
403\text{ C1 bytes}
+186\text{ C2 bytes}
+32\text{ salt bytes}
=621\text{ bytes}.
\]

At q16:

\[
16\cdot621=9{,}936\text{ query bytes}.
\]

The proof must save at least

\[
33{,}336-30{,}720=2{,}616\text{ bytes}
\]

to fit below 30 KiB.

---

## 14. Target V7 query record

A heterogeneous split-tensor target is:

- Stage A row: 32 M31 values = 992 bits = 124 packed bytes;
- Stage B row: 16 M31 values = 496 bits = 62 packed bytes;
- G fibre: four QM31 values = 496 bits = 62 packed bytes;
- one typed shared 256-bit salt = 32 bytes.

Total:

\[
124+62+62+32=280\text{ bytes/query}.
\]

At q16:

\[
16\cdot280=4{,}480\text{ bytes}.
\]

Gross query-record saving:

\[
9{,}936-4{,}480=5{,}456\text{ bytes}.
\]

This is a target, not yet an achieved wire size. It assumes one source row per
fibre. If the code-switch theorem requires all four source rows, this profile
fails its main byte rationale.

---

## 15. Net-overhead budget

Ignoring any claim-table saving, V7 can add at most

\[
5{,}456-2{,}616=2{,}840\text{ bytes}
\]

of extra roots, frontiers, code-switch messages and transcript material while
still reaching 30 KiB.

A third root alone costs 32 bytes, leaving 2,808 bytes.

Possible claim-table compression may improve this budget, but it is not
counted until the exact V6 terminal/relation dependency audit proves which
claims can be removed.

This is the central engineering gate:

> **The complete staged link overhead must be at most 2,840 bytes after
> accounting for the changed Merkle frontiers.**

If the source-tree geometry adds more than that by itself, the production
profile needs a different commitment layout or a 30–32 KiB target.

---

## 16. Hard project gates

V7 proceeds to deployment only if:

| Gate | Target | Hard failure |
|---|---:|---:|
| Proof body | ≤30 KiB preferred | >32 KiB without another major benefit |
| Full verify CU | ≤1.30M preferred | >1.35M |
| Expected grind | ≤1.25× V6 preferred | >1.5× V6 |
| Prover peak memory | <192 MiB preferred | >256 MiB |
| Security | ≥100-bit work-normalized | any unbudgeted dominant event |
| Hash width | 32 bytes initially | truncation without ledger theorem |
| Formal kernel | no `sorry`, no custom axioms | hidden source/model premise |
| Net proof gain | ≥3 KiB vs V6 | <10% gain with more complexity |

A 30–32 KiB proof can still be worthwhile if it materially reduces memory or
CU. A 33 KiB V7 with higher complexity and no operational gain should be
abandoned.

---

# Part V — formal verification programme

## 17. Verification philosophy

The V7 proof effort is not “formalise the paper after the implementation”.

The order is:

1. specify the exact interactive protocol;
2. state every external theorem interface;
3. prove deterministic algebra and extraction;
4. close finite parameter arithmetic;
5. implement a literal reference;
6. implement the optimized verifier;
7. prove optimized/reference equality;
8. extract the accepted Rust execution;
9. compose one accepted execution with the pure security theorem;
10. freeze and reproduce the binary.

Every claim belongs to exactly one category:

- **KERNEL:** proved in Lean from standard foundations;
- **PAPER:** exact externally published theorem interface;
- **ASSUMPTION:** named computational primitive assumption;
- **MEASUREMENT:** reproducible implementation fact;
- **OPEN:** unresolved research claim.

The repository should maintain a machine-readable claim register.

---

## 18. Lean module graph

Suggested pure-mathematics modules:

```text
AspisFormal/AspisFormal/V7SplitTensor/
  Profile.lean
  TowerBasis.lean
  BooleanZeta.lean
  StageATensor.lean
  StageBTensor.lean
  GammaRestriction.lean
  ClaimProjection.lean
  EncoderScalarExtension.lean
  SourceDomainGeometry.lean
  TargetDomainGeometry.lean
  LocalCodeSwitch.lean
  CodeSwitchCandidateExtraction.lean
  PublishedCodeSwitchInterfaces.lean
  SharedQuerySchedule.lean
  JointFrontierCertificate.lean
  FirstCompactSampler.lean
  V6BackendInterface.lean
  V6Composition.lean
  TranscriptRounds.lean
  FailureEvents.lean
  InteractiveSoundness.lean
  WorkNormalizedLedger.lean
  HidingView.lean
  HidingRankCertificate.lean
  TypedSharedSalt.lean
  CompleteSecurity.lean
```

Source-correspondence modules remain separate:

```text
aeneas-verif/V7/
  V7WireSource.lean
  V7TensorSource.lean
  V7MerkleSource.lean
  V7CodeSwitchSource.lean
  V7TranscriptSource.lean
  V7VerifierSource.lean
  V7AcceptedExecution.lean
  V7AcceptedSecurityBridge.lean
```

---

## 19. Profile and dimension theorems

`Profile.lean` fixes:

```text
row variables                 10
Stage-A lane variables         5
Stage-B lane variables         4
Stage-A real lanes            26
Stage-B real M31 limbs        12
target row coefficients     1024
V6 final coefficients        256
```

Prove:

```lean
stageACoefficients = 2^15
stageBCoefficients = 2^14
targetCoefficients = 2^10
```

Every byte formula is a function of the profile.

A profile fingerprint binds:

- lane order;
- basis order;
- padding locations;
- encoder rates;
- tree arities and tags;
- query counts;
- work positions;
- transcript labels;
- claim ordering;
- salt policy.

Rust and Lean consume the same generated manifest and both prove/check the
fingerprint.

---

## 20. Zeta-transform theorem

Define the Boolean zeta transform:

\[
(\zeta a)(B)=\sum_{S\subseteq B}a(S).
\]

Prove:

1. zeta is linear;
2. Möbius inversion is its inverse;
3. the MLE of `zeta a` equals the monomial polynomial with coefficients `a`;
4. padding lanes remain zero under inverse extraction;
5. the optimized in-place Rust zeta transform equals the mathematical zeta.

Core theorem shape:

```lean
theorem mle_zeta_eq_monomial
    (a : Fin (2^n) → F) (y : Fin n → K) :
  mle (zeta a) y =
    ∑ s, algebraMap F K (a s) * monomial y s
```

This theorem is generic and reusable beyond V7.

---

## 21. Exact gamma-restriction theorem

Prove separately:

```lean
theorem stageA_restrict_gamma :
  evalStageA A x (gammaLanePointA gamma)
    = ∑ lane : Fin 26, gamma^lane.val * lift (c1 lane x)
```

and:

```lean
theorem stageB_restrict_gamma :
  gamma^26 * evalStageB B x (gammaLanePointB gamma)
    = ∑ lane : Fin 3, gamma^(26 + lane.val) * c2 lane x
```

Then:

```lean
theorem splitTensor_eq_width29Batch :
  restrictA A gamma x + gamma^26 * restrictB B gamma x
    = width29Batch lanes gamma x
```

Finally prove that the discrepancy polynomial in \(\gamma\) has degree at most
28. Reuse the existing width-29 root-counting result rather than duplicating
it.

---

## 22. Claim projection theorem

Define the exact V7 public claim inventory.

Do not optimize it by inspection. Trace every claim consumed by:

- the semantic terminal;
- the initial relation claim;
- the mask component;
- gamma batching;
- code-switch constraints;
- the V6 relation tail.

Prove:

```lean
theorem compact_claim_inventory_sufficient :
  decodeV7Claims bytes = claims ->
  v7InitialRelationClaim claims gamma kappa =
  v6InitialRelationClaim fullV6Claims gamma kappa
```

Only after this theorem exists may omitted V6 claims be removed from the wire.

The baseline V7 reference format retains the full V6 claim table.

---

## 23. Abstract encoder interfaces

Represent source and target encoders explicitly:

```lean
structure V7Encoders where
  stageA : StageAMessage F -> StageAWord F
  stageB : StageBMessage F -> StageBWord F
  target : TargetMessage K -> TargetWord K
```

Prove deterministic facts for the concrete encoders:

- linearity;
- injective coefficient split;
- source and target distance/overlap bounds;
- scalar extension from M31 to QM31;
- exact circle/line evaluation identities;
- local row/fibre ordering;
- padding identities.

Do not put list decoding into this module. It is pure code algebra.

---

## 24. Deterministic local-code-switch model

Define:

```lean
structure V7IdealTranscript where
  stageAReceived : StageAWord F
  stageBReceived : StageBWord F
  targetReceived : TargetWord K
  disclosedFinal : FinalCoefficients K
```

Define the local consistency predicate at a source position \(x\):

```lean
LocalLinkConsistent gamma stageA stageB target x
```

and its consistency set.

Define a query failure exactly as V6 does:

```text
all link queries accept
and consistency-set size <= threshold.
```

The deterministic extraction theorem should read:

```lean
theorem accepted_link_supplies_matching_restriction
    (haccept : LinkAccepts transcript queries)
    (hquery  : not LinkQueryFailure)
    (hreduct : not CodeSwitchReductionFailure)
    (hcaps   : not CandidateListOverflow) :
  exists a b g,
    a in stageACandidateList
    and b in stageBCandidateList
    and g in targetCandidateList
    and g = restrictA a gamma + gamma^26 * restrictB b gamma
```

No probabilities appear in this theorem.

---

## 25. Exact published-theorem interface

Create a dedicated module analogous to
`V6PublishedTheoremInterfaces.lean`.

The module must state only the exact predicate required for:

- mixed Stage-A/Stage-B source domains;
- the selected source rates;
- the target row code;
- the prescribed gamma lane points;
- the local consistency threshold;
- the candidate-list caps;
- the response strategy being allowed to vary with challenges;
- any cross-domain correlated agreement condition.

Example shape:

```lean
def PublishedSplitTensorCodeSwitch
    (encA : ...)
    (encB : ...)
    (encG : ...)
    (profile : V7Profile) : Prop := ...
```

Then prove every finite substitution around the predicate:

- field cardinalities;
- list expressions;
- multiplicities;
- curve degrees;
- challenge caps;
- work bits;
- threshold floors/ceilings;
- domain sizes;
- query counts.

If the paper theorem does not imply this exact predicate, the audit says
**BLOCKED**. It must not be repaired by prose.

---

## 26. Shared-query formalisation

The optimized schedule has:

- q16 distinct fibre indices in `Fin 2^18`;
- one slot in `Fin 4` per fibre;
- target indices equal to the fibres;
- source indices derived from `(fibre,slot)`;
- three tree-frontier functions;
- a public compactness predicate;
- a bounded first-hit candidate stream.

Formalise:

1. exact uniform fibre sampling without replacement;
2. exact uniform slot sampling;
3. injectivity of the source-index map;
4. first-compact uniqueness and no-skip;
5. conditioned distribution;
6. link-query miss;
7. one-fold query miss;
8. their union when the same schedule is reused.

The first proof may use conservative conditioning:

\[
\Pr[B\mid C]\le\frac{\Pr[B]}{\Pr[C]}.
\]

A generated exact joint-frontier certificate can replace the conservative lower
bound later.

Do not assume compactness is independent of a bad set.

---

## 27. Frontier certificate

The V7 compact predicate spans different tree depths and index maps. Generate
a sparse dynamic-programming certificate externally, but verify it in Lean.

The certificate checker proves:

- every recurrence row;
- total mass;
- compact mass;
- cap-exhaustion probability;
- any rational lower bound used by the query theorem.

The generator is not trusted. Only the checker and certificate are in the
trusted formal argument.

Keep a human-readable JSON summary and a binary/sparse certificate file.

---

## 28. Composition with V6

Expose a narrow frozen V6 theorem:

```lean
theorem v6_backend_security
    (gCommitment : TargetCommitment)
    (evidence : V6AcceptedEvidence gCommitment) :
  ValidTargetMessage gCommitment
    or V6FailureEvent evidence
```

V7 proves:

```lean
theorem v7_split_tensor_composition :
  V7Accepted
    ->
  ValidSourceWitness
    or V7FrontEndFailure
    or V6FailureEvent
```

The proof must identify the target message extracted by V7 with the exact
target message consumed by the V6 evidence package. There may not be two
existentially chosen \(g\)'s.

This is why V6 must expose a stable theorem interface before V7 begins.

---

## 29. Failure-event inclusion

Define events before assigning numbers.

Minimum front-end event inventory:

```text
E_A_MERKLE_BIND
E_B_MERKLE_BIND
E_G_MERKLE_BIND
E_STAGE_ORDER
E_GAMMA_BATCH
E_LINK_QUERY_MISS
E_CODE_SWITCH_REDUCTION
E_SOURCE_LIST_OVERFLOW
E_TARGET_LIST_OVERFLOW
E_COMPACT_CAP_EXHAUSTED
E_PACKED_DECODING
E_TYPED_SALT_HYBRID
```

Then import, rather than restate, V6 events:

```text
E_V6_ONE_FOLD
E_V6_FINAL_QUERY
E_V6_RELATION_0..3
E_V6_SEMANTIC_*
E_V6_STATE_BINDING
```

Prove pointwise:

```lean
AcceptsV7 and not ValidSpend
  -> one of the listed events.
```

Only after this inclusion theorem exists should `V7SecurityLedger.lean`
contain probabilities.

---

## 30. Work-normalized Fiat–Shamir proof

Build a typed transcript-round AST.

Each round records:

- prover message;
- message length;
- commitments fixed by that message;
- challenges sampled next;
- work witness, if any;
- failure events strengthened by that work;
- random-oracle labels.

Prove the exact round count from the AST. Do not infer it from byte boundaries.

Work-placement invariants:

- Stage-A root precedes C2-generating challenges.
- Stage-B root and all individual claims precede gamma.
- \(R_G\) precedes every challenge testing the code switch.
- final256 precedes final work and query sampling.
- no proof-carried selector is accepted without all earlier candidates checked.

The final theorem should use rational/integer inequalities wherever possible,
not decimal “bits”.

---

# Part VI — hiding and zero knowledge

## 31. Hiding is not inherited automatically

V7 changes the complete public view.

The view includes:

- Stage-A root;
- Stage-B root;
- target root;
- opened tensor rows;
- opened target fibres;
- all code-switch sumcheck/OOD values;
- the V6 final256 vector;
- relation messages;
- semantic claims;
- first-compact counters and selectors.

The V6 hiding theorem must not be cited without showing that the V7 view is a
linear/deterministic image covered by the same mask translation.

---

## 32. Algebraic hiding proof

Construct the exact affine map

\[
\mathcal V_{V7}(w,m)
\]

from witness \(w\) and fresh mask variables \(m\) to every disclosed field
coordinate before hashing.

Prove either:

1. a translation theorem mapping masks for any two valid witnesses while
   preserving the complete view; or
2. a surjectivity/rank theorem for the conditional affine image.

Useful factorisation:

```text
source masked lanes
   -> zeta-transformed tensor rows
   -> gamma restriction
   -> target message
   -> V6 final256 and relation tail.
```

Because all arrows are linear after challenges are fixed, prove kernel
containments and row-span inclusions rather than recomputing unrelated ranks.

A generated sparse rank certificate is acceptable only through a proved Lean
checker.

---

## 33. Staged simulator

The simulator must respect transcript time:

1. simulate/program Stage A before lambda/chi;
2. receive lambda/chi;
3. simulate/program Stage B before gamma;
4. receive gamma;
5. simulate/program target root;
6. simulate code-switch and V6 views;
7. answer query openings consistently.

A single after-the-fact affine distribution argument is not enough if it
allows masks to depend on challenges sampled after their commitment.

The formal hiding theorem should expose each conditional distribution step.

---

## 34. Salt policy

Start with the safest wire:

- independent 32-byte salts for A, B and G opened rows.

Then test:

- one 32-byte salt shared across the three typed leaves at the same logical
  query;
- one shared A/B salt plus an independent G salt.

For shared salt, prove a joint random-oracle hybrid with exact typed inputs:

```text
H(tagA || profile || valueA || salt)
H(tagB || profile || valueB || salt)
H(tagG || profile || valueG || salt)
```

The charge is proportional to the number of hidden typed inputs, not to a
fictional shortened salt.

No 16-byte salt profile is considered at a \(2^{128}\)-query hiding budget.

---

# Part VII — implementation architecture

## 35. Repository layout

Suggested Rust modules:

```text
crates/aspis-core/src/
  v7_profile.rs
  v7_lane_zeta.rs
  v7_split_tensor.rs
  v7_code_switch.rs
  v7_query_schedule.rs
  v7_binary_openings.rs
  v7_wire.rs
  v7_transcript.rs
  v7_relation_bridge.rs
  v7_verifier.rs

crates/aspis-prover/src/
  v7_stage_a.rs
  v7_stage_b.rs
  v7_target.rs
  v7_code_switch_prover.rs
  v7_openings.rs
  v7_builder.rs

programs/aspis-verifier/src/
  v7_cu_probe.rs
  v7_entry.rs

xtask/src/
  v7_vectors.rs
  v7_cu_probe.rs
  v7_release.rs
```

Feature flags:

```text
v7-research
v7-reference
v7-cu-probe
v7-insecure-fixture
```

No V7 path is enabled by the production V6 feature.

---

## 36. Reference implementation first

Write a slow, literal host reference that:

- constructs A and B coefficient tensors;
- performs zeta and inverse-zeta;
- evaluates the restrictions literally;
- constructs \(g_\gamma\);
- uses unoptimized encoders;
- emits explicit arrays rather than packed bytes;
- computes all local consistency checks;
- emits a verbose proof object.

This reference is the executable mathematical oracle.

The optimized implementation must pass differential tests against it for every
field value and transcript output.

---

## 37. Wire-version sequence

### V7 wire R0 — audit/reference

- full V6 claim table;
- independent salts;
- separate link and V6 query streams;
- full 32-byte digests;
- explicit lengths;
- no frontier selector optimisation.

Purpose: establish correctness and exact proof census.

### V7 wire R1 — compact but modular

- shared multiproofs;
- first-compact schedules;
- full digests;
- independent or partially shared salts;
- separate query streams if required.

Purpose: prove the front-end theorem and measure realistic bytes/CU.

### V7 wire R2 — production candidate

- shared q16 fibre/slot schedule;
- compact claim inventory only if proved;
- typed shared salt only if proved;
- exact fixed profile;
- no optional fields;
- one top-level verifier path.

Every wire revision has a distinct discriminator and profile fingerprint.

---

## 38. Typed leaf design

Each leaf hash commits to:

- protocol version;
- profile fingerprint;
- tree type;
- packed canonical field values;
- salt;
- optionally the local row/fibre discriminator if not already unambiguously
  bound by the Merkle position.

Tree types must be non-colliding:

```text
V7_STAGE_A
V7_STAGE_B
V7_TARGET_G
```

Node hashes use a separate domain.

Reject:

- noncanonical M31 limbs;
- nonzero spare bits;
- wrong row widths;
- nonzero padding lanes where the profile requires zero;
- duplicate indices;
- out-of-range indices;
- under/over-consumed frontier;
- trailing bytes.

---

## 39. Transcript implementation

The transcript implementation is generated from a declarative schedule or
mirrors a single theorem-shaped Rust function.

Labels include the profile/version and separate:

- Stage-A root;
- Stage-B root;
- target root;
- code-switch messages;
- V6 backend messages;
- work witnesses;
- candidate streams;
- slot challenges.

A transcript snapshot test pins every absorbed byte and sampled challenge for
one deterministic fixture.

The host prover and SBF verifier replay the identical schedule.

---

## 40. Prover memory

The source tensors are larger in coefficient dimension but narrower in scalar
type than 29 independent QM31 rows.

Implement:

- streaming zeta by row block;
- streaming circle encoding;
- incremental Merkle construction;
- no duplicate full codeword copies;
- separate Stage-A and Stage-B lifetimes;
- target message construction after gamma;
- immediate zeroization of discarded attempt material;
- bounded first-good/first-compact attempts.

Measure:

- coefficient buffers;
- encoded buffers;
- Merkle storage;
- masks;
- scratch;
- peak RSS;
- grind time.

The memory goal is a genuine measured peak below 192 MiB, not merely raw
coefficient arithmetic.

---

# Part VIII — testing and adversarial audit

## 41. Algebraic KATs

Required known-answer tests:

- every one of 26 C1 singleton lanes;
- every one of 12 C2 lane/basis singleton limbs;
- all six padding lanes in Stage A;
- all four padding lanes in Stage B;
- gamma values `1`, `-1`, basis elements and random values;
- zeta/inverse-zeta round trips;
- literal width29 batch versus tensor restriction;
- reference versus optimized fold;
- scalar-extension encoder compatibility.

---

## 42. Transcript teeth

Each mutation must reject:

- Stage-A root changed after lambda;
- Stage-B root built under another lambda/chi;
- gamma changed after target root;
- target root from another profile;
- claim table changed after gamma;
- reused work nonce under another transcript;
- candidate counter skips an earlier compact schedule;
- slot order changed;
- link and V6 target roots differ;
- roots swapped between typed domains.

---

## 43. Commitment/opening teeth

Reject:

- a correct A opening under B's tag;
- a correct B opening under A's tag;
- correct values at the wrong index;
- one modified padding lane;
- one modified source row with unchanged target;
- one modified target fibre with unchanged source;
- duplicate query positions;
- shortened/extended frontier;
- reordered frontier;
- extra trailing digest;
- malformed packed limb at every byte boundary.

---

## 44. Soundness fixtures

Construct adversarial host fixtures for:

- arbitrary target root unrelated to A/B;
- target agreeing only on the sampled positions;
- one lane replaced by a high-degree received word;
- gamma-specific cancellation;
- different candidate codeword selected for each gamma;
- dense local agreement without a common decomposition;
- compactness-biased bad sets;
- cap exhaustion;
- all-zero and repeated-query schedules;
- malicious full claim table consistent only after batching.

These fixtures need not be computationally feasible attacks. They test that
the formal event taxonomy and rejection path cover the intended cases.

---

## 45. Fuzzing

Fuzz:

- parser;
- packed decoder;
- query derivation;
- frontier derivation;
- Merkle verifier;
- code-switch local evaluator;
- transcript driver;
- accepted entrypoint.

Properties:

- never panic;
- no out-of-bounds;
- deterministic replay;
- any accepted input reserializes canonically;
- reference and optimized arithmetic agree;
- all unused bytes are impossible.

---

# Part IX — measurement programme

## 46. Proof-size census

Every proof build emits:

```text
fixed semantic fields
claim table
roots
work witnesses
code-switch messages
opened A rows
opened B rows
opened G fibres
A frontier
B frontier
G frontier
V6 relation tail
padding/headers
total
```

No single “proof bytes” number without this decomposition.

Run a parameter sweep over:

- A/B heterogeneous versus both padded to 32;
- source rates;
- target rate;
- q14–q18 link queries;
- separate versus shared queries;
- per-tree versus total-frontier caps;
- independent versus typed-shared salts;
- final256 versus an extra reduction round.

---

## 47. CU probes

Build isolated SBF probes in this order:

1. packed Stage-A row decode and lane evaluation;
2. packed Stage-B row decode and basis reconstruction;
3. local target-link equality;
4. A binary multiproof;
5. B binary multiproof;
6. G binary multiproof;
7. first-compact and slot derivation;
8. code-switch sumcheck/reduction;
9. frozen V6 final256 evaluation;
10. frozen V6 relation tail;
11. semantic terminal;
12. full verifier without state mutation;
13. full verifier with atomic state mutation.

Maintain cumulative and isolated measurements.

A local optimisation is accepted only with:

- exact arithmetic equivalence test;
- updated SBF hash;
- repeated deterministic CU;
- no hidden increase elsewhere.

---

## 48. Main CU kill rule

At each cumulative stage, project only from already measured pieces.

Stop or redesign if:

```text
measured cumulative + conservative unmeasured allowance > 1.35M CU.
```

Do not justify an over-budget result by assuming a future Solana repricing.

A two-transaction receipt design may be retained as an emergency operational
fallback, but V7's primary target is one atomic verifier transaction.

---

# Part X — phased execution

## Phase 0 — V6 freeze

**Output**

- V6 tag;
- stable theorem interface;
- full CU/release bundle;
- reusable V6 backend evidence type.

**Kill condition**

- V6 itself remains mathematically or operationally unstable.

---

## Phase 1 — pure split-tensor algebra

**Implement/prove**

- Stage A/B definitions;
- zeta and inverse;
- basis reconstruction;
- exact width29 identity;
- profile fingerprints;
- KAT generator.

**Deliverables**

```text
V7SplitTensor/BooleanZeta.lean
V7SplitTensor/GammaRestriction.lean
crates/aspis-core/src/v7_lane_zeta.rs
results/v7/lane_kats.json
```

**Gate**

- no `sorry`;
- every singleton lane passes;
- reference and optimized host arithmetic agree.

---

## Phase 2 — theorem applicability audit

**Research**

- identify exact S-two/circle-code cross-domain theorem;
- identify exact polynomial-generator hypotheses;
- check mixed source arities;
- check target re-encoding;
- check response strategies varying with gamma;
- derive finite caps.

**Deliverables**

```text
docs/v7-code-switch-theorem-audit.md
V7SplitTensor/PublishedCodeSwitchInterfaces.lean
```

**Gate**

- exact predicate supported or clearly reducible;
- otherwise status `BLOCKED` and pivot to random-point fallback.

No SBF work before this gate.

---

## Phase 3 — host reference code switch

**Implement**

- literal source encoders;
- staged roots;
- target construction;
- separate query streams;
- local checks;
- verbose proof object.

**Measure**

- proof bytes;
- peak memory;
- encoding time;
- grind time.

**Gate**

- reference proof ≤34 KiB;
- projected production proof ≤31 KiB;
- peak memory ≤256 MiB;
- no hidden all-four-source-row requirement.

---

## Phase 4 — deterministic formal extraction

**Prove**

- ideal verifier;
- consistency sets;
- candidate lists;
- query failure;
- code-switch failure;
- extraction of one common target;
- composition with abstract V6 backend.

**Gate**

- accepted proof outside named events yields one target message used on both
  sides of the composition.

---

## Phase 5 — query and frontier formalisation

**Implement/prove**

- first-compact sampler;
- separate-stream probability;
- generated frontier certificate;
- shared fibre/slot sampler;
- joint conditioning;
- exact q bounds.

**Gate**

- production compactness probability leaves the intended security margin;
- cap exhaustion is explicitly budgeted.

---

## Phase 6 — SBF kernel prototype

**Implement**

- no-allocation packed arithmetic;
- typed binary multiproofs;
- local code-switch check;
- transcript skeleton;
- CU probes.

**Gate**

- front-end plus frozen V6 expensive slice projects below 1.25M CU;
- hard stop if projected full path exceeds 1.35M.

---

## Phase 7 — complete wire and prover

**Implement**

- production candidate grammar;
- serializer/parser;
- full prover;
- exact transcript;
- work positions;
- mutation/fuzz suite.

**Gate**

- proof target achieved;
- prover work/memory targets achieved;
- all proof bytes consumed exactly once.

---

## Phase 8 — complete hiding theorem

**Prove**

- exact V7 affine view;
- staged mask translation;
- rank certificate;
- typed-salt hybrid;
- simulator;
- pairwise witness bound.

**Gate**

- no “V6 hiding probably still applies” premise;
- at least 100-bit final hiding bound.

---

## Phase 9 — security ledger and BCS

**Prove**

- pointwise failure inclusion;
- exact event probabilities;
- exact work normalization;
- exact round count;
- primitive allowance;
- final ≥100-bit theorem.

**Gate**

- every event named;
- no provisional copied V6 term;
- no decimal-only conclusion.

---

## Phase 10 — Rust-to-Lean closure

**Extract/prove**

- parser;
- tensor evaluator;
- query sampler;
- Merkle verifier;
- code-switch verifier;
- V6 bridge;
- top-level entrypoint.

Construct one `AcceptedV7ExecutionEvidence`.

**Gate**

- one accepted translated execution supplies all common witnesses;
- no independent existential executions;
- CI replays the complete closure.

---

## Phase 11 — deployment and release

**Execute**

- pinned local-validator runs;
- full lifecycle;
- mainnet demonstration only after audit gates;
- cleanup/rent recovery;
- exact binary/proof/RPC archive.

**Release claim**

Use language equivalent to:

> A transparent staged split-tensor private-spend verifier, composed with the
> frozen V6 one-fold backend, executed atomically on Solana. The finite
> protocol arithmetic and implementation correspondence are machine checked;
> the remaining computational assumptions are listed explicitly.

Do not collapse all assumptions into “formally verified”.

---

# Part XI — research-cryptography standard for future Aspis work

## 49. Required artefacts for every research protocol

Every future protocol branch contains:

```text
docs/<protocol>-spec.md
docs/<protocol>-theorem-audit.md
docs/<protocol>-security-ledger.md
docs/<protocol>-source-map.md
formal/<protocol>/...
results/<protocol>/proof-census.json
results/<protocol>/cu.json
results/<protocol>/memory.json
vectors/<protocol>/...
manifest/<protocol>.json
```

---

## 50. Claim register

Each important claim has an ID and status:

| ID | Claim | Class | Evidence | Status |
|---|---|---|---|---|
| ALG-001 | tensor gamma identity | KERNEL | Lean theorem | closed |
| PAPER-001 | code-switch reduction | PAPER | exact predicate | open/closed |
| HASH-001 | SHA-256 collision bound | ASSUMPTION | ledger interface | external |
| IMPL-001 | SBF CU | MEASUREMENT | pinned result | measured |
| SRC-001 | Rust verifier matches model | KERNEL + tool boundary | Aeneas | open |

The README is generated from or checked against this register.

---

## 51. Rules

1. **No parameter number without a theorem or checked certificate.**
2. **No theorem name without its exact instantiated predicate.**
3. **No security number without a pointwise failure-event inclusion.**
4. **No implementation claim from a host model.**
5. **No source claim from separate existential executions.**
6. **No profile drift between prover, verifier, paper and Lean.**
7. **No hidden challenge-order dependency.**
8. **No unmeasured CU projection presented as a result.**
9. **No hiding claim based only on salts when field values are opened.**
10. **No production merge while a theorem audit says `BLOCKED`.**
11. **Preserve failed designs and explain why they failed.**
12. **Freeze reproducible bytes, not merely source tags.**

---

## 52. CI requirements

Every V7 push runs:

- Rust formatting/lints/tests;
- host reference/optimized differential tests;
- KAT replay;
- Lean build;
- `#print axioms` policy check;
- generated-certificate verification;
- Aeneas extraction/replay once source work starts;
- proof-census regression;
- SBF build for probe branches;
- exact manifest/profile fingerprint check.

Every production release additionally runs:

- clean-container build;
- exact SBF parity;
- deterministic proof reproduction;
- local-validator lifecycle;
- mutation suite;
- archived RPC replay.

---

# Part XII — final recommendation

## 53. Build order

The correct order is:

```text
finish and freeze V6
    ↓
prove 26+3 split-tensor algebra
    ↓
audit exact code-switch theorem
    ↓
build separate-query host reference
    ↓
prove deterministic extraction and V6 composition
    ↓
measure proof/memory
    ↓
build SBF kernels
    ↓
optimise to shared q16 fibre/slot schedule
    ↓
prove full hiding and security ledger
    ↓
close one accepted Rust execution
    ↓
deploy
```

## 54. Primary research question

The decisive question is not whether the gamma tensor identity works. It does.

The decisive question is:

> Can a staged, mixed-arity M31 circle-code partial-evaluation proof bind the
> post-gamma target root to the two pre-gamma source roots for at most 2,840
> bytes of net overhead and acceptable SBF cost?

Everything before that question is preparation. Everything after it is
engineering and assurance.

## 55. Expected outcomes

### Best case

- 28–30 KiB proof;
- one atomic verifier transaction;
- lower prover memory than V6;
- V6 semantics and terminal reused;
- one new, explicitly isolated theorem interface.

### Acceptable case

- 30–32 KiB proof;
- meaningful memory or CU improvement;
- same 100-bit target and full formal chain.

### Stop case

- theorem application requires a new unbounded conjecture;
- source rows must be opened four-at-a-time;
- link overhead exceeds the 2,840-byte budget;
- full verifier exceeds 1.35M CU;
- hiding requires enough extra masks to erase the size gain;
- complexity increases without at least a 10% operational improvement.

In the stop case, retain frozen V6 and archive V7 as a documented negative
result.

# Profile 23 publication plan

Status: authoring plan, not a mainnet claim. The canonical local Profile 23
release certificate is 30/30 after the proof-account-finalization and
live-pool changes. Local finalized proof-account fixtures are sealed. The
configured program address in the frozen local build is
`7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue`; that address is not evidence
of deployment. This plan does not assert a mainnet-beta event, an audit,
production readiness, or any historical “first.”

## 1. Publication objective

Write a self-contained cryptography-and-systems paper showing how Aspis
constructs and verifies a transparent, computationally hiding shielded-spend
proof under Solana's per-transaction compute limit. The paper's primary object
is one verification/state-transition transaction consuming a finalized,
pre-uploaded proof account. Proof-account creation, chunk upload, and
`FinalizeProof` are prior transactions and must remain adjacent to every
“one-transaction” statement.

The paper must do four things at publication quality:

1. specify the exact shielded-spend statement and protocol, rather than asking
   readers to reconstruct them from implementation notes;
2. give a theorem dependency chain for proven-Johnson soundness and
   complete-view computational hiding;
3. connect those theorems to the byte-level SBF implementation and its atomic
   account transition; and
4. make every numeric claim reproducible from a pinned source revision,
   machine-readable artifact, proof, binary, toolchain, and public transaction
   when the mainnet gate is eventually closed.

The paper must call the PCS a “WHIR-style multilinear PCS” and then specify its
differences. It must not claim protocol equivalence to paper WHIR.

## 2. Claim discipline and release gates

### 2.1 Claims available before mainnet

Subject to a fresh green release certificate after all current code changes,
the paper may report a locally reproduced Agave result with these qualifiers:

> For the pinned Profile 23 source, proof, default SBF binary, and Agave
> runtime, one instruction path verifies a transparent, computationally hiding
> shielded-spend proof from a finalized, pre-uploaded proof account and
> atomically records its nullifier and pool-state transition below 1.4M CU.

This sentence is a reproducibility claim, not a mainnet deployment, audit, or
production-readiness claim.

### 2.2 Claims blocked until mainnet evidence exists

Do not put “on mainnet-beta,” an explorer link, or a novelty claim in the
title, abstract, introduction, press copy, or repository headline until the
mainnet artifact proves all of the following:

- the transaction is on mainnet-beta, successful, and finalized;
- the invoked program is bound to the released default SBF identity;
- the transaction consumes the finalized proof account bound to the released
  proof hash;
- the complete proof is verified in that transaction;
- the nullifier marker and pool state are mutated atomically in that same
  transaction;
- the recorded compute consumption is at most 1,400,000 CU; and
- the signature, slot, program ID, proof-account address, release-certificate
  hash, proof hash, source revision, and explorer/RPC evidence are public.

The day-of novelty scan must then be rerun on the actual publication date.
Only if that dated scan remains negative and the mainnet evidence gate is
green may the exact, qualified template in
`docs/profile23-novelty-rescan-2026-07-13.md` be used. Keep both “to our
knowledge” and the dated-search qualifier. Do not generalize it to “first
private payment,” “first shielded pool,” “first STARK verifier,” or “first
transparent verifier” on Solana; public prior art falsifies those broader
claims.

### 2.3 Claims that remain out of scope

The paper must not claim:

- statistical HVZK;
- hiding in the standard model;
- a standalone SHA-256 PRG theorem;
- privacy against local filesystem, scheduler/timing, power, thermal, memory,
  or remote-prover/miner-traffic observations;
- fee, relayer, wallet, network-metadata, or account-graph privacy;
- an audit or production readiness;
- the complete proof-account lifecycle in one transaction;
- equivalence to paper WHIR; or
- post-quantum security without a separate assumption-by-assumption analysis.

### 2.4 Numeric claim rules

The manuscript must not copy numbers manually from prose notes. A paper table
generator should read the final release JSON and fail if its source hashes do
not match the frozen artifact manifest.

The soundness headline is the Profile 23 selected ledger:

```text
selected whole-ledger floor       101.30230658283051 bits
coarse whole-ledger sensitivity   100.80652861422749 bits
```

The selected analysis applies the factor three only to the final q16 miss and
then applies the conservative factor 40. The coarse sensitivity recomputes the
whole-ledger-times-three rule from Profile 23's own changed terms and its 32
BCS boundaries. The inherited `100.87976635696354` value is stale Profile 22
arithmetic and must not appear in the paper. Prefer “101.30-bit selected
ledger, remaining above 100.80 bits under the coarse sensitivity” or simply
“over 100 bits in the proven Johnson/MCA regime.”

The hiding theorem has two different bounds:

```text
real witness view versus Sim23    104.11238518950232 bits
two-witness pairwise view         103.11238518950232 bits
```

The abstract's hiding claim must use the pairwise value. The one-bit loss is
the factor two from
`Real(x,w0) -> Sim23(x) -> Real(x,w1)`. The paper must not call the one-sided
104.112-bit value a pairwise bound.

The frozen local release facts are a 61,599-byte proof with SHA-256
`35c4e79316bf4a2af1951e5d2f41b6ebb4ebb7bd1e91a3ba93c52e549bfe7949`, a
6,870,048-byte default SBF with SHA-256
`6b64baf559dcddbd6f9b1af1205effeb6afae6a5746a44421e8826251fe4cffb`, and a
1,207,123-CU worst path with 192,877 CU of headroom. The manuscript must still
use generated macros instead of freehand constants so later repins fail
closed.

### 2.5 Security games and quantifiers that the paper must state

The manuscript must define one common public-parameter object `pp23`, derived
deterministically from the pinned source, generated constants, code domains,
hash-domain tags, and Profile 23 schedule. “Transparent” means that generating
`pp23` uses no structured reference string, secret trapdoor, or trusted setup.
It does not remove the random-oracle, SHA-256, Poseidon2, code-transport, or
implementation assumptions, all of which must be listed separately.

The adversary in the stated theorems is classical and probabilistic; no
post-quantum claim is implied. All probabilities must name their randomness,
including the random oracle, honest prover coins, bounded-attempt entropy,
and verifier coins before Fiat–Shamir. The following games are mandatory:

1. **Relation soundness.** A classical adversary with at most `Q_H` adaptive
   random-oracle queries chooses the public pre-state, statement, accounts,
   and proof-account bytes. It wins if the pinned verifier accepts and applies
   a transition while no witness satisfies `R23(x,w)`. The theorem is
   argument soundness for the exact relation; do not call it knowledge
   soundness unless an extractor and extraction error are supplied.
2. **Interactive-to-Fiat–Shamir soundness.** Define the interactive failure
   event first, then the BCS/ROM game with all 32 prover-message boundaries,
   adaptive oracle queries, q3 selector message, and proof-or-Abort behavior.
   Keep the mathematical failure bound separate from parser, runtime, and CU
   measurements.
3. **Real versus simulator.** For every fixed public statement `x`, valid
   witness `w in R23(x)`, auxiliary string `aux`, classical distinguisher with
   `Q_H <= 2^128` adaptive queries including post-output queries, and at most
   `A=16` honest attempts, compare the exact declared output
   `View23(x,w) in {Proof(bytes, accounts, logs, mutation), Abort}` with
   `Sim23(x)`. State whether `aux` may depend on `(x,w)` and give the same
   oracle consistently to the experiment and distinguisher.
4. **Pairwise witness hiding.** Let the adversary choose
   `(x,w0,w1,aux)` with `R23(x,w0)=R23(x,w1)=1`; sample `b <- {0,1}` and give
   it `View23(x,wb)` plus `aux`. Bound its distinguishing advantage through
   `Real(x,w0) -> Sim23(x) -> Real(x,w1)`. Include variable proof length,
   selector, attempt count as modeled, and `Abort`; do not condition silently
   on successful proving.
5. **Atomic-transition safety.** Define the accepted pre-state and deterministic
   post-state independently of the cryptographic relation. State which facts
   follow from Solana transaction rollback and writable-account locking and
   which are implementation-refinement propositions supported by code and
   adversarial tests.

The term “complete view” always means the declared verifier-visible
Proof-or-Abort channel: finalized proof-account bytes, opened records and
frontiers, transcript/work values, proof length, transaction framing and
program logs, and deterministic public account mutation. It does not include
network traffic, transaction origin, fee payer linkage, the account graph,
local worker state, timing, storage, or physical side channels. Every theorem
and abstract claim must say “complete declared verifier view” or link directly
to this definition.

### 2.6 Exact one-input/one-output relation obligation

The paper must define `R23(x,w)` as the implemented atomic-v3, depth-20,
same-private-path replacement relation, not a generic shielded pool. The
public input `x` contains the statement version and depth, pool public key and
pre-transition sequence, current anchor, nullifier, output-note commitment,
replacement anchor, asset ID, and public fee, all in their canonical byte and
M31 encodings. The witness `w` contains the nullifier key, input/output salts,
output owner key, input asset ID, private input/output values, one private
depth-20 index and sibling path, and the exact range-lookup limbs used by the
trace.

The relation must write and prove these obligations explicitly:

```text
owner_key       = OwnerKey(nullifier_key)
input_note      = Note(owner_key, value, asset_id, input_salt)
nullifier       = Nullifier(nullifier_key, input_salt)
output_note     = Note(output_owner_key, value_out, asset_id, output_salt)
output_note     = public output_commitment
RootV3(input_note, siblings, private_index)  = current_anchor
RootV3(output_note, siblings, private_index) = output_anchor
input_asset_id  = public asset_id
0 <= value, value_out, fee < 2^30
value_out + fee = value, without integer overflow
```

The implementation precondition additionally requires the pool account to
match `(pool, sequence, current_anchor)`, the canonical nullifier PDA to be
unspent, the proof account to be finalized and owned by the configured
program, and every address, owner, length, version, reserved byte, field limb,
asset ID, and fee encoding to be canonical. Acceptance increments the pool
sequence exactly once, replaces its anchor with `output_anchor`, and records
the `(pool,nullifier)` marker atomically. The paper must not generalize this
relation to multiple inputs, multiple outputs, multiple assets in one spend,
public append semantics, arbitrary Merkle updates, or a complete wallet and
relayer protocol.

## 3. Paper thesis and contribution framing

The paper's thesis is not merely that an optimized verifier fits. It is that a
specific alignment of proof-system design, complete-view masking, transcript
scheduling, and SBF implementation makes the exact shielded-spend atom
simultaneously measurable and analyzable under a hard execution cap.

Proposed contributions, subject to external review of novelty and correctness:

1. **A fully specified transparent shielded-spend atom for Solana.** The
   statement binds pool identity and revision, current anchor, nullifier,
   output commitment, value/range constraints, and public transition data;
   the accepting instruction mutates the pool and nullifier state atomically.
2. **A proven-Johnson, rate-1/512 Profile 23 instantiation.** The argument
   transports the circle FFT subspace through a scaled-GRS Johnson analysis,
   polynomial-generator MCA, arity-four fold/list commutation, OOD binding,
   without-replacement q16 sampling, and a 32-boundary BCS ledger. It does not
   rely on the refuted capacity conjecture.
3. **A complete-view computational-hiding construction.** Good23 certifies
   exact affine image coverage, yielding an explicit witness-free field
   simulator with `epsilon_aff=0`; private Merkle, transcript, work, first-Good,
   and fixed-release hybrids extend it to finalized proof-account bytes,
   public logs, and deterministic state mutation.
4. **An execution-cap-aware implementation methodology.** Generated layout
   certificates, differential/adversarial teeth, production-feature isolation,
   and overlap-subtracted integrated CU ledgers bind the mathematical object
   to the measured default SBF binary.
5. **A public reproducibility package.** The package should bind source,
   theorem artifacts, generated constants, proof bytes, SBF bytes, runtime,
   release certificate, raw measurements, and—only after it exists—the
   finalized mainnet transaction.

Do not describe any item as novel merely because it was difficult to build.
The introduction should distinguish “our construction,” “our implementation,”
and “our proof,” and related work should identify inherited theorems precisely.

## 4. Theorem and lemma dependency order

The manuscript should expose two proof branches and one implementation branch,
then join them in the final system statement.

```text
frozen statement/layout/FS schedule
        |
        +--> circle-code/GRS isometry
        |       -> Johnson list bound
        |       -> polynomial-generator MCA
        |       -> arity-four fold/list commutation
        |       -> OOD + relation binding
        |       -> q3 selector correctness + q16 sampling
        |       -> local algebra terms
        |       -> BCS(32) + union ledger
        |       -> selected 101.302 / coarse 100.807
        |
        +--> Good23 component certificates
        |       -> complete affine image equality
        |       -> constant-cardinality preimages / uniform image law
        |       -> witness-free Sim23 field view
        |       -> q3 first-Good hiding law + cap-16/Abort law
        |       -> private-Merkle/EPRO/work hybrids
        |       -> real-vs-Sim23 104.112
        |       -> pairwise-witness 103.112
        |
        +--> canonical parser and account preconditions
                -> finalized proof-account state machine
                -> loader/programdata/upgrade assumptions
                -> host/SBF parity and corruption teeth
                -> verify-before-write atomic transition
                -> integrated overlap-subtracted CU ledger
                -> configured local default-binary identity
```

The formal section should state and prove results in this order:

1. **Definition (Profile 23 public statement, witness, and relation).** Give
   `R23(x,w)` equation by equation as required in Section 2.6. List every
   public field, private field, range, canonical encoding, and transition
   precondition; explicitly limit the theorem to one input and one output.
2. **Definition (transparent parameters and security games).** Define `pp23`,
   setup assumptions, relation-soundness and BCS games, real-versus-simulator
   and pairwise-hiding games, the complete declared view, auxiliary input,
   query/attempt bounds, and all excluded observables.
3. **Definition (frozen algebra and schedule).** Define M31/CM31/QM31, the
   circle domains, rate 1/512, q16 sampling, width 29, generator order
   `semantic0..15, mask16..25, H26, G27, D28`, `factor(D)=0`, q3 branch
   derivation, cap-16 retry, and fixed Proof-or-Abort release.
4. **Lemma (circle-subspace transport).** State the exact isometry or linear
   constraint carrying the circle FFT space into the scaled GRS object. Cite
   pinned theorem versions and state which step is proved locally.
5. **Lemma (Johnson/MCA batching).** Specialize the published
   polynomial-generator MCA theorem to the exact code, threshold, scalar
   powers, and two commitment phases.
6. **Lemma (fold/list and OOD consistency).** Connect arity-four folds,
   ambient-list commutation, terminal checks, two OOD samples, and the Boolean
   multilinear relation.
7. **Lemma (local algebraic binding).** Enumerate polynomial batching,
   gamma nonzero/collision events, copy/range poles, theta compression,
   zerocheck, helper, and assumption terms. Every term must map to one row in
   the machine ledger.
8. **Lemma (selector correctness and soundness conditioning).** Prove that
   three q16 candidates are derived from distinct post-final-nonce,
   domain-separated branches; `Good23` is schedule-only; the selected branch
   is the least Good branch; and an all-bad attempt retries or yields the
   declared `Abort`. Show that the committed word is fixed before candidate
   derivation and justify why the factor three applies to the final q16 miss,
   rather than treating the selector as a prover-controlled free choice.
9. **Theorem (interactive soundness).** Combine the previous lemmas with
   without-replacement q16 sampling and the selector-soundness lemma.
10. **Theorem (Fiat–Shamir/BCS soundness).** Apply the explicit attacker-query
   bound and 32 message boundaries, then state the selected and coarse floors.
11. **Lemma (Good23 complete product).** Prove the three certificate blocks,
    source guards, degrees, nonzero minors, and schedule-only decision rule.
    Require a deterministic certificate generator and a separately
    implemented checker that recomputes the public maps from the frozen layout
    rather than trusting certificate-provided matrices.
12. **Lemma (complete affine image and uniform preimages).** For each accepted
    schedule `s`, prove that the homogeneous solution space of the public
    field identities equals
    `V_s = image(A_s)`. State the dimensions, rank, kernel cardinality, and
    show that every `v in V_s` has exactly `|ker(A_s)|` mask preimages.
    Conclude that uniform ideal mask coins induce the uniform distribution on
    `V_s`; fingerprints and tests alone are not this proof.
13. **Construction (explicit `Sim23(x)`).** Row-reduce public identities,
    choose canonical free coordinates, sample uniformly from a canonical
    echelon basis of `V_s`, and wrap that field view through the remaining
    protocol layers without querying a witness.
14. **Lemma (selection hiding and Abort law).** In the programmed-oracle
    experiment, show that all three branch schedules, their Good bits, the
    least-Good selector, and the all-bad event have a witness-independent joint
    law. Include cap-16 `Abort` in the output distribution without conditioning
    the privacy theorem on success. This lemma is distinct from Item 8.
15. **Lemma (private Merkle, EPRO, and work simulation).** Give the explicit
    hybrid chain from the real field view to final serialized output. Account
    separately for hidden/prequeried inputs, programmed-state collisions,
    adaptive post-output queries, canonical-minimum nonces, proof-account
    framing, and deterministic mutation.
16. **Theorem (complete-view real versus simulator).** State the exact model,
    `Q_H`, attempt bound, error formula, and 104.112-bit floor.
17. **Corollary (pairwise witness hiding).** Apply the triangle inequality and
    state the 103.112-bit floor.
18. **Lemma (finalized-account state machine).** Define create, authorized
    chunk write, finalize, verify, and rejection transitions. Prove finalization
    irreversible only relative to the frozen program logic and its account
    ownership checks; list loader, programdata, upgrade-authority, account
    close/reallocation, and governance assumptions explicitly.
19. **Proposition (atomic implementation refinement).** State exactly what is
    established by parser parity, account checks, pool initialization,
    rollback, duplicate/race teeth, and verify-before-write ordering. Do not
    present tests as a formal proof of memory safety or production security.
20. **System theorem.** Join the soundness, hiding, transparent-setup,
    finalized-account, and atomic-state properties for the frozen local
    release object. Keep CU and any future mainnet observations as evaluated
    properties, not mathematical theorem premises.

Each imported theorem needs a version/date, theorem number, hypotheses, and a
paragraph showing that Profile 23 satisfies those hypotheses. Avoid a proof
that consists only of citations plus a final numeric ledger.

## 5. Explicit simulator presentation

`Sim23` is central enough to receive pseudocode, not just prose. The paper must
show these inputs and steps:

```text
Sim23(x):
  sample an attempt and q3 schedules using the programmed-oracle experiment
  evaluate public, schedule-only Good23 on all three schedules
  select the least Good schedule, or repeat up to cap 16 and output Abort
  form the public affine identity system for x and the selected schedule
  compute canonical y_public(x,s) and an echelon basis of V_s = image(A_s)
  sample v uniformly from V_s and set the complete field view to y_public+v
  simulate salted Merkle leaves/frontiers and program the transcript lazily
  sample canonical work nonces under the truncated-geometric minimum law
  serialize the selected Proof, including its schedule-dependent length
  apply the deterministic proof-account-finalization and public-state views
```

The proof must explain why this is witness-free, why uniform mask preimages
induce a uniform distribution on `V_s`, and why `Good23` consumes only public
schedule data. It must also state that no direct one-copy real-to-real coupling
has been proved; this is why pairwise hiding loses one bit.

The modeled public output includes:

- complete finalized proof-account bytes;
- roots, opened `value || salt` records, and frontiers;
- Fiat–Shamir and work nonces;
- proof length and transaction framing/logs;
- the public selector and failure/abort event; and
- deterministic public account mutation.

The side-channel sentence must travel with every hiding table:

> `epsilon_side=0` is by definition of the fixed public Proof-or-Abort channel,
> not a proof about excluded filesystem, scheduler/timing, power, thermal,
> memory, or remote-prover/miner traffic.

### 5.1 Required EPRO hybrid chain

The hiding proof must expose every distribution change rather than referring
to one aggregate “EPRO simulation.” At minimum, name the following hybrids,
their coupling, and their individual bad event:

1. `H0`: the honest Profile 23 prover on `(x,w)` with its real mask, salt,
   attempt, transcript, Merkle, and work randomness;
2. `H1`: replace the complete non-hash field view by the uniform affine-image
   sample certified by Good23 and the constant-cardinality preimage lemma;
3. `H2`: replace hidden salted-leaf preimages and mask/field-expander inputs
   lazily, while keeping every opened `value || salt` record and authentication
   frontier verifier-consistent;
4. `H3`: program the private-Merkle roots and transcript at fresh,
   domain-separated inputs, charging any adversarial prequery to the exact
   `A*C*Q_H/2^256` inventory term;
5. `H4`: replace the remaining oracle states by lazy uniform states, charging
   collisions among programmed inputs to the exact quadratic term and
   continuing to answer adaptive queries after the public output;
6. `H5`: generate all three post-final-nonce schedules, Good bits, least-Good
   selector, retries, and cap-16 `Abort` from their witness-independent joint
   law;
7. `H6`: replace each of the six work nonces by the exact canonical-minimum
   truncated-geometric distribution, program earlier failures and the first
   success, and charge only the stated exhaustion event;
8. `H7`: serialize the same schedule-dependent proof length and deterministically
   construct the finalized proof-account frame, program logs, and public
   account transition; and
9. `H8`: the output of the explicit witness-free `Sim23(x)`.

For each adjacent pair, the paper must identify the oracle domains, number of
distinct inputs rather than raw SHA invocations, whether the program point is
chosen before or after adversarial queries, and how later queries are
answered. The `C=969,993` inventory must be reproduced by family in a table
and generated from the canonical artifact. A shared bug in the certificate
generator and checker is not independent evidence, and privacy regressions
are teeth rather than substitutes for these hybrid arguments.

## 6. Rank-certificate provenance

An expert reader will notice that the complete-Good rank certificate is
computed on a Profile 22 fixture. State the transfer chain explicitly:

1. the ranks are functions of the frozen layout and public schedule, not of a
   witness;
2. the certificate records the three component fingerprints and bound product
   provenance;
3. the release gate checks the layout and Good23 definition fingerprints
   against live code;
4. the frozen local production-path audit runs Good23 on all three selector
   branches and checks
   the least-Good selection law; and
5. an independent checker reconstructs the public matrices from layout and
   schedule inputs, verifies dimensions, ranks, pivots, kernel cardinalities,
   nonzero minors, and the bound product fingerprint without accepting
   certificate-supplied matrices as authoritative; and
6. only this chain transfers the Profile 22 fixture certificate to the
   frozen Profile 23 schedule.

The generator and checker should use distinct derivation paths or
implementations, and both must hard-fail on layout, degree, source-set,
generator-order, or `Good23`-definition drift. Publish their inputs, outputs,
runtime, field-arithmetic convention, and a negative certificate that each
checker rejects.

Do not write that the certificate was “computed on the production proof.”
Refer to the release gate by its stable name
`layout_and_good23_fingerprints_match_live_code`, not its ordinal, because the
gate count can change.

## 7. Implementation and transaction section

Present the account lifecycle as two scopes:

```text
prior transactions: create proof account -> chunk uploads -> FinalizeProof
headline transaction: load finalized account -> verify -> recheck writable
                      state -> create/write nullifier marker -> update pool
```

The finalization step replaces the upload authority in the unchanged 40-byte
header with an all-zero sentinel. Production verification must reject a
mutable proof account. The paper should show why finalization is
authority-bound and irreversible in the implemented state machine, while
avoiding a broader claim about account deletion, chain governance, or program
upgrades.

The state-machine statement must be relative to an exact program version.
An Aspis-owned account is not intrinsically immutable: a future instruction
in an upgraded program could write, close, reallocate, or reinterpret it. For
the frozen local claim, bind the configured address to the measured SBF hash
and state that loader state and upgrade governance were not established by a
mainnet observation. For any later deployment claim, record the executable
Program account, ProgramData address and owner, deployed code bytes/hash,
remaining ProgramData capacity, finalized slot, and upgrade-authority state.
If an authority remains, identify it and treat replacement of the code as an
explicit trust assumption; call the program immutable only after the loader
reports no upgrade authority and the state is finalized.

The lifecycle proof and tests must cover:

- fresh, zero-filled, exactly sized, program-owned proof-account creation;
- signer-bound initialization, exact total length, authorized bounded chunk
  writes, byte-for-byte readback, and rejection of gaps, truncation,
  overlapping conflicting writes, out-of-bounds writes, wrong owner, and
  account-type substitution;
- one-way `FinalizeProof` under the stored authority, double-finalize and
  write-after-finalize rejection, payload preservation, and verification's
  zero-sentinel requirement;
- signed, one-shot `InitializeAtomicPool` on an exact zero-filled 48-byte
  program-owned account, canonical anchor, nonoverflowing sequence, and
  rejection of reinitialization, front-running without the account signature,
  and proof-account/pool-account retyping; and
- the effect of close/reallocation capabilities, loader upgrades, governance,
  and account ownership on every “irreversible” or “sealed” statement.

For the accepting transaction, describe this order:

1. validate account owners, sizes, mutability, canonical addresses, pool
   revision, and anchor;
2. derive the statement and statement digest from accounts;
3. load and parse the finalized proof;
4. verify the complete proof before any fallible state mutation;
5. prepare the marker or CPI and reacquire/recheck mutable state;
6. construct final pool and nullifier images; and
7. commit writes atomically.

Report corrupt-proof rollback, duplicate rejection, exact post-state images,
the same-pool/same-nullifier race, and different-nullifier/same-pool
serialization as adversarial test evidence. Make clear which race is
exercised only on the canonical System-account creation path and which result
is inferred from Solana writable-account locking rather than directly tested.

## 8. CU measurement methodology

The publication number must come from a single integrated instruction under a
pinned validator/runtime and default production binary. Standalone probes are
diagnostics only. The ledger rule is:

> derive disjoint intervals from ordered in-instruction CU markers, include
> setup and tail costs, and require the interval sum to equal the literal
> transaction simulation total exactly.

Never sum standalone phase probes. Never add an optimization saving to a total
unless the replacement and displaced work are measured in the same integrated
instruction. Variant comparisons require the same proof, runtime, heap,
compute-budget instructions, account shape, and binary feature context.

The final artifact has a 19-CU measurement-context discrepancy that must be
named, not normalized away:

```text
diagnostic acceptance tag 59             1,202,920 CU
production-only tag-59 baseline          1,202,939 CU
                                             difference: 19 CU
```

The diagnostic acceptance total reconciles its own phase ledger. The
production tag-60 totals reconcile from their own production-only tag-59
baselines plus measured mutation increments. These are distinct
binary/feature measurement contexts. The causal source of the 19 CU has not
been established by the artifacts, so the paper must not label it “marker
overhead” unless a controlled experiment proves that. Use the production-only
baseline for production headroom and the diagnostic total only for its phase
waterfall. The historical 1,202,868-versus-1,202,876 comparison and its 8-CU
difference are superseded by the final sealed-account build and may appear
only when explicitly labeled as history.

The evaluation should include:

- exact validator and Solana toolchain identifiers;
- host CPU/OS for prover timings, clearly separated from validator CU;
- SBF feature set, binary length, and SHA-256;
- proof path, length, SHA-256, and mined/unmined classification;
- account-owner path and pre-state;
- literal tag-59 and tag-60 CU, integrated ledger, and headroom;
- repeated local runs or an explanation of deterministic equality;
- one public finalized mainnet measurement only after it exists; and
- all failures/rejections, not only the accepting run.

### 8.1 Reproduction tiers

The artifact must separate verification from expensive regeneration so a
reviewer can choose a meaningful tier. Every tier names expected wall time,
cores, memory, disk, network access, nondeterminism, and its exact output:

1. **Tier 0: immutable-bundle audit.** Rehash cached source metadata, proof,
   SBF, JSON, generated constants, and paper macros; verify all cross-links,
   the 30/30 certificate, and stale-claim guards without compiling.
2. **Tier 1: fast semantic and teeth suite.** Run parser, transcript, relation,
   corruption, finalization, rollback, and privacy regression tests against
   cached fixtures. State which tests are deterministic and why.
3. **Tier 2: clean default build.** In a pinned container or Nix environment,
   rebuild the manifest-default SBF from a clean tree and require byte-for-byte
   equality, length, hash, feature set, and configured address consistency.
4. **Tier 3: local Agave replay.** Start the pinned validator/genesis/runtime,
   replay account setup and both tag-60 mutation paths, archive raw RPC
   requests/responses and validator logs, and reproduce literal CU plus exact
   pre/post account images.
5. **Tier 4: slow theorem/certificate jobs.** Regenerate and independently
   check Good23/rank products, ledger arithmetic, affine-image evidence,
   privacy inventory, and ignored adversarial tests. Distinguish a checker
   from a generator that shares the same matrices.
6. **Tier 5: fresh proving and mining.** Generate a fresh statement/witness,
   proof attempts, q3 schedules, PoW-mined proof, finalized account image, and
   accepting validator transaction. Report attempt counts and preserve random
   seeds only where doing so does not contradict the privacy model.

The bundle must retain the raw validator feature set, genesis, compute-budget
and heap-frame instructions, transaction bytes, RPC results, account dumps,
logs, rejection codes, host CPU/OS, Rust/Solana/Agave versions, lockfiles, and
container digest. A summarized JSON without the raw evidence is insufficient
for a systems artifact.

### 8.2 End-to-end lifecycle and prover costs

The headline CU number excludes proof-account creation, chunk upload, and
finalization by definition, but the evaluation must still measure and report
them. Give the number and size of setup transactions, CU, fees, rent-exempt
balance and retained storage, upload chunking, readback/finalization latency,
proof-generation wall time and peak memory, q3/cap-16 attempts and empirical
Abort rate, canonical-work mining time, and complete time-to-spend. Separate
deterministic validator CU from host-dependent prover/miner measurements.

Include controlled ablations for the principal structural optimizations. Each
ablation must use compatible statements, proofs, runtime settings, and feature
contexts or state why a literal comparison is impossible. Do not infer a
component saving by subtracting standalone probes or by comparing historical
profiles with different security parameters.

### 8.3 Throughput, contention, and failure evaluation

The pool account is writable on every accepted spend and therefore can
serialize otherwise independent nullifiers. Measure or tightly bound:

- same-nullifier races, different-nullifier/same-pool races, and independent
  pools under concurrent submission;
- account-lock conflicts, retries visible to clients, transactions per slot,
  and the cap imposed by both CU and writable-account scheduling;
- duplicate, stale-anchor, wrong-sequence, invalid-proof, malformed-account,
  unauthorized-finalize, write-after-finalize, reinitialize, and account-
  substitution failures, including whether each path leaves all state intact;
- front-running, replay, upload/finalization griefing, oversized-account and
  fee-payer DoS surfaces; and
- the operational consequence of a single hot pool and any sharding that is
  explicitly outside the proven relation.

Report these as systems limitations even if the cryptographic theorem is
unchanged. Do not turn Solana account-lock semantics into a throughput claim
without a controlled validator experiment.

## 9. Proof length and schedule leakage

The manuscript must name the two current proof sizes rather than silently
mixing them:

```text
unmined regression fixture       59,679 bytes
current canonical mined proof    61,599 bytes
```

The difference is attributed to minimal-subtree frontier geometry under a
different public Fiat–Shamir query schedule, not automatically to “mining
overhead.” Length is part of the complete public view. The hiding argument
covers it because the q3/first-Good schedule law is witness-independent and
`Sim23` serializes the same schedule-dependent shape. Include a direct
per-section byte table for both proofs in the artifact appendix. If a future
production repin changes either length, regenerate this text.

## 10. Manuscript structure

### Abstract

Use four sentences: problem and cap; construction; security result; measured
result. Use “over 100 bits in a proven Johnson/MCA regime” and the 103.112-bit
pairwise hiding value. Mention the finalized pre-uploaded account in the same
sentence as “one transaction.” Add mainnet wording only after the gate closes.

### 1. Introduction

- explain why transparent shielded-spend verification is difficult under
  Solana's 1.4M-CU limit;
- state the exact transaction object and exclusions;
- summarize the soundness/hiding/implementation alignment;
- list contributions with inherited versus local results distinguished; and
- include a boxed claim-boundary paragraph.

### 2. Background and related work

- M31/CM31/QM31 and circle FFT codes;
- polynomial commitments, Johnson list decoding, MCA, folding, OOD, and BCS;
- private Merkle and programmable-random-oracle simulation;
- Solana SBF execution and account atomicity; and
- nearest Solana privacy/verifier systems, led by Protocol 01, direct
  transparent-verifier work, Groth16 shielded pools, and attested/off-chain
  designs.

Related work must use the dated novelty artifact's pinned sources. It should
compare dimensions, not arrange projects into a marketing leaderboard.

### 3. Statement and system model

- exact one-input/one-output public statement/witness relation and equations;
- pool and nullifier state machine;
- account lifecycle and transaction scope;
- relation-soundness, BCS, real/simulator, pairwise-hiding, atomic-safety,
  random-oracle, auxiliary-input, and release-channel games; and
- transparency/setup and availability assumptions.

### 4. Profile 23 protocol

- transcript diagram with every message boundary;
- commitment phases, zerocheck, OOD, folds, final polynomial, work nonces;
- width-29 D-after-G layout and root-neutrality;
- q3 schedules, least-Good selector, cap-16 retry, and Abort; and
- proof serialization, finalized account frame, and parser invariants.

### 5. Soundness

- circle-to-GRS transport;
- Johnson/MCA batching and fold/list commutation;
- local relation/OOD/query arguments;
- q3 selector correctness and soundness conditioning;
- BCS theorem specialization with 32 boundaries;
- term-by-term ledger; and
- selected 101.302-bit result plus 100.807-bit coarse sensitivity.

### 6. Computational hiding

- ideal affine view and Good23 certificates;
- constant-cardinality mask preimages and uniform affine-image sampling;
- explicit witness-free `Sim23`;
- q3/cap-16 selection-hiding law and Abort, distinct from selector soundness;
- explicit private-Merkle/EPRO and canonical-work hybrid sequence;
- finalized proof account/log/state view; and
- real-vs-simulator and pairwise theorems with side-channel exclusions.

### 7. SBF implementation

- crate boundaries and generated constants;
- mixed-field and hash primitives;
- verifier/parser/account architecture;
- finalization and production feature isolation;
- loader, ProgramData, upgrade-authority, close/reallocation, and governance
  assumptions;
- atomic mutation ordering; and
- guard/test architecture, including independent derivation paths.

### 8. Evaluation

- proof generation and size;
- complete setup/upload/finalization lifecycle, rent/fees, prover/miner time,
  memory, and attempts;
- integrated CU waterfall and mutation paths;
- the 19-CU context discrepancy and the superseded historical 8-CU row;
- adversarial/rollback/race/privacy regression matrix;
- contention, throughput, account locks, and denial-of-service surfaces;
- binary/proof/release identities; and
- mainnet evidence if and only if the gate is green.

### 9. Limitations and open work

- model-scoped computational hiding and excluded side channels;
- no audit or production-readiness claim;
- pre-upload/finalization transactions and storage/rent costs;
- public metadata and unavailable wallet/relayer layer;
- reliance on pinned random-oracle and hash assumptions;
- no recursion, batching, multi-asset pool, or generalized private DeFi; and
- any remaining formalization or independent-audit gap.

### 10. Conclusion

Restate the exact engineering and proof result without novelty superlatives.
If mainnet and the day-of scan gates are green, place the qualified novelty
sentence at the end, not as a substitute for the technical result.

### Appendices

- complete protocol pseudocode and wire layout;
- full theorem proofs and imported-theorem hypothesis checks;
- complete soundness and EPRO ledgers;
- Good23 pivots/fingerprints and transfer chain;
- proof byte inventories;
- CU markers and reconciliation formulas;
- adversarial vector definitions;
- reproducibility commands and environment; and
- dated novelty methodology and pinned source list.

## 11. Required figures and tables

Figures:

1. system/account lifecycle with the headline transaction boundary;
2. complete Fiat–Shamir timeline, including 32 BCS boundaries, q3 fork, work,
   selector, and q16;
3. theorem dependency graph shown above;
4. Profile 23 lane layout and D/G root-neutral cancellation;
5. Good23 image/surjectivity geometry and the three certificate blocks;
6. `Real -> Sim23 -> Real` hybrid diagram with error terms;
7. private-Merkle/EPRO simulated complete view;
8. integrated CU waterfall for diagnostic tag 59 plus separate production
   tag-60 mutation increments; and
9. pool/nullifier pre-state, verification boundary, and atomic post-state; and
10. setup transactions versus the headline transaction, including writable-
    account contention boundaries.

Tables:

1. parameter set and domains;
2. exact relation equations, statement/witness fields, and privacy
   classification;
3. security games, quantifiers, adversary bounds, outputs, and assumptions;
4. soundness events with probabilities, sources, and union treatment;
5. selected versus coarse soundness derivation;
6. EPRO hybrid/input inventory and hiding bounds;
7. Good23 ranks, kernels, preimage counts, fingerprints, independent-checker
   evidence, and fixture/live transfer evidence;
8. proof section byte counts for regression and production schedules;
9. integrated CU buckets and both mutation paths;
10. lifecycle transaction count/CU/fees/rent and prover/miner resources;
11. corruption, ordering, finalization, rollback, duplicate, race, contention,
    and privacy regressions;
12. prior-work comparison by network, transparency, direct verification,
    transaction split, state mutation, and security evidence; and
13. reproducibility artifact manifest and tier runtimes.

Generate plots from JSON/CSV sources. Do not use screenshots of terminal
output as evidence.

## 12. Reproducibility artifact manifest

The final paper bundle must contain this table with hashes generated at
release time:

<!-- markdownlint-disable MD013 -->

| object | source of truth | required binding |
| --- | --- | --- |
| source revision | signed release tag/commit | clean or fully disclosed tree |
| release certificate | `results/stage2/profile23_one_transaction_release.json` | all gates green; own SHA-256 |
| claim/evidence matrix | `paper/profile23/claim-evidence-matrix.md` | every abstract, theorem, and evaluation claim mapped or blocked |
| security-game specification | manuscript definitions plus artifact schema | exact quantifiers, view, adversary, query and attempt bounds |
| soundness ledger | `results/stage2/profile23_d_after_g_soundness_epro.json` | selected 101.302; coarse 100.807; BCS 32 |
| Good23 product | `results/stage2/profile23_complete_good_product.json` | component/product fingerprints |
| independent Good23 checker | separate checker source, negative fixtures, output | reconstructs maps; dimensions/ranks/kernels/minors agree |
| hiding closure | `results/stage2/profile23_computational_hvzk_closure.json` | explicit simulator; 104.112/103.112 split |
| acceptance KAT | production-mined acceptance JSON | proof/runtime/wire and integrated buckets |
| mutation KAT | production-mined mutation JSON | both account paths, rollback/race, production baseline |
| proof bytes | canonical local mined `.bin` | path, length, SHA-256, account address |
| default SBF | freshly built default `.so` | length, SHA-256, configured local address, feature set |
| loader/deployment state | local declaration or future immutable evidence | Program/ProgramData linkage, code hash, capacity, authority, finalized slot |
| generated layout/constants | generation scripts plus outputs | layout hash and independent reference tests |
| toolchain | lockfiles and version capture | Rust, Solana/Agave, host OS/CPU |
| raw validator evidence | logs, RPC JSON, transactions, genesis, account dumps | exact runtime, CU, errors, and pre/post images |
| lifecycle evaluation | generated JSON/CSV | setup transactions, CU/fees/rent, time/memory/attempts |
| contention evaluation | generated JSON/CSV plus raw runs | same/different-nullifier and pool concurrency |
| novelty audit | dated Markdown and JSON | cutoff, queries, pins, limitations |
| mainnet evidence | new immutable JSON | signature/slot/finality/CU/accounts/hashes; pending |
| paper facts | generated TeX/Markdown macros | derived only from the frozen manifest |

<!-- markdownlint-enable MD013 -->

Archive the exact bundle under a content-addressed release and obtain a DOI
before camera-ready. Include a one-command verifier that rehashes the bundle,
checks artifact cross-links, rebuilds or verifies the SBF, reruns fast tests,
and optionally reruns slow rank/KAT jobs.

## 13. Authoring and review sequence

1. **Freeze terminology and scope.** Write the statement, account lifecycle,
   threat model, and claim-boundary page first.
2. **Write theorem statements before exposition.** Give every theorem exact
   hypotheses and numeric variables, then construct the dependency graph.
3. **Write soundness from the ledger outward.** Re-derive each row, update the
   corrected coarse figure, and have an independent cryptography reviewer
   check imported theorem applicability and union arithmetic.
4. **Write `Sim23` as an algorithm.** Have a privacy reviewer attempt to find
   a witness-dependent input, schedule, length, abort, log, receipt, or state
   field omitted from the view.
5. **Write the implementation refinement.** Have a Solana reviewer check
   account ownership, finalization, instruction order, rollback, race, upgrade
   authority, and the exact one-transaction boundary.
6. **Validate the frozen local release.** The finalization-aware KAT,
   30/30 release certificate, proof, and default SBF now agree; generate paper
   macros from those artifacts and fail on any later drift.
7. **Close mainnet evidence.** Deploy and execute only through the separate
   release checklist; capture finalized evidence. If it remains blocked,
   publish the local result without mainnet or novelty language.
8. **Rerun novelty on publication day.** Update the comparison table and claim
   gate. A negative search supports only the exact qualified formulation.
9. **Run four independent reviews.** Cryptographic soundness, computational
   hiding, Solana/runtime security, and artifact reproducibility each receive
   a written issue log and sign-off or an explicit limitation.
10. **Claim audit.** Search the manuscript, abstract, metadata, repository,
    slides, and announcement for `first`, `mainnet`, `one transaction`,
    `zero knowledge`, `104.112`, `100.879`, `audit`, and `production`; verify
    every occurrence against the gate rules.
11. **Reproduction dry run.** A clean machine follows the artifact README and
    reproduces hashes, fast tests, the ledger, and at least one validator run.
12. **Release preprint and artifact together.** Do not publish headline claims
    before their evidence bundle is public.

The draft should maintain a claim-to-evidence matrix. Each quantitative or
security sentence gets an artifact field, theorem, test, or external citation.
Unmapped sentences are rewritten or removed.

## 14. Preprint and venue plan

Release an IACR ePrint full version and a DOI-backed artifact bundle together.
An arXiv mirror is optional and should use identical claim language and a
cross-link to the authoritative artifact. Check all simultaneous-submission
and anonymity rules again immediately before posting.

For a double-blind venue, do not publish the ePrint, DOI, program address,
repository URL, signed tag, commit history, acknowledgments, grant metadata,
or mainnet transaction until the venue permits it. Produce a separate
content-addressed anonymous snapshot with neutral package names, scrubbed Git
history and document metadata, no author-controlled URLs, and an anonymous
artifact README. Record privately how every anonymous hash maps to the
canonical release bundle, then disclose that mapping only after the review
policy permits. A public program address or prior repository announcement can
deanonymize the submission even when author names are removed; the submission
checklist must treat that as an explicit venue decision, not an automatic
artifact step.

Choose the review venue after the theorem draft receives external feedback:

- **Financial Cryptography and Data Security** is the natural first candidate
  if the paper leads with a shielded-payment construction, deployment model,
  and empirical blockchain constraints.
- **USENIX Security, IEEE Symposium on Security and Privacy, or ACM CCS** fit
  if the strongest contribution is the end-to-end security/implementation
  result and the artifact is independently reproducible.
- **EUROCRYPT or CRYPTO** should be targeted only if reviewers judge the
  Good23/simulator or code-transport argument to be a broadly reusable new
  cryptographic result, not merely a careful system instantiation.

Do not put an unreviewed “first” claim into submission metadata. Venue
deadlines, page limits, artifact policies, double-submission rules, and
anonymity requirements are intentionally not frozen in this document; verify
them from official calls when selecting the submission cycle.

Prepare two versions from one source:

- a self-contained full version with proofs and reproducibility appendices;
  and
- a venue-length version that moves mechanical ledgers and full pivot lists to
  the full version but keeps the exact theorem hypotheses, claim boundary,
  primary security argument, and integrated measurement method in the body.

## 15. Definition of paper-ready

The manuscript is paper-ready only when:

- all theorem statements have complete assumptions and dependency links;
- `R23`, transparent parameters, all security games, exact declared view,
  adversary/query bounds, and one-input/one-output limitations are formal;
- selector soundness and selector-distribution hiding are separate results;
- the corrected 101.302/100.807 soundness figures are generated from the
  Profile 23 ledger;
- the abstract uses the 103.112-bit pairwise hiding floor and separately
  labels 104.112 as real-versus-simulator;
- `Sim23` is explicit and the full public view includes length, Abort, proof
  account, logs, and state mutation;
- the side-channel exclusion list appears beside the hiding claim;
- finalized proof-account enforcement is present and tested;
- every CU total comes from a reconciled integrated ledger;
- the 19-CU context difference is either explained by a controlled experiment
  or reported as a named context difference;
- the rank-certificate fixture-to-live transfer chain, constant-preimage
  argument, and independent checker are explicit and reproducible;
- the EPRO proof gives adjacent hybrids, oracle domains, inventory, bad events,
  post-output query handling, and canonical-work simulation;
- finalization claims are relative to the exact program version, loader,
  ProgramData, upgrade-authority, close/reallocation, and governance model;
- the source/proof/SBF/artifact hashes are mutually consistent;
- reproduction tiers, full setup lifecycle/prover costs, contention,
  throughput, and failure experiments are complete;
- the claim/evidence matrix contains no unsupported or blocked affirmative
  claim;
- the mainnet and day-of novelty gates control, rather than decorate, public
  language; and
- the venue-specific anonymous artifact has been checked before any public
  preprint or DOI action; and
- an independent clean-machine reproduction and claim audit are complete.

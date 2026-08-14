# Historical prepublication security review: Aspis Spend q18/g37 (v4)

This author-controlled engineering review was written before the q18/g37
publication. It records that release at the time it was frozen. Later
independent checkers and the separate V5 selected-Rust proof are described
in [`SECURITY.md`](../../SECURITY.md), the
[`AspisFormal` ledger](../../AspisFormal/README.md), and the
[`V5 release freeze`](../../release/preflight/v5-production-freeze.md).

## Scope

Reviewed at the `aspis-spend` branch:

- On-chain verifier and state machine:
  `programs/aspis-verifier/src/{dispatch,wire,lifecycle,verify,atomic_payment}.rs`
- Statement and cryptographic core:
  `crates/aspis-statement/src/{atomic_statement,spend,poseidon2,state_only_spend}.rs`
- Security argument:
  `paper/aspis-spend/sections/{soundness,hiding,limitations,evaluation}.tex`

The object under review was the transparent (no trusted setup) shielded-spend
**verification primitive** on Solana L1. It proves a depth-20, one-input /
one-output **same-private-path** leaf replacement and applies the atomic
pool / nullifier state transition in a single tag-65 transaction
(`dispatch.rs:175`). Statement v4 binds a per-deployment domain,
`sha256("aspis-spend-deployment-domain-v1" || program_id || domain_tag)`, into
both the pool account and every proof
(`atomic_statement.rs:33,49-59`; compared fail-closed at
`dispatch.rs:107-111` and `atomic_payment.rs:289-293`).

A single mainnet-beta execution finalized on 2026-07-16 (signature
`3G1voggsz...`, slot 433219840, 1,344,003 CU) under a disposable program that
was subsequently closed. That run advanced the pool from sequence zero to one
(`evaluation.tex:198-201`).

## Disposition

Suitable for publication as a **research result**: a working transparent
shielded-spend verification transition demonstrated once on L1, with an honest
and mostly self-attested security argument. **Not cleared as a value-bearing
service.** There is no deposit path, no anonymity-set growth, only a
*conditional* wrong-secret reduction rather than a complete deployed theft
theorem, and no live callable instance. No external audit was performed.

## Assessment

The on-chain authorization, identity, and atomicity checks are the strongest
part of this release. Dispatch is fail-closed (unknown and superseded tags
reject before any account access, `dispatch.rs:206`), every account-shape and
public-input variant has a rejecting no-mutation test, and all fallible
operations precede the first state copy. The state transition, digest binding,
replay handling, and rent accounting are covered by direct host tests that pin
ordering and no-mutation-on-failure (`atomic_payment.rs:1093-1121`), and the
statement and tree known-answer tests are pinned. Wire parsing, lifecycle,
atomic mutation, and statement binding are cleanly separated.

The weaknesses identified at freeze time were cryptographic and structural
rather than in the on-chain glue. The floors that matter most for a shielded
system are conditional: hiding rests on the affine-image premise (R-03),
soundness is work-normalized rather than raw (R-04), and authorization still
needs deployed and simulation extraction, the connection from real attacks to
the Lean game, target sampling, and concrete primitive and runtime bounds
(R-02). Later V5 work supplies the same-position Merkle reduction and the case
split for the attack event defined in Lean, but not those deployed or numerical
steps. The custom Merkle compression is unreviewed (R-08). Testing is extensive at the
host level and backed by a full mainnet reconciliation. The later standalone
rank checker independently reconstructs the eight rank identities; the other
cryptographic premises and the absence of coverage-guided fuzzing remain as
recorded.

The honest summary is that this is careful engineering of a narrow primitive,
held back by the conditional cryptographic premises and the absence of any
external review.

## Hostile checks

| Vector | Result | Evidence |
|---|---|---|
| Authorization | Pass | Upload authority must sign and match the stored key; finalize zeroes it irreversibly; pool init requires the pool key to sign (`lifecycle.rs:55-66,158-172,194-196`). |
| Account identity | Pass | Owner, writability, signer, aliasing, and canonical-PDA checks on all five accounts before any mutation (`atomic_payment.rs:244-283`). |
| State transition | Pass | Anchor equality, deployment-domain equality, nullifier freshness, and a full mutable-state recheck all precede the first copy; verifier runs before any CPI/write (`atomic_payment.rs:576-638`). |
| Rent / refund | Pass | Proof-account refund requires the proof account to sign, checks for overflow, and tombstones before draining (`atomic_payment.rs:323-365`); reconciled against finalized mainnet balances (`evaluation.tex:201-209`). |
| Proof parser | Partial | Fixed-width `production_take` parsing rejects trailing bytes and mis-sized inputs (`dispatch.rs:21-43`), but the proof-body verifier has had no coverage-guided fuzzing (R-08, testing gap). |
| Production dispatch | Pass | Only tags 0/1/59/60/62/63/64/65 are live; every historical or diagnostic tag fails before account access, pinned by test (`dispatch.rs:206`, `dispatch.rs:217-317`). |
| Deployment domain | Partial | Bound and compared fail-closed, but the domain tag is operator-asserted and not tied to cluster genesis; whoever controls the program-id keypair can reproduce the same domain on another cluster (R-05). |

## Findings

### R-01: Single-spend verification primitive; no deposit, no anonymity-set growth
**Severity: High. Status: documented-constraint.**

The release contains no deposit, mint, or leaf-append instruction. The only
live wire tags are init/upload/finalize/close for proof accounts, pool init,
and the read-only and applying spend tags (`dispatch.rs:60-207`). The one
`atomic_append_chain_anchor` construction in the statement crate is explicitly
retained only as a *rejected* capacity candidate and is not wired to any
instruction (`atomic_statement.rs:183-197`). `InitializeAtomicPool` takes a
**caller-supplied** initial anchor and sequence (`lifecycle.rs:183-223`); the
tree is never grown on-chain. The mainnet run advanced sequence 0→1
(`evaluation.tex:198-201`), so the demonstrated anonymity set is effectively
one. This is a verification primitive, not a shielded pool: without a deposit
path there is no set for a spend to hide within.

*Fix direction:* build and review a deposit/append instruction that grows the
committed set on-chain under the same atomicity discipline, and re-evaluate
hiding against a realistic set size rather than a one-element pool.

### R-02: Theft resistance is conditional, not unconditional
**Severity: High. Status: partially discharged; deployed connection and numerical bounds remain open.**

The repaired Lean result proves a narrower and correct statement. For a fixed
target nullifier, an accepted prover execution whose extracted secret is wrong
implies either extractor failure or a different input with the same nullifier.
The extractor receives the full execution record needed by the knowledge
assumption, not public proof bytes alone. A second theorem handles a different
valid opening of the exact same fixed input leaf. Neither result requires or
assumes that a compressing hash is globally one-to-one.

This is not yet a complete deployed theft theorem. Later V5 work proves the
same-position Merkle reduction and a complete case split for the fixed-victim
attack event defined in Lean. The project still needs to connect actual Tag-67
acceptance and real deployed attacks to that model, bound extraction failure,
justify extraction after the attacker has seen other proofs, define target
sampling or assume a uniform fixed-target guarantee, and supply concrete
bounds for credential recovery, the Poseidon2 nullifier, note commitment and
tree hash, PDA aliasing, setup, and Solana runtime failures. The current paper
states the multi-round extraction step as an assumption; weak unique response
is only supporting evidence. The result also says nothing about key management
or secret-key leakage.

*Fix direction:* prove the deployed acceptance-to-extraction link and the
exact multi-round extraction result, connect real attacks to the Lean game,
then justify concrete bounds for every listed failure. Until then, describe
this as a conditional fixed-victim case split and do not place real value under
its protection.

**Post-review V5 update (14 August 2026):**
`ApplicationMerkleBinding.lean` now proves the relevant Merkle reduction for
a different leaf at the victim's exact position, and deliberately does not
misclassify a legitimate opening at another position. The new fixed-victim
game separates extraction failure, credential recovery, nullifier collision,
note-opening collision, Merkle node collision, PDA aliasing, runtime/state
failure, and invalid victim setup, then proves the corresponding eight-term
union bound. The exact deployed acceptance-to-extraction connection,
multi-proof extraction, and concrete Poseidon2, PDA, and runtime probability
bounds remain open. The status therefore remains high severity for a
value-bearing system, although the missing cases are now stated precisely.

### R-03: Hiding floors use an explicit affine-image premise
**Severity: High. Status: rank identities independently checked; full-model completeness remains an assumption.**

At freeze time, the 104-bit hiding floor (`hiding.tex:368-372`; dominant term
104.0249... bits at Q_H = 2^128) holds only under the *complete affine-image
and rank-coverage* assumption (`hiding.tex:118-146`). That assumption asserts
the reconstructed affine field view is an exact model with specific ranks. It
is checked at release time by the maintainers' own GoodSpend rank checker; the
paper explicitly notes there is **no independent verifier** and that "the
hiding theorems therefore remain conditional" until one is published
(`hiding.tex:182-198`). The most security-relevant privacy claim is therefore
self-attested. That specific rank-checking gap was closed after this review:
`tools/verify_hiding_ranks.py` is a standalone verifier with independent field
arithmetic and map construction.

*Update: independent checker added.* `tools/verify_hiding_ranks.py` is a
standalone, stdlib-only Python
tool that shares no code with the prover: it uses its own M31/QM31 field
arithmetic, re-derives the public linear maps directly from the construction's
masking algebra, masked ten-round sumcheck, circle query-kernel source
families, and root-neutral gamma pairing (it does not import
`aspis_prover::state_only_hiding_rank` or call the GoodSpend builder), and
instantiates them at an independently sampled generic schedule (18 distinct
query roots, a random sumcheck point, a nonzero batching challenge) rather than
replaying the prover's transcript. Because every rank in the table is a generic
(Zariski-open) property of the frozen layout, reproducing each target at an
independent generic point shows the target is the true generic rank of the
public construction, the dimension count `im A = W` rests on. It confirms all
eight ranks in `tab:goodspend-ranks` (root-neutral joint 1404, serialized
terminal 324, terminal-plus-initial 328, `ker(initial,T_z)` coverage 1076, the
two remaining-`G/D` and inactive-`H1` query maps 288, and their terminal Schur
maps 12) against both the frozen certificate
`results/spend/spend_computational_hvzk_closure.json` and the paper, and prints
a pass/fail transcript. The root-neutral block (1404/324/328/1076, the
substantive coverage claim) is reconstructed exactly from the factor/exponent
schedule; the two raw-coverage blocks (288/12) reproduce the layer-zero query
code's column rank and terminal Schur rank using the exact eq terminals and a
generic distinct-point evaluation-code model of the circle wire (the
circle-specific twiddles are irrelevant to those column-rank facts), as the
transcript states. Run it with `python3 tools/verify_hiding_ranks.py` (a heavy
pure-Python computation, roughly twenty minutes; `--seed` re-runs at a
different generic point, and a second seed reproduces the same eight ranks).
This independently checks the rank/coverage dimension count. The full hybrid
argument still uses Assumption `lem:complete-affine-image` to identify the
declared execution view with the reconstructed linear model.

### R-04: Soundness floor is work-normalized; the raw bound is vacuous
**Severity: Medium. Status: documented-constraint.**

The headline 100.16-bit soundness floor is in a **work-normalized** (per-RO-query)
metric (`soundness.tex:322-334`). The raw BCS Fiat–Shamir bound exceeds one at
T = 2^128 and is "vacuous as a bound" there by the paper's own words
(`soundness.tex:299`). The value ≈106.79 is `-log2` of the work-normalized
bound at that query budget, not of the raw bound. Multiplying by `T = 2^128`
makes the raw upper bound exceed one, so it gives no nontrivial raw probability
at that budget.

*Fix direction:* present the ordinary bound as `min(1, T × b(T))` alongside the
normalized value, do not call 106.79 a raw security figure, and tighten the
proof-system parameters if a nontrivial ordinary bound at the target query
budget is desired.

### R-05: Deployment domain does not identify the cluster
**Severity: Medium. Status: documented-constraint.**

The deployment domain is `sha256(separator || program_id || domain_tag)`
(`atomic_statement.rs:49-59`). Two residuals remain:

1. **Controlled by the program-id key holder.** The domain is a deterministic function of the program
   id and an operator string. Whoever controls the program-id keypair can
   deploy the same program id on another cluster and reproduce an identical
   domain; the domain does not bind to anything an attacker without that key
   lacks.
2. **`domain_tag` is operator-asserted, not genesis-checked.** `initialize_atomic_pool`
   accepts any nonempty tag ≤64 bytes and never compares it to cluster genesis
   (`lifecycle.rs:200-212`). A devnet pool tagged `"mainnet-beta"` under the
   same program id yields a domain byte-for-byte identical to a genuine
   mainnet pool. The in-tree cross-domain tooth only shows that *different*
   tags reject (`atomic_payment.rs:1126-1186`); it does not detect a *lying*
   tag.

*Fix direction:* mix a value the deploying key cannot forge on a foreign
cluster (e.g. a genesis-hash or slot-hashes sysvar witness) into the domain, so
that a mismatched cluster cannot reproduce the domain even under the same
program id.

### R-06: No scaling or concurrency story
**Severity: Medium. Status: documented-constraint.**

State lives in a single sequential pool account whose sequence is bumped once
per spend (`atomic_payment.rs:616-638`), and each spend creates one persistent,
rent-bearing nullifier PDA (`atomic_payment.rs:367-427`). There is no queue,
no batching, and no tree-growth path. Writable locking on the single pool
serializes all spends against one another, and the nullifier set grows without
bound in rent-bearing accounts.

*Fix direction:* design a sharded or tree-structured nullifier/commitment
layout and a concurrency model that does not serialize all spends on one
account before any throughput claim is made.

### R-07: No live callable instance; thin CU headroom against repricing
**Severity: Medium. Status: open.**

The demonstrated program was closed after the single run, so there is currently
no live, callable deployment to exercise or audit end-to-end. The finalized
transition consumed 1,344,003 of the requested 1,400,000 CU, 96.0002%, leaving
~4% headroom (`evaluation.tex:184-185`). A future compute-cost repricing of any
syscall on the hot path (SHA-256, PDA derivation, CPI) could push the fixed
verification cost over the limit, which the paper acknowledges as a risk.

*Fix direction:* stand up a persistent audited deployment for independent
exercise, and either reduce the hot-path CU or validate behavior against
plausible repricing before relying on the current margin.

### R-08: Custom `merkle_node_compress_v3` wants external review
**Severity: Medium. Status: open.**

Internal Merkle nodes use a bespoke one-permutation 2:1 compression: the ordered
pair `(left, right)` fills the full width-16 Poseidon2-M31 state, a fixed
node-domain tweak is added to the last limb, one permutation is applied, and the
first eight limbs are retained (`poseidon2.rs:403-412`). Separation from the
length-committing leaf sponge is **by convention** (the primitive is only ever
called on internal nodes and the statement/tree version is bumped when it is
selected) rather than by an in-permutation domain tag. This is the binding
primitive for every note and tree node and has had no external cryptographic
review.

*Fix direction:* obtain external review of the compression's collision/domain-separation
properties, or move to a construction whose domain separation is enforced by
the permutation input rather than by call-site convention.

## Summary of severities

| ID | Finding | Severity | Status |
|---|---|---|---|
| R-01 | Single-spend primitive; no deposit / no anonymity-set growth | High | documented-constraint |
| R-02 | Later V5 work adds the same-position Merkle reduction and a modeled fixed-victim case split; deployed/simulation extraction, the deployed-game connection, target sampling, and concrete primitive/runtime bounds remain | High | partially discharged |
| R-03 | Hiding floors use the affine-image completeness premise; ranks independently checked | High | partially discharged |
| R-04 | Soundness floor is work-normalized; raw bound vacuous | Medium | documented-constraint |
| R-05 | Deployment domain can be reproduced on another cluster by the program-id key holder | Medium | documented-constraint |
| R-06 | No scaling / concurrency | Medium | documented-constraint |
| R-07 | No live instance; ~4% CU headroom vs repricing | Medium | open |
| R-08 | Custom `merkle_node_compress_v3` unreviewed | Medium | open |

R-03's rank subclaim was independently checked after this review; its
full-model completeness premise remains. The other findings retain the
dispositions above. The on-chain authorization, identity, atomicity, and rent
logic pass every hostile check in this review.

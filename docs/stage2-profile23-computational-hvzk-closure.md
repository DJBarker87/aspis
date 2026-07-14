# Profile 23 computational HVZK closure

**Status (`2026-07-14`): q18 complete-view computational hiding is closed in
the declared SHA-256 ROM/EPRO and fixed public release-channel model. This is
not statistical HVZK, not a standard-model SHA-256 PRG claim, and not a local
hardware/OS side-channel claim. The proof-independent closure, canonically
mined q18 production repin, tag-59/tag-60 host/SBF KATs, and local
one-transaction release are green with `35/35` gates. The `2026-07-13`
q16/cap16 release is superseded historical evidence.**

## Exact claim

Fix one public atomic-v3 statement `x`. For any two valid witnesses for `x`,
consider the complete public output of the honest Profile-23 prover:

```text
Output = Proof(
  finalized proof-account bytes,
  roots, opened value||salt records and frontiers,
  Fiat--Shamir and work nonces,
  transaction framing/logs,
  deterministic public account mutation
)
or Abort.
```

The abort outcome is part of the view; the theorem is not silently
conditioned on successful proving. Assume:

1. SHA-256, including the transcript, mask expansion, salt expansion,
   Merkle trees and work predicates, is one programmable 256-bit random
   oracle with the implemented rigid domain separation;
2. the distinguisher makes at most `Q_H = 2^128` adaptive oracle queries,
   including queries after seeing the output;
3. every one of at most `A=17` attempts starts with fresh independent OS
   entropy and a fresh durably burned public nonce;
4. the local honest prover and canonical-minimum miner keep rejected attempts
   private; and
5. the only public worker channel is the implemented fixed-boundary
   `Proof(bytes)`/payload-free-`Abort` release. Local filesystem, scheduler,
   process timing, power, thermal, memory and remote-prover/miner traffic are outside this
   declared channel model.

There is an efficient witness-free simulator `Sim23(x)` for this complete
output. For every valid witness `w`, the real output and simulator output are
computationally indistinguishable with one-sided advantage at most

```text
epsilon_real_vs_sim
  <= A*C*Q_H / 2^256
     + binom(A*C,2) / 2^256
     + 6*A*exp(-2^27),

C = 969,993.
```

At the declared bounds, the terms are respectively at most

```text
2^-104.02492234825198
2^-209.04984478399368
2^-193635243.91255844.
```

The first term dominates, giving `104.02492234825198` bits for real versus
simulator. For any two valid witnesses `w0,w1`, the written reduction is

```text
Real(x,w0) -> Sim23(x) -> Real(x,w1),
```

so the triangle inequality gives

```text
epsilon_pairwise <= 2*epsilon_real_vs_sim
```

and a pairwise-witness floor of `103.02492234825198` bits. Both forms are
above 100 bits in the declared model. No direct real-to-real hybrid with a
single copy of the EPRO bad-event ledger is assumed. The standard conditional
expressions are

```text
epsilon_real_vs_sim <= epsilon_aff
                    + epsilon_field_prg + epsilon_salt_prg
                    + A*C*Q_H/2^256
                    + binom(A*C,2)/2^256
                    + 6*A*exp(-2^27)
                    + epsilon_side,

epsilon_pairwise <= 2*epsilon_real_vs_sim.
```

For this precise claim, `epsilon_aff=0`, SHA-256 expansion is inside the same
ideal oracle so the two explicit PRG terms are zero, and
`epsilon_side=0` only by model exclusion: local filesystem and burned-nonce
ledger access, scheduler/process timing, power, thermal and memory channels,
and remote-prover/miner traffic are outside the fixed public channel. It is
not a physical side-channel bound.

## Why Good23 sets `epsilon_aff=0`

For a fixed public verifier schedule `s`, quotient only exact public linear
identities and write the complete non-hash field view as

```text
Y_s(w,R) = A_s R + b_s(w),
```

where `R` contains the ideal independent M31 mask coordinates, including the
zero-factor D lane. Perfect fixed-schedule translation requires

```text
b_s(w1)-b_s(w0) in image(A_s)                         (1)
```

for every valid same-statement witness pair.

The Good23 audit is not merely agreement with one frozen determinant. On
every accepted schedule, the runtime predicate reconstructs the canonical
maps and requires all of the following:

| accepted block | exact consequence |
|---|---|
| existing semantic/mask/G raw builders | separately visible C1/C2 query and three-terminal values have the canonical translation ranks |
| D raw block | rank `268/268` for 64 queried QM31 symbols plus three terminal QM31 values |
| inactive-balanced H1 padding | rank `268/268` on the exact physical H1 raw target |
| remaining G/D raw Schur complement | query rank `288`, terminal rank `12` |
| H1 raw Schur complement | query rank `288`, terminal rank `12` |
| root-neutral product | joint rank `1,404/1,404`, terminal rank `324`, terminal-plus-initial rank `328`, and all `1,076` coordinates of `ker(initial,T_z)` |
| source guards | every selected source has compressed terminal zero and pointwise `Gamma_gamma`-root difference zero |

There is no unchecked semantic-raw assumption hidden in this table. For each
semantic lane, the common relation-free block `896..=1023` has structurally
surjective rank 72 on the 72 q limbs for every distinct q18 tuple. Its
balanced q kernel and the minimum-q-degree root-neutral certificate supply the
certified semantic directions while the lane-separated terminal projection
reaches full rank. Together those are the complete
q-plus-three-terminal semantic raw map. The independent remaining G/D and H1
terminal pieces are exactly the two additional Schur certificates in Good23.

The static gate also pins q18, rate `1/512`, nonzero gamma, generator order
`semantic0..15,mask16..25,H26,G27,D28`, `factor(D)=0`, the atomic-v3 layout
fingerprint `0x233ba2ca68f94148`, and the complete degree tuple. Builder or
schema drift is fatal, not retryable.

The root-neutral rank certificate is pinned to the frozen 67,327-byte q18
fixture and transfers to the production proof through an explicit chain.
These ranks depend on the frozen layout and schedule rather than the witness;
the release gate requires the layout fingerprint and Good23 definition
fingerprint to match live code; and the production selector audit must be
green for all three Good23 branches. The released production audit is green
for all three branches. The production proof is not assumed byte-equal to the
rank fixture.

These checks match the fixed-schedule complete-view implication exactly:

1. translate the semantic one-time pads so their separately authenticated
   raw view agrees;
2. use inactive-balanced H1 padding to cancel the complete physical H1 raw
   difference;
3. use D and G source translations, including
   `Delta G=-gamma*Delta D`, to cancel the pointwise gamma-combined message;
4. after fixing raw values and the initial claim, the remaining actual
   eta-scaled H1 sumcheck difference lies in `ker(initial,T_z)`; the
   root-neutral `1,404` block supplies all `1,076` directions needed to
   cancel it; and
5. the combined message is now identically zero, so the linear encoder, OOD
   maps, relation maps, folds, later queried values and final polynomial are
   identical as well.

This proves (1) for every schedule that Good23 accepts. It needs no sampled
712-row PCS continuation determinant. Thus the ideal affine simulator is
exact for every emitted proof and `epsilon_aff=0`.

The simulator is witness-free, not merely a pairwise translation argument.
For each fixed accepted schedule `s`, let `V_s=image(A_s)`. The exact public
linear verifier identities define an affine solution set

```text
S_x,s = y_public(x,s) + V_s.
```

The Good23 ranks and source guards prove that the homogeneous solution space
of those identities is exactly `V_s`: the structural semantic q maps cover
their complete raw targets, the two raw Schur blocks cover the remaining
terminal coordinates, and the root-neutral block covers all of
`ker(initial,T_z)`. The simulator computes a canonical `y_public(x,s)` by
row-reducing these public affine identities and setting free coordinates to
their canonical zero values. It then samples a uniform element of `V_s` from
the canonical echelon basis and outputs their sum. This uses only `x`, `s`,
and the frozen public maps; it never constructs or queries a witness.

For every valid witness `w`, `b_s(w)+V_s=S_x,s` by (1). Uniform ideal mask
coins map uniformly onto `V_s` because every image element has the same number
of preimages under the linear map `A_s`. Therefore the simulator's field view
has exactly the honest ideal-mask distribution. It is then wrapped
round-by-round by the private-Merkle, programmed-transcript, canonical-work,
first-Good, and fixed-release steps below. This is the explicit simulator
construction supplied by the surjectivity result.

The Good23 decision is schedule-only. Its rank routines consume frozen public
shape plus public challenges, points, fold data and query indices; they do not
consume a witness, realized mask, salt, root as opaque data, opened value,
retry counter or prover-selected minor. Although the schedule structure also
stores proof-carried claims, those claims are not inputs to the rank decision.

## q3 and cap-17 conditioning

One retained attempt clones the state after the final nonce into three
independent label-44 branches. It absorbs exactly one selector byte in each
branch, evaluates all three Good predicates, and selects the least good
selector. Only that selector and its openings are serialized. An all-bad
triple is discarded and retried; other gate/build failures collapse to the
same opaque abort.

In the EPRO hybrid, conditioned on the ordinary no-prequery/collision event,
the three label-44 inputs receive independent uniform oracle answers given the
shared prefix. The three schedules, their Good bits, the least-good selector,
and the all-bad bit therefore have one witness-independent joint law. The
first-good theorem applies to this whole q3 experiment, not to only the
selected schedule.

Consequently the cap-17 all-bad probability is an availability term, not a
privacy term. Its proved bound is

```text
Pr[public Abort from Good exhaustion] <= 2^-105.21398677941983
```

up to the separately negligible bounded-sampler/build aborts. Including
`Abort` in the simulated output avoids dividing the privacy advantage by the
success probability. If a claim is instead conditioned on success, the bound
must be divided by the corresponding success probability.

`Profile23FixedReleaseController` publishes exactly one proof or abort at the
preselected boundary. The production-miner example keeps that boundary live
while the private worker runs. This closes the declared public-channel shape;
it does not claim protection against local machine observables.

## EPRO/private-Merkle specialization

Profile 23 reuses the Profile-21 protocol-specific simulator theorem but
specializes its field view to the no-switch Profile-23 wire, adds D and the
q3 selector, and uses the final Profile-23 inventory:

| hidden/programmed input family | count per attempt |
|---|---:|
| salted-leaf preimages over five trees | 305,152 |
| hidden leaf-salt derivations | 305,152 |
| hidden Merkle-node forest upper bound | 305,152 |
| field expander, including 4,096 D limbs | 53,892 |
| seed and attempt-binding inputs | 8 |
| distinct transcript inputs | 637 |
| **total `C`** | **969,993** |

The transcript count is a set of distinct oracle inputs. Replaying the common
pre-query prefix for three selectors does not count identical inputs three
times. The 637 inputs include the dedicated D-claims absorb, all three
selector absorbs, the two additional query streams, bounded squeeze/advance
programming and six work subdomains.

The private-Merkle simulator samples opened salts, computes their leaf
digests, gives maximal unopened frontier subtrees uniform labels, and hashes
upward. A bounded distinguisher can expose the replacement only by querying a
hidden salt/seed/preimage or by a programmed-state collision, which is what
the linear and quadratic EPRO terms charge. The selected 32-byte salts do not
meet the stronger BCS statistical private-Merkle lemma; they are justified
only by this bounded-query computational ROM argument.

Canonical work nonces are simulated by the exact truncated-geometric minimum
law and lazy conditional oracle rules for earlier failures, the first
success, and later queries. Profile 23 has six sequential hidden work states;
their prequery risk is already included in `C`, and their nonce-space
exhaustion gives the displayed final term without a `sum 2^g` loss.

The exact finalized proof-account frame is

```text
"ASPU" || proof_len_u32_le || [0u8; 32] || proof.
```

The unchanged 40-byte header carries the upload authority before finalization.
`FinalizeProof`, authorized by that stored authority, replaces bytes `8..40`
with the all-zero finalized sentinel. Production tags 59 and 60 require that
sentinel. This is a deterministic public transition on the simulated proof
account, so it adds no hidden input and no EPRO term. Successful atomic
mutation likewise adds no private field: conditional on the public statement
and public account branch it is a deterministic function of the simulated
proof. There is no receipt in the selected one-transaction path.

The active q18 unmined fixture is 67,327 bytes with SHA-256
`a5ed698a32d815ffd95f8d3e0be62d16620d32e216a087a350852726fb6ca238`.
Its minimal-subtree frontier geometry depends on the Fiat–Shamir query
schedule; the public witness-independent selector law makes
schedule-dependent length part of the simulated complete view, not a
witness-dependent leak. The fixture audit accepts all three Good23 selector
branches and confirms that serialized selector `0` is the required least Good
branch.

The released canonically mined q18 production proof is 66,367 bytes with
SHA-256
`f4e1e81f4a35b6b23f18430598ff98ec1f0db1146fabb4efd3c6715bcc847b53`.
Its canonical statement sidecar has SHA-256
`976e9a7e001382025eaf81cfcb28ac609db966d4a9912511f54e2b702077b6de`.
Its canonical public-input digest is
`21d73e39be93112f986f52c7d683f2ab478890360a306af81110852ffb16a30a`.
The production replay likewise accepts all three Good23 branches and confirms
serialized and least-Good selector `0`.

## Regression evidence and limits

The committed 67,327-byte q18 unmined fixture has a gap- and overlap-free
public byte inventory. The exact executable inventory is pinned by the privacy
regression and all five opening sections bind their roots, values, salts, and
frontiers. For comparison, the superseded q16 fixture's inventory was:

```text
header 16; nonce 32; roots 160; initial claim 16;
masked sumcheck 4,480; statement evaluations 1,344;
OOD 128; relation 448; final 64; work 48;
D claims 48; selector 1; counts 30;
opened values 12,800; opened salts 2,560; frontiers 37,504.
```

For q18, all five sections reject mutations to roots, values, salts and
frontiers. Transcript teeth bind D claims, work and selector before their
dependent challenges. The literal-witness scan and nonce-reuse guard are
green. The q18 fresh-attempt rerandomization run remains pending; the
`141.00 s` fresh-attempt result belongs to q16 and does not transfer. These
tests are regression teeth, not substitutes for the affine/EPRO theorem.

There is intentionally no “two concrete witnesses for the same spend
statement” byte test: producing such a pair for the frozen statement would
require breaking its binding commitments. Same-statement witness differences
are covered by the universal physical source/containment argument above.

## Claim boundary and local q18 integration

The following statements are now accurate:

```text
Profile23 complete non-hash affine simulation      exact on Good23
Profile23 computational complete-view hiding       green in declared ROM/EPRO
statistical HVZK                                    not claimed
standard-model SHA-256 PRG security                not claimed
filesystem/timing/power/thermal/memory/remote traffic ZK  not claimed
q18 default production tag/mutation                green in local 35/35 release
```

The q18 theorem artifact does not enable production by itself. The separate
engineering gates now bind the mined proof and statement above, production
tag-59/tag-60 host and SBF acceptance/mutation replay on both marker paths,
fresh default-SBF identity, and exact CU reconciliation.
`results/stage2/profile23_one_transaction_release.json` records
`released=true`, `status=released_all_required_gates_green`, and `35/35`
passing gates. Its fresh 915,656-byte default SBF has SHA-256
`da66a51b1f3ce95e907a87fca15fb9dc0cce66fd47646875ce2dff94879fd254`.
Tag 59 costs `1,310,162 CU`; tag 60 costs `1,312,055 CU` on the program-owned
marker path and `1,314,386 CU` on canonical System creation, leaving `85,614
CU` of worst-path headroom below 1.4M. The same certificate binds the
conservative soundness floor at `100.16144938287455` bits, alongside the
declared-model hiding floors proved
above.

The intended release scope remains one atomic transaction consuming a
finalized, pre-uploaded proof account whose unchanged 40-byte header contains
the all-zero authority sentinel. Proof-account creation, chunk upload, and
`FinalizeProof` are not part of that transaction. Append-only tag 62 seals
proof accounts, append-only tag 63 initializes pools, and the configured local
program id is `7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue`; this address is
not deployment evidence. The green certificate is local release evidence, not
a mainnet deployment or an external security audit; those remain separate
blockers. The q18 fresh-attempt rerandomization regression remains pending as
stated above and is not inferred from the release KATs.

## Superseded q16 integration evidence (`2026-07-13`)

The q16 release passed 30/30 gates using a 61,599-byte mined proof, a
6,870,048-byte default SBF, and tag-60 costs of `1,204,792 CU` on the
program-owned marker path and `1,207,123 CU` on canonical System creation. It
left `192,877 CU` of worst-path headroom and pinned declared-model
pairwise/one-sided hiding floors of `103.11238518950232` and
`104.11238518950232` bits. Those proof, binary, CU, and hiding values are
retained only as historical evidence and do not transfer to q18.

## Guards

```bash
NO_DNA=1 cargo test -q -p aspis-prover --lib \
  state_only_profile23_privacy_regressions -- \
  --skip profile23_fresh_attempt_rerandomizes_the_complete_public_view_and_burns_nonce

NO_DNA=1 cargo test --release -q -p aspis-prover --lib \
  state_only_profile23_privacy_regressions::profile23_fresh_attempt_rerandomizes_the_complete_public_view_and_burns_nonce \
  -- --ignored --nocapture

NO_DNA=1 cargo run --release -q -p aspis-prover \
  --example profile23_complete_good_product

NO_DNA=1 cargo test --release -q -p aspis-prover --lib \
  state_only_good23::tests::frozen_profile23_fixture_runs_exact_good23_on_all_selectors \
  -- --ignored --nocapture
```

Machine-readable closure:
`results/stage2/profile23_computational_hvzk_closure.json`.

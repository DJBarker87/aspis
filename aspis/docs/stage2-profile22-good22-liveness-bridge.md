# Profile 22 Good22 valid-view and liveness bridge

Date: 2026-07-13

Status: **the four-M31 frozen-schedule “deficit” was an invalid target, not a
missing direction in the current protocol-coupled view, which is contained at
`4036/4036/4036/4036`.  A stronger, prospective bridge is now green: append
one full-domain zero-factor QM31 lane `D` after production `G`, and the exact
root-message-neutral conditional image reaches `1076/1076`.  A fixed
root-neutral polynomial-kernel minor is nonzero.  Production is unchanged,
and termination remains conditional on promoting that minor, the separate
H1/G/D raw certificates, and the three-selector transcript into one reviewed
profile.**

No proof bytes, transcript challenge, mask sampler, PCS word, verifier
predicate, or transaction arithmetic changed in this correction.

## Result

On the frozen profile-22 q16 schedule, exact M31 block elimination gives:

```text
selected mask View                              4036
protocol-coupled physical View                  4036
+ zero-initial, zero-terminal sumcheck fiber    4036
+ active zero-sum helper View                   4036
```

All three containment predicates are true.  The corresponding intentionally
overstrong control remains:

```text
selected mask View                              4036
+ physical source with an independent zero SC  4040
+ zero-initial-only SC ambient                  4040
+ active helper                                 4040
```

That red control grants a transcript difference an arbitrary terminal
mismatch.  The verifier rejects such a difference.  It remains in the report
so this exact modelling mistake cannot silently return.

## The compressed terminal functional

Let `Q = QM31^271` be the compressed degree-27 sumcheck wire.  It contains

```text
initial claim,
then c0,c2,...,c27 for each of ten rounds.
```

For a running claim `a`, the omitted coefficient is fixed by the production
boundary equation:

```text
p(0)+p(1)=a
c1 = a - 2*c0 - sum_{k=2}^{27} c_k.
```

Reconstructing `c1` and evaluating each round at the transcript challenge
defines the exact QM31-linear verifier terminal functional

```text
T_z : Q -> QM31.
```

The implementation evaluates this functional independently of the rank
elimination and compares it to the production optimized degree-27 evaluator.
Its frozen fingerprint is

```text
T_z fingerprint = 0x6bad575484b04bfd.
```

Compressed observation 270 (round-9 `c27`) has a nonzero coefficient and is
used as the dependent coordinate.  Therefore:

```text
dim_M31 ker(T_z)                         = 1080,
dim_M31 ker(initial_claim,T_z)           = 1076.
```

The generated 1,076-direction basis balances every other free observation
against observation 270.  Every generator is checked to have initial claim
zero and terminal zero.

## Why the mask image is exactly `ker(T_z)`

After quotienting the exact separate raw openings, the replay checks every
remaining mask-source generator, not only semantic sources:

```text
post-raw source generators checked       17324
semantic C1 sources                       included
all ten mask-only C1 sources              included
explicit G sources                        included
H/helper zero-SC paths                    checked separately
T_z(source SC image)                      zero for every source
masked-sumcheck image rank                1080
```

Thus inclusion plus dimension gives the executable identity

```text
Image(S | ker(raw)) = ker(T_z).                         (1)
```

Conditioning additionally on the already bound initial claim gives

```text
Image(S | ker(raw,initial))
    = ker(initial,T_z),
```

the 1,076-M31 conditional sumcheck fiber used by the valid-view gate.

This is the right conditional object.  Given the public statement openings,
the verifier recomputes the masked terminal.  Any two accepting sumcheck
wires with the same initial claim and those same openings differ by an
element of `ker(initial,T_z)`.  An independently variable terminal is not an
accepting transcript difference.

## Physical coupling

The mask oracle is not an unrelated prover polynomial.  Production computes

```text
H(x) = sum_c factor_c(x) * C_c(x) + ...
```

from the same committed masked semantic C1 values opened by the PCS.
Consequently a physical semantic difference `d_c` necessarily carries the
exact `factor_c*C_c` sumcheck image.  The valid-view replay inserts that
coupled image with the same raw and gamma-scaled PCS source.

The old direct control inserted the physical raw/PCS source with a zero
sumcheck image.  Its four compatibility pivots are

```text
[1080,1081,1082,1083],
```

the four M31 limbs of compressed observation 270.  Applying `T_z` to the four
compatibility quotient columns gives an invertible `4x4` M31 map:

```text
rank                         4
fingerprint  0xd5819ed12907e16d.
```

This pins the old four-direction discrepancy to the terminal functional; it
is not an unnamed PCS or physical-mask deficit.

## Valid-view containment theorem

For a fixed parser-valid schedule satisfying the canonical raw ranks and
rank 1,080 in the post-raw sumcheck image:

1. Equation (1) follows from the all-source terminal-zero guard and the rank
   equality.
2. Every physical semantic change carries its exact `H` sumcheck image,
   because `H` is evaluated from the same committed C1 values.
3. Conditional on public openings and the bound initial claim, every legal
   accepting sumcheck difference lies in `ker(initial,T_z)`.
4. The 1,076-direction kernel is contained with zero residual PCS image.
5. Every active zero-sum H/helper difference remains contained in the final
   PCS quotient.

Therefore the full protocol-valid physical, conditional-sumcheck, and helper
view is contained.  This theorem does not assert containment of the invalid
independent-terminal direct sum.

## Frozen executable evidence

```text
masked sumcheck rank                         1080
joint PCS rank                                712
mask View rank                               4036
coupled physical rank                        4036
coupled legal rank                           4036
coupled helper rank                          4036
conditional SC generators                    1076
terminal identity guard                      true
all-source terminal-zero guard               true
mask image equals terminal kernel            true
physical compatibility-to-T rank                4
joint raw-plus-sumcheck minor rows            3324
joint raw-plus-sumcheck fingerprint  0xdc4f40449cb8c16f
```

The independent sparse/dense physical PCS projection remains pinned at
`0xa1e218dad3c9dadc`.

The 3,324-row provenance is the block-triangular union of the 2,244 raw
opening pivots and 1,080 post-raw sumcheck pivots, with the latter rows offset
by 2,244.  It makes the frozen numeric determinant selection executable.  It
does not by itself prove the `q`-degree bound or provide the missing full-rank
denominator-free polynomial-kernel family used by the selector projection.

## Weighted inactive-sum repair screen

The zero-width weighted-inactive-sum family was fully screened before the
valid target was identified.  It is not needed and does not repair the
overstrong independent direct sum:

| group | extra sources | public claim rank | full mask | full physical |
|---|---:|---:|---:|---:|
| first 8 mask-only | 8 | 4 | 4040 | 4044 |
| all 10 mask-only | 10 | 4 | 4040 | 4044 |
| all 16 semantic | 16 | 4 | 4040 | 4044 |
| one claim over all 26 | 26 | 4 | 4044 | 4048 |

The final union also raises the selected PCS rank from 712 to 716.  The
family is frozen as a negative host-only screen; it does not change the wire.

## What remains open: Good22 termination

The valid-view correction removes the supposed four-coordinate repair
obligation.  It does not prove that a random parser-valid schedule reaches
the required raw and post-raw sumcheck ranks.

For each ordered distinct q16 tuple `q`, the missing structural statement is
an every-q common-envelope/nonzero-minor theorem for the joint matrix

```text
[ R_q(z) ; S_q(z) ].
```

Raw-query monicity alone proves only the raw block.  It does not prove the
1,080-row post-raw sumcheck minor.  A frozen schedule scan is not a theorem.

If a q-uniform nonzero minor of degree at most 41,040 is proved, the existing
field ledger gives

```text
beta <= 41040/(2^31-1) ~= 2^-15.6753,
```

and a cap of 16 attempts makes exhaustion negligible for the requested
100-bit class.  Until that q-uniform premise is proved, the bounded first-good
manager remains fail-closed and the rejection probability is not bookable.

The nonzero gamma sampler remains necessary; the retired `gamma=0` replay is
still a valid negative tooth for the PCS continuation.  It is not a current
parser-valid schedule.

### Executed common-tail polynomial-kernel screen: red

The first denominator-free attempt to weaken the every-q premise has now been
made executable and measured on the frozen profile-22 schedule.  It uses the
common relation-free inactive tail `896..=1023`.  In each of the four natural
`{1,x,y,xy}` sectors, the query kernel is written as

```text
g_q(t) h(t),       g_q(t) = product_i (t-q_i),       deg(h) < 16.
```

Balancing the inactive sum leaves 63 M31 source directions per lane.  The
matrix has the following exact shape:

```text
semantic plus mask-only M31 lanes                    26
explicit-G tower-coordinate lanes                     4
balanced source columns per lane                     63
source columns                                      1890

raw terminal rows                         27*3*4 =  324
full compressed-sumcheck rows                  271*4 = 1084
matrix rows                                         1408
maximum protocol-valid target rank             324+1080 = 1404
measured rank                                       1271
deficit                                              133
```

The selected rank-1,271 minor provenance fingerprint is
`0x85f56a35c80963ce`.  The query roots were distinct and excluded `1`; the
failure is not a malformed-schedule artifact.

Therefore this common-tail source family does **not** supply a nonzero
1,404-column joint minor.  In particular, the proposed q-degree `22464`,
`rho_q = 22464/(2^17-15)`, and four-selector cap bound are not supported by
this construction.  They remain counterfactual formulas only, pending a
different executable polynomial-kernel family with full rank and a proof that
its nonzero minor implies the complete Good22 continuation predicate.

Frozen command:

```text
NO_DNA=1 cargo run --release -q -p aspis-prover \
  --example profile22_polynomial_kernel_rank -- \
  results/stage2/proofs/atomic_state_only_profile22_v3_unmined.bin \
  52e96f99756fe8fd2d8b7a700019b143d7eb549af1bf1ae987e99a75cadcd4c9
```

### Mixed polynomial-kernel screen: green for raw plus sumcheck

The red common-tail result is repaired numerically without giving semantic
lanes any constrained cells.  The mixed source frame is:

```text
16 semantic lanes:       63 common-tail g_q*h directions per lane
10 mask-only M31 lanes: 959 full-domain directions per lane
4 M31 coordinates of G: 959 full-domain directions per coordinate
```

For each unrestricted lane the global four-sector query kernel has dimension
`4*(256-16)=960`.  Intersecting it with the one physical inactive-sum equation
leaves 959 directions.  The executable frame fixes source zero as its balance
anchor and emits the cleared polynomial columns

```text
s_0(q) v_j(q) - s_j(q) v_0(q).
```

Thus there is no rational denominator.  A common-tail column has degree at
most one in each q root and a cleared full-domain column has degree at most
two.

Frozen measurement:

```text
potential source columns                              14434
processed before both projections closed              13477
joint rank                                        1404/1404
separate-terminal projection rank                   324
terminal-conditioned sumcheck rank              1080/1080
terminal-plus-SC-initial projection rank             328
terminal-and-initial-conditioned rank            1076/1076

selected common-tail columns in minor                880
selected cleared full-domain columns                  524
q degree per individual root bound       880 + 2*524 = 1928
q total-degree bound                         16*1928 = 30848
minor fingerprint                       0xd413eee382667cb5
```

The 1,076 line is exactly `ker(initial_claim,T_z)`.  It is deliberately called
**initial-neutral**, not root-message-neutral: this probe does not impose that
the gamma-combined PCS root message is pointwise zero and does not eliminate G
as a gamma-weighted dependent lane.  Consequently it does not yet imply the
helper/coupled/PCS continuation checks in the strong Good22 predicate.

The now-retired initial-neutral selector screen conservatively booked q degree
`30864`, adding 16 to the executable numerator bound as an anchor guard.  With
`N=2^17`, it gave

```text
rho_q <= 30864/(N-15) = 0.23550058371548258
beta_attempt <= 41040/(2^31-1) + rho_q^4
             = 0.003094980564788099
             < 2^-8.3358539347
beta_attempt^16 < 2^-133.3736629557.
```

These numbers are retained as a comparison only.  The fixed minor exists for
the raw-plus-sumcheck map, but it is superseded below by the true root-neutral
minor for the complete-view route.

## D-after-G root-neutral complete-view bridge

The missing implication can be made structural with one prospective wire
change.  Keep every production generator index and append one full-domain
QM31 lane:

```text
semantic and mask-only C1       0..25
H                                  26
G                                  27
D, with direct mask factor zero    28
```

For a D source, set `delta_G=-gamma*delta_D`.  Since production already
requires `gamma != 0`, this is an exact source-space restriction and

```text
gamma^27*delta_G + gamma^28*delta_D = 0
```

pointwise on all 1,024 message rows.  D contributes no direct mask-oracle
term, so the corresponding compressed-sumcheck image is exactly
`-gamma*F_G*D`.  This is the legitimate version of the old “zero-direct H1”
diagnostic: H1 itself is never assigned a zero direct image.

### Frozen exact result and negative controls

```text
production H/G indices                              26 / 27
new D index                                               28
D separate raw rank                               268 / 268
inactive-balanced H1-padding raw rank              268 / 268
existing root-neutral conditional rank                  1072
with D/G root-neutral directions                  1076 / 1076
post-raw sources checked terminal-zero                  17324
conditional minor fingerprint              0xcc3e3f3feeac0dbb
```

The H1 guard uses the exact public H1 raw view: 64 queried QM31 symbols and
three terminal QM31 values, hence `4*64+4*3=268` M31 coordinates.  Its source
is only inactive H1 padding, balanced against the global inactive dependent
row.  The old 304-row idealized-H allocation is retired and is not evidence
for this premise.

Two algebraically allowed controls remain red:

| schedule | before D | with D | target | fingerprint |
|---|---:|---:|---:|---:|
| terminal certificate | 748 | 786 | 1076 | `0x42e4e7e860fa7ad0` |
| last-round affine-degenerate | 900 | 912 | 1076 | `0xfe338a9a49ff661d` |

Thus D proves a fixed-schedule bridge and supplies a nonzero polynomial
witness.  It does not make every parser-valid field schedule good.

### Complete-view implication

Fix one parser-valid schedule and work after the private-Merkle/EPRO hybrid,
so individual salted roots are simulated and all field challenges are fixed.
Let `R` be the complete separately authenticated q16-plus-three-terminal raw
map, `S` the compressed masked-sumcheck map, and

```text
Gamma_gamma(M) = sum_j gamma^j M_j
```

the pointwise combined message.  The prospective schedule predicate
`Good22_D` requires all of the following, separately:

1. The sixteen relation-free semantic mask maps perform the same-statement
   one-time-pad translation for every physical semantic difference, including
   their inactive-balance identities and separately visible raw values.
2. Each existing C1/G raw block has its canonical rank, the new D raw map has
   rank 268, and the inactive-only balanced H1-padding map has rank 268 onto
   the exact physical H1 raw target.  These are different premises; D rank
   does not prove H1 rank.
3. The exact root-neutral source map has rank 324 on its allowed terminal raw
   projection, rank 328 after the shared initial claim, and joint rank 1404.
   Equivalently, after fixing raw and initial values, its sumcheck image is all
   of `ker(initial,T_z)`, of M31 dimension 1076.
4. Every selected source is pointwise `Gamma_gamma`-zero and has exact
   compressed terminal zero.  Generator order, `factor(D)=0`, nonzero gamma,
   inactive balancing, and the selected minor provenance are fingerprinted.
5. The production encoder, initial relation, OOD evaluation and folds are the
   same linear maps used by the rank model for fixed challenges.

Under these premises, take two valid same-statement witnesses.  First
translate the semantic one-time pads so their separately public C1 field view
agrees.  The unpadded copy helper is supported on the compiled active rows.
Use the inactive-balanced H1 padding to cancel its complete 268-coordinate
raw difference.  This step does **not** erase H1's direct unmasked-oracle
contribution; it only makes the separately authenticated H1 view equal.

The remaining gamma-combined message difference is a raw-zero, relation-zero
message.  Because D is a full QM31 message lane, translate D pointwise to
cancel that message.  In particular an H1 message difference `h` is canceled
by `delta_D=-gamma^-2*h`; its D raw image is zero because the H1 raw image was
already zero.  Equivalently, source-by-source C1 differences may be paired
into G, while D/G kernel directions use `delta_G=-gamma*delta_D`.

After raw values, the initial claim and the combined message agree, the
remaining sumcheck difference still contains the **actual** eta-scaled H1
oracle difference.  Both honest unmasked oracles have Boolean sum zero, and
equal terminal openings force the verifier terminal difference to zero.
Therefore that entire residual lies in `ker(initial,T_z)`.  Premise 3 supplies
a raw-zero, root-zero mask translation that cancels it.

At that point

```text
Delta Gamma_gamma(M) = 0.
```

The circle encoder is linear, so the combined root codeword difference is
also zero.  The initial relation, every circle/line OOD value, every relation
polynomial, every folded word and later queried fiber, and the final
polynomial are deterministic linear functions of that same zero difference.
They are therefore identically equal.  No 712-row PCS determinant, sampled
PCS kernel, or fold-specific continuation assumption remains.

This is a fixed-schedule non-hash field-view theorem.  It does not equate the
individual C1/C2 Merkle roots; private salted commitment simulation and EPRO
programming remain mandatory. The D wire and its differential tests are now
implemented in nondefault Profile 23; mined production and full-view privacy
closure remain separate release gates.

### Executed root-neutral polynomial witness

The explicit q-kernel source frame is green on the frozen schedule:

```text
joint rank / target                              1404 / 1404
terminal projection rank                                324
terminal plus initial projection rank                    328
conditioned root-neutral SC rank                 1076 / 1076
pointwise root-zero sources checked                    10617
selected semantic common-tail columns                  1008
selected mask-only full-domain columns                  380
selected D common-tail columns                           16
q total-degree bound                                  28544
sum selected inverse-gamma exponents                  23105
safe M31 gamma-coordinate degree       4*23105+16 = 92436
z degree in the root-neutral minor                    41040
minor fingerprint                        0xb7472b1f2b1d03e7
```

The fixed log-19 domain gap is closed by exhaustive exact enumeration.  For
every fiber `q in 0..2^17`, the root used above equals
`line_domain_x_for_circle(19,1,q)`; all 131,072 roots are distinct, and none is
one.  Thus distinct sampled fiber indices imply distinct roots and
`g_q(1)!=0` automatically.  No root-one anchor or extra q-degree row is
needed.

The gamma clearing uses `Norm(gamma)^e`, not an illegal QM31 rescaling of an
M31 source.  A semantic or mask-only table has only one M31 source coordinate;
multiplying it by `gamma^e` would leave its legal source module.  The factor
four in 92,436 is therefore retained.

For the complete raw-view product, the 41,040-degree root-neutral minor
contains 324 terminal pivots but only one independent G/D combination.  A
conservative promoted certificate separately multiplies the missing
independent G-or-D 12-row terminal certificate and the H1-padding 12-row
certificate:

| determinant component | continuous M31 degree |
|---|---:|
| root-neutral raw plus compressed SC minor | 41,040 |
| independent remaining G/D raw certificate | 120 |
| inactive-balanced H1 raw certificate | 120 |
| inverse-gamma coordinate clearing | 92,436 |
| **conservative product** | **133,716** |

The raw query portions are structural for every ordered distinct q16 tuple;
the 120-degree rows are their three-terminal Schur complements.  The host-only
executable now eliminates all 256 query coordinates first and freezes the
source column, terminal pivot row and nonzero pivot value for each remaining
row:

```text
remaining G/D terminal Schur rank     12 / 12
remaining G/D minor fingerprint       0x0a2dbf8f1a9059c0
H1 inactive-padding terminal rank     12 / 12
H1 minor fingerprint                  0x5c61aee383dff271
complete product fingerprint          0x1d6697447b7a1448
```

The product provenance binds those two fingerprints to the 1,404-row
root-neutral fingerprint `0xb7472b1f2b1d03e7` and to the exact
`q=28544`, `z=41280`, `gamma=92436`, `continuous=133716` degree tuple.  The
source, row and value lists are in
`results/stage2/profile23_complete_good_product.json` and are replayed by
`profile23_complete_good_product`.

The exact schedule-only host predicate and q3 least-good selector are now
implemented in `state_only_good23`.  It evaluates all three independent
label-44 branches before selecting and requires root-neutral rank plus both
raw Schur ranks; the frozen Profile-23 fixture is green on selectors 0, 1 and
2 and selects 0.  The definition fingerprint is
`0x9cdd6a6c14b796760c8dd73329effbfc734a048ccecc4ce10f214bdae3a6af2a`.
The exact release replay currently costs about 60 seconds per q3 set, so
common-map caching is a production-host latency task even though it has no
on-chain CU effect.  See `docs/stage2-profile23-good-schedule-host.md`.

## Conditional three-selector fallback

This protocol-change fallback avoids needing the minor to be nonzero for
*every* ordered distinct q16 tuple. It is now implemented as nondefault
Profile 23. It does not alter the historical Profile-22 wire or increase the
cap of 16 attempts.

After the final PCS polynomial and final work nonce have fixed the Fiat--Shamir
prefix, derive `m=3` independently domain-separated candidate q16 tuples.  A
tuple is ordered and without replacement internally; tuples may overlap each
other.  The honest prover evaluates the same schedule-only Good22 predicate on
the three candidates, chooses the least good selector, and retries the entire
attempt if all three are bad.  The proof must carry a canonical selector in
`0..3`.  The verifier absorbs a new query-candidate domain tag plus that
selector after the final nonce and derives only the selected tuple; the honest
prover clones the pre-selector state to test all three labels.  This keeps the
on-chain delta to one tagged absorb and one selector byte.  The verifier need
not run the host rank gate.

This selector must be sampled only after every PCS root, fold record, final
polynomial and existing work nonce.  Sampling it earlier would reveal the
queries before the prover is bound to the PCS tail and would invalidate the
existing commit-before-query and grinding argument.

The candidate liveness theorem has three explicit premises:

1. the executable D-after-G root-neutral polynomial-kernel minor above, plus
   the independent G/D and H1 raw certificates, form one nonzero product with
   continuous degree at most `133716` and q-degree at most `28544`; and
2. the promoted `Good22_D` implementation checks the exact premise inventory
   of the complete-view implication above; the older initial-neutral mixed
   minor is not silently substituted; and
3. the three candidate-query streams are conditionally independent and exact
   uniform ordered-distinct tuples under the transcript/EPRO hybrid.

Under those premises, condition first on the common continuous schedule.  The
continuous bad event is shared by all three candidates, while the remaining
q-bad events are independent.  With

```text
p = 2^31-1
N = 2^17
rho_q = 28544/(N-15) = 0.21779836254454168
beta_attempt <= 133716/p + rho_q^3
             = 0.010393777091336816
             < 2^-6.5881361659.
```

At the unchanged cap 16, the rank-exhaustion contribution is therefore

```text
beta_attempt^16 < 2^-105.4101786541.
```

This Profile-23 liveness bound is **bookable**: the complete product is
executable, and the three-selector transcript/soundness/EPRO inventory is
independently pinned by `profile23_soundness_epro_ledger`. The common-attempt
builder, selector wire/parser, verifier, valid selectors 0/1/2, fixed release,
and diagnostic SBF measurement are integrated. This does **not** enable the
default production tag: the canonically mined tag-60 run and full-view privacy
closure remain pending.

### Bounded query-sampler abort

Each q16 candidate uses the existing 64-draw bounded distinct sampler.  Failure
to collect 16 distinct indices entails at least 49 duplicate draws; before
completion each draw collides with probability at most `15/2^17`.  Thus

```text
epsilon_sampler_one
  <= binom(64,49) * (15/2^17)^49
  < 2^-594.3816392172.

epsilon_sampler_cap16_m3
  <= 16*3*epsilon_sampler_one
  < 2^-588.7966767164.
```

The clean builder rule is to abort the private attempt if any of the three
bounded samplers exhausts.  Because a controlled build failure currently
collapses the whole manager to the same public abort rather than consuming a
retry, the complete availability expression contains this union term
separately:

```text
Pr[public abort]
  <= beta_attempt^16
     + 16*epsilon_build_other
     + 48*epsilon_sampler_one.
```

### Soundness cost

A malicious prover may choose any of the three verifier-accepted query tuples;
the verifier does not enforce the honest "least good" rule.  Multiplying the
*entire* current soundness ledger by three is conservative:

```text
epsilon_sound,m3 <= 3 * 2^-102.4647288576847
                  =     2^-100.8797663569635.
```

The more accurate conditional argument changes only the final q16 miss term:
all batching, folding, algebraic and hash events precede the selector.  The
selector is nevertheless a new prover-message/challenge boundary unless a
byte-exact proof merges it into the existing final-nonce boundary.  The
conservative profile-23 BCS inventory therefore uses factor 32, not the old
factor 31.  With the q term multiplied by three, the current projections are

```text
after profile-23 BCS factor 32  101.6242346777 bits
after factor-40 sensitivity     101.3023065828 bits.
```

Those values are pinned by the executable
`profile23_soundness_epro_ledger` and the machine artifact
`results/stage2/profile23_d_after_g_soundness_epro.json`. The selector was not
a free host optimization: Profile 23 implements the new profile/layout
fingerprint, canonical selector parsing, three transcript query streams, KAT,
selected-opening serialization, mutation teeth, public-view/EPRO inventory,
and whole-soundness x3 ledger above.

### EPRO and entropy rows

The complete-view algebra does not discharge the commitment compiler.  D adds
one 1,023-QM31 balanced private source, 67 opened QM31 values per proof
(`64` queried plus `3` terminal), 1,072 serialized bytes, and 64 bytes to each
C2 leaf.  It adds no Merkle tree or salt count, but it changes the salted-leaf
preimage width and mask-expander query inventory.  The three selector streams
also add honest-prover random-oracle queries even though only the selected
opening is serialized.

The promoted executable EPRO ledger exposes

```text
field-expander inputs = 53,892
transcript inputs     = 637
literal inventory C  = 969,993
```

The exact leading term is `104.1123851895` bits and the programming-collision
term is `209.2247704720` bits. These are bookable for the implemented
nondefault Profile-23 transcript inventory; they do not certify the still-
pending mined production and full-view privacy closure.

## Guards

Fast terminal/sign/kernel identity:

```sh
NO_DNA=1 cargo test -q -p aspis-prover --lib \
  compressed_sumcheck_terminal_and_conditional_kernel_match_the_wire
```

Frozen exact valid-view replay:

```sh
NO_DNA=1 cargo test --release -q -p aspis-prover \
  --test profile21_hvzk_privacy \
  frozen_actual_protocol_coupled_view_is_contained -- --ignored
```

Complete prospective Good-product provenance:

```sh
NO_DNA=1 cargo run --release -q -p aspis-prover \
  --example profile23_complete_good_product
```

Profile-23 soundness and EPRO repin:

```sh
NO_DNA=1 cargo run -q -p aspis-prover \
  --example profile23_soundness_epro_ledger
```

Deficient-schedule negative control:

```sh
NO_DNA=1 cargo test --release -q -p aspis-prover \
  --test profile21_hvzk_privacy \
  single_last_round_exclusion_is_red_for_documented_minimal_containment \
  -- --ignored
```

The host replay command is:

```sh
NO_DNA=1 target/release/examples/profile21_good_schedule_probe minimal-actual
```

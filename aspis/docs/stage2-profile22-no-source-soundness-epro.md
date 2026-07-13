# Profile 22 no-source theorem ledger

Date: `2026-07-13`

Status: **the selected Johnson soundness arithmetic is green at 102.4647 bits
after the frozen profile-20 BCS factor, and the conditional computational-ROM
privacy term is green at 104.1247 bits for `Q_H <= 2^128`, `R <= 16`.
This is not yet a complete-system claim.**  Affine containment is currently
proved only on the frozen q16 schedule, and the bounded-attempt/fixed-release
wallet policy is not implemented.  The final production proof must also mine
all six work records and exercise the atomic mutation path.

The machine-readable ledger is
`results/stage2/profile22_no_source_soundness_epro.json`.  Its arithmetic is
pinned by
`crates/aspis-prover/examples/profile22_soundness_epro_ledger.rs`.

## Exact protocol object

Profile 22 is profile 20 with private salted Merkle leaves.  It retains the
ordinary atomic width-28 relation, transcript order and PCS:

```text
message dimension                         1,024
circle symbols                          524,288
four-symbol query fibers                131,072
rate                                      1/512
scalar columns                               28
q                                             16
tree depths                   [17,17,15,13,11]
private value widths        [416,128,64,64,64]
batch work                                    38
fold work                         [39,35,31,27]
final/query work                              38
```

There are exactly six work subdomains: batch, four folds and final/query.
There is no `X`, `F`, `U`, `delta`, `tau`, source root, source work,
translated root, source MCA event or source-query event.  Private salting
changes leaf preimages and opening bytes.  It does not change the committed
field values, their code, the relation polynomial, the fold equations or the
query sampler.

The five private records are `value || salt32`.  A q16 tuple opens at most 16
records in each tree, hence at most 80 salts or 2,560 salt bytes.  Projecting
distinct layer-zero queries to a later layer can collide, so 80 is a maximum,
not an assertion about every transcript.

## Version-pinned Johnson reduction

The following local PDFs and hashes are the source pins used by the numeric
ledger:

- S-two Whitepaper, ePrint 2026/532, PDF dated 2026-03-24, SHA-256
  `e3b0132ec598ca16835c1de3c85d0c8b07c41b5f063f1d88b5a9628c22252c3f`:
  Theorem 31, Corollary 1, Lemmas 3--4 and Theorems 19 and 22.
- Bordage--Chiesa--Guan--Manzur, ePrint 2025/2051, revision dated
  2026-05-19, SHA-256
  `23519c2d5d6541ee53e635b10c22d5f5964301b79a853d9394da267062e520a6`:
  Definition 3.19, Lemmas 4.1 and 4.4, Theorem 8.2, Definition 9.1,
  Theorem 9.2 and Lemma 9.3.
- WHIR, ePrint 2024/1586, SHA-256
  `ccacc62cf5529ff95c3cf115cf730b020336f8d95c310c8deb64e3beac30ce61`:
  Lemma 4.13, Theorem 4.20 and Lemma 4.21.

The exact circle FFT subspace and its Johnson correlated-agreement base case
come from S-two.  The BCGM results are used only through the cited
code-agnostic tensor/linear-image reductions and as an ambient-RS check.
BCGM Theorem 9.2 alone is not treated as a subcode-inheritance theorem for
the exact circle FFT space.  No up-to-capacity or revised-capacity conjecture
is used.

Let

```text
K     = QM31,
Q     = |K| = (2^31-1)^4,
rho   = 1/512,
alpha = 1.05*sqrt(rho) = 0.04640388251536719.
```

There are 131,072 complete four-symbol fibers, so the Johnson agreement cap
is

```text
A = floor(alpha * 131072) = 6082.
```

S-two Theorem 19 gives the 28-column powers-generator row.  S-two Lemma 4
gives the four degree-three fold rows, and WHIR's fold/list commutation is
applied to the same scalar combined word.  The q row is the exact
without-replacement probability

```text
C(6082,16) / C(131072,16),
```

normalized by the final 38-bit work record.  The OOD row uses list cap 240,
root caps `[1024,255,63,15]`, two samples per round and sample space
`Q-|CM31|`.

## Reconciled soundness ledger

The atomic local rows use the current registry, not the stale generic
profile-20 placeholders: 183 copy terms, tuple width 17, pole numerator
`4*(183+1024)`, theta degree 24 and ten degree-27 zerocheck rounds.

| event | bits |
| --- | ---: |
| width-28 powers batching after batch g38 | 108.3684875342 |
| four fold rows after `[39,35,31,27]`, union | 112.0797907885 |
| q16 without replacement after final g38 | 108.9018865972 |
| two-sample OOD/list union | 213.1000183949 |
| relation sumchecks and OOD mixers `24/Q` | 119.4150374966 |
| nonzero gamma plus three-point batching `29/(Q-1)` | 119.1420190022 |
| copy-inactive nonzero-gamma claim `27/(Q-1)` | 119.2451124951 |
| atomic tuple compression `183*17/Q` | 112.3968373178 |
| atomic copy/range poles `4*(183+1024)/Q` | 111.7627900366 |
| atomic theta collision `24/Q` | 119.4150374966 |
| zerocheck equality-point reduction `10/Q` | 120.6780719024 |
| zero-sum h1 helper batching under mu `1/Q` | 123.9999999973 |
| mask/original batching under nonzero eta `1/(Q-1)` | 123.9999999973 |
| ten degree-27 zerocheck rounds `270/Q` | 115.9231844003 |
| Poseidon2 public-digest assumption | 124.0000000000 |
| SHA-256/ROM assumption | 128.0000000000 |

These five state-only zerocheck rows are distinct.  Theta binds the 25
constraint lanes; the ten-coordinate equality point reduces a nonzero Boolean
residual table to its MLE; mu binds the separately claimed zero sum of h1;
eta binds the mask oracle to the original constraint oracle; and `270/Q` is
the interactive sumcheck protocol error.  The eta, mu and equality-point
terms are unioned explicitly and are not hidden inside `270/Q`.

Eta and gamma are sampled with explicit nonzero conditions. They are
exact-uniform on `QM31 minus {0}`, hence the `Q-1` denominators. Excluding
zero gamma is also required by the affine-privacy gate: gamma zero is an
exact production-continuation counterexample even when raw and masked-
sumcheck ranks are full. Any full-field polynomial/MCA failure bound used for
gamma transports to this sampler by conditioning on `gamma != 0`; dividing
by `Pr[gamma != 0]=(Q-1)/Q` is exactly the displayed replacement of `Q` by
`Q-1`, so this sampler change does not assume a new MCA theorem. Exhausting
all three nonzero draws is a completeness rejection with probability
`Q^-3` per such challenge (apart from the separately bounded M31 limb
sampler exhaustion); it is not a zero fallback or a soundness event. Line
OOD samples are exact-uniform outside CM31. The
secure-circle poles `+i,-i` already lie in CM31, so the pinned OOD sample
space `Q-|CM31|` does not omit two additional points.  The LogUp/copy/range
denominator events are the displayed `4*(183+1024)/Q` row.  There is no
delta or source denominator.

Their direct union is

```text
107.41892516807158 bits.
```

Profile 22 adds no prover-message/challenge boundary to profile 20, so it
retains the profile-20 transcript-compiler factor 31.  Applying it gives

```text
107.41892516807158 - log2(31)
  = 102.46472885768470 bits,
```

or 2.464729 bits above the target.  A factor-40 sensitivity is
102.0969970732 bits.  The factor remains a named compiler pin: a transcript
boundary change must recount it rather than silently inheriting 31.

The paired batch/final work sensitivity, with the fold schedule unchanged,
is:

| batch and final work | event union | after factor 31 | after factor 40 |
| ---: | ---: | ---: | ---: |
| g36 | 105.5602957610 | 100.6060994507 | 100.2383676662 |
| g37 | 106.5116166736 | 101.5574203632 | 101.1896885787 |
| **g38 selected** | **107.4189251681** | **102.4647288577** | **102.0969970732** |

Changing only a difficulty threshold changes neither proof bytes nor verifier
CU: the verifier still decodes two `u64` records and evaluates the same two
SHA predicates.  It does change honest proving work.  If `K` is the
zero-based minimum successful nonce for success probability `p=2^-g`, then
`E[K]=2^g-1` failed candidates and `E[K+1]=2^g` predicate hashes/trials (up
to negligible conditioning on existence below `u64::MAX`).  The two selected
g38 stages therefore cost an expected

```text
2*2^38 = 549,755,813,888 predicate hashes.
```

Including unchanged folds g39/g35/g31/g27, the expected six-stage totals are

```text
g36 pair:   723,836,207,104 hashes
g37 pair:   861,275,160,576 hashes
g38 pair: 1,136,153,067,520 hashes.
```

The g38 selection adds 412,316,860,416 expected hashes over g36 and makes
total expected mining about 1.5696 times larger.  This prover-side cost buys
more than two bits of soundness margin even under the factor-40 sensitivity;
g36's 0.238-bit factor-40 margin is too brittle to freeze.

S-two Theorem 22 states

```text
eps_BCS(T) <= (T+R_BCS)*max_i eps_i + 3*(T^2+1)/2^256.
```

The ledger conservatively replaces `max_i` by the direct event union and
uses the factor 31 for `(1+R_BCS/T)`.  At `T<=2^128`, the normalized hash term is
at most about `2^-126.4150`.  Including a 128-bit SHA row in the union and
then multiplying the complete union by 31 is more conservative than that
term.  It must not be interpreted as a standard-model SHA theorem.

The 102.4647-bit row is applicable only when the production path checks
g38 before gamma, checks the four fold records in their own rounds, checks
the final g38 before q16, and absorbs each accepted nonce at the frozen
position.  An unmined diagnostic fixture supplies no work credit.

## Exact profile-22 random-oracle inventory

The privacy statement is computational in a domain-separated SHA-256 random
oracle.  The selected 32-byte salts do not instantiate the BCS statistical
private-Merkle lemma, which calls for independent `2*lambda`-bit leaf salts.
For `lambda=256` that route would require 64-byte salts.

### Merkle forest

The five trees contain

```text
2^17 + 2^17 + 2^15 + 2^13 + 2^11 = 305,152 leaves.
```

They have exactly 305,147 internal nodes.  The conservative ledger books
305,152 node inputs, leaving five inputs of slack.  It separately books one
salted-leaf preimage and one hidden salt-derivation input for every leaf.
Maximal unopened frontier labels are a subset of the node inventory; counting
them again would double count the same forest.

### Field expander

The atomic mask inventory consumes 22,850 M31 outputs:

```text
5,262 relation-free cells
+ 10*1,024 mask-only C1 cells
+ 1,024 QM31 G cells
+   813 QM31 independent h1-padding cells
= 22,850 M31 coordinates after tower expansion.
```

The implementation permits 16 candidate words per M31 output and obtains
eight words per SHA block.  The complete bounded input cap is therefore

```text
22,850 * 16 / 8 = 45,700.
```

There is no source expander.  The eight-input seed/binding allowance is kept
as a conservative constructor bound, including the field-seed derivation and
the currently derived-but-unused reserved source-seed value.  Public,
deterministic hashes that the simulator can evaluate directly are not hidden
pre-query events.

### Transcript and work

In the non-rejecting execution, the ordinary profile-20 schedule has

```text
43 absorb inputs, 49 squeeze inputs, 49 advance inputs, 6 work inputs.
```

For the programmed bound, there are at most 67 calls to the bounded QM31
sampler: both eta and gamma permit up to three nonzero draws. Each call can
consume at most four SHA blocks. The q16 sampler has a
64-word cap, or eight blocks.  Thus

```text
P_FS = 67*4 + 8 = 276,
C_transcript = 43 + 276 squeeze + 276 advance + 6 work = 601.
```

This is lower than profile 21 because profile 22 has no nonzero delta, source
work or source transcript records.  The difference is structural, not a
credit taken from a normal non-rejection trace.

### Complete input bound

The conservative one-attempt input inventory is

```text
salted-leaf preimages                             305,152
hidden leaf-salt derivation inputs                305,152
hidden Merkle-node inputs                         305,152
bounded field-mask expander inputs                 45,700
seed/binding inputs, conservative upper bound           8
bounded transcript/work inputs                        601
                                                   -------
C                                                  961,765
```

Every root, opened value-plus-salt record and frontier is covered by the
Merkle rows.  Every challenge, advance and work predicate is covered by the
transcript rows.  Proof-account framing, logs and mutation are treated below;
they introduce no new hidden random-oracle family.

## Conditional computational-ROM theorem

Let `Q_H` be the distinguisher's total adaptive random-oracle queries,
including post-proof queries, and let `A<=16` bound local proving attempts.
Let:

- `eps_aff` be the all-schedule affine-simulation error;
- `eps_field_prg` and `eps_salt_prg` be explicit expander advantages outside
  the ideal-RO model; and
- `eps_side` cover release timing, failed attempts, logs and external prover
  channels.

The conservative bound is

```text
eps_priv <= eps_aff
          + eps_field_prg + eps_salt_prg
          + A*C*Q_H / 2^256
          + binom(A*C,2) / 2^256
          + 6*A*exp(-2^25)
          + eps_side.
```

The last term before `eps_side` is six-stage nonce-space exhaustion at the
worst g39 stage.  The simulator conditions each work subdomain with the exact
minimum-success law and a lazy response rule; it does not pay `sum 2^g`.

At `Q_H<=2^128`, `A=16` and `C=961,765`:

```text
A*C*Q_H / 2^256            = 2^-104.1246751001
binom(A*C,2) / 2^256       < 2^-209.2493502940
6*A*exp(-2^25)             < 2^-48,408,806.0613.
```

For one attempt the leading term is `2^-108.1246751001`.  The sixteen-attempt
bound costs exactly four bits.  In the declared ideal-RO model,
`eps_field_prg=eps_salt_prg=0` because both expansions are domain-separated
queries to that oracle.  A standard-model statement must restore and
instantiate both terms.

## Complete public view

The simulator's output must cover all of the following, not just opened field
values:

1. all five roots, opened records and maximal frontier hashes;
2. all proof bytes and the account framing
   `"ASPU" || proof_len_u32_le || upload_authority32 || proof_bytes`;
3. chunk-upload history, if visible, as public framing of those same bytes;
4. production logs and return data;
5. the pre/post pool and nullifier account images;
6. the System-owned marker branch, payer/rent deltas and CPI result; and
7. failed attempts, retry count, proving/mining progress, release time and any
   remote-prover channel.

For a fixed public statement and public marker branch, successful mutation is
deterministic: increment sequence, install the public output anchor, and
write the public pool/nullifier marker.  Rent effects are public functions of
the supplied accounts.  These surfaces add no witness-dependent field value
once the proof has been simulated.  They still need a production integration
test showing no diagnostic trace, return data or failed-attempt bytes escape.
There is no receipt in the one-transaction construction.

The diagnostic-unmined profile-22 fixture is pinned at 56,686 bytes and
SHA-256 `77736f0ea30ae9e2516537213e7dce386c9be69e3c772e5b50f03c57892136f8`.
Its typed privacy audit classifies every byte with no gap or overlap.  That is
not yet the final production-proof pin: mined nonces change later challenges,
the q16 tuple, and potentially projected frontier counts.

## Residual obligations

The numeric terms above do not hide the remaining theorem gaps:

1. **Affine universalization and liveness.**  The canonical schedule-only
   `Good22` predicate, bounded unpublished manager, and exact containment
   replay are implemented.  Every emitted schedule therefore passes the
   physical/legal/helper containment test.  What remains open is a uniform
   quantitative success bound for the nonzero-gamma raw/sumcheck gate; until
   that is proved, cap 16 is a privacy-accounting ceiling rather than a proved
   negligible no-proof probability.
2. **Fixed release (`eps_side`).**  OS entropy, durable nonce burn,
   zeroization, and the one-output fixed-boundary controller are implemented
   and tested.  The wallet must still invoke the controller at the declared
   witness-independent boundary and ensure that no failed root, proof, work
   nonce, retry count, progress line, error class, telemetry event, or remote
   worker message escapes.  Local hardware/OS/power/storage leakage and a
   late callback remain in `eps_side` unless separately modeled.
3. **Production work and mutation.**  One actual profile-22 proof must mine
   all six records, pass the production verifier with no bypass, and complete
   the atomic mutation in the same instruction.  Diagnostic-unmined evidence
   does not discharge this.
4. **Model boundary.**  This is computational ROM/EPRO privacy, not
   statistical private-Merkle ZK and not a standard-model SHA-256 PRG claim.

Once those obligations are green on the same wire, the no-source shape needs
no code-switch theorem and no source-MCA/query row.  The soundness number is
then the 102.4647-bit Johnson row above, while the leading bounded-query
privacy term is 104.1247 bits.

## Guard

```text
NO_DNA=1 cargo run --release -q -p aspis-prover \
  --example profile22_soundness_epro_ledger
```

The guard recomputes the Johnson agreement cap, batching, folds, exact q16
miss, OOD union, atomic local rows, BCS factors, tree/input inventory and
`Q_H=2^128,A=16` privacy exponents.  It intentionally proves arithmetic only.

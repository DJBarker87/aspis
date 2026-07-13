# Atomic profile-21 upper-G/H rank scan

Status: **red for hiding containment.** This is an exact host-only diagnostic
on the existing tag-37/profile-21 q16 transcript. It does not enable a
production acceptance path and it does not justify adding upper message
coefficients to G or H.

## Result

The frozen lower-half masking construction has masked-sumcheck rank 1080 and
PCS rank 712. The conservative same-statement semantic audit adds four M31
directions, at PCS pivots `1084..1087`, so the required rank is 716. Legal
zero-initial-claim sumcheck directions add nothing after those semantic
directions.

Giving the existing G lane arbitrary coefficients in message rows
`1024..2047` raises the PCS rank from 712 to 808. Giving H those coefficients
does exactly the same. Giving both G and H upper coefficients still has rank
808: their induced public-observation increments are the same 96-dimensional
M31 space. Every variant then needs the four semantic pivots and reaches 812.
Therefore none contains the conservative semantic space.

```text
support             PCS       +semantic   +legal SC   contained
lower baseline      712       716         716         no
upper G only        808       812         812         no
upper H only        808       812         812         no
upper G and H       808       812         812         no
```

The deterministic minor fingerprints are:

```text
semantic            0x1cd18a38f9c573e1
upper G             0x918c2eb84d4176de
upper H             0x245d9ec15975d760
upper G and H       0xa44357704645655f
```

This kills the proposed no-new-oracle hiding shortcut at q16. Increasing the
query count cannot repair a containment failure already present in the
literal q16 View, so no q18 scan is credited.

## Literal geometry and the 1/512 boundary

The probe uses the real profile-21 q16 query indices, all four normalized
folds, the raw openings, OOD samples, relation coefficients and final vector.
For a log-11 message on the current log-19 word the exact geometry is:

```text
message coefficients             2048 QM31
codeword length                 524288
actual rate                       1/256
layer-zero openings/oracle        64 M31
later openings/oracle            192 QM31
OOD values/oracle                   8 QM31
relation coefficients/oracle       28 QM31
final coefficients/oracle           8 QM31
PCS tail/oracle                   236 QM31
joint PCS ambient                1212 M31
```

Thus extending the message from log 10 to log 11 while retaining the current
log-19 word silently changes the rate from 1/512 to 1/256. Retaining rate
1/512 requires a log-20 word of length 1,048,576. That is not a parameter
substitution in this artifact: it changes the leaf domain/path geometry and
requires a fresh exact Fiat--Shamir query schedule and soundness ledger. Four
folds leave eight final QM31 coefficients, not four.

## What is exact, and what is not proved

The diagnostic uses exact sparse circle-encoder basis entries for the
log-19 word and the production fold/opening formulas. Upper-G raw kernels are
first quotiented through the already-full rank-1080 sumcheck image; this is
necessary because raw-G cancellation can carry nonzero sumcheck work. H is
then tested both independently and jointly. The semantic audit covers all 16
semantic columns and lower rows `1..1023`, with the same four-dimensional
compatibility quotient used by the profile-21 semantic tooth. It also tests
all legal residual sumcheck directions.

The result is a fixed-transcript exact rank counterexample, not an HVZK proof,
an MCA theorem or an integrated-CU measurement. In particular, it gives no
credit for the extra upper coefficients in the one-transaction bridge.

## Reproduction

```sh
cargo check -p aspis-prover
cargo run --release -p aspis-prover --example profile21_upper_oracle_rank -- \
  results/stage2/proofs/atomic_state_only_profile21_v3_unmined.bin
```

The compact machine-readable result, including the actual query tuple and
all three variant fingerprints, is
`results/stage2/atomic_profile21_upper_oracle_rank.json`.

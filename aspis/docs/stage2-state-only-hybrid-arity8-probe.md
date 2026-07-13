# State-only hybrid arity-4/arity-8 PCS probe

Date: 2026-07-13

Status: **host algebra green; complete-view hiding deficit unchanged; CU not
measured; soundness transport open. Do not assign a production tag.**

## Decision

Pure two-round arity 16 is rejected before implementation. It changes each
query from four 4-symbol fibers (16 authenticated symbols total) to two
16-symbol fibers (32 total), and the first layer alone grows from 4 to 16
symbols. The exact rate-1/32 state-only measurement attributes 295,209 CU to
the current layer-zero query block. Arity 16 multiplies the data-dependent
layer-zero symbol/recombination count by four; two fewer roots cannot be
credited as an integrated saving without measuring a new instruction.

The only structurally credible grouped-fold variant keeps the first fold
unchanged and groups the remaining three binary variables:

```text
message: 1024 --arity 4--> 256 --arity 8--> 32 explicit coefficients
codeword: 32768 --arity 4--> 8192 --arity 8--> 1024 final evaluations
query:       4 symbols          8 symbols       (12 total, versus 16)
roots:       C1/C2              one line root   (versus three line roots)
```

This variant is an arithmetic/CU research candidate, not a hiding repair. The
exact complete-view rank gate still has a 120-M31 (30-QM31) deficit.

## Exact algebra

For one arity-8 coefficient chunk, define

```text
A(X) = sum_{i=0}^7 a_i X^i
B(X) = (b_0 + b_7 X + b_6 X^2 + ... + b_1 X^7) / 8.
```

The relation polynomial is the sum of `A(X)B(X)` over all chunks. It has
degree at most 14 and therefore 15 QM31 coefficients. The root-of-unity
boundary is

```text
sum_{omega^8=1} P(omega) = 8 * (p_0 + p_8) = sum_i a_i b_i.
```

At the transcript challenge `beta`, the primal coefficients fold as

```text
a'_j = sum_{i=0}^7 beta^i a_{8j+i},
```

and the dual weights fold as

```text
b'_j = (b_{8j} + beta^7 b_{8j+1} + ... + beta b_{8j+7}) / 8.
```

Thus `P(beta) = sum_j a'_j b'_j`. The codeword implementation performs two
existing normalized line arity-4 folds with challenge `beta`, followed by the
remaining binary line fold with challenge `beta^4`; equivalently its internal
binary challenges are `beta, beta^2, beta^4`.

The host rank run checked the degree-6 first-round boundary/fold identity and
the degree-14 second-round identity on every one of the 1,024 message basis
rows using the actual rate-1/32 circle encoder. A separate core test checks the
materialized arity-8 dual fold on random QM31 vectors.

## Exact opening surface and rank result

The q29 fixture has 29 distinct `q >> 3` later leaves. Its hybrid PCS tail is:

| Block | QM31 values |
|---|---:|
| one later layer (`29 * 8`) | 232 |
| two rounds of two OOD samples | 4 |
| relation polynomials (`7 + 15`) | 22 |
| final coefficients | 32 |
| **tail total** | **290** |

Release-mode exact rank output:

| Quantity | M31 rank/dimension |
|---|---:|
| complete joint serialized coordinates | 1,636 |
| declared valid complete-view image | 1,512 |
| selected mask image | 1,392 |
| valid-witness helper augmentation | 1,392 |
| **ambient deficit** | **120 = 30 QM31** |

The valid-witness containment tooth remains green, but full ambient HVZK does
not. The fewer later openings do not remove the missing directions: the final
polynomial grows from 4 to 32 coefficients, and the complete image moves by
the same amount on both sides. This falsifies the hoped-for claim that merely
collapsing the later roots closes the existing masking deficit.

## CU status

No hybrid SBF instruction or production proof wire was built, because the
rank result is not green and the soundness obligations below are open. The
following are measurements of the current arity-4 instruction, not hybrid
measurements:

| Current exact rate-1/32 q29 block | CU |
|---|---:|
| query shared setup | 2,219 |
| layer-zero query only | 295,209 |
| all three later query layers only | 175,069 |
| full query arithmetic | 472,497 |
| all Merkle verification | 187,681 |

Operation-count deltas are directional only:

- authenticated query symbols fall from 16 to 12 (25%);
- later symbols fall from 12 to 8 (33.3%);
- normalized binary fold steps fall from 12 to 10 per path (16.7%), or from
  9 to 7 in the measured later-only block (22.2%);
- later roots fall from three to one;
- relation convolution products rise from 5,440 to 6,144 (12.9%);
- relation coefficients fall from 28 to 22;
- the explicit final polynomial grows by 28 QM31 values.

Applying 22.2--33.3% to the measured 175,069-CU later-query block suggests a
38.9--58.4K query saving, but that is **not a measurement**. Merkle/root savings
and final32 costs have not been isolated on the current instruction. No
six-figure CU claim is made from this probe.

## Soundness obligations

The degree-7 generator `(1,beta,...,beta^7)` is a polynomial generator. The
May 2026 revision of Bordage--Chiesa--Guan--Manzur states that all polynomial
generators have mutual correlated agreement for Reed--Solomon codes up to the
Johnson bound. S-two proves cross-domain correlated agreement for its
multi-table circle-FRI construction up to Johnson. Those are the right core
results, but neither source identifies this custom two-round Aspis transcript
as an instance automatically.

Before production, all of the following remain mandatory:

1. Prove that the grouped normalized circle/line fold is the required
   scaled-GRS/circle-code morphism at both rounds, including the final32 code.
2. Transport polynomial-generator MCA for `Gen_4(alpha)` and
   `Gen_8(beta)` through the exact M31/QM31 batch and the Aspis circle subcode.
3. Prove the fold/list-decoding commutation statement for the grouped
   arity-8 round (or reduce it rigorously to the source theorem).
4. Re-derive query gathering for one 4-symbol layer-zero fiber and one
   8-symbol later fiber, including deduplication and final-index mapping.
5. Define a fresh append-only Fiat--Shamir tag and order. The second OOD
   samples and `beta` must be sampled only after the one later root is bound;
   final32 and queries follow the second relation message.
6. Recompute the Johnson T1/T2/BCS union and the per-fold grinding schedule.
   The current four-round `[39,35,31,27]` schedule is not reusable.
7. Re-run the 1/32 finite-length and query-sampling ledger at q29. No
   revised-capacity or refuted old-capacity assumption may be smuggled in.

Primary sources:

- [S-two Whitepaper, ePrint 2026/532](https://eprint.iacr.org/2026/532)
- [All Polynomial Generators Preserve Distance with Mutual Correlated Agreement, ePrint 2025/2051](https://eprint.iacr.org/2025/2051)
- [WHIR, ePrint 2024/1586](https://eprint.iacr.org/2024/1586)

## Reproduction

```text
NO_DNA=1 cargo test -p aspis-core \
  materialized_arity8_dual_preserves_the_folded_dot

NO_DNA=1 cargo test --release -p aspis-prover \
  --test state_only_full_proof \
  rate32_q29_hybrid_arity4_arity8_complete_view_rank_probe \
  -- --ignored --nocapture
```

The host prototype deliberately does not define a production proof parser,
Merkle format, transcript tag, or verifier acceptance path.

# Stage 2 evaluator and feasibility decision

Date: `2026-07-10`

Status: **the no-proof SpendV0-min evaluator milestone passes; the original
single-verification-transaction product gate fails after one explicit shrink
attempt. Split verification is the named continuation.** This is not an
end-to-end proof result.

## Executable statement oracle

`aspis-statement` implements the direct semantic evaluator before any proof
plumbing. It pins Poseidon2-M31 to `p3-mersenne-31 = 0.6.1`: width 16,
rate/capacity 8/8, alpha 5, 8 full rounds and 14 partial rounds. The scalar
implementation passes Plonky3's default width-16 KAT and differential tests
over 16 deterministic states against the pinned upstream crate. Parameter
source: [Plonky3](https://github.com/Plonky3/Plonky3); construction source:
[Poseidon2](https://eprint.iacr.org/2023/323.pdf).

The 13-vector economic corpus passes in
`results/stage2/evaluator_corpus.json`: valid spend, field-wrap inflation,
wrong asset/public binding, wrong anchor, wrong path, forged ownership key,
wrong nullifier, wrong output commitment, double-spend replay, zero and
`2^30-1` boundaries, `2^30` rejection, and balance mismatch. In particular,
the attack `(P-1) + 2 = 1 mod P` is rejected by the integer range check before
the field equality can launder it.

At demo depth 20 the evaluator schedules 49 Poseidon2 permutations (1 owner,
3 note, 2 nullifier, 3 output, 40 Merkle), or 1,078 permutation rounds. A
four-round-per-wide-row candidate uses 294 Poseidon rows and k' = 80 opened
values; the active-row bracket is 64 degree-5 terms, 64-128 linear terms, one
degree-3 LogUp relation, 64 range terms and an lr10 eq kernel.

## Isolated SBF measurements

All runs use Agave 2.3.0 and repeat five times identically.

| measurement | CU result |
| --- | ---: |
| frozen Stage 1 pre-composition projection, k64 | 1,175,086 |
| k80 wide-leaf/RLC delta over the same k64 synthetic probe | +54,720 |
| evaluator-low composition, naive | +312,103 |
| evaluator-low composition, structured/Horner | **+185,462** |
| realistic composition, structured/Horner | +220,594 |
| software Poseidon2, one permutation | 24,100 incremental |
| software Poseidon2, 49-permutation depth-20 schedule | 1,179,744 total |
| software Poseidon2, 73-permutation depth-32 schedule | **fails at 1.4M cap** |

The composition figures subtract a matching RLC-only instruction, so the
gamma RLC already included in the frozen layout allowance is not counted
twice. The k80 layout delta includes the synthetic wide-leaf and RLC growth
and replaces the arithmetic-only k64->k80 delta when totals are formed.

The explicit shrink is real code, not a percentage guess: it shares each
x^5 across Poseidon outputs, uses Poseidon2's addition-only MDS network,
switches constraint batching to Horner form, and evaluates the gamma RLC by
Horner. It saves 126,641 CU from the evaluator-low composition kernel; the
matching k80 RLC-only run falls from 64,752 to 33,931 CU.

Corrected totals:

| case | projected CU | over 1.19M | over 1.4M |
| --- | ---: | ---: | ---: |
| freehand optimistic, naive | 1,439,026 | 249,026 | 39,026 |
| evaluator-confirmed low, naive | 1,541,909 | 351,909 | 141,909 |
| **evaluator-confirmed low, after shrink** | **1,415,268** | **225,268** | **15,268** |
| realistic, after shrink | 1,450,400 | 260,400 | 50,400 |

The isolated probes are not an integrated proof measurement, but the
negative is robust enough for the stated gate: after the required shrink,
even the evaluator-confirmed low case exceeds the absolute transaction cap.
A waiver of the 10% slack rule alone cannot fix that.

## Named rule change: split verification

The continuation changes the headline to verification/finalization **across
three transactions**:

1. Verify the statement reduction and write a receipt binding the statement,
   session/proof hash, C1/C2 roots, terminal point, claimed-evaluation digest,
   main/helper claims, gamma-combined claim, authority and expiry.
2. Verify the wide PCS against exactly that receipt and advance it to
   `PcsVerified`.
3. The pool consumes the receipt once, rechecks authority/session/expiry and
   public binding, rejects an existing nullifier, and applies the output state
   transition.

`aspis-statement::split` implements and adversarially tests this receipt state
machine now: canonical order succeeds; PCS-before-statement, binding
mix-and-match, failed verification, wrong authority, expiry, inconsistent
combined claim and replay-after-consume all reject. It is a seam, not yet the
statement verifier or pool instruction.

The machine-readable decision is
`results/stage2/feasibility_decision.json`. The next engineering gate is to
connect real statement and PCS verification to the receipt transitions and
measure each transaction independently. No one-transaction claim survives
this decision.

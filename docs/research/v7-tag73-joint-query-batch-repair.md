# Tag-73 joint query-batch repair

Date: 2026-08-27

Status: implemented and focused host-tested on
`research/v7-tag73-joint-batch-20260827`; release artifacts and devnet evidence
must be regenerated before deployment.

## Problem

The frozen V6 query batch uses weights
`1, rho, ..., rho^15`. Tag-73 inserted that batch immediately after relation
round zero. In the joint composition, a nonzero error at query ordinal zero
could therefore cancel the scalar error already carried from round zero for
every value of `rho`.

This does not invalidate the standalone V6 degree-15 batching theorem. It
invalidates the stronger Tag-73 step that treated the query injection as
independently exact while simultaneously using the surrounding relation tail
to establish acceptance.

The exact counterexample and repair theorem are kernel checked in
`AspisFormal/AspisFormal/K1/V7Tag73JointQueryBatchSoundness.lean`.

## Repair

Tag-73 now uses weights
`rho, rho^2, ..., rho^16`. V6/Tag-72 retains its frozen start-at-one helper.

The complete post-injection discrepancy is

```text
pre_query_discrepancy - rho * query_batch_residual(rho).
```

Its constant coefficient is the prior relation discrepancy. If the sixteen
expected and authenticated vectors differ, the polynomial is nonzero for
every prior discrepancy and has degree at most 16. At most 16 nonzero field
challenges can therefore hide the joint error.

## Compatibility and cost

- no proof field, offset, length, root, query schedule, frontier, or work-bit
  change;
- V6/Tag-72 behavior is unchanged;
- the same 15 prepared field multiplications generate all 16 weights;
- only the absorbed Tag-73 query claim and the three later relation messages
  change;
- existing Tag-73 proofs, hashes, reproducible binaries, CU evidence, and
  devnet lifecycle records must be regenerated.

## Focused evidence

- six `aspis-core::v6_query_batch` tests passed, including the shifted
  three-fold composition and ordinal-zero guard;
- the V7 compact prover/verifier round trip passed with a 30,400-byte body,
  compact counter 5, and frontier count 201;
- the focused V7 test command used 813,711,360 bytes maximum resident memory
  and no swaps;
- the RAM-intensive Pool proof round trip remains explicitly ignored locally
  and must be replayed on the NUC after the current certificate job releases
  memory.

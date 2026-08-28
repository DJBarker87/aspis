# V7 Tag-73 eight-lane CU lock

Date: 2026-08-28

Status: selected research configuration locked for formal/source integration.
This is not a deployment authorization.

## Outcome

The real combined one-transaction eight-lane Pool path is below 1.3M CU in
all four release shapes without changing the cryptographic relation, query
count, digest width, grinding, terminal transport, or state bindings. The
selected wire uses the measured +320-byte canonical fixed-field representation.

| Operation | History path | CU | TxV1 bytes | CU margin to 1.3M | Byte margin to 4,096 |
| --- | --- | ---: | ---: | ---: | ---: |
| Private transfer | same page | 1,145,926 | 799 | 154,074 | 3,297 |
| Private transfer | rollover | 1,191,499 | 832 | 108,501 | 3,264 |
| Withdrawal | same page | 1,136,171 | 964 | 163,829 | 3,132 |
| Withdrawal | rollover | 1,201,754 | 997 | 98,246 | 3,099 |

The final row is the worst case. It is 1,754 CU above the preferred 1.2M
comfort target but comfortably below the hard 1.3M gate. The search is locked
here rather than adding more release complexity for a marginal cosmetic win.

These are real successful combined LiteSVM executions with the exact
1,400,000-CU runtime limit, strict 35/31/34-bit work checks, selected Pool CPI,
792-byte ASR8 validation, atomic lane/history/nullifier writes, and withdrawal
SPL CPI where applicable. They are not sums of separately measured components.

## Frozen representation

- terminal request: compact ASQ8, 320 bytes;
- semantic statement: authenticated ASF8 reconstruction, 1,880 bytes;
- verifier result: ASR8, 792 bytes;
- maximum proof body: 30,824 bytes, account-backed (+320 bytes versus the
  compact fixed-field encoding);
- honest strict fixtures in this sweep: 30,720--30,824 bytes;
- query count: 16;
- authentication: two typed 208-bit Merkle trees;
- C1/C2 widths: 26/3;
- work: 35/31/34 bits;
- transaction target: true TxV1 below 4,096 bytes.

Decision: **SPEND PROOF BYTES FOR CU**. The +320-byte canonical fixed-field
representation is selected; no transaction-carried hint, additional fatter
proof hint, full-ASF8 request, or expanded ASR8 is selected.

## Exact evaluator refactorings

All selected changes preserve the same polynomial or field expression.

1. Copy pattern basis: reuse the finite 14-pattern support rather than rebuild
   repeated endpoint expressions.
2. Packed range shared selector: factor common selector work across the frozen
   range lanes.
3. Active-mask basis: group the 64 row blocks by their seven actual 16-bit
   active masks.
4. Copy selector tensor basis: evaluate the same endpoint selector products
   in the frozen `(side, slot, local)` and `(side, pattern, local)` bases.
5. Four-slot gamma block order: interchange the slot/block loops while keeping
   the same 104 decoded C1 limbs, powers, and per-slot reduction boundaries.
6. Packed digest selector tensor: use
   `sum_e high[b_e] low[l_e] R_e = sum_l low[l] sum_{e:l_e=l} high[b_e] R_e`
   over the unchanged public-digest residuals.
7. Copy tag dot basis: group the same 272 static tag products by the 30 frozen
   `(side, slot, local)` coordinates, reducing up to four M31 products per
   exact u64 channel.
8. Copy finish dot basis: batch only the selected tag/low and weight/low dot
   products with exact two-, three-, and four-product helpers.

The old isolated semantic-terminal prefactorisation remains intact:
821,667 CU to 407,973 CU, a 413,694-CU component saving. The higher figures in
this report are complete Pool plus verifier transactions, including account
authentication, proof verification, result validation, state mutation,
history/nullifier writes, and withdrawal custody work.

## Rejected final experiments

- Affine tag base plus small-offset reconstruction was algebraically exact but
  used dynamic double/add loops and regressed to 1,340,075 CU.
- Extending finish-dot batching to the 43 pattern-local products regressed the
  worst case from 1,201,754 to 1,203,587 CU. It is not in the locked source.
- Full ASF8, expanded ASR8, and additional proof-byte hints are not selected:
  current evidence gives no reason to add more bytes or formal/source surface
  area after canonical fixed fields plus the zero-byte path cleared the gate.

## Focused equivalence checks

Only the four targeted checks were rerun for the lock:

- `four_slot_block_gamma_equals_slot_major_off_domain`;
- `compiled_copy_lane_matches_host_reference_off_domain`;
- `packed_public_digest_matches_all_transfer_and_withdrawal_bindings`;
- `honest_transfer_and_withdrawal_vanish_on_every_boolean_row`.

All pass. The Copy test compares the complete compiled evaluator against the
independent typed host registry off-domain. The digest test covers every
Boolean binding row and randomized off-domain points for transfer and
withdrawal. The honest relation vanishes on all 1,024 Boolean rows for both
operations.

## Selected build

The selected verifier feature set is:

```text
v7-pair-forest-fixed-canonical-exact-once-audit
v7-pair-forest-lane-invariant-audit
v7-pair-forest-packed-digest-selector-tensor-audit
v7-pair-forest-binary-copy-weights-audit
v7-pair-forest-endpoint-selector-cache-audit
v7-pair-forest-semantic-factor-audit
v7-pair-forest-pattern-window-audit
v7-pair-forest-copy-tag-dot-basis-audit
v7-pair-forest-copy-finish-dot-basis-audit
v7-pair-forest-packed-range-audit
v7-pair-forest-active-mask-basis-audit
v7-gamma-four-slot-block-audit
```

Artifacts:

| Program | Bytes | SHA-256 |
| --- | ---: | --- |
| verifier | 1,968,872 | `ad84706b714dedfe89e5f3ebcf91dff8ab300ab3dfe3eb2d7d846e1bf0c635d4` |
| Pool | 526,656 | `f3ae8d96164189bec2e134b659e4fc5bd39a6b16488cde1bbd23f278a9369c76` |

The verifier build ran on `nuc.local` inside a systemd cgroup with
`MemoryHigh=4G`, `MemoryMax=6G`, `MemorySwapMax=0`, and exited successfully.

## Evidence and replay

The four final ledgers are:

```text
results/v7-pair-forest-combined-rejection-litesvm-20260828/evidence/transfer-same-page-cu-locked-r1-txv1-1400000.json
results/v7-pair-forest-combined-rejection-litesvm-20260828/evidence/transfer-rollover-cu-locked-r1-txv1-1400000.json
results/v7-pair-forest-combined-rejection-litesvm-20260828/evidence/withdrawal-same-page-cu-locked-r1-txv1-1400000.json
results/v7-pair-forest-combined-rejection-litesvm-20260828/evidence/withdrawal-rollover-cu-locked-r1-txv1-1400000.json
```

Replay uses the checked-in release harness:

```text
results/v7-pair-forest-combined-rejection-litesvm-20260828/harness/target/release/aspis-v7-pair-forest-combined-rejection \
  <pool.so> <verifier.so> <output-ledger.json> <strict-fixture.bin> \
  success 1400000 asq8 <13-or-255> <transfer-or-withdrawal>
```

## Remaining release gates

This locks the runtime direction; it does not claim end-to-end mainnet
readiness. The exact selected rewrites still need their Lean/Aeneas and
production-source composition closure. The remaining K1.2--K1.5/circle
instantiations and exact Pool writer/caller theorem must be composed into the
accepted production call. Then the selected binaries need reproducible build
evidence, adversarial lifecycle replay, and a finalized TxV1 4,096-byte devnet
lifecycle before the final mainnet-readiness audit and explicit deployment
approval.

# V7 deposit-invariant promotion and terminal CU attribution — 2026-09-02

## Result

**DEFAULT-OFF DEPOSIT PROMOTION GREEN; TERMINAL UNIVERSAL-CU GATE BLOCKED BY Q16 COUNTER VARIANCE.**

The persisted-lane induction and source inventory justify the deposit-specific
removal of two redundant computations. The feature remains absent from
`default` and is now included only in the default-off
`v7-pair-forest-one-tx-candidate` aggregate. A disposable Agave 4.2.0 rerun
finalized a genuine live transfer at 1,245,883 CU and a genuine live withdrawal
at 1,284,170 CU. Both are below the project 1,300,000-CU gate, but these two
samples do not establish a universal terminal CU ceiling.

The apparent regression is not caused by the deposit promotion and is not a
changed verifier. The old and new live runs execute the identical verifier
binary, SHA-256
`97df12937d46e25a2eeefeac16ce31925fd473c672d6b656548be9220adbcc6d`.
The new proofs reached later transcript-derived compact-query candidates.

## What the deposit path removed—and what it retained

The generic lane decoder previously reconstructed the active Merkle root from
the complete frontier on every deposit. The generic successor encoder then
reconstructed and compared the same successor relation a second time. Under
`pair-forest-deposit-invariant-audit`, only those two redundant computations
are replaced:

1. the source decoder consumes the proved Pool-owned persisted-lane invariant;
2. the deposit append helper performs the existing binary-carry transition;
3. the successor encoder writes the byte-exact authenticated output without a
   second Poseidon reconstruction.

Nothing cryptographic was removed. The note commitment, occupied/empty pair
leaf construction, tree hash, append transition and custody CPI are unchanged.
The path still checks the Pool owner and writable bit; exact lane PDA; account,
tree and digest versions; format binding; master and lane identities; lane
count and tree depth; canonical digest limbs; capacity; every inactive
frontier slot; genesis root; exact retained current-history root; history-page
PDA/header/fill; exact account count and alias freedom; token program, mint,
source, authority and vault bindings; exact balance delta; and rollover-page
freshness.

The source inventory found exactly three persisted lane writers: genesis
initialization, checked deposit successor and authenticated terminal successor.
The main Lean theorem
`persisted_lane_reachable_is_genesis_or_authenticated_output` and the
translated-source theorem
`translated_reachable_is_genesis_or_byte_exact_authenticated_output` close the
induction. Their focused evidence is in
`results/v7-persisted-lane-source-formal-closure-20260901/summary.json`.

## Deposit measurements

The unchanged default-off SBF hash is
`9cd1401327493134ca42ed13a7e72d7e6c375c488f7aa2ede42b39f402b6c89d`.
All 256 sequential deposits finalized on a disposable feature-active cluster;
simulation and landed CU matched, wires were byte-identical, custody deltas
were exact, and nonselected lanes remained unchanged.

| Source index | Page shape | Bytes | Landed CU | Exact generic comparison |
|---:|---|---:|---:|---:|
| 0 | genesis | 651 | 640,272 | -472,127 CU (-42.442235%) |
| 1 | same page | 617 | 594,743 | generic path exhausted 1,400,000 before token CPI |
| 2 | same page | 617 | 594,683 | unavailable |
| 3 | same page | 617 | 594,776 | unavailable |
| 7 | same page | 617 | 594,730 | unavailable |
| 15 | same page | 617 | 594,714 | unavailable |
| 255 | page rollover | 684 | 643,854 | unavailable |

The audit path's same-page range over the complete run was 594,215–594,776 CU.
The maximum was the rollover at 643,854 CU. This is a real deposit-path saving,
not a terminal verifier saving.

## Why the terminal CU moved

Tag-73 uses the first of 64 transcript-derived q16 schedules whose binary
Merkle frontier has at most 203 nodes. The counter is not proof-carried, so the
verifier must derive candidates from zero upward and establish that every
earlier schedule fails the cap. Proof/transcript entropy therefore changes
runtime CU even with byte-identical verifier code.

| Case | Old counter/frontier | New counter/frontier | Old verifier CU | New verifier CU | Delta |
|---|---:|---:|---:|---:|---:|
| Transfer, same page | 10 / 201 | 25 / 197 | 1,132,448 | 1,190,388 | +57,940 |
| Withdrawal, same page | 14 / 198 | 26 / 201 | 1,146,905 | 1,196,055 | +49,150 |

Solving those two observed deltas gives approximately 3,983.01 CU per rejected
candidate and 451.29 CU per frontier node. Integer coefficients 3,983 and 451
predict the transfer delta as 57,941 and the withdrawal delta as 49,149—one CU
from each observation. Across additional genuine proofs using the same
verifier binary, the observed counter-0 to counter-32 verifier range was
1,088,745–1,220,632 CU. Those heterogeneous samples are attribution evidence,
not a universal linear bound.

The read-only `inspect-live-proof` utility makes the diagnosis reproducible.
It decodes the exact ASF8, derives the two-frontier length, invokes the same
host verifier path with all work checks enabled and prints the accepted counter
and frontier. Future live prover metadata also records both fields directly.

## Correction to the frozen reference

The 1,201,757-CU / 997-byte measurement remains valid, but its scope must be
stated precisely: it was a **counter-zero withdrawal-rollover proof** on
LiteSVM, with frontier 202 and an older verifier binary. It was the worst Pool
state shape measured conditional on counter zero. It was never a maximum over
the full reachable 0–63 compact-counter schedule.

The associated activation report already recorded that the proof was selected
for counter zero and that release required the correlated-grinding/final-nonce
argument. That K1.3–K1.5 closure is proceeding independently and was not
modified here. Until it closes, final-nonce search cannot honestly be used as a
production CU-selection rule. Conversely, weakening the first-schedule check
would change the protocol/security argument and is out of scope.

The current live withdrawal has only 15,830 CU of headroom below the project
gate. Therefore the statement “every honest V7 terminal transaction is below
1,300,000 CU” is not established. A higher counter could also threaten the
Solana 1,400,000-CU transaction limit. This is a liveness/release blocker, not
an observed fund-safety failure: measured rejected transactions retained full
atomic rollback.

## Promoted-candidate live evidence

| Case | Result | Bytes | Simulated / landed CU | Slot |
|---|---|---:|---:|---:|
| Transfer, same page | finalized pass | 1,378 | 1,245,883 / 1,245,883 | 592 |
| Withdrawal, same page | finalized pass | 1,543 | 1,284,170 / 1,284,170 | 761 |
| Fresh-signature transfer replay | finalized reject | 1,378 | 27,322 / 27,322 | 624 |
| Fresh-signature withdrawal replay | finalized reject | 1,543 | 40,669 / 40,669 | 793 |
| Stale selected lane | finalized reject | 1,378 | 78,825 / 78,825 | 582 |

The transfer and withdrawal each contained exactly one terminal instruction,
were simulated and submitted byte-identically, and finalized. Withdrawal moved
250 tokens from a 1,000-token vault to a zero-balance bound destination. Both
replays and the stale-lane case preserved protected state except for the
required payer fee.

## Classification and deployment boundary

- Public testnet TxV1: active in epoch 1025; V7 not executed there.
- Public devnet TxV1: inactive; prior evidence unchanged.
- Public mainnet TxV1: inactive.
- Production identities: unavailable and not selected.
- `mainnetReady`: **false**.

No production deployment is warranted from this milestone. The deposit
promotion is safe to review as a default-off candidate change, but the terminal
release gate needs either the independent final-nonce/q16 security closure or a
protocol-preserving universal CU bound, followed by new production-identity
and public-cluster evidence.

Machine-readable evidence is in
`results/v7-deposit-invariant-promotion-20260902/summary.json` and
`results/v7-deposit-invariant-promotion-20260902/cu-regression-attribution.json`.

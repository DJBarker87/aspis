# V7 verifier receipt lifecycle — focused LiteSVM evidence

Status: harness preparation in progress. The SBF artifact identity and final
runtime output will be filled only after the single clean, focused
`v7-pool-dispatch-profile` build is available.

This directory is scoped to the verifier-owned ASRA lifecycle introduced by
commit `de997860` and replayed from clean source commit
`b484a8772680e90681cb099b57929b9700c1d4a1`.

The harness reuses, without regenerating, the frozen honest Tag-73 fixture in
`results/spend/v7-devnet-20260825-fullc2/`. It installs each complete unsealed
ASPU account as an isolated LiteSVM genesis fixture and exercises:

- tag 74 over a pre-funded canonical PDA, including a wrong-authority
  anti-squat rejection and the exact rent-deficit path;
- tag 74 fresh creation plus a second tag-74 failure after a successful System
  CPI in the same transaction, proving complete rollback;
- early tag-75 rejection while the proof remains unsealed;
- tag 62 proof finalization followed by tag 75 and the full frozen honest
  Tag-73 verifier;
- mutated ASVQ, wrong PDA, duplicate finalization, and wrong close signer with
  exact account snapshots on every rejection;
- tag 76 for both pending and verified receipts with exact embedded-authority
  rent refunds.

Every transaction carries a 1,400,000-CU limit. The JSON records transaction
CU and each top-level verifier instruction's exact `Program ... consumed ...`
log, fees, rent movements, return data, System CPI observations, and before /
after owner-lamport-data snapshots.

Boundaries:

- This is an isolated LiteSVM run, not a deploy, RPC send, wallet operation, or
  cluster simulation.
- ASPU chunk transport tags 0/1 are not replayed; their completed account image
  is the pinned genesis fixture. Tag 62 sealing is replayed.
- The selected Tag-73 profile remains the committed
  `AtomicPaymentStatementV4` private-transfer relation. This is not a claim for
  the newer full Pool payment relation.

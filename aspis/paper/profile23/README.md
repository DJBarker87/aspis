# Profile 23 manuscript skeleton

This directory is the future source root for the Profile 23 paper. It contains
no publication claim yet. The authoritative writing and release rules are in
`docs/profile23-paper-plan.md`.

## Working title

**Aspis: Transparent, Computationally Hiding Shielded-Spend Verification and
State Update from a Pre-Uploaded Proof in One Solana Transaction**

“One transaction” means verification plus atomic nullifier/pool mutation from
a finalized, pre-uploaded proof account. Account creation, uploads, and
finalization happen beforehand. Do not add “mainnet-beta” or “first” to the
title unless their separate release gates are green.

## Abstract skeleton

1. Solana's 1.4M-CU execution limit makes direct transparent verification of a
   complete shielded-spend statement difficult.
2. We describe Profile 23, a rate-1/512, q16 WHIR-style multilinear-PCS
   construction whose accepting instruction consumes a finalized,
   pre-uploaded proof account and atomically records the nullifier and pool
   transition.
3. In the random-oracle model under the stated hash and code-transport
   assumptions, the frozen profile's proven-Johnson/MCA-based soundness ledger
   is 101.302 bits and remains 100.807 bits under a coarse whole-ledger
   sensitivity; an explicit witness-free simulator gives 104.112 bits for a
   real view versus simulation and 103.112 bits for two-witness pairwise
   computational hiding in the declared SHA-256 programmable-random-oracle,
   fixed Proof-or-Abort channel model.
4. The frozen local Agave artifact is a 61,599-byte proof, a 6,870,048-byte
   default SBF with SHA-256
   `6b64baf559dcddbd6f9b1af1205effeb6afae6a5746a44421e8826251fe4cffb`,
   and a 1,207,123-CU canonical System-create path with 192,877 CU of headroom;
   these measurements are from the pinned local Agave environment and are not
   a mainnet deployment claim.

The abstract must also carry the pre-upload qualifier. The body must state that
the hiding claim is neither statistical HVZK nor a local-side-channel result.

## Section skeleton

1. Introduction
2. Background and related work
3. Shielded-spend statement, account model, and adversary
4. Profile 23 protocol and transcript
5. Proven-Johnson/MCA soundness
6. Good23 and complete-view computational hiding
7. Solana SBF implementation and atomic transition
8. Evaluation and reproducibility
9. Limitations and open work
10. Conclusion
11. Appendices: wire, proofs, ledgers, certificates, vectors, artifact guide

## Planned source tree

```text
paper/profile23/
  manuscript.tex
  macros-generated.tex       # generated only from frozen JSON artifacts
  references.bib
  claim-evidence-matrix.md
  sections/
  figures/
  tables-generated/
  artifact/README.md
```

No numeric fact should be typed directly into `manuscript.tex` if it exists in
an artifact. A generator must fail on the forbidden inherited soundness value,
a missing pairwise hiding field, a non-finalized proof account, a red release
gate, or a missing mainnet signature when mainnet language is enabled.

## Theorem labels to reserve

- `def:profile23-statement`
- `def:profile23-relation`
- `def:profile23-transparent-parameters`
- `def:profile23-security-games`
- `def:profile23-complete-view`
- `def:profile23-schedule`
- `lem:circle-grs-transport`
- `lem:johnson-mca-batch`
- `lem:fold-list-ood`
- `lem:local-algebraic-binding`
- `lem:selector-soundness`
- `thm:interactive-soundness`
- `thm:bcs-soundness`
- `lem:good23-product`
- `lem:complete-affine-image`
- `lem:uniform-mask-preimages`
- `alg:sim23`
- `lem:selection-hiding-abort`
- `lem:epro-complete-view`
- `thm:real-vs-sim23`
- `cor:pairwise-hiding`
- `lem:finalized-account-state-machine`
- `prop:atomic-refinement`
- `thm:profile23-system`

## Hard editorial guards

- Headline soundness: selected `101.30230658283051`; coarse sensitivity
  `100.80652861422749`. Never print inherited `100.87976635696354`.
- Headline hiding: pairwise `103.11238518950232`; real-versus-simulator
  `104.11238518950232` is separately labeled.
- `epsilon_side=0` means excluded observables are absent from the declared
  channel, not that physical side channels were proved secure.
- State that the rank certificate originates from a Profile 22 fixture and
  transfers through layout/Good23 fingerprint checks plus all-selector live
  schedule audits.
- Name the diagnostic/production tag-59 measurement-context difference; do
  not guess its cause.
- The final frozen diagnostic/production tag-59 context is 1,202,920 versus
  1,202,939 CU, a 19-CU difference. The earlier 8-CU comparison is superseded
  history, not a current measurement.
- Explain schedule-dependent proof length as part of the simulated view.
- Bind the frozen local object to configured program address
  `7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue`, sealed proof accounts,
  append-only `FinalizeProof` tag 62, and `InitializeAtomicPool` tag 63.
- State that the configured address is not deployment evidence. Any future
  deployment claim must additionally bind Program/ProgramData, deployed code
  bytes, loader owner, remaining capacity, finalized slot, and upgrade
  authority state.
- Never use a naive sum of isolated CU probes.
- Never claim mainnet, historical priority, audit, or production readiness
  without its corresponding evidence gate.

## Security-definition guards

- `R23` is exactly the atomic-v3, depth-20, one-input/one-output,
  same-private-path replacement relation. It is not a generalized pool,
  multi-input transaction, public append, or wallet protocol.
- The soundness theorem is argument soundness unless the manuscript supplies
  an extractor. Its ROM game quantifies the adversary, chosen statement and
  pre-state, `Q_H`, 32 BCS boundaries, q3 selector, and accepted false
  relation event.
- Pairwise hiding quantifies a fixed `x`, valid `w0,w1 in R23(x)`, auxiliary
  input, adaptive post-output oracle queries, `Q_H <= 2^128`, `A <= 16`, exact
  variable-length declared view, and `Abort`.
- Selector correctness/soundness and selector-distribution hiding are separate
  lemmas. The former fixes commitments before q3 and justifies the factor-three
  q16 term; the latter proves the first-Good/Abort law witness-independent.
- Good23 must prove image equality and constant-cardinality mask preimages. A
  checker independent of the certificate generator reconstructs public maps
  and verifies dimensions, ranks, kernels, pivots, and minors.
- The EPRO proof is an explicit adjacent-hybrid chain covering affine field
  replacement, salted leaves, private Merkle, prequeries, programmed-state
  collisions, post-output queries, q3 selection, canonical work, serialization,
  finalization, logs, and deterministic mutation.

## Artifact and evaluation guards

The artifact README defines six tiers: cached hash/cross-link audit, fast
semantic teeth, clean byte-identical SBF rebuild, local Agave replay, slow
theorem/certificate jobs, and fresh proving/mining. It must give expected
time, CPU, memory, disk, network, nondeterminism, raw logs, and outputs for
each tier.

Evaluation covers the excluded setup lifecycle even though it is not part of
the headline transaction: account creation, upload chunks, finalization,
CU/fees/rent/storage, prover and miner wall time/memory, q3 attempts, and
time-to-spend. It also covers same/different-nullifier races, same-pool
contention, independent pools, account locks, throughput, stale-anchor and
finalization failures, front-running/replay/griefing, and DoS surfaces.

For double-blind review, prepare a scrubbed content-addressed artifact without
the program address, repository history, author URLs, DOI, ePrint, grant
metadata, acknowledgments, or deployment transaction. Keep the private mapping
to the canonical release and reveal it only when venue policy permits.

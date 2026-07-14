# Profile 23 manuscript

This directory contains the standalone Profile 23 LaTeX manuscript, its
bibliography, claim-to-evidence matrix, and artifact notes. Build the paper
from `profile23.tex`.

**Current profile status (`2026-07-14`):** the active q18/cap17 release is
green at 35/35 gates and the exact released proof/program pair has completed a
finalized devnet rehearsal. The final tag-60 transaction landed at slot
`476231605` with 1,314,332 CU. The `2026-07-13` q16/cap16 certificate is
superseded historical evidence and is not the current Profile-23 release.

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
2. We describe Profile 23, a rate-1/512, q18 WHIR-style multilinear-PCS
   construction whose accepting instruction consumes a finalized,
   pre-uploaded proof account and atomically records the nullifier and pool
   transition.
3. In the random-oracle model under the stated hash and code-transport
   assumptions, the q18 proof-independent proven-Johnson/MCA-based
   conservative release floor is 100.161 bits; an explicit witness-free
   simulator gives 104.025 bits for a
   real view versus simulation and 103.025 bits for two-witness pairwise
   computational hiding in the declared SHA-256 programmable-random-oracle,
   fixed Proof-or-Abort channel model.
4. The 35/35 local release binds a 66,367-byte mined q18 proof, a 915,656-byte
   manifest-default SBF, and a worst literal tag-60 System-create path of
   1,314,386 CU, leaving 85,614 CU below the 1.4M cap. The same identities
   completed a finalized devnet tag-60 transaction at 1,314,332 CU; neither
   result is mainnet evidence. The 61,599-byte
   proof, 6,870,048-byte SBF, and 1,207,123-CU System-create path belong to
   the superseded q16 certificate and do not transfer to q18.

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
  profile23.tex
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

- Current q18 headline soundness: conservative authorizing floor
  `100.16144938287455`. Never substitute the superseded q16
  values `101.30230658283051` and `100.80652861422749`, or the inherited
  `100.87976635696354`, into a current claim.
- Current q18 headline hiding: pairwise `103.02492234825198`;
  real-versus-simulator `104.02492234825198` is separately labeled.
- `epsilon_side=0` means excluded observables are absent from the declared
  channel, not that physical side channels were proved secure.
- State that the active minimum-q-degree rank certificate is pinned to the q18
  fixture and transfers through layout/Good23 fingerprint checks plus exact
  all-selector schedule audits; it is not a q16 proof-byte transfer.
- Name the diagnostic/production tag-59 measurement-context difference; do
  not guess its cause.
- The q16 diagnostic/production tag-59 context was 1,202,920 versus 1,202,939
  CU, a 19-CU difference. Both that comparison and the earlier 8-CU comparison
  are superseded history, not current q18 measurements.
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
  relation event. The active work-normalized BCS statement checks both
  `T=1` and `T=2^128`; at `T=1` the multiplier on the round error is 33.
- Pairwise hiding quantifies a fixed `x`, valid `w0,w1 in R23(x)`, auxiliary
  input, adaptive post-output oracle queries, `Q_H <= 2^128`, `A <= 17`, exact
  variable-length declared view, and `Abort`.
- Selector correctness/soundness and selector-distribution hiding are separate
  lemmas. The former fixes commitments before q3 and justifies the factor-three
  q18 term; the latter proves the first-Good/Abort law witness-independent.
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

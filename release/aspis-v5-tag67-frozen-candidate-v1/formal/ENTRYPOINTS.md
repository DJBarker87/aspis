# V5 formal entry points

The maintained and source-authentic proof developments remain in the
repository rather than being partially copied into this compact bundle. The
release tag pins their complete dependency graph at source commit
`06788d44d30ea8cbd391899dddaf6f0acc6e4a3f`. All paths below are relative to
that checkout.

## Combined capstone

- Theorem:
  `FormalClosureStream1.current_source_combined_capstone`
- Source:
  `aeneas-verif/current-source-abc-capstone-20260722/proof/CurrentSourceABCapstone.lean`
- Source SHA-256:
  `0b5fe370eba730c48306bf4a25a2c228d8315570b9cabb930b2878604bf3d950`
- Replay:
  `aeneas-verif/current-source-abc-capstone-20260722/replay-lean432.sh`
- Replay SHA-256:
  `b65561ceae9fd42ab6a75200bf3f7eb868d8ea00c68703116719bc29dab40c2e`

This theorem joins source-authentic Component A at the frozen concrete
schedule, Component B, actual-current Component C including the packed public
output, and Tag-67 wire/verifier closure.

## Component C public output

- Theorem:
  `generated_public_run_output_matches_deployed`
- Source:
  `aeneas-verif/component-c-runtime-downstream/released-trace-families-current-20260722/proof/RuntimeReleasedTraceFamiliesCurrentJoin.lean`
- Source SHA-256:
  `75b0f3e7ebc3adeb3050be69376d6c07d13aafcef3f9073b5485d6215d457d3a`
- Replay:
  `aeneas-verif/component-c-runtime-downstream/released-trace-families-current-20260722/replay-lean432.sh`
- Replay SHA-256:
  `22f829f471db3a330ad66afcbeb37d8b4939d6eb96bacae9f4884938f6b7dcfc`

## Tag-67 wire and work verifier

- Theorem:
  `AspisTag67WorkVerifierClosure.tag67AcceptedWireAndVerifierClosure`
- Source:
  `aeneas-verif/tag67-work-wire-correspondence/proof/Tag67WorkVerifierClosure.lean`
- Source SHA-256:
  `ca7710a24cba91915feb730d0f045fff039fc95cf9c66262144e1211badc81ca`
- Axiom audit:
  `aeneas-verif/tag67-work-wire-correspondence/proof/Tag67WorkVerifierClosureAxiomAudit.lean`
- Axiom-audit SHA-256:
  `d3d65ea3beb019b2014e0aad301d74f4c0f282b1cf31cb46e4379a0453f2fb1b`

The only Tag-67 implementation/model premise retained by the capstone is:

```text
∀ state nonce,
  actualTranscriptGrindingDigest state nonce =
    rustHash state ((3 : Byte) :: List.ofFn (nonceLEBytes nonce))
```

The audited capstones use only
`{propext, Classical.choice, Quot.sound}`.

## Runtime GoodA gate

The production verifier derives the selected public schedule and accepts only
when the actual 12×12 M31 GoodA and 4×4 QM31 GoodB checks pass. The
source-authentic Component-A theorem above is specialized to the frozen
schedule; the universal all-schedule executable correspondence remains a
separate proof project.

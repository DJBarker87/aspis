# Component-B unified source-authentic correspondence

> Release status (2026-07-23): this dated bundle is now imported by
> `FormalClosureStream1.current_source_combined_capstone`. The integration work
> described at the end of this extraction report has been completed; the
> snapshot identities and local theorem scope below remain the provenance
> record.

## Result

The Component-B executable chain is closed on Lean 4.32 against one combined
Charon/Aeneas universe.  The retained LLBC contains the actual generic sampler,
`sample_zero_boundary_round`, the actual call-through helper, public round
construction and ten-round evaluation, the real degree-27 evaluator, boundary
sum, and current field operations.

The strongest theorem is
`ComponentBSamplerUnifiedCapstone.sampled_helper_mixing_and_terminal_covector`
in `proof/sampler/ComponentBSamplerUnifiedCapstone.lean`.  Given an actual
successful generated sampler run and canonical public mixing/evaluation
inputs, it proves existence of the actual generated helper result
`(.some mixed, terminal)`, proves the generated boundary of `mixed` is exactly
`totalClaim`, proves `terminal` canonical, and identifies its exact-field value
with maintained `AspisV5SumcheckCommitment.terminalCovector`.  The sampled mask
is the same generated value passed to the helper; there is no nominal-copy,
field-adapter, platform-width, evaluator-faithfulness, or generic transport
premise.

Sampler transition totality and canonicality of externally supplied point,
total claim, eta, and real polynomial remain explicit.  Transcript binding,
Fiat--Shamir, PCS authentication, sampler uniformity, deployed ZK, and freeze
are outside this local algebra theorem and are not claimed.

## Source and tools

- workspace HEAD: `27e8265d28de88e7967626a2d2432ef161fb4f49`
- exact source statuses:
  ` M crates/aspis-prover/src/v5_sumcheck_mask.rs`,
  ` M crates/aspis-prover/src/v5_mask.rs`;
  `state_only_sumcheck.rs` and `field.rs` are clean
- `v5_sumcheck_mask.rs` SHA-256:
  `26ed8e873da039503976fe08dcd26894b847c75007497d290fa74c4c9296319a`
- source diff SHA-256:
  `5e54d5bf9ad5095e94eebe277fe868a66384063b7af9e42700da5039af8f6c1f`
- `v5_mask.rs` SHA-256:
  `a1516a5ab348d1e374d908844545054f1fd5647ea12ff56cff273cb1b2b7d05c`
- `v5_mask.rs` diff SHA-256:
  `4170850921b8d54eca1456313de5553a07a75caf20e3e21cd6cea2070eee1de6`
- `state_only_sumcheck.rs` SHA-256:
  `5458d3134a3123b8b02bef0374ccbf96a05461974d7e274966c6a3f0d2d496f9`
- `state_only_sumcheck.rs` diff SHA-256:
  `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`
- `field.rs` SHA-256:
  `dadd6bac7c6c44fcb13e1a1ca26e9d2b6f767370bb6e802640948f15fc795836`
- `field.rs` diff SHA-256:
  `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`
- Charon: `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`
- Aeneas: `b59d5188c082f704a418c7cb4e52ad69328002d1`
- extraction Rust: `nightly-2026-06-01`
- replay: Lean `4.32.0`, using the pinned Aeneas compatibility backend

This lane made no Rust edit during the completion.  The final extraction was
refreshed after an externally owned cleanup removed the unused
`zero_boundary_coefficient` accessor; the retained helper, sampler, evaluator,
mixing, boundary, and field semantics are unchanged.  `field.rs` and
`state_only_sumcheck.rs` were not edited by this lane.

## Extraction identity

Successful `--start-from` matchers, in retained order:

1. `aspis_prover::v5_sumcheck_mask::v5_sumcheck_mask_mixing_evaluate_correspondence`
2. `aspis_prover::v5_sumcheck_mask::_::sample`
3. `aspis_prover::v5_sumcheck_mask::sample_zero_boundary_round`

Explicit includes are the current `aspis_core::field` graph, the real
`evaluate_state_only_polynomial`, the real `state_only_boundary_sum`, and the
three state-only constants.  The LLBC has `has_errors=false`, 129 ordered
declarations, and 68 file records.  Its SHA-256 is
`e2f683b62a7827e6b30c66cbb5038ee069db4979fe56508997e307e64d678bf4`.

Generated source spans include:

- sampler helper: `v5_sumcheck_mask.rs:211:0-223:1`;
- sampler: `v5_sumcheck_mask.rs:88:4-101:5`;
- zero-boundary sampler: `v5_sumcheck_mask.rs:65:0-80:1`;
- round construction: `v5_sumcheck_mask.rs:153:4-165:5`;
- ten-round evaluator: `v5_sumcheck_mask.rs:168:4-181:5`;
- mixing: `v5_sumcheck_mask.rs:187:4-207:5`;
- boundary entry: `state_only_sumcheck.rs:110:0-110:80`, with indexed loop
  `124:4-129:5`;
- real degree-27 evaluator entry: `state_only_sumcheck.rs:160:0-163:9`,
  block closure `169:22-169:36`, and indexed loop `182:4-185:5`.

Raw generated root SHA-256 is
`1cc6555cd62e88ba3a408830ee6116653a2f73ec6bb1b76f69fa362890956f21`.
Raw generated `Types` and `Funs` hashes are respectively
`1e0e6981c60e9c1cf53bb2bb50a29927448d13f7fb71c1c57342cd49c56f10bc`
and
`a01017f0060aa93aba3c1ecb9dc56c90b01d51bb02b6ddc87c098ffbd115c30c`.
Normalized Lean-4.32 `Types` and `Funs` hashes are respectively
`656fa422534d8579536ca51c2efa11334604336dfd4eb8b2d531cc79acd8ad87`
and
`504211a6c77a3df5116a5b256a6cce38c4e4ee48e5eaa5816851c5877d206414`.
The retained raw-to-normalized compatibility diff SHA-256 is
`36dbbd59c200b31cfa80c5b12047bcc899ec99d6f3097892b9fccca579dedcbc`.
Replay recomputes and byte-compares it.  Its complete delta is: use the
Lean-4.32 `Aeneas.Std`/Rust-attribute imports, remove generated-only heartbeat
and recursion directives, type two shift counts as `u32` rather than `i32`,
and elaborate two `Option` matches/results without changing their types or
branches.

## Proof inventory

The chain proves, against generated definitions:

- successful sampling supplies a canonical initial claim and ten canonical
  exact zero-boundary rounds;
- generated and maintained zero-boundary equations imply one another;
- generated half, boundary sum, degree-27 evaluator, round update, public
  ten-round recurrence, exact field tower, and terminal covector agree;
- generated mixing is coefficientwise and has endpoint `totalClaim`;
- the actual combined helper returns both the mixed round and terminal result;
- sampler success specializes that helper theorem without a copy/transport
  seam;
- evaluator logic is portable across the generated 32/64-bit platform split,
  so no `System.Platform.numBits = 64` premise remains.

Negative teeth are universal/concrete theorems for adjacent commitment block
swap, reversing all 28 round coefficients, changing a nonzero zero-boundary
constant, and changing the canonical exact adapter.  They are in
`proof/ComponentBUnifiedTeeth.lean`.

## Verification

The durable clean replay starts from an empty output directory and compiles
three generated modules plus all 47 proof/audit modules: 50 oleans total.
There are 200 exported theorem declarations and 200 exact `#print axioms`
audits.  Every reported closure is contained in
`{propext, Classical.choice, Quot.sound}`; no `sorryAx` occurs.  Handwritten
proofs and normalized generated code contain none of the forbidden constructs
or raised proof limits.  The retained clean replay log SHA-256 is
`36d3c32bc47c26328c9a21801ca04b1b18fc9143f59d50f1a5c6b460c7612630`.

Rust verification:

- targeted real-helper differential test: 1 passed;
- complete `aspis-prover --features v5-mask --lib`: 118 passed, 0 failed,
  10 ignored;
- `git diff --check`: clean.

The retained full Rust test log SHA-256 is
`1c238571ae0bdaa11599e172c7c2269f2c8470925327869cfaf8f6b0c7a8e8ae`.
The targeted Rust test log SHA-256 is
`bc267fa65916de75c5a335f05ba79703f1471ca174dc13a1d96c16183f7287fb`;
the `git diff --check` log SHA-256 is
`75ebccfc18cc5b1a8b32589edccfa2e9f53d9f4dcde857010b3235519655e37f`.
The replay-script SHA-256 is
`3d80714dc7af277a4b2d9bb07652f1affc41dc85f0bf45446290e9e6cf246f1f`.
The 70-entry authoritative nested manifest SHA-256 is
`0f420aebd37f7e64af89d75f88f4932190338e1b0138d3bc989421855424f4bb`.

Central import placement and repository-level composition are complete:
`FormalClosureStream1.current_source_combined_capstone` imports the
Component-B result alongside the frozen-schedule Component-A bridge,
Component-C public output, and Tag-67 verifier closure. No local executable or
arithmetic seam remains in this Component-B chain.

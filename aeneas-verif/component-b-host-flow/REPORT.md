# Component-B authentic sampler -> real-host flow -> terminal correspondence

## Verdict

The deterministic executable chain is closed, source-authentically, on Lean
4.32:

```text
authentic V5SumcheckMask::sample success
  -> explicit caller installation of that sample
  -> one immutable real-host handle
  -> the same mask for commitment / initial claim / sumcheck / terminal
  -> authentic extracted evaluate
  -> maintained terminalCovector
```

The strongest theorem is
`ComponentBSamplerHostFlowTerminalCapstone.authentic_sample_flows_through_host_and_evaluates_to_terminal`.
It composes the source-authentic sampler/evaluator capstone
`ComponentBSamplerTerminalCapstone.sample_success_evaluates_to_terminal`
with the source-authentic host-flow theorem
`AspisComponentBHostFlow.Extracted.V5RealHostInputsSumcheckMaskProvenanceAndFlow`.

This is deliberately **not** an entropy or uniformity theorem.  The host
receives its mask from its caller.  `nextWordTotal` says only that the supplied
word source returns a next word; it says nothing about its law, independence,
domain separation, unpredictability, or CSPRNG quality.  Existing integration
fixtures use deterministic `XorShift`, and no security conclusion is drawn
from those fixtures.  This remains a feature-gated v5 candidate result, not a
deployed-v4, production-ZK, freeze, or release claim.

## Strong theorem and exact premises

For an arbitrary source type and authentic generated `Qm31WordSource`, the
capstone takes:

1. `nextWordTotal`: every source state returns one word and successor state;
2. the exact successful generated sampler equation
   `V5SumcheckMask.sample sourceInst source = ok (Ok mask, finalSource)`;
3. `System.Platform.numBits = 64`, the target recorded by the extraction;
4. canonicality of the ten public evaluation-point QM31 coordinates; and
5. `callerMask = samplerMaskToHost mask`, the explicit caller installation
   edge between the independently extracted sampler and host representations.

Its conclusion executes `Host.bind callerMask`, and proves that each of the
four authentic accessors returns that same `callerMask`.  The caller equality
is therefore load-bearing in the actual host calls, not a decorative premise.
It then executes the authentic evaluator on the coordinatewise-maintained
sample and proves that the exact result is the maintained
`AspisV5SumcheckCommitment.terminalCovector`.

The representation theorem
`hostMaskToMaintained_samplerMaskToHost` is a full structure equality: initial
claim, all ten rounds, all 28 coefficients per round, and every QM31 limb agree.
No coefficient, round, or limb is dropped or reordered.

`authentic_sample_caller_installation_nonvacuous` separately witnesses the
caller premise for every authentic sampled mask.

## Real-host source refactor

Owning source:
`crates/aspis-prover/src/v5_real_host_proof.rs`, SHA-256
`691dedfdcfbe4e8570d2501a2c16813f5c7840cc4f64d68046403069c75b7dbc`.

The semantics-identical refactor introduced one private immutable field:

```rust
struct V5RealHostBoundSumcheckMask<'a> {
    mask: &'a V5SumcheckMask,
}
```

Its constructor and four accessors perform no arithmetic, allocation, clone,
mutation, or substitution.  Both real-host input adapters bind the caller's
mask once; the builder uses the four role accessors for:

- `V5StructuredBLane::encode` (commitment input),
- `initial_claim()` before `eta`,
- `prove_v5_masked_state_only_zerocheck`, and
- `evaluate(challenges)` for the terminal identity.

The Rust regression test `bound_sumcheck_mask_roles_are_pointer_identical`
proves pointer identity for the four roles and distinguishes a second concrete
mask.  It passed 1/1.

## Source-authentic extraction

Pinned tools:

- Charon `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`
- Aeneas `b59d5188c082f704a418c7cb4e52ad69328002d1`
- Rust nightly `2026-06-01` / rustc `1.98.0-nightly`
- replay kernel: Lean `4.32.0`

Host-flow LLBC:

- path: `llbc/bound_mask_flow.llbc`
- SHA-256:
  `5a64e3b6f19895ca05168327e5c4646cc632e0dc4e3a49a464507c411e9bb426`
- `has_errors = false`
- ten ordered declarations
- embedded `v5_real_host_proof.rs` is byte-for-byte the current source

Sampler LLBC (owned by the Component-B mask bundle):

- path:
  `../component-b-mask/llbc/component_b_v5_sampler_authenticated_constants_20260721.llbc`
- SHA-256:
  `b5eb3e06ef32cc2734acda7927f43413fa4aa18f4c84281228a76765c2e96b14`
- `has_errors = false`
- 88 ordered declarations
- embedded `v5_sumcheck_mask.rs` is byte-for-byte the current source

The host raw Aeneas module is replay-retargeted only at its outer namespace to
avoid colliding with the sampler's independently extracted `aspis_prover`
namespace.  Generated heartbeat/recursion declarations are removed; all
handwritten proofs compile at Lean's default limits.

## Kernel and hostile audit

The unified replay first rebuilds the existing current-source evaluator and
maintained-terminal base (49 source theorem/audit pairs; 74 emitted axiom
records), then rebuilds the authenticated half arithmetic, sampler, host flow,
and final composition (50 theorem/audit pairs; 50 emitted axiom records).  The
complete run therefore checks 124 emitted axiom records, including all five
exports from the final composition file.

Every accepted closure is contained in:

```text
{propext, Classical.choice, Quot.sound}
```

The host-flow correspondence and final composition are warning-free.  Reused
authenticated arithmetic and sampler proofs still emit linter-only warnings;
the replay reports those honestly, while rejecting any host-flow/final warning
and every `sorryAx` occurrence.  Accepted sources contain no `sorry`, `admit`,
`native_decide`, handwritten `axiom`, `unsafe`, `ofReduceBool`, or raised
handwritten limit.  The sampler constant
`STATE_ONLY_SUMCHECK_COEFFICIENTS = 28` is proved from the authentic
`Usize.add_spec`; it is not discharged with `decide` or a recovery term.

Negative teeth include:

- a concrete host terminal substitution differing in an M31 limb;
- the sampler's wrong-pivot, coefficient, boundary, and half-operation teeth;
- the maintained evaluator/terminal operational teeth from the base replay.

## Reproduction

Lean 4.32 unified replay:

```sh
AENEAS432_BACKEND=/private/tmp/aspis-aeneas-lean432-check.p116iK/aeneas/backends/lean \
  aeneas-verif/component-b-host-flow/replay-lean432.sh
```

Rust checks:

```sh
cargo fmt --all -- --check
CARGO_TARGET_DIR=/private/tmp/component-b-host-flow-rust \
  rustup run nightly-2026-06-01 cargo test --release --locked \
    -p aspis-prover --lib --features v5-mask \
    bound_sumcheck_mask_roles_are_pointer_identical -- --nocapture
cargo check --release --locked -p aspis-prover --features v5-mask
```

## Compact durable replay set

`CURATED_FILES.txt` is the checkout-ready inventory for this result.  It keeps
the three authentic, error-free LLBC files, the generated definitions and
normalization witnesses actually consumed by the replay, every handwritten
proof, the arithmetic dependencies, manifests, reports, and replay scripts.
It excludes build caches, `.olean` files, logs, failed or historical LLBC
files, unused raw duplicates, and debug modules.

The Component-B mask manifest was correspondingly narrowed to files consumed
by the current replay.  This is a packaging change only: the replay still
rebuilds all 124 axiom records from source, and the removed entries were not
inputs to any accepted proof.  A full unified replay after the narrowing is
the release gate for this compact set.

## Remaining security boundary

Closed here: deterministic sampler success, exact caller installation,
immutable four-role object provenance, authentic evaluation, and equality to
the maintained terminal covector.

Still external and not claimed:

- word-source entropy, uniformity, independence, and domain separation;
- production CSPRNG and retry/liveness ownership;
- PCS/Merkle binding, SHA/RO, and Fiat--Shamir/BCS assumptions;
- production tag-67 dispatch, a universal CU bound, freeze, or release.

The correct headline is therefore: **source-authentic deterministic
Component-B sample-to-terminal correspondence is kernel-checked; mask-source
security and production deployment remain separate named interfaces.**

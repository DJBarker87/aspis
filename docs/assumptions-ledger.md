# What Aspis assumes

Aspis connects Lean-checked mathematics, proofs about selected production Rust,
a reproducible compiled Solana program, and direct runtime evidence. Each layer
is explicit about what it establishes and what it relies on.

## How the layers fit together

This page separates four questions that are easy to conflate:

1. Does the mathematical construction have the claimed properties under its
   stated cryptographic premises?
2. Do the selected production Rust paths implement the maintained models?
3. Do the pinned source and tools reproduce the exact SBF that ran?
4. Did the real transaction, account topology, compute schedule, and cleanup
   behave as recorded?

Lean addresses the first question, Charon/Aeneas and bridge proofs address
selected parts of the second, the reproducible-build record addresses the
third, and tests plus runtime and chain evidence address the fourth. These
layers reinforce one another, but they are not a single universal end-to-end
proof and none silently proves the assumptions of an adjacent layer.

## In plain language

The main assumptions are:

1. The published cryptographic results used by Aspis apply to this exact
   mixed-field construction, and the recorded bad events completely cover
   false acceptance at the stated release parameters.
2. SHA-256 and Poseidon2 provide the security properties required by the
   transcript, commitments, Merkle trees, and spent markers.
3. The production proof builder receives fresh operating-system randomness
   where the construction requires it.
4. The successful-call, valid-input, and explicit execution/model
   hypotheses used by the selected Rust bridge theorems hold for the execution
   being described. One specific Tag-67 Rust transcript-hash call is an
   additional isolated equation.
5. Lean, Charon, Aeneas, Rust, LLVM, and the pinned build tools execute
   correctly.
6. Solana performs account locking, system calls, state updates, and compute
   accounting as recorded for the release.

## Selected production-Rust coverage

The current Rust-to-model theorem covers these release paths:

- Component-A extracted matrix execution to maintained GoodA for the selected
  release schedule;
- the generated Component-B sampler/evaluator/C2 layout to the maintained
  ten-round terminal;
- Component C's actual four rounds, finish, packer, and deployed public rows;
- Tag-67 magic, LE64 reads, projection, digest predicate, and six ordered work
  checks; and
- the combined A/B/C public output and Tag-67 verifier at that schedule.

The runtime verifier recomputes GoodA and GoodB on every selected branch. That
runtime fact is broader than the current production-Rust Component-A theorem:
a universal all-schedule source theorem remains open. A complete joint
serializer theorem and universal all-input Rust Poseidon2 equality also remain
open, and the adaptive PCS/Fiat–Shamir argument is supported by cited results
rather than an internal reproof.

The transcript-call equality retained by the Tag-67 work-verifier subtheorem is
stated verbatim below. It is not the only premise of the full composition:
Component C's `GeneratedPublicRun` carries folded-word, coefficient,
challenge, and successful-execution equalities, Component B consumes
successful-call and valid-input hypotheses, and no current theorem derives
all component packages from arbitrary verifier acceptance. The strongest
outside-review targets are the complete cryptographic event cover, exact
literature applicability, the custom Poseidon2-M31 primitive, those
execution/model links, Rust outside the selected coverage, Solana
account/state/refund behavior, and future runtime repricing; see
[`SECURITY.md`](../SECURITY.md) for the prioritized list.

The detailed table below identifies where each assumption is used, the
evidence that constrains it, and what follows if it fails.

| Assumption or trusted boundary | Used for | Evidence in this repository | If it fails |
| --- | --- | --- | --- |
| The false-acceptance event decomposition is complete, and the published Johnson/MCA, circle-FRI, PCS/BCS/CMS results apply to the exact mixed M31/QM31 construction and parameters | Argument soundness, commitment opening, and the work-normalized endpoint | Parameter manifests, the Lean finite-event calculation, and the paper's explicit theorem mapping; these verify the implication and arithmetic, not the event-cover premise itself | The corresponding soundness or zero-knowledge reduction does not follow |
| Each separately hashed work predicate admits the stated random-oracle reduction to the later challenge/output, and actual work events map completely and injectively to the six-event ledger | The V5 work factors and exactly-once work accounting | `V5WorkNormalizedApplicabilityRepair.lean`, `V5NonceWorkAuthentication.lean`, and `V5ImplementedWorkNormalizedEndpoint.lean` isolate these as premises | A positioned grinding factor may not apply to the event it is meant to reduce, or an event may be omitted/double-counted |
| Fiat–Shamir is modelled through SHA-256 as a programmable random oracle | Non-interactive soundness and simulation | Transcript schedule, domain separation, query accounting, and the cited compiler theorem | The Fiat–Shamir security claims do not follow |
| SHA-256 has the required collision/preimage and random-oracle properties | Transcript binding, Merkle binding, grinding, and simulation | Payload/order tests, SBF syscall execution, and the Tag-67 hash-call boundary below | Binding, grinding, or the ROM reduction may fail |
| Poseidon2 over M31 has the required cryptographic security, the deployed function satisfies `Poseidon2Faithful`, and accepted execution yields the extracted arithmetic, Poseidon2, Merkle, copy/LogUp, and public-input equations | Note commitments, nullifiers, Merkle relations, and the maintained spend relation | Constant-binding CI and kernel-checked known-answer permutations, node hashes, owner derivation, notes, and nullifiers. `V5AcceptedSpendRelation.lean` proves that the extracted equations imply the complete relation; the deployed acceptance-to-extraction theorem and probability bound remain open | Commitment/nullifier security or the maintained relation-to-code connection may fail |
| The cited extractor and simulation-extraction results hold for this protocol, and Poseidon2 has the required fixed-target second-preimage security for the nullifier target selected by the security game | Authorization and theft resistance | `TheftResistance.lean` proves the generic wrong-secret event reduction; `V5TheftResistance.lean` derives its nullifier-binding premise from the exact V5 spend relation. The extractor input is a complete execution record, not public proof bytes alone. Neither theorem assumes global hash injectivity. Efficient-attacker/game modelling, deployed acceptance/extraction, target sampling or a uniform per-target bound, and concrete probabilities remain external | Argument soundness may still give witness existence, but authorization possession or the claimed theft bound may not follow |
| The combined owner-key and note commitment has fixed-target second-preimage security, and the Merkle construction is binding, for the victim note | Ruling out a second opening of the same note under a different public nullifier | `V5TheftResistance.lean` proves the fixed-leaf/different-opening reduction. Known-answer tests check the functions, but the alternative-leaf Merkle reduction, complete computational game, and numerical bounds remain open | The on-chain marker still rejects a repeated nullifier, but the same semantic note might be reopened under a different nullifier |
| Component-B/C successful-call, valid-input, and explicit runtime/model hypotheses describe the same real execution | Selected Rust-to-model composition and public-output correspondence | The final integration theorem packages the component theorems; `GeneratedPublicRun` exposes folded-word, coefficient, challenge, and execution equalities | The component theorems remain individually valid, but the package does not establish arbitrary acceptance-to-model correspondence |
| The actual Tag-67 transcript digest call equals `rustHash(state, DOM_GRIND \|\| nonce_le64)` | Final connection between the Rust work verifier and Lean | `AspisTag67WorkVerifierClosure.exactGrindingHashInput` isolates this equation; `tag67AcceptedWireAndVerifierClosure` consumes it | The work-byte and six-step theorem no longer describes the runtime digest call |
| Lean/mathlib, Charon/Aeneas, Rust/LLVM-to-SBF, and the pinned build tools execute correctly | Kernel checking, extraction, compilation, and source-to-binary identity | Version pins, replay scripts, the 77-source/91-toolchain build-time inventory, and the clean-source byte-parity record | A proof, translation, or binary may not represent the intended source |
| Solana's account-locking, System Program CPI, SHA syscall, and CU schedule behave as recorded | Atomic state transition and the V5 CU policy | Runtime 2.3.13 release measurements plus an exact all-selector replay on mainnet Agave 4.1.0 across absent, program-owned, and prefunded marker paths; the mainnet runner requires bump 255 and simulation of the exact signed transaction bytes at or below 1,356,912 CU | A later runtime or wider runner policy requires a new replay and ceiling |
| The production host receives fresh, independent OS entropy where the construction requires it | Masking, public Fiat–Shamir salts, and the 17-attempt schedule search | Production-only RNG types, retry-control tests, and exclusion of fixture RNG/selector overrides from the production caller | The hiding or retry-distribution argument may fail |

## Tag-67 hash-call boundary

The final implementation theorem retains one code-to-model equation:

```text
∀ state nonce,
  actualTranscriptGrindingDigest state nonce =
    rustHash state ((3 : Byte) :: List.ofFn (nonceLEBytes nonce))
```

Given successful generated work-byte guards and reads, the exact projection,
leading-zero predicate, six ordered work checks, Component-C public output,
and ordered Tag-67 work-verifier behavior are theorem conclusions. Component-C
public output and the current A/B/C package additionally retain the
successful-call, valid-input, and execution/model assumptions described
above.

## Limits of the V5 security calculation

The deployed V5 arithmetic has width 19, scalar-powers degree 18, a batching
challenge sampled from the nonzero extension field, six positioned work
predicates, and exactly 30 S-two public-coin rounds after `m0`. Lean proves the
old width-29/full-field expression is a conservative upper bound and then
proves the final integer `<= 2^-100` implication under the named premises.

That theorem still receives the actual false-acceptance decomposition,
virtual-oracle/code membership, separate-output grinding reduction, Rust
sampling/transcript correspondence, authenticated-round semantics,
PCS/Merkle and Fiat--Shamir applicability, cited MCA/BCS/CMS applicability,
branch bounds, and the actual-event bijection as inputs. The q18/g37
100.161-bit fractional, work-normalized figure is not silently transferred to
V5. See the dated
[mathematical status review](reviews/mathematical-status-20260814.md).

The verifier itself recomputes GoodA and GoodB on every selected branch. The
production-Rust Component-A theorem proves the selected release schedule; a
universal all-schedule source theorem for that gate remains separate from the
runtime enforcement claim.

## Runtime scope

The original runtime 2.3.13 topology calculation covers tree-size variation
inside the frozen replay family for SBF
`4cf3c1d5ddd47efa68875c0070247e007083c5c9bb2d5988db0d644a609edf40`.
It does not price transcript challenge-retry paths outside that family. The
mainnet Agave 4.1.0 replay adds the longest accepted prefunded-marker CPI path
and sets a 1,356,912-CU runner policy limit with 43,088 CU of headroom.
Mainnet readiness and execution require nullifier PDA bump 255 and
simulation of the exact signed transaction bytes at or below that limit, and
the transaction declares the same compute limit. The
[runtime record](../results/spend/v5-mainnet-runtime-4.1.0-20260723/)
pins that comparison.

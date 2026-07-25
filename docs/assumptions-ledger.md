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

1. The published cryptographic results used by Aspis apply to this
   construction and its release parameters.
2. SHA-256 and Poseidon2 provide the security properties required by the
   transcript, commitments, Merkle trees, and spent markers.
3. The production proof builder receives fresh operating-system randomness
   where the construction requires it.
4. One specific Rust transcript-hash call performs the operation represented
   in the Lean model.
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

The only retained transcript-call equality is stated verbatim below. The
strongest outside-review targets are the cryptographic reduction boundaries,
the custom Poseidon2-M31 primitive, that one call equality, Rust outside this
selected coverage, Solana account/state/refund behavior, and future runtime
repricing; see [`SECURITY.md`](../SECURITY.md) for the prioritized list.

The detailed table below identifies where each assumption is used, the
evidence that constrains it, and what follows if it fails.

| Assumption or trusted boundary | Used for | Evidence in this repository | If it fails |
| --- | --- | --- | --- |
| Published Johnson/MCA and PCS/BCS results apply to the stated construction and parameters | Argument soundness, commitment opening, and the work-normalized endpoint | Parameter manifests, the Lean finite-event calculation, and the paper's explicit theorem mapping | The corresponding soundness or zero-knowledge reduction does not follow |
| Fiat–Shamir is modelled through SHA-256 as a programmable random oracle | Non-interactive soundness and simulation | Transcript schedule, domain separation, query accounting, and the cited compiler theorem | The Fiat–Shamir security claims do not follow |
| SHA-256 has the required collision/preimage and random-oracle properties | Transcript binding, Merkle binding, grinding, and simulation | Payload/order tests, SBF syscall execution, and the Tag-67 hash-call boundary below | Binding, grinding, or the ROM reduction may fail |
| Poseidon2 over M31 has the required cryptographic security and the deployed function satisfies `Poseidon2Faithful` | Note commitments, nullifiers, Merkle relations, and theft-resistance arguments | Constant-binding CI and kernel-checked known-answer permutations, node hashes, owner derivation, notes, and nullifiers | Commitment/nullifier security or the maintained relation-to-code connection may fail |
| The cited round-by-round extractor and simulation-extractability premise holds | The theft-resistance corollary | `TheftResistance.lean` proves the implication from this premise and nullifier binding | Argument soundness still gives witness existence, but the theft-resistance knowledge claim does not follow |
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
and current A/B/C composition are theorem conclusions rather than additional
code-to-model assumptions.

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
Mainnet readiness and execution require canonical nullifier PDA bump 255 and
simulation of the exact signed transaction bytes at or below that limit, and
the transaction declares the same compute limit. The
[runtime record](../results/spend/v5-mainnet-runtime-4.1.0-20260723/)
pins that comparison.

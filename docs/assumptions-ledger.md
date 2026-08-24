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
4. The production SHA-256 callback implements the byte-string hash described
   by the mathematical model. The rest of the selected accepted proof-checker
   path is followed from one successful translated execution rather than by
   assuming separate intermediate Rust/model equalities.
5. Lean, Charon, Aeneas, Rust, LLVM, and the pinned build tools execute
   correctly.
6. Solana performs account locking, system calls, state updates, and compute
   accounting as recorded for the release.

## Selected production-Rust coverage

The current source theorem starts at one successful translated call to the
released V5 proof checker. It follows the parser, transcript, six work checks,
18-query sampler, five authenticated opening sections, prepared claims, FRI
consumer, coordinate calculations, and four-round relation checker. The FRI
and relation values are proved to come from that same execution. The accepted
twelve-component accumulator schedule and general dot implementation are also
proved. The final theorem derives the exact general terminal weights and dot,
the compact constructor, four folds, final assembly and dot, and the final
composition internally. Once its clean replay is green, one successful
selected translated verifier call deterministically yields the maintained
accepted-path security-event conclusion.

The pinned Aeneas version translated the compact mutable loop body but emitted
an ill-typed back-function for its small outer fold wrapper. Audit then found
that the handwritten replacement reconstructed the array from an empty
iterator, discarding its writes. Lean records a counterexample to the old
wrapper and uses a corrected source-shaped wrapper over the translated
subcalls. The Rust and deployed program were unaffected. An extended Aeneas
translation of the unchanged production function emits the correct iterator
handback. The final proof connects that generated caller to the fold-semantics
theorem rather than receiving their equality as an assumption.

The tracked [compact-fold extraction record](../aeneas-verif/v5-relation-acceptance-20260815/extraction/compact-fold-extended-20260824/)
pins the unchanged production file, tools, extraction-only patches, LLBC,
direct generated source, normalized source, and successful Lean object. The
normalization replaces the generated mutable-array iterator declaration with
the already-used exact slice/from-slice model; it does not add a source
equality assumption.

This replaces the older public description based on separate Component A/B/C
packages and caller-provided intermediate equalities. Those historical
theorems remain in the repository, but they are no longer the main
implementation claim.

The selected theorem still does not cover all Rust. The outer Solana account
wrapper, upload and cleanup paths, compiler, runtime, and code outside the
released accepting proof-checker path remain separate. The adaptive
PCS/Fiat--Shamir argument is supported by cited results rather than reproved
from first principles. See [`SECURITY.md`](../SECURITY.md) for the prioritized
review list.

The detailed table below identifies where each assumption is used, the
evidence that constrains it, and what follows if it fails.

| Assumption or trusted boundary | Used for | Evidence in this repository | If it fails |
| --- | --- | --- | --- |
| The false-acceptance event decomposition is complete, and the published Johnson/MCA, circle-FRI, PCS/BCS/CMS results apply to the exact mixed M31/QM31 construction and parameters | Argument soundness, commitment opening, and the work-normalized endpoint | Parameter manifests, the Lean finite-event calculation, and the paper's explicit theorem mapping; these verify the implication and arithmetic, not the event-cover premise itself | The corresponding soundness or zero-knowledge reduction does not follow |
| The named external-event bounds fit the reserved budget | Turning the checked deterministic accepted path into a numerical false-acceptance or theft claim | The accepted proof-checker path, circle-code side conditions, linked four-fold candidate chain, nineteen-value reduction, prepared claims, distinct-query sampler, and raw/work-normalized arithmetic are checked. Published decoding and Fiat--Shamir results, primitive security, extraction, compiler, and runtime bounds remain explicit inputs | The deterministic theorem remains valid, but the numerical security claim does not follow |
| Each separately hashed work predicate admits the stated random-oracle reduction to the later challenge/output, and actual work events map completely and injectively to the six-event ledger | The V5 work factors and exactly-once work accounting | `V5WorkNormalizedApplicabilityRepair.lean`, `V5NonceWorkAuthentication.lean`, and `V5ImplementedWorkNormalizedEndpoint.lean` isolate these as premises | A positioned grinding factor may not apply to the event it is meant to reduce, or an event may be omitted/double-counted |
| Fiat–Shamir is modelled through SHA-256 as a programmable random oracle | Non-interactive soundness and simulation | Transcript schedule, domain separation, query accounting, and the cited compiler theorem | The Fiat–Shamir security claims do not follow |
| SHA-256 has the required collision/preimage and random-oracle properties | Transcript binding, Merkle binding, grinding, and simulation | Payload/order tests, SBF syscall execution, and the V5 hash-call boundary below | Binding, grinding, or the ROM reduction may fail |
| Poseidon2 over M31 has the required cryptographic security, the deployed function satisfies `Poseidon2Faithful`, and accepted execution yields the extracted arithmetic, Poseidon2, Merkle, copy/LogUp, and public-input equations | Note commitments, nullifiers, Merkle relations, and the maintained spend relation | Constant-binding CI and kernel-checked known-answer permutations, node hashes, owner derivation, notes, and nullifiers. `V5AcceptedSpendRelation.lean` proves that the extracted equations imply the complete relation; the deployed acceptance-to-extraction theorem and probability bound remain open | Commitment/nullifier security or the maintained relation-to-code connection may fail |
| The cited extractor and simulation-extraction results hold for this protocol, and Poseidon2 has the required fixed-target second-preimage security for the nullifier target selected by the security game | Authorization and theft resistance | `TheftResistance.lean` proves the generic wrong-secret reduction; `V5TheftResistance.lean` connects it to the exact V5 spend relation. `V5FixedVictimTheftGame.lean` adds credential recovery, alternative openings, and chain failures to one eight-event bound. The extractor input is a complete execution record, not public proof bytes alone. Deployed acceptance/extraction, extraction after observed proofs, target sampling or a uniform per-target bound, and concrete probabilities remain external | Argument soundness may still give witness existence, but authorization possession or the claimed theft bound may not follow |
| The combined owner-key and note commitment and the Poseidon2 tree hash have the required fixed-target and collision security for the victim note | Ruling out another opening or another leaf at the victim's position under the victim root | `V5TheftResistance.lean` proves the fixed-leaf/different-opening reduction. `ApplicationMerkleBinding.lean` proves that a different leaf at the same position and root exposes a concrete node-hash collision, while a different position may be a valid opening. `V5FixedVictimTheftGame.lean` includes both cases in the fixed-victim event bound. Known-answer tests check selected function results, not primitive security; numerical bounds remain external | The on-chain marker still rejects a repeated nullifier, but the victim note might be reopened under a different nullifier or leaf |
| The production SHA-256 callback hashes the concatenated Rust slices exactly as the mathematical SHA-256 function hashes their bytes | Transcript and work hashing, Merkle authentication, and the production-to-model primitive boundary | The generated source fixes every label, payload, nonce encoding, and callback call site. Known-answer tests exercise the callback. Cryptographic security and syscall semantics are not proved by Lean | The accepted control-flow theorem still holds, but its hash, Merkle, and transcript interpretation would not describe production |
| Lean/mathlib, Charon/Aeneas, Rust/LLVM-to-SBF, and the pinned build tools execute correctly | Kernel checking, extraction, compilation, and source-to-binary identity | Version pins, replay scripts, the 77-source/91-toolchain build-time inventory, and the clean-source byte-parity record. The corrected compact mutable fold is retained as generated Lean plus its recorded normalization and bridge proof; no source equality is supplied by the final theorem's caller | A proof, translation, or binary may not represent the intended source |
| Solana's account-locking, System Program CPI, SHA syscall, PDA derivation, and CU schedule behave as recorded | Atomic state transition, marker uniqueness, and the V5 CU policy | `V5NullifierMarkerReplay.lean` proves that the same marker address cannot be consumed successfully twice in sequence, even if two different nullifiers derive that address. Runtime 2.3.13 measurements and an all-selector replay on mainnet Agave 4.1.0 cover absent, program-owned, and prefunded marker paths. Recorded pre-execution runner source requires bump 255 and exact-wire simulation at or below 1,356,912 CU; the immutable lifecycle evidence does not pin the exact executed runner commit. The exact deployed program checked the derived PDA address but did not require the numeric bump to be 255 | If Rust or Solana does not follow the modeled locking, rollback, CPI, and persistent-write behavior, the chain-level argument can fail. The marker theorem has not yet removed PDA aliasing from the deployed theft game; a later runtime or wider runner policy requires a new replay and ceiling |
| The production host receives fresh, independent OS entropy where the construction requires it | Masking, public Fiat–Shamir salts, and the 17-attempt schedule search | Production-only RNG types, retry-control tests, and exclusion of fixture RNG/selector overrides from the production caller | The hiding or retry-distribution argument may fail |

## SHA-256 callback boundary

Lean follows the production transcript and Merkle call sites, byte framing,
domain labels, nonce encoding, state advancement, and order of the six work
checks. The remaining primitive boundary says that the production callback's
result is SHA-256 of the concatenated byte slices passed at that call site.

This assumption is deliberately narrow. It is not a statement that an
arbitrary Rust execution matches Lean, and it does not supply any transcript,
query, opening, FRI, or relation value. SHA-256 collision, preimage, and
random-oracle properties are separate cryptographic assumptions.

## Limits of the V5 security calculation

The deployed V5 arithmetic has width 19, scalar-powers degree 18, a batching
challenge sampled from the nonzero extension field, six positioned work
predicates, and exactly 30 S-two public-coin rounds after `m0`. Lean proves the
old width-29/full-field expression is a conservative upper bound and then
proves the final integer `<= 2^-100` implication under the named premises.

`V5DeployedFalseAcceptance.lean` defines the false-acceptance event and the
conditional probability endpoint. The accepted-path proof chain now supplies
the deterministic parser, transcript, opening, FRI, decoded claim table,
initial relation value, relation tail, and both accumulator equalities from one
successful translated run. Once the final clean replay is green, that call
yields the maintained accepted-path security-event conclusion. The numerical
endpoint also needs the cited
decoding and Fiat--Shamir results, Poseidon2 and SHA-256 security, extraction,
and the per-event bounds. Given those inputs, Lean derives the work-normalized
`2^-100` result and the ordinary probability bound
`min(1, T / 2^100)` for `1 <= T <= 2^128`.

`V5BoundedQuerySamplerUniformity.lean` and
`V5WithoutReplacementQuerySoundness.lean` remove one smaller premise from the
finite arithmetic. Conditioned on obtaining 18 distinct values within 64
independent uniform draws, the output schedule is exactly uniform. For a fixed
set of at most 6,082 out of 131,072 positions, Lean proves the exact probability
that all 18 output positions lie in that set. It also proves the unconditioned bound when draw-limit exhaustion
is treated as rejection. A separate joint-event premise with a 32-bit work
factor gives the `2^-111` inequality. The files do not show that SHA/Rust
supplies the ideal draws, that FRI supplies the fixed set, or that the joint
work premise holds.

The source check of [S-two ePrint 2026/532](https://eprint.iacr.org/2026/532)
has now been specialized to the released width-nineteen construction. Lean
checks the exact field, code space, distance, agreement threshold, list
parameters, degree, and nonzero challenge denominator. The paper's decoding
result remains a named external premise because Lean cannot import a proof
from a PDF, but its parameter matching is no longer left implicit.

The custom parts are proved separately: one initial candidate is followed
through all four folds, the distinct-query sampler is analyzed directly, and
the challenge-dependent nineteen-word reduction avoids an extra decoder-list
factor. The selected production proof-checker path is connected to those
objects by the final accepted-path theorem, subject to its clean replay and
the explicit terminal/hash callback boundaries. Hash security, Fiat--Shamir,
extraction,
compiler, and runtime behavior remain external assumptions rather than hidden
branches.

The V5 arithmetic keeps its own 100-bit target. The checked core is below
`0.7 * 2^-100`; all separately bounded external events must fit the remaining
`0.3 * 2^-100`. Deterministic code equalities are trust boundaries until
proved, not invented probabilities. The q18/g37 100.161-bit figure is not
transferred to V5. See the dated
[mathematical status review](reviews/mathematical-status-20260814.md).

The verifier itself recomputes GoodA and GoodB on every selected branch. The
accepted-path work concerns the released successful proof-checker route;
it does not turn the older schedule-general component question into a claim
about unrelated verifier modes.

## Runtime scope

The original runtime 2.3.13 topology calculation covers tree-size variation
inside the frozen replay family for SBF
`4cf3c1d5ddd47efa68875c0070247e007083c5c9bb2d5988db0d644a609edf40`.
It does not price transcript challenge-retry paths outside that family. The
mainnet Agave 4.1.0 replay adds the longest accepted prefunded-marker CPI path
and sets a 1,356,912-CU runner policy limit with 43,088 CU of headroom.
Recorded pre-execution runner source required nullifier PDA bump 255 and
simulation of the exact signed transaction bytes at or below that limit, and
the transaction declared the same compute limit and used bump 255. The
immutable lifecycle evidence does not pin the exact executed runner commit.
The exact deployed program derived and checked the PDA but did not require the
numeric bump to be 255; that in-program restriction was added later. The
[runtime record](../results/spend/v5-mainnet-runtime-4.1.0-20260723/)
pins that comparison.

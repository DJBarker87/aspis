# Aspis assumptions ledger

Aspis V5 has an end-to-end formal proof of the selected accepting verifier
callback and a conditional security calculation. This ledger names the
interfaces used to connect that theorem to cryptographic probability,
compiled SBF bytes, and finalized Solana state.

## Claim boundary

The completed accepted-path theorem starts from any successful translated
call to `verify_mode9_composite_with_live_statement` and derives the exact
parse, transcript, six work checks, 18 queries, five authenticated opening
sections, FRI execution, claim table, relation execution, and both final
accumulators. It reaches the maintained accepted-path security-event
conclusion without caller-supplied accumulator equalities.

Two formal composition tasks remain at the publication boundary:

1. identify the translated Rust public-statement fields with the abstract
   `V5PublicStatement` used by the false-acceptance and theft experiments; and
2. lift the deterministic accepted-call classification into the causal
   probability experiment used by the conditional work-normalized theorem.

Accordingly, the paper claims end-to-end accepted-path verification and a
conditional 100-bit work-normalized protocol result. It reserves a deployed
theft-resistance number until those compositions and the external budgets are
instantiated.

## Assumptions and evidence

| Interface or assumption | Used for | Evidence that fixes the interface | Consequence if violated |
| --- | --- | --- | --- |
| Published circle-decoding results apply to the released domains and agreement thresholds | FRI list decoding and candidate recovery | Lean checks M31, all released domains, encoder order, dimensions, distances, degree bounds, query count, and agreement inequalities | The decoding step in the soundness reduction loses its cited justification |
| The published BCS state-restoration / Fiat-Shamir theorem applies to the recorded public-coin schedule | Non-interactive soundness and adaptive query accounting | Exact byte transcript, domain separation, 30 public-coin boundaries, six work positions, and work-normalized ledger | The ideal-to-non-interactive probability step must be replaced |
| Solana's SHA-256 callback returns SHA-256 of the exact supplied byte lists | Transcript and Merkle implementation semantics | Generated callback boundary, typed event expansion, literal byte framing, and known-answer tests | The source-level hash observations can diverge from the mathematical transcript or Merkle model |
| SHA-256 supplies the collision, target-preimage, and modeled random-oracle properties assigned to it | Authentication, transcript binding, grinding, and Fiat-Shamir | Separate named events in the unified ledger | The corresponding event budget must absorb the failure |
| The deployed Poseidon2 wrappers equal the maintained permutation and framing | Note, owner, nullifier, and relation equations | Pinned constants, Lean's complete 22-round algebra, Rust KATs, domain-separated wrapper tests, and `Poseidon2Faithful` | The maintained spend relation may describe different hashes from the program |
| Poseidon2-M31 has the required collision and target-preimage security | Note commitments, nullifiers, Merkle relations, and theft reductions | Symbolic primitive events and the published parameter record | Primitive failure contributes directly to false acceptance or theft |
| The deployed prover receives fresh operating-system randomness | Masking, salts, and retry selection | Implementation RNG types and exclusion of fixture RNG from the release caller | The hiding or retry-distribution argument can fail |
| Knowledge extraction and the fixed-victim reduction apply with the stated event bounds | Theft resistance | Explicit extractor interface and eight-event fixed-victim classification | Soundness may still provide witness existence while the knowledge/theft conclusion loses its bound |
| Charon, Aeneas, Lean, and mathlib process the recorded sources correctly | Rust translation and kernel checking | Pinned revisions, authenticated patches, tracked generated Lean, clean 331-module replay, and axiom audit | The checked Lean term may fail to represent the selected Rust or intended logic |
| Rust, LLVM, platform tools, and the SBF build are correct | Source-to-program correspondence | Pinned clean source, dependency locks, tool hashes, and byte-for-byte SBF reproduction | The deployed bytes may differ semantically from the reviewed source despite matching the recorded build |
| Solana implements the recorded account locks, rollback, PDA derivation, System Program CPI, and persistent writes | Atomic state transition and spent-marker behavior | Source-shaped state model, runtime 2.3.13 measurements, Agave 4.1.0 selector replay, exact-wire simulation, and finalized receipts | The chain-level state conclusion can diverge from the maintained model |
| The archived RPC responses and release manifests faithfully record finalized history | Historical proof/program reconstruction | Hash-chained release bundle, full payer archive, proof reconstruction from 79 uploads, and SBF reconstruction from 1,466 loader writes | The historical execution identity would need fresh independent chain evidence |

## Poseidon2 parameter status

Aspis uses Poseidon2 over Mersenne31 with width 16, `alpha = 5`, 8 full rounds,
and 14 partial rounds. The constants come from `p3-mersenne-31 0.6.1` and are
pinned in both Rust and Lean.

Recent algebraic cryptanalysis improves round-skipping, preimage, and collision
attacks against Poseidon2. The 2026 analysis reports that the studied full
parameter sets retain their asserted 128-bit level under its ideal-degree and
Groebner-basis assumptions, while recommending per-parameter evaluation for
deployed instances. No published paper located by the 24 August 2026 review
gives a dedicated concrete advantage for the exact Aspis tuple. Aspis therefore
uses a symbolic Poseidon2 primitive-security term. The constants and execution
are verified; the cryptographic advantage is supplied by the assumption.

The dated evidence and bibliography route are recorded in the
[24 August novelty and cryptanalysis scan](novelty-rescan-2026-08-24.md).

## Work-normalized and raw security

The checked protocol subtotal is

```text
B_protocol <= 0.7 * 2^-100.
```

The conditional endpoint allocates

```text
B_external <= 0.3 * 2^-100
```

to the named primitive, Fiat-Shamir, extraction, credential, toolchain, and
runtime events. Their sum is then at most `2^-100` in the work-normalized
experiment. The dominant raw batching term after the 37-bit grind has already
been paid is about 70--71 bits. These are two views of the same release
accounting and are reported separately.

## Runtime profile

The frozen SBF is
`4cf3c1d5ddd47efa68875c0070247e007083c5c9bb2d5988db0d644a609edf40`.
Runtime 2.3.13 measurements cover the frozen replay family. The Agave 4.1.0
replay additionally covers absent, program-owned, and prefunded marker paths.
The mainnet runner used a 1,356,912-CU policy ceiling and required exact signed
wire simulation before submission; the transaction landed at 1,334,452 CU.

The observed nullifier PDA bump was 255. The recorded pre-execution runner
source required bump 255 for the measured compute policy. The deployed program
derived and checked the PDA address, while the numeric bump-255 program check
was added later. The finalized address and state transition remain fixed by
the archived transaction.

## Review priorities

The highest-value external review targets are:

1. the exact applicability of the cited decoding and BCS Fiat-Shamir results;
2. a dedicated cryptanalysis of the Aspis Poseidon2-M31 parameter set;
3. the Rust-public-statement to abstract-statement bridge;
4. the deterministic-to-probability-experiment composition;
5. the source-to-SBF toolchain boundary; and
6. the Solana account, rollback, marker-persistence, and refund semantics.

The exact theorem map is in [formal verification](formal-verification.md), and
the security reporting policy is in [`SECURITY.md`](../SECURITY.md).

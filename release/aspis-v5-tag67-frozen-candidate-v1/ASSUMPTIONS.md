# Aspis assumptions ledger

Aspis has machine-checked mathematics, source-authentic implementation
theorems, a frozen SBF, and direct Solana measurements. The remaining
assumptions are listed here so the result can be read at full strength without
turning every public paragraph into a disclaimer.

| Assumption or trusted boundary | Used for | Evidence in this repository | If it fails |
| --- | --- | --- | --- |
| Published Johnson/MCA and PCS/BCS results apply to the stated construction and parameters | Argument soundness, commitment opening, and the work-normalized endpoint | Parameter manifests, the Lean finite-event ledger, and the paper's explicit theorem mapping | The corresponding soundness or zero-knowledge reduction does not follow |
| Fiat–Shamir is modelled through SHA-256 as a programmable random oracle | Non-interactive soundness and simulation | Transcript schedule, domain separation, query accounting, and the cited compiler theorem | The Fiat–Shamir security claims do not follow |
| SHA-256 has the required collision/preimage and random-oracle properties | Transcript binding, Merkle binding, grinding, and simulation | Exact payload/order tests, SBF syscall execution, and the Tag-67 hash-call boundary below | Binding, grinding, or the ROM reduction may fail |
| Poseidon2 over M31 has the required cryptographic security and the deployed function satisfies `Poseidon2Faithful` | Note commitments, nullifiers, Merkle relations, and theft-resistance plumbing | Constant-binding CI and kernel-checked known-answer permutations, node hashes, owner derivation, notes, and nullifiers | Commitment/nullifier security or the maintained relation-to-code connection may fail |
| The cited round-by-round extractor and simulation-extractability premise holds | The theft-resistance corollary | `TheftResistance.lean` proves the implication from this premise and nullifier binding | Argument soundness still gives witness existence, but the theft-resistance knowledge claim does not follow |
| The actual Tag-67 transcript digest call equals `rustHash(state, DOM_GRIND || nonce_le64)` | Final Rust-to-Lean work-verifier correspondence | `AspisTag67WorkVerifierClosure.exactGrindingHashInput` and `tag67AcceptedWireAndVerifierClosure` | The work-wire and six-step theorem no longer describes the runtime digest call |
| Lean/mathlib, Charon/Aeneas, Rust/LLVM-to-SBF, and the pinned build tools execute correctly | Kernel checking, extraction, compilation, and source-to-binary provenance | Version pins, replay scripts, the 77-source/91-toolchain build-time inventory, and the clean-source byte-parity record | A proof, translation, or binary may not represent the intended source |
| Solana's account-locking, System Program CPI, SHA syscall, and CU schedule behave as recorded for the frozen runtime | Atomic state transition and the accepted-input CU ceiling | Local-validator executions on runtime 2.3.13, selector/marker replays, account checks, and the accepted-topology CU policy | Atomicity or the 1,353,616-CU ceiling must be re-established for the changed runtime |
| The production host receives fresh, independent OS entropy where the construction requires it | Masking, public Fiat–Shamir salts, and the 17-attempt schedule search | Production-only RNG types, retry-control tests, and exclusion of fixture RNG/selector overrides from the production caller | The hiding or retry-distribution argument may fail |

## Exact Tag-67 boundary

The final implementation theorem retains one correspondence equation:

```text
∀ state nonce,
  actualTranscriptGrindingDigest state nonce =
    rustHash state ((3 : Byte) :: List.ofFn (nonceLEBytes nonce))
```

Parser guards, work-wire projection, the leading-zero predicate, the six
ordered work checks, Component-C public output, and the current A/B/C
composition are theorem conclusions rather than additional correspondence
assumptions.

The verifier itself recomputes GoodA and GoodB on every selected branch. The
source-authentic Component-A bridge proves the frozen concrete schedule; a
universal all-schedule source theorem for that gate remains separate from the
runtime enforcement claim.

## Runtime scope

The V5 accepted-input ceiling is a conservative measured-and-derived bound for
the frozen grammar, SBF
`4cf3c1d5ddd47efa68875c0070247e007083c5c9bb2d5988db0d644a609edf40`,
and Solana runtime 2.3.13. A change to any of those inputs creates a new
measurement target.

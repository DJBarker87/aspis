# Tag-67 work-wire and verifier correspondence

Status: **kernel-green and included in the V5 production capstone**

Pinned Charon/Aeneas extraction connects the production Tag-67 wire parser and
work-verifier helpers to the maintained Lean model. The final theorem is
`AspisTag67WorkVerifierClosure.tag67AcceptedWireAndVerifierClosure` in
[`proof/Tag67WorkVerifierClosure.lean`](proof/Tag67WorkVerifierClosure.lean).

Tag 67 is enabled in the default verifier dispatch. The theorem is part of the
formal closure for the frozen SBF with SHA-256
`4cf3c1d5ddd47efa68875c0070247e007083c5c9bb2d5988db0d644a609edf40`;
dispatch relies on it while supplying the exact hash-application equation
below.

## What the theorem closes

Generated acceptance proves all of the following:

- the exact work-wire magic and zero-tail guards;
- six actual little-endian `u64` reads;
- batch, fold 0, fold 1, fold 2, fold 3, and final record order;
- difficulties 37, 34, 33, 30, 25, and 32;
- exact transcript labels and absorb payload ordering;
- selector acceptance only for 0, 1, or 2;
- construction of the maintained `WorkWireView`;
- equality with the canonical maintained work-wire projection;
- equality of the extracted digest predicate and
  `digestHasLeadingZeroBits`; and
- the complete six-step short-circuit check/absorb/next execution.

The closure no longer assumes an arbitrary wire view,
`ExactWorkWireProjection`, `ExactGeneratedLE64RuntimeReadBridge`, a
digest-predicate correspondence, or a six-step verifier correspondence.

## Exact remaining boundary

The one implementation/model premise is:

```text
∀ state nonce,
  actualTranscriptGrindingDigest state nonce
    = rustHash state ((3 : Byte) :: List.ofFn (nonceLEBytes nonce))
```

At Rust level this names the actual function-pointer application:

```text
(self.hash)(&[&self.state, &[DOM_GRIND], &nonce.to_le_bytes()])
```

The theorem identifies the precise payload and call boundary. `HashFn` remains
an arbitrary supplied function; cryptographic hash security and
Fiat–Shamir/random-oracle reasoning are imported at the protocol layer.

## Strongest statements

| Statement | File |
| --- | --- |
| Actual guards and LE64 reads construct the exact maintained view | `proof/Tag67WorkWireLE64Bridge.lean` |
| Extracted predicate equals the maintained predicate | `proof/Tag67DigestPredicateProof.lean` |
| Six ordered before/after state pairs and next results | `proof/Tag67SixActualStepsProof.lean` |
| Extracted six-step acceptance iff exact positioned execution | `proof/Tag67WorkVerifierClosure.lean` |
| Maintained hash interface from the single application equation | `proof/Tag67WorkVerifierClosure.lean` |
| Final wire, digest, and six-step composition | `proof/Tag67WorkVerifierClosure.lean` |

`Tag67WorkVerifierClosureAxiomAudit.lean` audits the exported capstones. Lean
4.32 reports only `{propext, Classical.choice, Quot.sound}`.

## Pinned provenance

- source base: `27e8265d28de88e7967626a2d2432ef161fb4f49`
- Charon: `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`
- Aeneas: `b59d5188c082f704a418c7cb4e52ad69328002d1`
- Rust extraction toolchain: `nightly-2026-06-01`
- proof replay: Lean `4.32.0`

The normalized generated Lean and proof sources are retained in `generated/`
and `proof/`. Raw translations, LLBC, and build logs are preserved at
[`research-archive-v5-production-closure-2026-07-22`](https://github.com/DJBarker87/aspis/tree/research-archive-v5-production-closure-2026-07-22).

## Validation

- focused core grinding tests: 2 passed;
- proof-facing six-step Rust tests: 3 passed;
- pinned digest and six-step extraction: passed;
- Lean 4.32 default-limit replay: passed;
- forbidden-premise and forbidden-token audits: passed.

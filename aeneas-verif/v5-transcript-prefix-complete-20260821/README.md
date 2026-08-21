# Complete V5 transcript prefix source check

This bundle closes the two helper gaps left by
`../v5-transcript-prefix-helpers-20260820/` and checks the unchanged outer
`verify_v5_wire_prefix` function.

## What is proved

The Lean proofs are universal proofs about Aeneas translations of the
unchanged Rust helpers, not tests of one proof file:

- `extracted_zerocheck_success_exact` proves the exact registry and helper-sum
  absorbs followed by theta, ten point coordinates, and mu;
- `extracted_semantic_sumcheck_success_exact` proves the exact split of the
  4,480-byte proof section into ten 448-byte rounds, each absorbed with its
  round byte before its challenge.

The earlier helper bundle proves the other four calls: the first root, second
root, masked-sumcheck claim, and batch nonce. All six larger calls in the
prefix therefore have unchanged-source proofs.

`generated/Outer/Funs.lean` is a fresh Charon/Aeneas translation of the
unchanged production `verify_v5_wire_prefix`. The checker binds its successful
path to the typed model in
`AspisFormal/V5TranscriptPrefixNormalizedGenerated.lean`. It checks all 17
transcript-affecting calls, their exact order and arguments, the values passed
to the terminal-context comparison, and every value returned to later verifier
phases. It also checks the live-statement digest call and transcript creation
that the older extraction had replaced.

There is no Rust source rewrite in this bundle. The only generated-Lean
normalization is the diagnostic text passed to Aeneas' `Result.expect` model
in the semantic helper. That model ignores the text on success and failure;
the replay checks that this is the sole difference from regenerated output.

This proves source control flow and transcript inputs. SHA-256 security and
the ideal-randomness argument are separate, explicitly stated assumptions.

## Pinned identities

- `programs/aspis-verifier/src/v5_cu_probe.rs` Git blob:
  `ca28d560e44e5e82e689321f32289831c889a0bd`
- Charon commit:
  `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`
- Charon executable SHA-256:
  `776344b8bfb7f3ec4ba78d5007ae79c1ef3f4ed654de05f04266693759a37375`
- Aeneas commit:
  `d860ac47ed548d3da6d799afc013779ce470516c`
- Aeneas executable SHA-256:
  `7eb0cf355544457ae9740c649921582b4f61c9de63ef63a1ae45e016f151ed0d`
- Lean: `v4.32.0`
- unchanged outer `Funs.lean` SHA-256:
  `18624db7ce0430a57b578501af5302b378f6dfe8805059cf32992397a89497ec`

## Check

With the Aeneas Lean library in `LEAN_PATH`:

```bash
./aeneas-verif/v5-transcript-prefix-complete-20260821/verify-lean432.sh
```

The script runs the unchanged-outer checker, compiles both generated helper
proofs with Lean 4.32, checks the pinned identities when the tool paths are
provided, and rejects proof shortcuts.

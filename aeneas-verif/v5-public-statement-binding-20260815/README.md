# V5 public-statement binding

This bundle checks the narrow question that matters for the public spend:
which pool anchor, nullifier, output commitment, output anchor, asset and fee
does the terminal use?

Charon extracted `decode_statement` from the unchanged production file
`programs/aspis-verifier/src/v5_atomic_terminal.rs`. Aeneas translated that
function to Lean. The proof then establishes, for every input rather than only
the released proof, that:

1. one successfully decoded 216-byte statement cannot produce two different
   Rust statement values;
2. its six spend fields are therefore unique;
3. equality of the decoded context statement and the live statement makes all
   six terminal fields equal to the live fields; and
4. once the polynomial-opening argument supplies those six terminal values,
   they satisfy the existing Lean predicate `OpenedColumnsMatchStatement`.

The source in `v5_cu_probe.rs` rejects unless
`context_statement == live_statement`. That line and the call passing
`live_statement` into `verify_v5_atomic_terminal_from_bytes` are protected by
the replay's full-file source hash. Aeneas does not currently translate the
whole `verify_v5_wire_prefix` function, so the implication from successful
execution of that large function to the equality check remains a small,
explicit Rust-control-flow step rather than a generated Lean theorem.

The larger unresolved security step is not statement parsing. It is proving
that a successful polynomial-commitment/FRI verification yields opened columns
whose six values are exactly the values consumed by the terminal. The proof
names that relation `RemainingPCSStatementBinding`.

## Extraction

The checked extraction used:

```text
Charon cb50ff16b9f1066b8a97dc06da704de2da2fa41c
Aeneas b59d5188c082f704a418c7cb4e52ad69328002d1
Lean 4.32.0
```

The temporary extraction crate imports the unchanged production module with a
Rust `#[path = "..."]` declaration and starts Charon at:

```text
crate::v5_atomic_terminal::decode_statement
```

The generated decoder keeps the statement codec calls external. Their
transparent fixed-width models are in `FunsExternal.lean`; importantly, the
decoder-uniqueness and live-equality theorems do not rely on a cryptographic or
injectivity assumption about those helpers.

## Replay

Build the maintained statement model once, then run:

```bash
cd AspisFormal
NO_DNA=1 lake build AspisFormal.V5AcceptedSpendRelation
cd ..

LEAN432_BIN=/path/to/lean-4.32.0 \
AENEAS_LEAN_LIB=/path/to/aeneas-lean432/lib/lean \
  aeneas-verif/v5-public-statement-binding-20260815/replay-lean432.sh
```

The replay verifies the exact production source hashes, compiles the generated
definitions and handwritten proof, rejects proof escapes, and checks that the
four public theorems use only Lean/mathlib's standard `propext`,
`Classical.choice`, and `Quot.sound` foundations.

# Exact V5 FRI transition-decoder semantics

This bundle connects the loop-free decoder references to exact field
mathematics.  Charon extracts the references, Aeneas translates them to Lean,
and `V5FriDecoderReferenceSemantics.lean` proves that every successful decode
returns exactly the four canonical QM31 values represented by the 64 input
bytes.  The selected decoder is also proved to return the requested one of
those four values after validating the complete leaf.

The accompanying Kani bundle at
`kani-verif/v5-fri-transition-decoders-20260820` universally checks that the
unchanged production decoder loops have exactly the same successful and
failing results as these references.  The Kani/Rust-to-MIR/model-checker
translation is the explicit source boundary needed because the current Aeneas
translation cannot close the production iterator loop directly.

No released-proof fixture or concrete leaf is assumed.

## Replay

Extraction requires:

- Charon commit `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`;
- Aeneas commit `b59d5188c082f704a418c7cb4e52ad69328002d1`.

Run:

```sh
CHARON_BIN=/path/to/charon \
AENEAS_BIN=/path/to/aeneas \
./replay-extraction.sh

LEAN432_BIN=/path/to/lean-4.32.0 \
AENEAS_LEAN_LIB=/path/to/aeneas-lean432-oleans \
V5_FRI_COMBINED_LEAN_OUT=/path/to/checked-fri-oleans \
V5_FRI_COMPONENTB_LEAN_OUT=/path/to/checked-component-b-oleans \
./replay-lean432.sh
```

Replay the production/reference result equality separately with
`../../kani-verif/v5-fri-transition-decoders-20260820/verify.sh`.

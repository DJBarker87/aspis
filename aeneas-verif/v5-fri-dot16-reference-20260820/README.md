# Fixed-index V5 FRI dot semantics

This bundle connects the loop-free `indexed_dot16` Rust reference to exact
field mathematics. Charon extracts that same Rust source, Aeneas translates
it to Lean, and `V5FriDot16ReferenceSemantics.lean` proves that every
successful result contains the four ordinary 16-term QM31 dot products of the
64 canonical little-endian M31 input words.

The accompanying Kani bundle at
`kani-verif/v5-fri-dot16-exact-20260820` universally checks that the unchanged
iterator-based production helper has exactly the same complete `Option`
result as `indexed_dot16`. This is the explicit Rust/MIR/model-checker
toolchain boundary needed because the pinned Aeneas version cannot join the
production iterator's live mutable loan.

The Lean proof covers:

- all 64 little-endian word decodes and canonicality checks;
- all 256 prepared M31 weight limbs;
- exact overflow-free four-product blocks;
- exact M31 reduction of all four blocks;
- every coordinate of all four QM31 outputs; and
- equality with the conventional 16-term field dot product.

No concrete input or released-proof fixture is assumed.

## Replay

Extraction requires the pinned tools:

- Charon commit `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`;
- Aeneas commit `b59d5188c082f704a418c7cb4e52ad69328002d1`.

Run:

```sh
CHARON_BIN=/path/to/charon \
AENEAS_BIN=/path/to/aeneas \
./replay-extraction.sh

LEAN432_BIN=/path/to/lean-4.32.0 \
AENEAS_LEAN_LIB=/path/to/aeneas-lean432-oleans \
./replay-lean432.sh
```

The Kani production/reference equivalence is replayed separately with
`../../kani-verif/v5-fri-dot16-exact-20260820/verify.sh`.

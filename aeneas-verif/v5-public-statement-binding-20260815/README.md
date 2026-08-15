# V5 public-statement binding

This bundle checks the narrow question that matters for the public spend:
which pool anchor, nullifier, output commitment, output anchor, asset and fee
does the terminal use?

Charon extracted `decode_statement` and the terminal claim reader from the unchanged production file
`programs/aspis-verifier/src/v5_atomic_terminal.rs`. Aeneas translated that
code to Lean. The proof then establishes, for every input rather than only
the released proof, that:

1. one successfully decoded 216-byte statement cannot produce two different
   Rust statement values;
2. its six spend fields are therefore unique;
3. equality of the decoded context statement and the live statement makes all
   six terminal fields equal to the live fields; and
4. once the polynomial-opening argument supplies those six terminal values,
   they satisfy the existing Lean predicate `OpenedColumnsMatchStatement`;
5. the claim reader uses exactly the point-major byte position
   `16 * (19 * point + lane)`; and
6. the terminal adapter copies semantic lanes 0 through 15 and lane 16 into
   the old evaluator positions, leaves the removed positions zero, and reads
   the mask from point 3, lane 17 (bytes 1184 through 1199); and
7. if the exact public row residuals made by the production semantic evaluator
   vanish, the opened relation uses the live anchor, nullifier, output
   commitment, output anchor, asset, and fee.

The seventh result is universal. It does not assume the six desired
equalities. It starts from the residual equations themselves. In particular,
the fee is not a separate proof-table value: production inserts the live fee
into the balance residual. Comparing that equation with the maintained
balance equation, and using both 30-bit fee bounds, proves integer equality of
the fees rather than equality only modulo M31.

The source in `v5_cu_probe.rs` rejects unless
`context_statement == live_statement`. That line and the call passing
`live_statement` into `verify_v5_atomic_terminal_from_bytes` are protected by
the replay's full-file source hash. Aeneas does not currently translate the
whole `verify_v5_wire_prefix` function, so the implication from successful
execution of that large function to the equality check remains a small,
explicit Rust-control-flow step rather than a generated Lean theorem.

## Production evaluator audit

The replay now also pins the complete source files that contain the semantic
evaluator, its row constants, and the 30-bit fee limit. The checked Lean model
records these exact source positions:

The source audit follows the four functions that carry these checks into the
value accepted by the verifier:

1. `atomic_semantic_packed_impl` makes the fee, digest and asset row
   residuals and places them in semantic positions 66 through 76.
2. `atomic_state_only_selected_constraint_composition_compiled_v3` folds the
   packed semantic values, the copy value and the Poseidon values with
   `theta`.
3. `atomic_state_only_selected_unmasked_terminal_value_compiled_v3`
   multiplies that composition by the zerocheck equality value and adds the
   helper term.
4. `verify_v5_atomic_terminal_from_bytes` reads the exact claim table, calls
   the unmasked terminal, compares its result with the authenticated real
   claim, checks the mask claim, and checks the final affine equation.

| Public check | Production row | Semantic position before packing |
|---|---:|---:|
| Fee balance | 864 | 66 |
| Current anchor, 8 limbs | 379 | 67 through 74 |
| Output anchor, 8 limbs | 699 | 67 through 74 |
| Nullifier, 8 limbs | 731 | 67 through 74 |
| Output commitment, 8 limbs | 779 | 67 through 74 |
| Input asset | 795 | 75 |
| Output asset | 799 | 76 |

There are 35 raw row residuals: one fee equation, 32 digest-limb equations,
and two asset equations. The production code then:

1. multiplies each row residual by its multilinear row selector;
2. packs four semantic positions at a time;
3. folds the packed semantic lanes, the copy lane, and the Poseidon lanes with
   `theta`;
4. multiplies the composition by the zerocheck equality value and adds the
   helper term; and
5. checks that result against the authenticated terminal claim. The V5 adapter
   also checks the mask opening and the affine masked-terminal equation.

This audit matters because a single accepted scalar is not logically the same
thing as 35 zero row residuals. A cancellation in packing or challenge folding,
or a failure of the sumcheck/PCS extraction argument, must be handled by the
soundness proof.

The remaining condition is therefore narrow and explicit:
`RemainingPCSStatementBinding` takes the fixed 1,024-by-16 trace table
extracted from the accepted commitments. It states that the exact production
cells in that table map to the maintained opened columns and that all 35 row
residuals vanish. The theorem cannot choose a convenient table after seeing
the statement, and it does not assume the desired six field equalities. The
theorem `production_public_residuals_bind_live_statement` proves that this
condition, the maintained arithmetic constraints, and equality of the decoded
and live statements imply all six field equalities.

The maintained Lean project also composes this result with the generic
25-lane `theta` batching and four-coordinate tower-packing proofs. The exact
source locations of all 35 public residuals are proved: row, semantic lane and
base-four slot uniquely identify each residual. If the extracted per-row
`theta` polynomial is identically zero, tower-basis injectivity exposes every
one of those raw residuals and the six-field theorem applies.

The maintained Lean project now proves the algebra after the accepted masked
sumcheck in `V5AcceptedTerminalResidualExtraction.lean`. In particular, it
proves all of the following rather than putting them into one unnamed
assumption:

1. the Rust equality-factor formula agrees with the big-endian 1,024-row
   multilinear selector;
2. those ten row bits select exactly one Boolean trace row;
3. a nonzero 1,024-row table has a nonzero ten-variable multilinear
   polynomial of total degree at most ten;
4. an accepted mixed equation with nonzero `eta` forces the unmasked oracle
   to have zero Boolean sum;
5. helper cancellation at `mu` has at most one field root;
6. a fixed nonzero Boolean table vanishes on at most a `10 / |K|` fraction of
   equality points; and
7. one fixed nonzero 25-lane row polynomial has at most 24 roots in `theta`.

Outside those three separate algebraic events, the fixed trace gives
identically zero per-row `theta` polynomials, which feed directly into the
35-residual and six-public-field theorem. Choosing the nonzero row before
looking at `theta` is explicit, so the theta bound is 24 roots rather than a
union bound over all 1,024 rows.

`V5AcceptedSumcheckSourceBridge.lean` now proves the deterministic ten-round
sumcheck step instead of assuming the mixed-boundary equation as one block.
It records the exact value flow checked by the verifier:

1. round zero checks `p(0) + p(1)` against the supplied initial claim;
2. each later round checks that boundary against the preceding evaluation;
3. each 448-byte message is absorbed with its round byte before its challenge
   is derived;
4. challenge `i` depends on messages zero through `i`, not on later messages
   or openings; and
5. the returned value is the tenth message evaluated at the tenth challenge.

For reference messages derived from one fixed committed polynomial, Lean
proves that a wrong initial claim which nevertheless reaches the authenticated
reference terminal must be repaired in one of the ten rounds. That repair
challenge is a root of a nonzero polynomial of degree at most 27, so one fixed
round has at most 27 repairing field elements. Outside that event, an
authenticated mask sum and authenticated reference terminal give the exact
mixed-boundary equation used by the residual proof. The deterministic record
does not itself prove that dependency order; the source and probability work
listed below must show that the polynomial is fixed before `eta` and each
reference message is fixed before its corresponding round challenge.

This leaves smaller, separately named obligations rather than one catch-all
premise:

- successful Rust execution must project to the modeled ten boundary checks,
  message bytes, challenges, and returned value;
- the mask commitment must authenticate the initial mask sum;
- the commitment/FRI openings must authenticate one fixed oracle and its final
  evaluation;
- Fiat--Shamir must justify conditional challenge randomness for the ten
  adaptive degree-27 events; and
- the production residual rows must supply the low-level range, balance, and
  asset equations. Failure of the last step is now
  `AcceptedArithmeticResidualExtractionFailure`; the final theorem no longer
  accepts `ConstraintsSatisfied` as an unnamed argument.

The one-root helper result and the `10 / |K|` and `24 / |K|` finite-set
results are also not final probability claims. They require source-order
proofs showing, respectively, that the helper is fixed before `mu`, the table
is fixed before the equality point, and the residual rows are fixed before
`theta`, together with the corresponding challenge-distribution argument.
No combined numerical bound is claimed here.

A pinned full-evaluator extraction was attempted. Charon rejected the
resulting standard-library iterator graph with
trait-clause mismatches for `Zip`, `ChunksExactMut`, `IterMut`, and
`Enumerate`. Disabling Charon's final type check produced an LLBC file, but
Aeneas then stopped with an internal type-translation error in Rust's
`Iterator` trait. Treating that unchecked LLBC as proof evidence would be
unsound. The large evaluator therefore remains protected by exact source
hashes and the explicit source-shaped residual model; the decoder and claim
reader are the source-extracted portions.

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
crate::v5_atomic_terminal::claim
```

The generated decoder keeps the statement codec calls external. Their
transparent fixed-width models are in `FunsExternal.lean`; importantly, the
decoder-uniqueness and live-equality theorems do not rely on a cryptographic or
injectivity assumption about those helpers.

## Replay

Build the maintained statement model once, then run:

```bash
cd AspisFormal
NO_DNA=1 lake build AspisFormal.V5AcceptedSumcheckSourceBridge
cd ..

LEAN432_BIN=/path/to/lean-4.32.0 \
AENEAS_LEAN_LIB=/path/to/aeneas-lean432/lib/lean \
  aeneas-verif/v5-public-statement-binding-20260815/replay-lean432.sh
```

The replay verifies the exact production source hashes, compiles the generated
definitions and handwritten proof, rejects proof escapes, and checks that the
public theorems use only Lean/mathlib's standard `propext`,
`Classical.choice`, and `Quot.sound` foundations.

# V5 production relation-transcript source proof

This bundle checks the four-round transcript helper
`replay_real_v5_relation_rounds` from the production V5 verifier.

Charon extracts the production function and Aeneas translates it to Lean.
The pinned translator does not accept the original Rust `for` loops or the
dynamic borrow in the later-root branch.  The extraction-only patch makes two
mechanical changes:

- the fixed `0..4` and `0..2` loops become `while` loops with the same bounds
  and increments; and
- the unchanged later-root branch is moved into a helper called from the same
  position.

The repository's production Rust is not changed.

Pinned identities for this snapshot:

- `v5_cu_probe.rs` Git blob: `ca28d560e44e5e82e689321f32289831c889a0bd`;
- Charon commit: `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`;
- Aeneas commit: `9a30bf93807d8043a1a968b6456eb78747c81cb4`;
- Lean: `v4.32.0`.

## Proved result

`generated_replay_relation_rounds_exact` is a theorem about the complete
Aeneas-generated function, not a fixture.  Under the observation definitions
in `FunsExternal.lean`, every successful execution performs exactly:

- two OOD challenge/absorb/mix sequences in each of four rounds;
- one seven-coefficient relation-sumcheck absorb per round;
- one fold-work check and absorb using `v5_fold_nonces[round]` per round;
- one fold challenge per round; and
- the three later-root absorbs after rounds zero, one, and two.

The proof expands both generated loops through their exact two and four fixed
iterations.  It covers every `ParsedProbeData` value represented by the
generated types.  Its printed axioms are only Lean's standard `propext`,
`Classical.choice`, and `Quot.sound` foundations.

The observation model deliberately erases field values and hash state.  This
bundle proves source call order, indices, and nonce flow.  It does not prove
SHA-256 security, Fiat--Shamir random-oracle security, field decoding, or the
mathematical relation verifier; those are separate repository layers.

`V5TranscriptRelationFinalJoin.lean` connects this exact observation trace to
the maintained byte-complete relation schedule: erasing only the values which
the extraction deliberately cannot observe produces the generated Rust trace
for all four rounds and all four fold nonces.  The same file imports the
independently translated production relation caller and proves alongside that
schedule equality that caller success forces the returned four coefficients
to equal the final polynomial already accepted by FRI.

This joined theorem is not the missing arithmetic proof.  The nested
`verify_v5_relation_stress_with_additive` call is still opaque in the caller
snapshot, so proving that every successful nested execution agrees with the
maintained relation model remains a separate obligation.

## Remaining source boundary

The `for`-to-`while` conversion and helper extraction are visible in
`extraction/v5-relation-replay-while.patch`.  Their equivalence is not a Lean
theorem about Rust compiler semantics.  The generated theorem applies to the
patched extraction tree.  A complete production claim must retain that small
source-transformation boundary unless Charon/Aeneas gains support for the
unchanged spelling.

## Files

- `relation-harness/`: package manifest pointing at the production verifier.
- `extraction/`: exact extraction-only source patch.
- `generated/`: Aeneas output plus explicit observation definitions.
- `proof/V5TranscriptRelationSourceProof.lean`: exact body, inner-loop,
  outer-loop, and complete-helper proofs.
- `proof/V5TranscriptRelationFinalJoin.lean`: exact observable projection to
  the maintained schedule and the production final-polynomial gate.
- `import-normalization/`: a one-line patch applied only to a temporary replay
  copy so two independent generated modules can coexist without changing the
  checked-in Aeneas snapshots.
- `replay-lean432.sh`: checks the source, patch, tool commits, and binary
  hashes; regenerates the Lean; compares it with the reviewed snapshot; and
  recompiles the proof with Lean 4.32.
- `replay-final-join-lean432.sh`: recompiles both generated snapshots, the two
  maintained transcript modules, and the joined theorem without rerunning
  extraction; it also checks and prints the theorem axioms.

## Replay

The replay expects the pinned Charon and Aeneas checkouts and an Aeneas Lean
library compiled with Lean 4.32. `AENEAS_LEAN_PATH` should contain the complete
Lean search path printed by `lake env printenv LEAN_PATH`, including mathlib.

```bash
ASPIS_CHARON_REPO=/path/to/charon-cb50ff16 \
ASPIS_AENEAS_REPO=/path/to/aeneas-9a30bf93 \
AENEAS_LEAN_LIB=/path/to/aeneas-lean432/.lake/build/lib/lean \
AENEAS_LEAN_PATH="$(cd /path/to/aeneas-lean432 && lake env printenv LEAN_PATH)" \
./aeneas-verif/v5-transcript-relation-source-20260820/replay-lean432.sh
```

The smaller final-join replay is useful on a machine that has the Lean/Aeneas
libraries and an existing `AspisFormal` build but not the extraction tools:

```bash
AENEAS_LEAN_LIB=/path/to/aeneas-lean432/.lake/build/lib/lean \
AENEAS_LEAN_PATH="$(cd /path/to/aeneas-lean432 && lake env printenv LEAN_PATH)" \
ASPIS_FORMAL_BUILD_ROOT=/path/to/repository \
./aeneas-verif/v5-transcript-relation-source-20260820/replay-final-join-lean432.sh
```

The raw generated relation caller remains unchanged. During either replay a
temporary copy loses only its unused `ProgramError` discriminant attribute,
because both independently generated modules otherwise request the same Lean
instance name. The replay verifies that this is the only change before it
compiles the joined theorem.

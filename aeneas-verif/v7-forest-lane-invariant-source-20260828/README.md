# V7 eight-lane Pool invariant fast-path source bridge

This focused bundle records the exact source boundary for the default-off
eight-lane Pool CU experiment introduced at production source commit
`86d072be`.  It exists because the optimized terminal path removes two
duplicate 20-level Poseidon reconstructions from Pool code:

1. decoding the selected live lane before verifier CPI; and
2. encoding the verifier-authenticated next lane after verifier CPI.

The byte codec, account identity, state bindings and settlement relation are
not relaxed.  The sole omitted operation is recomputing the active Merkle root
from the persisted index/frontier.  That fact is represented explicitly by
`ProgramOwnedLaneInvariantCapability.Holds`; it is not inferred from account
ownership.

## Exact retained boundary

The translated `hot_decode_projected` source checks all of the following:

- the invariant capability is present and the account image is exactly 768
  bytes;
- `ASL8`, lane version, lane count 8, depth 20 and the 32-byte forest format
  binding;
- the expected nonzero master and exact expected lane;
- `ASPT`, tree version, depth, hash version and digest-encoding version;
- little-endian index and capacity bound;
- canonical M31 decoding of the active root and all 20 frontier digests;
- every inactive frontier node equals its exact empty root; and
- index zero has the exact genesis root.

The Solana owner, writable, signer and lane-PDA checks occur in the production
caller around the pure decoder.  They remain explicit as
`CallerSideSolanaLaneChecks`; this bundle does not misattribute them to the
extracted pure projection.

`valid_strict_encoder_bytes_equal_fast_encoder_bytes` and its converse show
that a valid strict lane and the invariant fast encoder produce the same
768-byte image.  The fast path is fail-closed when the named capability is
absent.

## Exhaustive writer and activation boundary

The hash-pinned production source has exactly three writes to lane account
data:

- eight fresh genesis images during Pool initialization;
- one checked append image after an exact public deposit; and
- one next-lane image after authenticated exact-ASR8 terminal settlement.

Checkpointing reads lanes and does not write them.  Both compact ASQ8 and the
default-off full-ASF8 audit route share the same authenticated terminal
settlement writer.

The translated writer model has exactly the corresponding three constructors.
The strongest preservation theorem is
`translated_production_lane_write_preserves_program_owned_invariant`.  Its
premise is the single explicit inductive capability, with separate
initialization, checked-deposit and authenticated-settlement preservation
fields.

Activation is stricter than Pool ownership:

- successful translated initialization creates only
  `newlyInitializedPda` activation;
- deposit and settlement must consume an already activated predecessor and
  preserve its activation origin; and
- a legacy account could be activated only through an explicit
  `CheckedOneTimeMigrationCertificate` which establishes the strict
  root/frontier fact, checks the canonical target lane PDA and consumes a
  one-shot migration authority.

There is no migration instruction in the pinned production source.  Therefore
fresh initialized lane PDAs are the only production-established activation
route.  A release must either use fresh PDAs or first implement, audit and
prove the separately specified one-time migration.  Existing ownership alone
does not enable the fast path.

## Source relationship and trust boundary

`harness/src/lib.rs` is a pure, fixed-width accepted-source projection of the
hash-pinned production codec and writer decision tree, suitable for Charon and
Aeneas.  `source-audit.sh` pins the relevant production Rust files and audits
the exact three lane-write sites and dispatch routes.  This is not a claim
that Aeneas translated Solana `AccountInfo` or CPI behavior; those caller-side
facts remain outside this focused extraction.

The generated Lean code is transparent except for the standard Rust
`Option<T>` equality template.  The imported `FunsExternal.lean` implements
that equality transparently.  The generated `_Template.lean` retains the
ordinary Aeneas template axiom but is not imported or compiled.

The cryptographic statement that the active root equals reconstruction from
the active frontier is intentionally not proved by this source bundle.  It is
the one named inductive capability that the main mathematical proof must
instantiate for genesis and both production mutations.

## Principal theorems

- `hot_decode_success_requires_capability_and_exact_length`
- `hot_decoder_rejects_missing_program_owned_invariant`
- `valid_strict_encoder_bytes_equal_fast_encoder_bytes`
- `fast_encoder_bytes_are_strict_encoder_bytes`
- `initialization_success_has_exact_source_relation`
- `checked_deposit_success_has_exact_source_relation`
- `authenticated_settlement_success_has_exact_source_relation`
- `translated_production_lane_write_preserves_program_owned_invariant`
- `translated_write_renews_activation`
- `translated_hot_decode_has_complete_activation_boundary`
- `translated_write_to_fast_decode_activation`

Every printed axiom set is a subset of `propext`, `Classical.choice` and
`Quot.sound`.  There is no `sorry`, `admit`, `native_decide`, project-specific
axiom or conclusion-shaped restore function in any compiled source/proof file.

## Focused replay

```sh
./source-audit.sh

CHARON_BIN=/Users/dominic/aeneas-verif/charon/bin/charon \
AENEAS_BIN=/Users/dominic/aeneas-verif/aeneas/bin/aeneas \
./replay-extraction.sh

AENEAS_LEAN_BACKEND=/Users/dominic/aeneas-verif/aeneas/backends/lean \
./replay-lean.sh

./replay-focused-rust.sh
```

The scripts are intentionally focused: no broad regression, devnet, deploy,
push or signing action is performed.

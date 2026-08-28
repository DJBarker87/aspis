# V7 eight-lane Pool invariant fast-path source bridge

This focused bundle records the exact source boundary for the default-off
eight-lane Pool CU experiment introduced at production source commit
`86d072be`, extended by the authenticated verifier-side source port
`a789a9c6`, and extended again by the default-off selected terminal cuts at
`2dae6bea`, `d49af9e3` and `37c6ea1f`.  It exists because the optimized terminal path removes two
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

The verifier-side feature gate additionally requires exactly six distinct,
read-only CPI accounts.  It authenticates the proof under the exact verifier,
the master/checkpoint/lane under the exact Pool, their canonical PDAs and
identities, and the registry/entry under an immutable verifier-release root.
The entry must select the exact Pool, verifier, Tag-73 forest profile, release,
statement version and an active slot.  These checks are represented in the
translated source by `ExactDirectAsq8ReleaseAuthentication`; none of them is
treated as a substitute for the lane invariant capability.

The pinned constants are deliberately audit-fixture values: Pool program
`[0x41; 32]`, registry program `[0x44; 32]`, immutable policy flag one, zero
registry authority and policy binding `[7; 32]`.  They are not mainnet release
identities.  Production activation remains blocked until generated deployment
constants replace them and are pinned by reproducible release evidence.

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

The verifier composition is stricter still:
`translated_direct_asq8_reader_consumes_fresh_pool_invariant` accepts only a
`FreshInitializedVerifierLaneCapability` whose boundary is exactly
`newlyInitializedPda`.  Even complete released Pool/registry authentication is
proved to reject when the separate lane capability is absent.  The current
verifier source does not expose a migration activation path.

## Selected terminal cuts

Three additional CU cuts have separate translated/source boundaries:

- direct ASR8 reuse occurs only after the exact selected verifier program has
  returned exactly 792 bytes and the canonical ASR8 decoder has accepted them;
  `translated_direct_result_success_has_exact_gate` proves that the direct
  path retains all four upstream authentication/canonicality facts and the
  same six material result equalities as statement reconstruction;
- packed public-digest accumulation receives the identical selector and four
  residuals, while `selector_mul_symbolicPack4` proves the exact commutative-
  ring factoring identity used to move one selector multiplication outside
  the fixed four-term pack; and
- binary Copy weights retain every generated endpoint and its order.  The
  translated consumer accepts only exact zero/keep or one/add cases, and
  `specialized_binary_weight_eq_literal` proves skip/add equals the original
  multiplication by a binary weight.  The focused Rust test visits every
  checked-in generated link across both variants and representative full
  20-bit append indices.

The source-shaped harness translates the gates and schedules rather than the
full QM31 terminal evaluator.  The hash-pinned production files and focused
equivalence tests bind those projections to deployed control flow; the
generic Lean ring equalities discharge the arithmetic rewrites.  No cut
changes a transcript, constraint, endpoint, result field or byte codec.

## Source relationship and trust boundary

`harness/src/lib.rs` is a pure, fixed-width accepted-source projection of the
hash-pinned production codec, writer decision tree and verifier release gate,
suitable for Charon and Aeneas.  `source-audit.sh` pins the relevant Pool and
verifier Rust files, the exact three lane-write sites, six-account forwarding,
release constants and dispatch routes.  This is not a claim that Aeneas
translated Solana `AccountInfo`, PDA derivation, `Clock` or CPI behavior; those
runtime facts remain outside this focused extraction and are pinned by the
production source audit.

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
- `direct_asq8_lane_read_success_has_exact_gate_and_capability`
- `translated_direct_asq8_reader_consumes_fresh_pool_invariant`
- `exact_release_authentication_without_lane_invariant_rejected`
- `translated_direct_result_binding_eq_reconstructed`
- `translated_direct_result_success_has_exact_gate`
- `translated_digest_factoring_preserves_exact_schedule`
- `selector_mul_symbolicPack4`
- `translated_link_then_action_success_is_exact`
- `specialized_binary_weight_eq_literal`

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

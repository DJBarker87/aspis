# V7 Registry V2 production-call source composition

This bundle closes the strongest honest composition presently available around
the Registry V2 one-transaction eight-lane Pool call. It changes no production
Rust, proof system, Pool state, wire format, deployment, or transaction.

The principal theorem is
`translated_components_compose_exact_accepted_path` in
`proof/V7RegistryV2ProductionAcceptedPathComposition.lean`. Starting from
successful executions of the independently translated components, it proves a
single exact accepted-path predicate containing:

- literal ASQ8 reconstruction from the authenticated master, retained
  checkpoint, selected lane, request, and candidate afterstate;
- literal validation and canonical 792-byte ASR8 encoding;
- exact Registry V2 caller authentication, selected-verifier result binding,
  same-page or rollover writeback, nullifier creation, custody transition, and
  rejected-transaction rollback inherited from the caller bridge;
- byte identity from the verifier's canonical ASR8 through the caller
  certificate and returned Pool state;
- transaction-local agreement for every 256-bit Registry/Entry/caller field;
- literal loader-v3 Program/ProgramData observations and immutable executable
  SHA certificates for both Registry and selected verifier.

The representation-agreement structures contain finite equalities only. They
do not assert verifier acceptance, cryptographic soundness, writeback, or
rollback. All accepted-state conclusions are derived from successful
translated executions.

## Frozen source and component inventory

The measured one-transaction runtime source is
`7179f7c550fe0461f4251dea5268af73876da91d`. The relevant verifier and Pool
source in this branch is byte-identical to that revision.

| Component | Frozen revision | Role |
|---|---|---|
| Registry V2 one-terminal caller | `883fa397d27e3f4fe28acea7899083479b7affd8` | ASQ8 request, Registry V2 gates, immediate ASR8, atomic writeback/rollback |
| Literal AccountInfo projection | `9a5fd7aec741242b840d934e4eaaeb3c41e6016c` | fixed-width caller correspondence |
| Immutable deployment certificate | `16fed4eec8f9372989a96aa23d7816b7a07bc222` | exact 256-bit fields and loader-v3 certificate roots |
| Current generic Tag-73 caller | `91b6863aa2074ecc82d0f91baaacce525b6fd6dc` | `verify_v7_read_only_with_statement_digest` at source `bcd03b1`; `v7_verifier.rs` is byte-identical through `7179f7` |
| Earlier literal ASQ8 dispatch | `041780f4ef0be98c5b1675df87917046b62b4c2f` | four-account Registry V1 path at `bbb1bd6`; inventoried but not substituted for current Registry V2 |
| Current production codecs | this bundle | `reconstruct_asq8_statement_box_v1` and `emit_result_v1` at the `7179f7` source |

The source hashes for the two current verifier files are:

```text
22f88dc409dbc90bed8eecfbb8ecf0a209bb51313194ae3456ac303e36c1a5f5  programs/aspis-verifier/src/v7_pair_forest_dispatch.rs
06b6f32cf7a75e0a84ef2d7671eb8a6c3e91a61049414288ff682e801834a951  programs/aspis-verifier/src/v7_verifier.rs
```

## Codec source bridge

Charon 0.1.223 extracts the two literal current production roots. Aeneas
`d860ac47-tag73-variantfn-namespace-r1` translates them. The source bridge proves:

- `translated_reconstruction_success_is_exact`: translated reconstruction
  success equals the exact ASF8 statement assembled from authenticated state;
- `translated_emit_success_has_exact_canonical_result`: translated emission
  success implies exact statement/result validation and a canonical
  792-byte ASR8 encoding.

Two unrelated generated namespaces collided when this graph was imported with
the Registry graph. `source-transform/namespace-codec-generated-identifiers.sh`
is a checked Lean-only staging transform. It verifies exact occurrence counts,
then namespaces the generated `ProgramError` and standard `Option` equality
identifiers. It does not alter Rust, control flow, bytes, fields, or any
cryptographic operation.

## Smallest remaining literal source boundary

One boundary still prevents a theorem whose *single premise* is the literal
production entry-point execution from Pool entry through selected Tag-73
verification and settlement:

```text
process_with_clear_return_data
  -> validate ASQ8 / borrow proof AccountInfo data
  -> verify_statement_v1
  -> verify_v7_read_only_with_statement_digest
  -> emit_result_v1
```

Charon extracts the complete current caller. The pinned Aeneas first rejects
the `accounts[0]` projection. The extraction-only `.first()` rewrite in
`source-transform/current-asq8-caller-first-account.patch` passes that point
but then fails returning the nested proof-account data borrow
(`InterpBorrows.ml:2497`). Extracting `verify_statement_v1` separately reaches
the transfer/withdrawal dispatch and fails its mutable-borrow-inside-shared-
borrow joins.

This is a source-tool/borrow-join limitation, not a protocol or cryptographic
failure. It **does block the literal one-root production-call theorem**. It does
not invalidate the independently translated codec, generic Tag-73 caller,
Registry, deployment-certificate, or Pool writeback theorems. This bundle does
not disguise the missing join as an acceptance premise or an opaque axiom.

The smallest next source task is therefore a behavior-preserving extraction
normalization of that one `AccountInfo` lifetime join, followed by a structural
map from the current ASF8 statement/digest and canonical ASR8 types into the
already-green generic Tag-73 caller graph.

## Trust boundary

The explicit boundaries are Solana `AccountInfo` borrow/persistence and CPI
semantics, loader-v3 decoding/PDA derivation, SHA-256, SPL Token behavior,
Charon/Aeneas/compiler provenance, and the Lean kernel. The deployment bundle
already narrows loader/PDA/SHA to named primitive results and proves all
subsequent gates.

The compiled proofs contain no `sorry`, `admit`, `sorryAx`, `native_decide`,
project axiom, or conclusion-shaped acceptance assumption. Archival generated
`*_Template.lean` files are not imported. Every printed theorem uses only a
subset of:

```text
propext
Classical.choice
Quot.sound
```

See `REPLAY-RESULT.md`, `evidence/NUC-RUNS.md`, `evidence/AXIOMS.txt`, and
`extraction/COMMANDS.md` for the focused replay record.

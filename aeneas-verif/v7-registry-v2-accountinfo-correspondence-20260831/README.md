# V7 Registry V2 production AccountInfo correspondence

This focused bundle narrows the remaining source boundary in the Registry V2
one-terminal caller bridge at parent commit
`883fa397d27e3f4fe28acea7899083479b7affd8`. It changes no production Rust,
wire format, cryptography, Pool state or deployment.

## Proved correspondence

Charon/Aeneas translates the literal production helper
`aspis_pool::registry::require_readonly_registry_account` and the exact
Registry V2 codecs. Lean proves:

- `production_readonly_success_iff`: success is exactly owner equality plus
  non-executable, non-writable and non-signer flags;
- `production_readonly_success_iff_projected_account`: the literal
  `AccountInfo` result agrees with the fixed-width `AccountView` used by the
  preceding caller bridge;
- `production_registry_pair_iff_fixed_source_shape`: the literal registry and
  entry accounts jointly agree with their two projected fixed-width account
  views;
- `production_registry_pair_supplies_fixed_account_fields`: literal success
  supplies the exact owner/writable/signer conjuncts consumed by the fixed
  Registry V2 caller theorem;
- exact true/false characterizations of the production 32-byte required-
  binding equality helper.

The projection theorem is deliberately finite and honest. Production keys are
256-bit values while the operational source model uses `u64`; no globally
injective map between those spaces exists. `FixedWidthProjection.ReflectsPair`
therefore requires equality reflection only for each concrete
`account.owner`/`registry_program` pair in the transaction. The theorem never
turns a 64-bit collision into an accepted source equality.

## Literal caller audit

The complete production roots both extract cleanly with Charon 0.1.223:

- generic caller
  `aspis_pool::pair_forest::process_pair_forest_terminal_with_verifier_v1`;
- concrete wrapper
  `aspis_pool::pair_forest::process_pair_forest_terminal_v1`.

The raw artifacts have `has_errors=false`. Current Aeneas cannot honestly
translate either complete caller. The generic and concrete roots stop at the
generic callback's higher-ranked/free lifetime relation. The extraction-only
patch in `toolchain/` specializes the callback and return-data sink to the
exact production callees without changing production Rust behavior. That
passes the lifetime gate and exposes the next, independent limitation: Aeneas
cannot merge the shared `AccountInfo` interior-borrow graph at a control-flow
join (`InterpReduceCollapse.ml:1716`).

This is why the bundle proves the smallest literal production helper and its
fixed-width account projection instead of claiming that the whole
`AccountInfo` caller translated.

## Generated compatibility normalizations

The compiled generated source has three transparent replacements for external
templates:

- the exact 32-byte array `ne` operation for the codecs;
- the readonly helper's `RefCell`, `Rc`, `Pubkey` and Pubkey equality types/
  operations, none of whose interior mutation methods are called by this
  helper;
- an explicit `Aeneas.Std.read_discriminant` at `Std.U32` for
  `PoolV1ProgramError as u32`. This removes an Aeneas-generated namespace
  ambiguity with `ProgramError`'s `isize` discriminant; it is the literal Rust
  cast, not a semantic assumption.

## Remaining explicit boundaries

- the complete production caller's HRTB and shared-`AccountInfo` borrow-join
  translation limitations described above;
- instance-local equality reflection for every additional 256-bit value
  projected into the fixed-width operational caller;
- literal Registry V2 PDA derivation, loader-v3 ProgramData parsing,
  executable SHA-256 and immutable-deployment certificate composition;
- Solana ownership, borrow, CPI, return-data and atomic rollback semantics;
- selected Tag-73 verifier acceptance and the already named cryptographic
  boundaries;
- Charon, Aeneas, the Rust compiler and Lean kernel.

The first boundary is a tooling/source-model boundary, not a reason to trust a
failed translation. The fixed-width whole-caller theorem at the parent commit
and this literal account theorem compose only after the remaining concrete
field projections are supplied.

## Replay

```sh
./source-audit.sh
AENEAS_LEAN_BACKEND=/path/to/aeneas/backends/lean \
LEAN_BIN=/path/to/lean-4.31.0 \
./replay-lean.sh
```

The Lean replay copies the committed modules into a disposable directory,
builds the smallest dependency chain serially, scans every compiled source for
forbidden constructs, and deletes the disposable directory. Exact extraction
commands, hashes, resource use and translator failures are frozen in
`REPLAY-RESULT.txt` and `evidence/`.

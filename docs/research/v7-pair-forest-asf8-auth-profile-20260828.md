# V7 pair-forest full-ASF8 authentication profile (default off)

Date: 2026-08-28

This audit implements a production-inactive verifier component for Variant 1:
one exact 1,880-byte `ASF8` instruction plus the unchanged four read-only
accounts `[proof, master, checkpoint, selected lane]`. It changes no proof
bytes, transcript, hashes, cryptographic relation, production dispatch, or
default feature.

## Trust direction

The component never treats an ASF8 identity field as authenticated merely
because it decoded canonically.

1. `decode_v7_pair_forest_asf8_statement_v1` parses exactly 1,880 canonical
   bytes and rejects trailing data.
2. `authenticate_v7_pair_forest_asf8_accounts_v1` authenticates four distinct,
   read-only, non-signer, non-executable accounts without consulting ASF8.
   The proof owner must be the executing verifier. The Pool program is derived
   from the master owner, must also own checkpoint and lane, and is used to
   rederive the canonical master/checkpoint/lane PDAs. Master, checkpoint, and
   lane codecs are decoded independently.
3. `compare_v7_pair_forest_asf8_to_authenticated_accounts_v1` checks exact
   equality of master/checkpoint/lane identities, deployment domain, asset,
   checkpoint sequence/root, selected output lane, and the complete 800-byte
   account-derived live snapshot.
4. `scan_v7_pair_forest_asf8_proof_wire_v1` independently checks finalized
   proof-account framing, exact body length/frontier count, canonical staged
   proof grammar, and the proof-carried ASJA candidate. Composition requires
   that candidate to equal ASF8 exactly.

ASF8 intentionally has no caller-provided profile, release, or Pool-program
fields. The profile/release are selected only by the compiled verifier
component (`V7_STAGED_PAIR_PROFILE_BINDING` and
`V7_STAGED_PAIR_RELEASE_BINDING`); the Pool program is account-owner-derived.

The component then returns custom error `0x41534638`. It is absent from
`dispatch.rs`, cannot emit ASR8, and cannot accept a proof.

## Focused host evidence

Commands:

```text
CARGO_BUILD_JOBS=2 cargo test -p aspis-verifier asf8 -- --nocapture
CARGO_BUILD_JOBS=2 cargo test --release -p aspis-verifier asf8_host_component_measurement_separates_all_three_phases -- --ignored --nocapture
```

Results:

- four focused ASF8 tests passed; one manual measurement test remained ignored
  in the normal run;
- the canonical profile, separated phase composition, account/statement/proof
  mutations, trailing bytes, counterfeit common owners, and fail-closed result
  were exercised;
- release measurement used a 30,504-byte canonical proof wire, not the small
  frontier fixture.

One release host run (256 iterations) reported:

| Component | Mean host time |
| --- | ---: |
| ASF8 canonical parse (1,880 bytes) | 483 ns |
| Account/PDA authentication (1,344 state bytes) | 14,926 ns |
| Statement/account exact comparison | 43 ns |
| Canonical proof-wire scan (30,504 bytes) | 16,029 ns |
| Full ASF8 composition | 31,738 ns |
| Existing compact ASQ8 composition | 31,260 ns |

These are host wall-clock component observations, not Solana CU and not a
claim that ASF8 is cheaper than ASQ8. They show that the additional canonical
ASF8 parse/comparison is small beside the shared PDA/account and proof-wire
work on this host. The already committed TxV1 sizes remain unchanged: ASF8
adds exactly 1,560 serialized bytes and the maximum withdrawal rollover is
2,569 bytes, leaving 1,527 bytes under the 4,096-byte envelope.

## SBF stack gate and bounded streaming attempt

The first exact bounded build command was:

```text
NO_DNA=1 CARGO_BUILD_JOBS=2 cargo build-sbf --manifest-path programs/aspis-verifier/Cargo.toml --no-default-features --features v7-pair-forest-asq8
```

The compiler completed but emitted unsafe SBF stack diagnostics, so this is a
failed SBF activation gate despite Cargo's zero exit status:

- existing canonical ASF8 decoder frame: 6,464 bytes (2,272 over the 4,096
  offset);
- full ASF8 composed validator frame: 13,696 bytes;
- existing ASQ8 composed validator frame: 11,328 bytes;
- full ASF8 process wrapper frame: 5,760 bytes.

One permitted stack-safe attempt then added
`validate_v7_pair_forest_asf8_streaming_v1`. It heap-lifts the decoded account
objects and validates the fixed ASF8 envelope, late-statement header, live
snapshot, candidate, payment public input, and account equalities as separate
components. The dedicated audit-only feature has no dispatcher arm:

```text
NO_DNA=1 CARGO_BUILD_JOBS=2 cargo build-sbf --manifest-path programs/aspis-verifier/Cargo.toml --no-default-features --features v7-pair-forest-asf8-audit
```

Neither the streaming validator nor its process wrapper produced an SBF stack
diagnostic. The bundle still reports the three uncalled public typed paths:
the generic ASF8 decoder (6,464 bytes), host-style typed ASF8 composition
(8,832 bytes), and existing ASQ8 composition (11,328 bytes). Per the bounded
audit rule, those unrelated/uninvoked frames were not refactored or repeatedly
rebuilt. The activation gate is therefore: wire only the streaming component
in an isolated diagnostic/production route and demonstrate it in LiteSVM;
never wire the typed convenience validator.

This mechanical representation change preserves the exact codec and equality
ledger and does not alter the proof or cryptography.

No LiteSVM transaction was run because reaching this component would require
adding a diagnostic dispatch surface; the task allowed focused SBF/host
component evidence instead.
No network call, signature, transaction submission, deployment, merge, or push
was performed.

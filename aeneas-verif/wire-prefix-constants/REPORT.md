# Source-authentic v5 real-host prefix constants

This bundle connects the constants extracted from the real feature-gated Rust
host to the maintained repaired mode-9 wire inventory.  It authenticates the
6,423-byte real-host prefix and every offset and byte count within that
prefix.  It does **not** prove the serializer, parser, selected-good relation,
PCS/Merkle checks, transcript security, production dispatch, or a release
claim.

## Strongest result

`extracted_prefix_constants_match_repaired_wire` proves that the extracted
Rust offsets land on the maintained semantic segments for:

- the C1 and C2 roots;
- the initial Component-B claim and ten-round sumcheck;
- the point-claim block;
- the three terminal values;
- the inactive claim;
- the five public Fiat--Shamir salts; and
- the zero reserve.

It also proves that:

```text
wirePrefixOffset + extracted V5_REAL_PREFIX_BYTES = atomicContextOffset
11112           + 6423                           = 17535
```

The extracted arithmetic is checked separately before importing the
maintained model.  This avoids treating a mirrored numeral as a
correspondence theorem: the generated `Result Usize` computations, including
checked addition, multiplication, subtraction, and the u8-to-usize cast, are
executed in the kernel for both supported platform widths.

## Extracted values

| Rust constant | Relative value |
| --- | ---: |
| header / C1 root | 23 |
| C2 root | 55 |
| initial claim | 87 |
| sumcheck | 103 |
| sumcheck bytes | 4,480 |
| point claims | 4,583 |
| point-claim bytes | 1,216 |
| terminals | 5,799 |
| terminal bytes | 48 |
| inactive claim | 5,847 |
| public-salt reserve | 5,863 |
| public-salt count / bytes | 5 / 160 |
| zero reserve | 6,023 |
| zero-reserve bytes | 400 |
| total prefix | 6,423 |

The five salts are derived from the extracted four-round arity-4 FRI
constant: two fixed salts plus three later-layer salts.  The extraction
therefore contains a concrete definition of
`aspis_core::circle_fri::FIXED_ARITY4_ROUNDS`; no opaque declaration is used.

## Provenance

- Charon: `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`
- Aeneas: `b59d5188c082f704a418c7cb4e52ad69328002d1`
- Rust: `nightly-2026-06-01`
- generated backend: Lean 4.31
- maintained replay: Lean 4.32
- LLBC: 54 ordered declarations, `has_errors = false`
- LLBC SHA-256:
  `5cfae89b4282ed89b23f97411544a196157beac174c066e5a1942c6ff957cc41`

The LLBC embeds the five owning `aspis-prover` source files byte-for-byte.
Charon records the two cross-crate `aspis-core` source names and spans but
leaves their `contents` fields empty; the replay therefore binds those two
dependency files by frozen SHA-256 and checks the literal
`FIXED_ARITY4_ROUNDS = 4` declaration.  It does not misdescribe absent LLBC
source bodies as embedded bytes.

The complete bound source inventory is:

| Source | SHA-256 |
| --- | --- |
| `crates/aspis-prover/src/v5_real_host_proof.rs` | `691dedfdcfbe4e8570d2501a2c16813f5c7840cc4f64d68046403069c75b7dbc` |
| `crates/aspis-prover/src/v5_mask.rs` | `776023289bd4955b1703bd496e0eaa738b1015977e0f8f8ba19d8121bf90d5a5` |
| `crates/aspis-prover/src/lib.rs` | `91a7ccaa9c0ad591f498abb753f632a01ea5ba2d6b413c010026fb1a17bfd7f1` |
| `crates/aspis-prover/src/v5_spend_messages.rs` | `b7aedef68597b3187896c626c1135b8a1c1eee521125907f01c56175c76afa66` |
| `crates/aspis-prover/src/v5_cu_envelope.rs` | `87ef0a65dd420ac4faa62ff7a1c61290b754528500a06bff7fb8118845f06d91` |
| `crates/aspis-core/src/circle_fri.rs` | `6ce32a64e6e996680592a214cea07d2a982fe26aec8416064e8b0a66d3406289` |
| `crates/aspis-core/src/lib.rs` | `707467acca89d780f713c8dc6274a3be854b95d7ad8224d9530fb9879c3f80a3` |

The Charon roots are the `V5_REAL_PREFIX_*` constants in
`v5_real_host_proof.rs`, with the transitive lane-count and public-salt
constants retained.  The extraction explicitly includes:

```text
aspis_core::circle_fri::FIXED_ARITY4_ROUNDS
```

so the salt count is not conditional on a cross-crate opaque constant.

## Kernel audit

`replay-lean432.sh` performs all of the following from the retained artifacts:

1. verifies the manifest hashes;
2. verifies the LLBC declaration count and `has_errors = false`;
3. compares every embedded owning-crate source file byte-for-byte with the
   workspace, and hash-binds the two cross-crate dependency sources;
4. reconstructs and checks the mechanical Lean-4.31-to-4.32 normalization;
5. rejects `sorry`, `admit`, `native_decide`, `axiom`, `unsafe`,
   `ofReduceBool`, and raised handwritten limits;
6. compiles the generated module, exact arithmetic layer, and maintained
   correspondence layer; and
7. audits all 38 exported theorems.

Every theorem has axiom closure contained in
`{propext, Classical.choice, Quot.sound}`.

## Exact remaining boundary

This bundle closes the constants/layout edge only.  A source-authentic proof
that the real serializer emits these fields in this order, and that the real
verifier parser consumes the same bytes, remains a separate executable
correspondence task.  The broader v5 construction also remains conditional on
its named Component-A, Component-C, transcript, PCS/Merkle, entropy, and
production-dispatch interfaces.

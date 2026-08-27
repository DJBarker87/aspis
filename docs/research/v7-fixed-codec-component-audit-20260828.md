# V7 fixed-QM31 byte-for-CU component experiment

Date: 2026-08-28

Implementation commit: `f4756ede`

Scope: default-off codec and parser experiments for the 641-QM31 fixed section
of Tag-73. This is component evidence only. None of these grammars is selected
by a production profile or reachable from verifier dispatch, and none of the
numbers below is a full-verifier or combined transaction CU projection.

## Exact byte arithmetic

The selected grammar packs all 2,564 M31 limbs as one continuous 31-bit
stream, occupying 9,936 bytes. The experiments preserve the same 641 field
values and split them after the 385 pre-final QM31 values:

| Grammar | Pre-final encoding | Final256 encoding | Fixed bytes | Delta | Maximum proof body | 30 KiB headroom |
| --- | --- | --- | ---: | ---: | ---: | ---: |
| selected | packed | packed | 9,936 | 0 | 30,504 | 216 |
| A | canonical | independently packed | 10,128 | +192 | 30,696 | 24 |
| B | independently packed | canonical | 10,064 | +128 | 30,632 | 88 |
| C | canonical | canonical | 10,256 | +320 | 30,824 | -104 |

For the frozen 197-node-frontier fixture, whose selected body is 30,192
bytes, the corresponding exact lengths are 30,384, 30,320 and 30,512 bytes.
All four fixture bodies need 32 uploads at 960 bytes per upload. At maximum,
A and B need 32 uploads; C needs 33.

The independent packed segments are exactly 5,968 bytes for the first 1,540
limbs and 3,968 bytes for the final 1,024 limbs. Each segment has four padding
bits and its own padding check. Canonical segments use four little-endian
`u32 < P` limbs per QM31.

## Value and parser equivalence

`crates/aspis-core/src/v7_fixed_codec_experiment.rs` implements:

- exact-length parsing for all three grammars;
- canonical-M31 validation for every limb;
- rejection of nonzero padding in either independent packed segment;
- a streaming reader with exact exhaustion checks;
- an inactive full-wire parser which leaves roots, nonces, q16 records, salts
  and both frontiers byte-for-byte unchanged and validates the existing q16
  packed-field canonicality;
- selected-proof transcoders which first parse the selected Tag-73 wire and
  then preserve its entire post-fixed-section tail byte-for-byte.

The focused equivalence test decodes all 641 values through each grammar and
checks both value-for-value equality and equality of the complete 10,256-byte
canonical field image consumed by existing transcript record construction.
Length, canonical-limb, packed-padding and incomplete-reader mutations fail
closed.

This is not yet full transcript equivalence. A secure accepted profile must
give each new grammar a distinct profile/release binding, so the global
Fiat-Shamir transcript and challenges will deliberately differ even though
the field record bytes following the binding are identical. Production
integration therefore needs a parametric transcript/read schedule or a
separate exact driver for the selected new grammar; accepting multiple wire
encodings under the existing binding is a hard reject.

## Static hot-path inventory

The isolated checksum kernel performs the same 641 QM31 additions after
decoding, making the measured difference a parser/decoder difference plus any
mode/account framing effect in the probe.

| Grammar | Streaming packed-byte loads | Canonical QM31 loads |
| --- | ---: | ---: |
| selected | 9,936 | 0 |
| A | 3,968 | 385 |
| B | 5,968 | 256 |
| C | 0 | 641 |

At production integration, canonical final256 can additionally avoid the
current 4,096-byte field-to-byte rewrite in
`decode_and_absorb_final256`; canonical pre-final permits borrowed absorption
only for transcript records that are already contiguous in the wire. Neither
effect is included in this component kernel, and no relation, query, Merkle,
fold or transcript-hash computation is removed here.

## Host component timing

Command:

```text
cargo test -p aspis-core --release --features v7-fixed-codec-experiment \
  host_fixed_codec_component_benchmark -- --ignored --nocapture
```

Each result is 20,000 complete fixed-section decodes on the local host:

| Grammar | ns per 641-QM31 decode | Delta versus selected |
| --- | ---: | ---: |
| selected | 5,087 | 0 |
| A | 8,267 | +3,180 |
| B | 10,348 | +5,261 |
| C | 4,050 | -1,037 |

These are non-CU host timings. In particular, the two mixed readers are
slower in this literal prototype even though A later saves SBF instructions;
host timing is not a substitute for SBF measurement.

## SBF component transaction measurement

The committed snapshot was copied to the task-owned NUC directory
`/home/dombarker/project-offloads/v7-fixed-codec-phasec-VirOk5`. The program
was built with `solana-cargo-build-sbf 2.3.0`, platform-tools v1.48, under the
transient no-swap unit `aspis-v7-fixed-codec-sbf-06` with
`MemoryHigh=8G` and `MemoryMax=12G`:

```text
cargo-build-sbf --manifest-path \
  audit/v7-fixed-codec-probe/program/Cargo.toml
```

The SBF artifact is 26,328 bytes with SHA-256
`2684b035104f484c85af98d7a8e9faa5bc544413d05ab4c5b2a800fd48b8e319`.
The lockfile pins the root-compatible `blake3 1.5.5`, `zeroize 1.8.1`,
`borsh 1.5.7`, `proc-macro-crate 3.2.0` and `indexmap 2.7.1`, because newer
transitive releases require edition-2024 Cargo newer than platform-tools'
Cargo 1.84.

The release LiteSVM harness installs each fixed section in an otherwise
identical read-only account, invokes the same SBF program, checks that all
four modes return the identical 16-byte algebraic checksum, and reports the
whole isolated component transaction cost. The second warm run was unit
`aspis-v7-fixed-codec-harness-02`:

| Grammar | Account bytes | Component transaction CU | Delta versus selected component |
| --- | ---: | ---: | ---: |
| selected | 9,936 | 174,747 | 0 |
| A | 10,128 | 139,127 | -35,620 |
| B | 10,064 | 180,549 | +5,802 |
| C | 10,256 | 56,957 | -117,790 |

The immediately preceding build-and-run produced the exact same four CU
values. These figures include the probe entrypoint, account borrow, canonical
validation, decode, 641 QM31 additions and return-data write. They exclude the
real verifier transcript, semantic relation, query authentication, Merkle
work and Pool caller. They must not be added mechanically to or subtracted
from an existing full-verifier phase ledger.

The component result makes C the only host-positive and strongly SBF-positive
literal decoder, but C exceeds the frozen 30 KiB maximum by 104 bytes. A is
SBF-positive in this component while leaving only 24 bytes of maximum
headroom. B is negative in both host and SBF component measurements. This is
factual ranking data, not a production selection.

## Focused checks

```text
cargo test -p aspis-core --features v7-fixed-codec-experiment \
  v7_fixed_codec_experiment -- --nocapture
# 4 passed, 1 ignored, 0 failed

cargo check --manifest-path audit/v7-fixed-codec-probe/program/Cargo.toml
# PASS

cargo check --manifest-path audit/v7-fixed-codec-probe/harness/Cargo.toml
# PASS
```

No broad regression, network, deployment, Pool/ASQ8/ASR8 edit or production
dispatch change was performed.

## Formal and source obligations before any activation

1. Freeze a new grammar/profile/release binding; never make the selected
   Tag-73 binding accept multiple encodings.
2. Prove that exact parsing returns the same ordered 641 QM31 values and the
   same canonical per-record transcript bytes as the corresponding abstract
   proof fields.
3. Prove every parser error is fail-closed, including exact lengths,
   independent packed padding, canonical `u32 < P`, frontier count and q16
   canonicality.
4. Refactor or duplicate the concrete transcript driver so it consumes the
   selected grammar while leaving every semantic, relation, final-vector,
   gamma/query and Merkle check unchanged.
5. Re-extract the fixed-field parser/read schedule and accepted verifier
   caller with Charon/Aeneas, then reconnect the K1 parsed-proof/profile
   binding. The existing algebraic and proximity theorems require a codec
   equivalence instantiation, not a changed security theorem.
6. Only after a production-inactive full verifier profile exists, measure its
   component checkpoints and full transaction. The isolated values in this
   note do not establish a net full-verifier CU saving.

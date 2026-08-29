# Pool V1 selected-verifier profile: frozen Tag-73 read-only payment

Date: 25 August 2026

Status: P3f source/profile slice implemented behind the opt-in
`v7-pool-dispatch-profile` feature. Host acceptance and substitution tests pass.
The single authorized local-SVM attempt did not enter the handler: the loader
returned `UnsupportedProgramId` / `Program is not deployed`, so no CU or ASVS
success result exists. The four SBF stack-frame violations from that candidate
have since been removed and a fresh opt-in SBF build passes; a new SVM result,
Pool atomic composition and deployment remain open.

## Exact scope

This profile exposes the already-frozen Tag-73 verifier through the P3d/P3e
`ASVQ` to `ASVS` contract. It changes no proof bytes, transcript input,
frontier grammar, work threshold, arithmetic, Merkle check or terminal check.
It calls the existing
`verify_v7_read_only_with_statement_digest(hash, proof, frontier_nodes,
program_id, release_binding, attempt_id, statement, statement_digest,
check_pow)` function.

The relation is exactly the current same-private-path
`AtomicPaymentStatementV4` relation. It is **not** the future Pool V1
historical-anchor relation, does not prove append-only Pool output persistence,
does not prove vault conservation or withdrawal semantics, and is not the
future 1-to-2 P4 relation. The `PrivateTransfer` historical-envelope fields in
this profile authenticate transport context only; they do not upgrade the
underlying proof relation.

The handler accepts no Pool account and performs no account write. It emits
return data only after complete proof acceptance.

## Profile and release identity

The exact profile-binding preimage, with no terminator or newline, is:

```text
aspis:pool-v1:verifier-profile:tag73-read-only-atomic-payment-v4:asvq-v1
```

Its SHA-256 profile binding is:

```text
34992c192aecf5262ad2a78f5c7e075c81673f5ca38eec227841f7278a2bc1c1
```

The accepted frozen Tag-73 release binding is:

```text
7ac8fe92c3f4919972d65d0b59a7898ed1005cb4016fdb1f3daff0aebb49a0f9
```

The profile requires the full-C2, 203-frontier-node, all-work-checked wire and
an exact 30,504-byte proof body. The frozen accepted proof used by the focused
integration test has raw SHA-256:

```text
e8e15ce268447b92ac1344292bc879dcb0bf7534621ce077d8790097975dcecb
```

## Canonical payload

`ASVQ` is the frozen 384-byte P3d binding prefix followed by this exact
392-byte profile payload. The complete request is therefore 776 bytes. All
integers are little-endian.

| Offset | Bytes | Field | Required value |
| ---: | ---: | --- | --- |
| 0 | 4 | profile magic | `A7P1` |
| 4 | 1 | profile version | `1` |
| 5 | 1 | proof source | `1` = sealed exact-size `ASPU` account |
| 6 | 1 | work policy | `1` = check every frozen work witness |
| 7 | 1 | atomic statement version | `4` |
| 8 | 2 | frontier-node count | `203` |
| 10 | 2 | reserved | all zero |
| 12 | 4 | proof-body length | `30,504` |
| 16 | 32 | proof-body digest | raw SHA-256 of the declared body |
| 48 | 32 | verifier program | actual executing verifier program id |
| 80 | 32 | release binding | exact frozen Tag-73 release above |
| 112 | 32 | attempt id | exact proof-account public key |
| 144 | 32 | atomic statement digest | derived from the exact 216 bytes below |
| 176 | 216 | `AtomicPaymentStatementV4` | exact canonical encoding |

The embedded 216-byte atomic statement is:

| Offset | Bytes | Field |
| ---: | ---: | --- |
| 0 | 1 | version `4` |
| 1 | 1 | tree depth `20` |
| 2 | 6 | reserved zero |
| 8 | 32 | pool key |
| 40 | 8 | sequence |
| 48 | 32 | current anchor, eight canonical M31 limbs |
| 80 | 32 | nullifier, eight canonical M31 limbs |
| 112 | 32 | output commitment, eight canonical M31 limbs |
| 144 | 32 | output anchor, eight canonical M31 limbs |
| 176 | 4 | canonical M31 asset id |
| 180 | 4 | fee |
| 184 | 32 | deployment domain |

The inner atomic statement digest is
`SHA256("aspis/atomic-payment-statement/v4" || canonical_statement_216)`.
This is distinct from bytes 248..280 of the outer 384-byte ASVQ prefix: that
outer field is the P3d domain-separated digest of the complete 392-byte
profile payload, selected profile/release, versions and payload length. The
selected verifier recomputes both digests from bytes; neither is accepted as
an independent caller claim.

## Proof account and exact checks

The sole instruction account is the proof account. It must be owned by the
currently executing verifier, read-only, nonsigning and nonexecutable, with
exact data length 30,544 bytes:

```text
ASPU || 30504_u32_le || zeroed_upload_authority[32] || proof_body[30504]
```

The generic Pool planner permits lifecycle-compatible trailing allocation,
but this selected profile deliberately does not: any byte after the declared
30,504-byte body is rejected as noncanonical profile framing. The handler
recomputes raw SHA-256 of the body and matches it against both duplicated
payload and outer-binding fields. It also checks the proof key equals both the
outer proof-account binding and the embedded attempt id.

The handler rejects wrong/zero required identities, changed profile or
release, mismatched duplicated program/release/attempt/proof fields, any
changed atomic statement or digest, a frontier other than 203, disabled work
checks, noncanonical field limbs, malformed/unsealed/overallocated proof data,
extra accounts, instruction trailing bytes and any verifier error. Exact
`ASVS` (384 bytes, success code `0x41530001`) is set only after the frozen
verifier returns success.

The production dispatcher recognizes the existing four-byte `ASVQ`
discriminator rather than allocating a numeric lifecycle tag. A length gate
keeps the historical 169-byte numeric tag-65 wire disjoint. The route and Pool
statement module are compiled only with `v7-pool-dispatch-profile`; the frozen
existing Tag-73 build does not enable that feature.

## Root-history SBF stack closure

The failed candidate build linked four host/reference root-history functions
that returned or copied an 8 KiB value by value. The emitted frames were:

- `RootHistoryPageV1::new`: 16,448 bytes;
- `RootHistoryPageV1::genesis`: 16,512 bytes;
- `RootHistoryPageV1::encode`: 8,320 bytes; and
- `RootHistoryPageV1::decode`: 16,640 bytes.

The account format remains exactly 8,256 bytes. The reference value model and
its by-value API remain available on the host, while the SBF-safe interface is
the checked in-place slice path that decodes one 32-byte digest at a time. The
Tag-73 verifier does not otherwise consume root-history state. No heap, unsafe
code, account-layout change, digest change or append-order change was
introduced. Focused host tests passed 7/7, including exact wire equality,
canonical-unused-root error priority and fail-without-write behavior.

The single NUC build ran under an 8 GiB `MemoryMax`, zero-swap systemd cgroup
with `NO_DNA=1 CARGO_BUILD_JOBS=2`. `cargo-build-sbf` 2.3.0, platform-tools
1.48 and SBF Rust 1.84.1 completed with exit 0 and zero stack-frame/error
lines. `/usr/bin/time -v` recorded 559,284 KiB maximum RSS and zero swaps. The
resulting `aspis_verifier.so` is 1,169,992 bytes with SHA-256
`83eb614e4525771c343213d647f6bd94adb80cc5e22325dd10f32b7d64316e66`.
The 21,151-byte build log has SHA-256
`6c9b2c1ae9cf432b44dbb73a52ebc425f55e7be9cb75237c5de5738d4b690d15`.
No simulation, deployment or transaction followed this build.

## Remaining gates

- The one authorized SVM attempt is frozen in
  `results/spend/v7-devnet-20260825-fullc2/v7-pool-dispatch-profile-p3f-svm.json`.
  It failed at loader/program-cache dispatch before handler execution, so the
  P3f CU gate is **not measured**. The genesis audit found the expected
  executable program and ProgramData accounts. The four stack diagnostics are
  now closed by the successful build above, but Agave's original log also
  covers delay-visibility and closed-cache states, so that fix alone does not
  retroactively prove the unique cause of the failed attempt. The last frozen
  production Tag-73
  simulation consumed 1,258,013 CU, leaving only 41,987 CU below 1.3M. P3f adds
  raw SHA-256 over 30,504 proof bytes, the 392-byte outer
  payload digest, the 208-byte envelope digest, the 216-byte atomic-statement
  digest, canonical/duplicate checks, CPI and return-data overhead.
- Authenticate the selected executable through the final registry governance
  and upgrade policy.
- Compose authenticated `ASVS` evidence atomically with the future relation's
  nullifier, tree/history and vault transition. This same-path profile is not
  a substitute for that future proof relation.
- Retain SHA-256/syscall correctness, Solana CPI/return-data authenticity and
  Rust-to-formal source refinement as explicit external boundaries.

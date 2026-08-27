# V7 sealed proof-body digest cache V1

Date: 2026-08-28

Implementation base: `041780f4ef0be98c5b1675df87917046b62b4c2f`

Status: default-off lifecycle implementation; no production dispatch, Pool,
ASQ8, proof grammar or cryptographic verifier is changed.

## Exact inactive format

The opt-in Cargo feature is `sealed-proof-digest-cache-v1`. The existing
unsealed upload remains byte-for-byte unchanged:

| Offset | Bytes | Unsealed `ASPU` |
| ---: | ---: | --- |
| 0 | 4 | `ASPU` |
| 4 | 4 | proof-body length, `u32` little-endian |
| 8 | 32 | upload authority |
| 40 | declared length | proof body |

The inactive finalizer accepts only an exact-size `ASPU` account and produces:

| Offset | Bytes | Sealed digest V1 `ASD1` |
| ---: | ---: | --- |
| 0 | 4 | `ASD1` |
| 4 | 4 | unchanged proof-body length |
| 8 | 32 | raw SHA-256 of exactly the declared proof body |
| 40 | declared length | unchanged proof body |

Consequently the account and proof-body byte costs are both exactly zero. The
new lifecycle path is not routed from a wire tag, and the current verifier does
not consume `ASD1`.

## Executable invariants

`finalize_proof_with_body_digest_v1_and_hash` checks program ownership,
writability, non-executable account state, upload-authority signature and key,
`ASPU` magic, and exact `40 + declared_length == account_data_length` before
the first write. It hashes the single exact body slice, writes the digest, and
writes `ASD1` last. There is no fallible operation after the first write.

Every existing mutator remains `ASPU`-specific. Focused tests show that upload,
reinitialization, legacy finalization and repeated versioned finalization all
reject an `ASD1` image without changing it.

`validate_readonly_sealed_proof_body_digest_v1` additionally requires the
consumer account to be verifier-owned, read-only, non-signer and
non-executable. It checks exact framing, expected declared length and expected
cached digest without rehashing the body. This is the intended hot-path API.

`audit_sealed_proof_body_digest_v1` is a rehashing replay/test helper. It
rejects stale body bytes, stale cached digest bytes, alternate magic and
trailing data. It is deliberately not the CU-saving hot path.

## Exact formal and Rust-to-Lean obligations before activation

A focused Charon/Aeneas bundle must connect translated production source to
the following facts, without replacing any of them by a conclusion-shaped
premise:

1. Successful finalization starts from `ASPU`, an exact declared body range,
   the runtime program owner, a writable non-executable proof account, and the
   exact signing authority stored at bytes 8 through 39.
2. The hash callback receives the singleton slice list containing precisely
   `data[40..40+declared_length]`, with no header or trailing bytes.
3. Successful finalization preserves the account length, declared length and
   every proof-body byte; it changes only bytes 8 through 39 to the callback
   result and bytes 0 through 3 to `ASD1`.
4. Every error before hashing or sealing leaves the complete account image
   unchanged. The two post-hash writes cannot fail, and `ASD1` is written last.
5. `init_proof`, `upload_chunk`, legacy `finalize_proof`, and the versioned
   finalizer accept no `ASD1` input. Any activated close path must either gain
   its own proved `ASD1` case or remain explicitly unavailable.
6. Successful hot-path validation implies exact `ASD1` magic, exact account
   length, exact expected body length, exact expected digest, verifier program
   ownership, and read-only/non-signer/non-executable account flags.
7. The downstream verifier consumes only the returned body bounds and checks
   the cached digest against the already authenticated request binding before
   proof acceptance. It must not silently fall back to legacy `ASPU` framing.

The explicit external boundaries are Solana's enforcement of account owner and
read-only metadata, persistence/rollback of program-owned account writes, and
the SHA-256 syscall equation for the callback. The SHA boundary must state the
raw one-slice convention used by the frozen proof-body binding.

At the Lean lifecycle level, the bridge needs a state-transition theorem of
the form:

```text
successful ASD1 finalization
  -> exact old ASPU authority authentication
  -> cached_digest = SHA256(exact declared body)
  -> body/length preserved
  -> all lifecycle mutators reject the resulting image
```

The consumer composition theorem must then use program ownership plus
read-only execution to carry that equality from finalization to verification.
It must not assume arbitrary byte arrays with an `ASD1` prefix are immutable.

No CU reduction is claimed by this implementation. The finalization cost and
the terminal-transaction delta require an SBF measurement after an actual
consumer dispatch is integrated.

# v5 root-absorb input correspondence

Status: the deterministic input to each root absorption is source-authentic and
kernel-checked. This does not prove the hash function, random-oracle model, or
the state transition implemented by `Transcript::absorb`.

## Closed chain

The feature-gated verifier now computes each root absorption input in a pure,
inlined helper used by the real transcript call:

- round root: label `12`, record `layer || root || public_fs_salt` (65 bytes);
- C2 root: label `13`, record `root || public_fs_salt` (64 bytes).

Charon/Aeneas extracts both helpers and both label constants. Lean 4.32 proves
their exact labels and record bytes for arbitrary roots and salts, and proves
the two labels are distinct. The account-level composition theorem additionally
ties the helper inputs to the actual 6,423-byte prefix parser, the five public
salt windows, the five private root windows, and the C1/C2 prefix/private-root
equality check.

Strongest files:

- `proof/V5TranscriptAbsorbInputProof.lean`
- `../v5-transcript-records/proof/V5TranscriptPrefixCompositionProof.lean`

All exported theorem closures are contained in
`{propext, Classical.choice, Quot.sound}`.

## Frozen artifacts

- verifier source SHA-256:
  `213eb050c6cb5b6bb89ae02419c1efebe280fd51871755b37abf2fe56601e800`
- LLBC SHA-256:
  `7254081d55e5c632080717bf120acbce828bd40e9176700bb121cae3b4fb3467`
- raw Aeneas Lean SHA-256:
  `74e8b97f8be09de16876c2397904c846c337ac443d8d1f6aa32e6b3cb912f8ea`
- normalized generated module SHA-256:
  `999c9f6e19d52e9a08157969fdccb563f5e748c337da5be179760afcad3a211f`
- proof SHA-256:
  `ad838cf516b2362ce6761b0fc766de261702b0e2f0fe91227d8a4176ff795112`

The LLBC-embedded `v5_cu_probe.rs` bytes equal the source hash above. Charon
reports `has_errors = false`.

Pinned tools:

- Charon `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`
- Aeneas `b59d5188c082f704a418c7cb4e52ad69328002d1`
- Rust `nightly-2026-06-01`
- proof replay: Lean `4.32.0`

## Exact extraction

```sh
cd programs/aspis-verifier
CARGO_TARGET_DIR=/private/tmp/aspis-v5-transcript-absorb-charon-target \
RUSTUP_TOOLCHAIN=nightly-2026-06-01 \
/private/tmp/aspis-aeneas-tools.aTcyie/charon/bin/charon cargo \
  --preset=aeneas \
  --sysroot=default \
  --start-from='crate::v5_cu_probe::real_v5_round_root_absorb_input,crate::v5_cu_probe::real_v5_c2_root_absorb_input' \
  --include='aspis_core::transcript::label::M31_CIRCLE_ROUND_ROOT' \
  --include='aspis_core::transcript::label::M31_CIRCLE_C2_ROOT' \
  --dest-file="$PWD/../../aeneas-verif/v5-transcript-absorb-input/llbc/v5_transcript_absorb_input.llbc" \
  -- --release --locked -p aspis-verifier --features v5-cu-probe,no-entrypoint
```

The Aeneas command is the standard pinned Lean backend invocation with
`-abort-on-error -warnings-as-errors`; the raw output is retained in
`generated-raw/`.

## Exact remaining boundary

The verifier's `absorb_real_v5_round_root` and `absorb_real_v5_c2_root` call
`Transcript::absorb` with the proved pair. What remains outside this result is:

1. source-authentic semantics for the stored `HashFn` closure and transcript
   state transition;
2. the cross-call order through intervening Fiat-Shamir challenges;
3. SHA/hash-as-random-oracle and Merkle/PCS security assumptions.

No theorem here claims any of those boundaries are discharged.

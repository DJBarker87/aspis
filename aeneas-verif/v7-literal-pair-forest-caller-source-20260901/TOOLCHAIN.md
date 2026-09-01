# Pinned toolchain

Source revision: `309b9c73353366a32671901be64cf8386404fd89`

Linux host:

`Linux nuc 6.8.0-110-generic #110-Ubuntu SMP PREEMPT_DYNAMIC Thu Mar 19 15:09:20 UTC 2026 x86_64`

Tools:

- Charon `0.1.223`, Rust toolchain `nightly-2026-06-01`, binary SHA-256
  `b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c`;
- Aeneas `d860ac47-tag73-looparity-shared-index-r1`, patched tree
  `f20adbb48524bea486594d0a404dc0a40805a86b`, binary SHA-256
  `7c8d3b918ba45ad7bb0008efe95733e72953007349d531a46e13215cc6c098bf`;
- Lean `4.31.0` commit `68218e876d2a38b1985b8590fff244a83c321783`,
  binary SHA-256
  `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`;
- Cargo `1.94.1 (29ea6fb6a 2026-03-24)`;
- rustc `1.94.1 (e408947bf 2026-03-25)`.

The only LLBC metadata rewrite is
`toolchain/rename_m31_constructor.py`, SHA-256
`1dfc4f7984e9c30f85a5a813cb6bfc4f70661003f88192c7b548af13eeec7197`.
It asserts that exactly one function has the Rust name
`aspis_core::field::M31` and changes only that declaration's Lean rename to
`M31_ctor`.

The accepted full-caller Charon command and its exact remaining opacities are
reproduced verbatim by `replay-extraction-nuc.sh`. The earlier opaque-exact-six
profile remains frozen in
`evidence/logs/frozen-aspis-v7-literal-metadata-charon-r2.log`; the transparent
exact-six profile is recorded in `REPLAY-RESULT.txt` and its LLBC is frozen
under `extraction/`.

The exact-six source closure adds three pinned extraction components:

- reachable-domain-equivalent length preflight, SHA-256
  `169f7309e092400f034366db40c987d25dbe8c0c0edd398b44431f5f94f302df`;
- identity shared-slice reborrow pass, SHA-256
  `0e7a1de83e485a650f830c787f6dbb7beef8fa1e652b938e0907d5eb50b210fd`;
- immutable single-element shared-slice index exception, SHA-256
  `543b5de2bbe9c04995364b8ac4497581582fb471416fd4c3de49d72fe42b3052`.

`toolchain/build-aeneas-shared-index-r1.sh` starts from Aeneas commit
`d860ac47ed548d3da6d799afc013779ce470516c`, validates every inherited patch,
applies the two new patches, and asserts the exact patched tree, version and
static-binary digest above. Its frozen build used Docker image
`sha256:ef96e46342a4159b6a62663e1ff5474a5f5deaf260daf08ea7b0963974418db7`:

- unit `aspis-v7-aeneas-shared-index-build-r1.service`;
- invocation `ba6f6b9c762e420099e51ad2374ee091`;
- wall `54.20 s`;
- host-wrapper peak RSS `43,472 KiB`;
- swap `0` (host High 6 GiB / Max 8 GiB; container memory+swap 8 GiB).

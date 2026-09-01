# Pinned toolchain

Source revision: `309b9c73353366a32671901be64cf8386404fd89`

Linux host:

`Linux nuc 6.8.0-110-generic #110-Ubuntu SMP PREEMPT_DYNAMIC Thu Mar 19 15:09:20 UTC 2026 x86_64`

Tools:

- Charon `0.1.223`, Rust toolchain `nightly-2026-06-01`, binary SHA-256
  `b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c`;
- Aeneas `d860ac47-tag73-looparity-r1`, binary SHA-256
  `7a6633fbb01fad506336c1a1ef54382924d261fe0bf4ac1a8c8f119e90462a4a`;
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

The accepted full-caller Charon command and all opacities are reproduced
verbatim by `replay-extraction-nuc.sh` and frozen in
`evidence/logs/frozen-aspis-v7-literal-metadata-charon-r2.log`.

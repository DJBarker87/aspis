# Toolchain pins

- Production source: `cee5947cbd5929a2be96d8f7ec29728afec2d3dd`
- Charon: `0.1.223`, repository commit
  `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`, Linux binary SHA-256
  `b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c`
- Aeneas: pinned `aeneas-d860-v6-linux` binary SHA-256
  `c8dbc1f076bcbacf3493be46f7be669051c60b206ca00a6f0abf6df07b7ce50b`
- Aeneas Lean backend: Lean `v4.31.0`
- Kernel capstone: Lean `v4.32.0`, mathlib `v4.32.0`
  (`81a5d257c8e410db227a6665ed08f64fea08e997` in the locked manifest)

All NUC commands ran as task-owned user scopes with `MemoryHigh=22G`,
`MemoryMax=28G`, and `MemorySwapMax=0`.

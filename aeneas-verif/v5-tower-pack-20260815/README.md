# Release Rust proof for four-value tower packing

This package proves one narrow fact used by the V5 constraint checks.

The release Rust function `qm31_pack_base4` is extracted from the pinned
`aspis-core` source in release mode with Charon and translated to Lean with
Aeneas.  For every four canonical M31 values supplied as base-field QM31
values, Lean proves that the function returns those values in the exact
`(c0.a,c0.b,c1.a,c1.b)` order.  The result is then connected to the concrete
`(1,i,u,i*u)` basis of the maintained QM31 model.  The basis packing is
therefore injective: a zero packed value means all four underlying M31 values
are zero.

This proof does not by itself show that every production caller supplies the
intended residuals or that the row selector chooses the intended row.  Those
are separate source-connection obligations.

The replay script checks the pinned Rust source, harness, Charon and Aeneas
revisions, regenerates the translated definitions, compares them with the
checked copies, and builds the Lean proof with Lean 4.32.0.

```bash
ASPIS_CHARON_REPO=/path/to/pinned/charon \
ASPIS_AENEAS_REPO=/path/to/pinned/aeneas \
AENEAS_LEAN_LIB=/path/to/aeneas/lean/library \
./aeneas-verif/v5-tower-pack-20260815/replay-lean432.sh
```

The source tree is not patched or modified during replay.

# Toolchain pins

- Charon `0.1.223`
  - SHA-256: `b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c`
- Aeneas `d860ac47-tag73-variantfn-namespace-r1`
  - SHA-256: `017fc5685a79d4aa3aa19f9529d57fdf167c1387c9b1fee63a254994f5ff9d5a`
- Lean `4.31.0`
- Aeneas Lean backend: source tree paired with Aeneas commit `d860ac47`

The `M31_ctor` metadata rewrite is namespace disambiguation only. Its script
asserts that exactly one `aspis_core::field::M31` function declaration is
renamed and never edits a body, type, operand, or control-flow edge.

# V5 deployed Merkle source extraction

This directory records a successful Charon/Aeneas extraction of the complete
V5 private-opening call graph from the source commit used for the mainnet
program. It does not modify the program source and it does not rebuild the SBF
binary.

The source identity is commit
`06788d44d30ea8cbd391899dddaf6f0acc6e4a3f`. The four extracted source files
have these SHA-256 hashes:

| File | SHA-256 |
|---|---|
| `crates/aspis-core/src/merkle.rs` | `76aa94ce9db033715c04e42effe4fe67807b7a2409dcae6595332be8f1cf9747` |
| `crates/aspis-core/src/state_only_private_openings.rs` | `178968bf12967eead324f07e8e0047c5e018874998540e103afad2dcea33cfdb` |
| `crates/aspis-core/src/state_only_private_merkle.rs` | `f0edc31d07d30f5b19fcaf872fba18678d13d1ba5fac1199f1f4d2be74c74f9b` |
| `programs/aspis-verifier/src/v5_private_openings.rs` | `916c14930d419bc0cd794a3d1e01c4e45fea9f4dbbc1f44f89f71caf3ff63c49` |

`source-adapter.patch` and `immediate-return-adapter.patch` are
extraction-only rewrites. They fix the hash backend to one opaque call, rewrite
unsupported iterator and loop shapes, and unroll the fixed five-section
driver. The second patch replaces the first patch's provisional failure flag
with recursive helpers that stop before hashing an incomplete radix-four
group. This preserves the deployed verifier's first-error hash-call prefix;
on success it also returns the same scratch vectors. Scratch contents after a
rejected call are intentionally outside the claimed observation because the
production caller returns the error without reading them.

The patched Rust type-checks. Charon then reaches
`verify_v5_private_openings` and Aeneas emits complete definitions for the
parser, topology constructor, leaf hashing, radix-four and binary-cap
authentication, the five helper calls, returned remainder, and trailing-byte
check. Aeneas emitted no partial function bodies.

The only opaque cryptographic operation is `merkle.fixed_hashv`. Any later
proof must take as an explicit premise that it equals Solana `hashv` (SHA-256)
over the concatenation of the exact ordered slices. This package makes no
collision, preimage, or random-oracle claim.

## What this does not prove

This is a complete extraction artifact, not the final source-equality proof.
`AspisFormal/V5MerkleSourceAdapter.lean` proves the generic control-flow
lemma: the loop-shaped and recursive scans have the same result and ordered
hash-call prefix, and successful runs have the same scratch vectors and
frontier position. It explicitly names, but does not assume or discharge, the
two remaining code connections: original deployed LLBC to the loop model, and
generated Aeneas helpers to the recursive model. The generated definitions
must then be connected to:

- `VerifyStateOnlyPrivateOpeningWithTopologySourceEquality`;
- `VerifyV5DriverCompositionSourceEquality`.

Until those proofs exist, the repository must not say that the deployed Rust
Merkle verifier has been proved equal to the mathematical model. Concrete Rust
tests support the rewrites, but tests do not replace that universal proof.

## Tool versions

- Charon: `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`
- Aeneas base: `b59d5188c082f704a418c7cb4e52ad69328002d1`
- Aeneas extraction extensions: `b4e0f598`, `156a8d23`, `7c8dc061`,
  `d5cb4d05`, `b49f69d8`, `35b05b92`

Run `replay-extraction.sh` with `CHARON_BIN` and `AENEAS_BIN` pointing to
those builds. The script checks the source identity, checks and applies the
adapter, type-checks it, and requires a complete Aeneas extraction.

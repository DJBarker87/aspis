# aspis-core

`no_std`, byte-exact verifier core shared by the host and the SBF program:
field tower, SHA-256 Fiat–Shamir transcript, circle-domain parser and fold
arithmetic, Merkle openings, sumcheck wires, and the masking algebra. Every
byte the on-chain verifier consumes is produced and checked by this crate
identically on both targets.

Concept-to-file index: [docs/code-map.md](../../docs/code-map.md).

# V7 one-transaction Linux SBF derivation

The capped `r5` run built the exact `da77d5f5` Pool and verifier from two
independent source exports. All four build commands exited zero, each pair of
SBFs was byte-identical, peak cgroup memory was 2,257,649,664 bytes, and swap
remained zero.

The derived Linux x86_64/platform-tools-v1.48 identities are:

| program | bytes | SHA-256 |
|---|---:|---|
| atomic-marker Pool | 525,888 | `82606a25f00fd683b06186cdaae519b52c793d9a2f16f9d3f7c40c2b241685c2` |
| Tag-73 verifier | 1,812,264 | `c43960303f2d67606362dc09d74f3a7983dcfcbe0665984a385a0efa7ddc5e47` |

The harness then exited one because it still required the historical
Darwin-built verifier (`4ee9...`, 1,700,384 bytes). The difference is not
hidden: both ELFs have the same entry point and identical `.rodata`, while the
Linux build has a larger `.text` section. The historical artifact remains
frozen as historical runtime/CU evidence; it is not relabelled as a Linux
reproduction.

During `r5` the audit also established that `cargo +solana` reads Cargo's
legacy `6f17...` registry namespace independently of host Cargo's `1949...`
namespace. The complete 186-package/399-index-entry SBF namespace was frozen
after the run. Therefore `r5` derives the Linux identities but is not the final
provenance-complete release replay. One corrected replay must authenticate both
namespaces before and after building and reproduce the identities above.

No Agave lifecycle, CU measurement, public RPC simulation, signing,
submission or deployment occurred in this run.

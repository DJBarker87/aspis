# V7 deterministic TxV1 Agave fixture audit

This directory records the offline result for the exact eleven-case
one-transaction lifecycle bundle generated from the atomic marker lifecycle
source at `da77d5f5a22681200cceec8e90fc69ac2cc81ad8`.

Two independent optimized generator executions produced byte-identical
`bundle.json` files and byte-identical complete template checksum inventories.
The offline validator checked all 44 files, every content-addressed account,
all canonical 320-byte ASQ8 requests, the exact eleven-case set, the frozen
source trees, and rollback-required metadata for every negative case.

The wallet's real zero-signature TxV1 preflight accepted all eleven inputs.
The four distinct packet shapes are 833, 866, 998 and 1,031 bytes, each with
one required signature and at least 3,065 bytes of headroom below 4,096.

Marker coverage is deliberate:

- seven cases start from an absent/zero-lamport System-owned marker;
- three start from a one-lamport dusted System-owned marker and require the
  Allocate+Assign path;
- replay starts from the exact consumed Pool-owned marker;
- malformed proof, mutated proof and failed withdrawal CPI all require exact
  outer-transaction rollback metadata after marker reservation can occur.

This is not Agave execution evidence. The prior Pool SBF hash is invalid for
the new marker-creation source, and no fresh SBF build was run locally. The
template therefore carries a null Pool SBF binding and the executable runner
refuses it. The exact remaining prerequisite is a capped Linux dual SBF build
from `da77d5f5`, followed by deterministic template materialization against
those exact Pool/verifier binaries (or an equivalent regeneration with
`--pool-sbf`) and Agave 4.2+ execution of all eleven cases. LiteSVM results and
component-CU sums are not substituted.

No key was loaded. Nothing was signed, submitted, deployed or sent to a
public cluster.

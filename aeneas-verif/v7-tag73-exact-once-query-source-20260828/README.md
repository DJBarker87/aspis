# Tag-73 deferred query exact-once source bridge

This bundle pins the selected verifier source revision
`8178d3de1d24d7a3a0102739cb63aca8d7a125a8` and bridges its deferred
canonical query path to ordinary-kernel Lean proofs.  It does not modify
production Rust, wire data, cryptography, transcript order, or a release
profile.

## Proven result

`AspisFormal/K1/V7Tag73ExactOnceQueryConsumerBridge.lean` proves:

- the deferred query domain is `Fin 16 × (Fin 104 ⊕ Fin 48)`;
- its cardinality is exactly 2,432 limbs;
- the canonical sixteen-ordinal schedule visits every query limb exactly
  once (a `List.count = 1` theorem, not only a set-cardinality theorem);
- these 2,432 limbs complement the separately checked 2,564 fixed-section
  limbs to all 4,996 canonical limbs;
- exact-length layout is necessary and sufficient below the frontier cap,
  so truncation, trailing data, and an oversized frontier fail closed;
- any noncanonical query limb fails closed; and
- an accepted deferred run has the same transcript-event list and order as
  eager validation.  Query canonicality checks introduce no transcript event.

The Aeneas source proofs add the concrete source connection:

- the extraction wrapper is definitionally equal to the selected production
  `parse_deferred_query_canonicality` method;
- its checked arithmetic gives a 20,268-byte no-frontier body, and its source
  branches reject oversized and every nonexact zero-frontier length;
- the selected record widths evaluate to 403 and 186 bytes;
- successful normalized `gamma_combine_v6_packed_layer0` control flow implies
  successful calls to the unchanged decoders at widths 104 and 48; and
- either decoder returns `NonCanonicalM31` if its full scan reports a nonzero
  invalid flag.

## Extraction boundary

`extraction/direct/V7CanonicalConsumer.llbc` is Charon output rooted at the
untouched selected `verify_and_gamma_combine_v7_canonical_openings`.  It pins
construction of all sixteen `(query, ordinal)` entries, sorting, duplicate and
range rejection, one `wire.query(ordinal)` call and one gamma call per loop
entry, Merkle leaf construction, and final authentication.  Gamma and the
cryptographic helpers remain opaque in this direct artifact.

`extraction/normalized/V7CanonicalConsumerNormalized.llbc` exposes the gamma
body and both packed decoders.  Its extraction-only source input was produced
by `source-transform/normalize_gamma_validation.py`: the script first checks
the exact selected `v6_onefold.rs` SHA-256, preserves both length guards and
both decoder calls, and erases only the infallible field arithmetic after
successful decoding.  The deterministic hash/Merkle definitions in
`FunsExternal.lean` exist only to make the validation-control model executable;
no cryptographic claim depends on them.  The direct LLBC remains the authority
for untouched call order and crypto boundaries.

`extraction/parser/V7CanonicalDeferredParser.llbc` is rooted in the small
extraction-only harness.  The harness immediately calls the production
inherent parser; no parser implementation is copied.

Aeneas emitted seven calls whose phantom const generic could not be inferred
after its closure type erased that parameter.  The checked-in generated
`Funs.lean` supplies `(N := N)` at those calls.  This is an elaboration-only
repair and changes no translated term.

## Exact extraction configuration

All Charon runs used version `0.1.223`, preset `Aeneas`, and the paths below.
The serialized LLBC records these options and source contents.

- direct root:
  `crate::v7_fixed_canonical_audit::verify_and_gamma_combine_v7_canonical_openings`;
  includes the three field structs; opaque `aspis_core::field`, gamma, private
  leaf hashing, and the two-subtree verifier;
- normalized root: the same root/includes, with only `aspis_core::field`,
  private leaf hashing, and the two-subtree verifier opaque;
- parser root: `crate::parse_v7_canonical_deferred`; includes
  `aspis_core::v7_fixed_canonical_audit`; opaque `aspis_core::field`.

Aeneas was the pinned `aeneas-d860-v6-linux` binary (reported version
`unknown`; SHA-256 in `PIN.json`), backend `lean`, split files, JSON emission.

## Replay discipline

Run proof compilation only on the NUC under a task-owned cgroup, for example:

```sh
ssh dombarker@nuc.local "systemd-run --user --scope \
  --unit=aspis-v7-exact-once-replay.scope \
  -p MemoryMax=10G -p MemorySwapMax=0 -p TasksMax=256 \
  /usr/bin/time -v /path/to/replay-proofs.sh \
  /path/to/pinned/repo \
  /home/dombarker/project-offloads/aeneas-d860-v6/backends/lean"
```

The replay script verifies the revision and selected source hashes, compiles
the generated modules and both source proofs in a temporary Aeneas-backend
directory, then compiles the assumption-free project leaf.  Regenerating LLBC
requires the exact Charon/Aeneas binaries named in `PIN.json`; do not run that
step in a release worktree.

For the archived NUC source snapshot, which intentionally has no `.git`
directory, set `ASPIS_ALLOW_HASH_ONLY=1`; all three selected source hashes are
still mandatory.  Normal git worktrees must contain the pinned revision as an
ancestor.

## Remaining explicit boundaries

- Charon/Aeneas establishes source shape and result flow, not SHA-256 or
  Merkle cryptographic correctness; those stay at the existing cryptographic
  proof boundary.
- The validation-only normalization intentionally does not prove the erased
  post-decode gamma field arithmetic.  It proves only that acceptance cannot
  bypass either canonical decoder.
- The transcript theorem covers unchanged order on accepted executions and
  fail-closed rejection for malformed executions.  Source correspondence uses
  the concrete fact that the selected query consumer has no transcript
  argument or transcript-mutating call; the surrounding transcript verifier
  remains a separate maintained bridge.

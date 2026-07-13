# Profile 22 local artifact CLI

Status: prepared and bounded-check tested; the expensive proof search has not
been run and no proof artifact has been generated.

The host-only example is
`crates/aspis-prover/examples/profile22_local_artifact.rs`.  It accepts exactly
three positional arguments:

1. a new local proof path;
2. a private durable mask-nonce-ledger directory; and
3. an absolute release time as Unix seconds.

The executable constructs the fixed-release controller before it invokes
`build_hiding_atomic_state_only_profile22_first_good_v3`.  That hardened API
owns fresh OS randomness, complete local mining, the sixteen-attempt ceiling,
the strong Good22 decision, and rejected-buffer scrubbing.  The executable has
no raw-attempt API, deterministic attempt entropy, diagnostic verifier, RPC,
transaction, signer, keypair, or upload path.

The release channel receives either the opaque proof or `Abort` at the fixed
public boundary.  On a proof release it first runs
`verify_atomic_state_only_profile22_v3` with proof-of-work checking enabled.
Only an accepted production proof is written, using create-new semantics.  It
then syncs the proof file and its containing directory.  A write or sync
failure removes the partial artifact.  Abort and verification failure create
no artifact.

Successful standard output has exactly two fields and no attempt metadata:

```text
length=<decimal byte length>
sha256=<lowercase SHA-256>
```

The proof bytes themselves remain only at the requested local path.  Controlled
failure is silent apart from the process exit status.  Nothing is signed or
sent.

## Bounded checks

These checks do not invoke the expensive worker:

```sh
NO_DNA=1 cargo check -q -p aspis-prover --example profile22_local_artifact
NO_DNA=1 cargo test -q -p aspis-prover --example profile22_local_artifact
```

## Deliberate operator invocation

This is intentionally not run by tests or automation.  The release epoch must
be in the future and the output file must not exist:

```sh
NO_DNA=1 cargo run --release -q -p aspis-prover \
  --example profile22_local_artifact -- \
  /private/path/profile22-proof.bin \
  /private/path/profile22-nonce-ledger \
  RELEASE_UNIX_SECONDS
```

No default feature gate is enabled by this example.

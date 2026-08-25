# V7 Tag-73 deployed `challenge_qm31` source closure

This isolated K1 bundle replaces the sole opaque transcript callback in the
full compact-semantic extraction with a transparent Charon/Aeneas translation
of the unchanged deployed Rust method.  It does not edit K1.6, the compact
semantic source bundle, production Rust, Pool code, a shared aggregator, or
deployment state.

## Result

The source is pinned to deployed commit
`1589706d38a5e8ca705fbf7aaed2c82cf8595510` and the `crates/aspis-core` tree
`4a869518c17b226068499b7c7880e05212315cd6`.  The extraction root only calls
`Transcript::challenge_qm31` and returns the updated transcript.

The generated module contains transparent definitions for:

- `Transcript.squeeze_block`;
- the retry-loop body and loop for one M31 limb;
- the mutable-iterator body and loop for four limbs;
- `Transcript.challenge_qm31`; and
- the extraction wrapper.

Aeneas leaves only `P` and `M31::ZERO` in its external template.  The checked
module closes them by the exact deployed values `2147483647#u32` and
`0#u32`; it introduces no behavior axiom.

`proof/V7Tag73ChallengeQm31SourceCertificate.lean` proves from those concrete
definitions that:

- a squeeze hashes one 33-byte slice `state || 1` for the returned block and
  one 33-byte slice `state || 2` for the next transcript state;
- four source bytes at coordinate `4*i .. 4*i+4` decode as little-endian
  `u32`;
- `word & 0x7fffffff` is exactly reduction modulo `2^31`;
- rejection occurs exactly when the masked result is `2^31-1`;
- each selected limb invokes the exact range `0..8`;
- the first accepted candidate stops that limb, while range exhaustion
  returns `accepted = false`;
- an exhausted limb makes the outer loop return `Err(())` immediately;
- the sampler starts from four zero limbs and assembles its success result in
  `(c0.a,c0.b,c1.a,c1.b)` order; and
- four successful eight-attempt limbs consume between 4 and 32 words, hence
  at most four 32-byte blocks, with every returned limb canonical.

The adjacent formal leaf
`AspisFormal/AspisFormal/K1/V7Tag73SamplerDecoderExact.lean` supplies the
inductive first-accepted and exact eight-rejection/exhaustion facts.  The
source certificate additionally reduces active generated loop bodies only
from explicit range, arithmetic, slice, copy, increment, and squeeze
equations.  Its finite `ExactLoopTrace` replay lemma chains only those literal
generated-body equations into the corresponding deployed retry-loop result;
it does not assume a generic sampler-faithfulness statement.

## Compact extraction bridge

`replacement/V7CompactSemanticChallengeOpaqueNoDedup/FunsExternal.lean`
defines the exact name expected by the compact generated `Funs.lean`.  It:

1. preserves the compact transcript state and wraps its total hash callback
   in Aeneas' outer `Result`;
2. calls the transparent source-generated sampler;
3. converts the duplicate generated `CM31`/`QM31` records field by field; and
4. returns the source-generated successor transcript state.

With this module earlier in `LEAN_PATH`, the unchanged compact generated
`Funs.lean` compiles without its original `challenge_qm31` axiom.  The replay
performs that precedence check in a temporary tree; the compact bundle itself
is never modified.

## Exact residual boundary

The transcript's hash member remains an arbitrary total function.  The proof
fixes every byte passed to it and every subsequent state transition, but it
does not claim SHA-256 collision resistance, random-oracle behavior, or
sampler uniformity.  Those cryptographic claims remain outside this source
closure.

There is no conclusion-shaped sampler axiom, generic copy-lane premise, or
blanket faithfulness premise in the checked closure.  The raw generated
`FunsExternal_Template.lean` is retained only as provenance and visibly has
the two constant holes described above; it is not compiled.

## Toolchain and replay

The isolated static translator is Aeneas base `b59d5188` plus the audited
Lean-4.32 translator patch, with binary SHA-256
`4632746db1bf6c3953f2971078965a2a5a8ad6cf5f75636b46b397bc50c550b5`.
Full compiler, patch, container, and cgroup details are recorded in
`toolchain/TOOLCHAIN.md`; `toolchain/build-patched-aeneas.sh` reconstructs the
binary without modifying the shared toolchain.

`replay.sh` first checks the executable modes recorded in
`FILE-MODES.manifest`, then checks the frozen source hashes and reruns
Cargo/Charon/Aeneas,
canonicalizes path and invocation-only LLBC metadata, byte-compares the rest
of the structured LLBC tree and the normalized generated definitions,
rebuilds the formal decoder and source proof, rejects proof escapes, compiles
the concrete callback replacement, and finally recompiles the unchanged
compact generated `Funs.lean` against that replacement.  Its only MIR-option
whitelist is the recorded bundled `null` versus replayed `"Built"` spelling;
all other structured drift fails the replay.

`replay-accepted-source-composition.sh` is the narrow follow-on check.  It
pins the current production `V7CompactSemanticSourceBridge.lean`, compiles it
against the concrete replacement `FunsExternal.olean`, and parses the
kernel's `#print axioms` output for all three public accepted-source
theorems.  It accepts only `propext`, `Classical.choice`, and `Quot.sound` and
also rechecks the green replacement certificate output.  The transcript's
arbitrary total hash function remains an explicit record field, not an
opaque sampler axiom.

That focused composition replay is green under
`v7-tag73-qm31-accepted-source-compose03.scope`: 2,699,552 KiB maximum RSS,
zero swaps, and 7.35 seconds wall time.  All three public accepted-source
theorems report exactly the three standard Lean axioms above and no
`challenge_qm31` callback axiom.  `COMPOSITION-RESULT.md` records the exact
unit, invocation, source hash, compiled olean hash, and residual boundary.

Run the focused replay on the NUC under the recorded cap:

```sh
systemd-run --user --scope \
  -p MemoryMax=12G -p MemorySwapMax=0 -- \
  /usr/bin/time -v env LEAN_NUM_THREADS=1 ./replay.sh
```

The focused Lean 4.32 checks completed with zero swaps.  The final source-only
certificate run used 6,949,708 KiB maximum RSS.  The green end-to-end replay
(`v7-tag73-qm31-replay-final8.scope`) used 6,946,924 KiB maximum RSS and
completed in 39.54 seconds.  The audited theorem closures report only
`propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.

From this bundle directory, `sha256sum -c MANIFEST.sha256` verifies every
checked payload together with the focused K1 leaf, audited translator patch,
and unchanged compact Types/Funs consumed by the integration replay.

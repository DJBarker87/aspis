# V5 transcript-prefix extraction audit

This package records a focused audit of the successful transcript operations
inside the archived V5 `verify_v5_wire_prefix` function.

Pinned Aeneas cannot conveniently start this proof at the original generic
hash-function boundary. The extraction artifact therefore used a temporary
helper named `verify_v5_wire_prefix_from_initialized_transcript`. The helper is
not deployed source. Its complete source change is recorded in
`deployed-prefix-initialized-transcript.patch`:

- rename the function;
- replace `hash: HashFn` with an already initialized `Transcript` argument;
- remove the live-statement digest check; and
- remove `Transcript::new(hash)`.

Everything after transcript initialization is unchanged. The removed digest
check and initialization remain obligations of the real caller; this package
does not silently assume that they happened.

`check-normalized-success-path.py` checks every retained external call and its
arguments, in order, against the pinned generated Lean function. It also
checks the terminal-context expression and the successful returned fields.
The corresponding typed program is
`V5TranscriptPrefixNormalizedGenerated.lean`.

`V5TranscriptPrefixExtractionBridge.lean` interprets that typed program. The
generated artifact declares transcript operations and six larger helpers as
opaque external functions, so their event traces cannot be recovered by
unfolding the generated term. The bridge therefore states the six helper
observations explicitly. Given those observations, it proves that the
successful prefix has exactly the event order and payloads in `sourcePrefix`.
Direct absorbs and challenge positions need no helper premise. Separate
theorems record the values used in the terminal-context comparison and the
successful return.

This is not definitional equality with the generated function's opaque
external semantics. The normalization equivalence is a checked transformation
boundary, and the six helper observations remain named proof obligations.
This package also makes no claim about SHA-256 security, sampler success,
Charon, Aeneas, the removed digest check, or transcript construction.

See `manifest.txt` for source, artifact, generated-file, patch, and tool
identities. With the pinned artifact directory available, run:

```sh
V5_PREFIX_ARTIFACT_DIR=/path/to/v5-transcript-final-prefix \
  ./verify-artifacts.sh
```

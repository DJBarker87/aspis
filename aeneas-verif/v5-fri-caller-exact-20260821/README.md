# Exact data flow through the V5 Merkle/FRI caller

This bundle records the two unchanged production functions which connect the
private-opening verifier to the FRI verifier. Charon extracted the Rust after
the replay-only patch in `extraction/v5-fri-fixed-callbacks.patch` replaced two
higher-order callback arguments with first-order wrappers. Each wrapper calls
the original production function once with the original callback.

Aeneas translated `verify_v5_private_suffix` and `verify_mode9_fri_phase`.
The generated body is retained in `generated/V5FriCaller/FunsRaw.lean.txt`;
Aeneas left the three large callees external. The proof therefore takes those
three callees as explicit function parameters instead of inventing their
behavior.

## Result

`accepted_fri_phase_yields_exact_call_trace` proves that every successful
source-shaped caller execution has one trace in which:

- the roots, 18-query array, and proof slice passed to the Merkle verifier are
  exactly the corresponding parsed inputs;
- the two returned record slices are compared with the parsed statement;
- the challenge and relation-claim bytes passed to preparation are exact;
- the opening returned by the Merkle call is the same value passed to FRI;
- the prepared claims returned by preparation are the same value passed to
  FRI; and
- the fold challenges, final polynomial, and returned pair are exact.

The theorem is parametric in the three callees. Separate bundles prove those
callees and structural adapters connect their independently generated Rust
types. This bundle proves caller data flow; it does not by itself prove the
Merkle, preparation, or FRI algorithms.

`proof/V5FriCallerMerkleBridge.lean` then connects the first of those calls to
the independently translated, unchanged Merkle verifier. For every successful
caller trace, `accepted_caller_opening_yields_exact_merkle_and_fri_view`
produces the exact five-tree authenticated run and proves that its returned
opening is field-for-field identical to the opening passed to FRI.

The source wrapper remains an explicit translation-tool edge. Its hash-pinned
Rust patch is a one-call wrapper which supplies the production Solana SHA-256
callback; the large higher-ranked callback signature is outside Aeneas's
current translation support. The Lean theorem
`accepted_exact_merkle_call_yields_authenticated_fri_view` discharges the
source-equality premise after specializing the extracted caller to that exact
one-call model. It does not claim that Aeneas translated the wrapper body.

`proof/V5FriCallerAcceptedResolverBridge.lean` completes the join to the
maintained released-security theorem. It proves that the concrete accepted
FRI-call resolver has the exact parser output and read schedule, then feeds
that result into the released accepted-false event. The former abstract
whole-consumer equality is no longer an input to this endpoint.

The concrete resolver is built from `ProductionCallerEnvironment`, which is
exactly the information omitted from the small mathematical production call:
the parsed verifier input, ordered query array, transcript challenges, three
caller functions, successful translated caller result, and accepted FRI call.
`resolveFromProductionCaller_uses_production_caller` derives the former
universal resolver premise from that data. The remaining focused source/tool
edges are the fixed SHA-256 Merkle wrapper and the fixed-inverse FRI wrapper;
the latter states only that the successful FRI call retained the same returned
opening.

## Recorded files

| File | SHA-256 |
|---|---|
| `extraction/V5FriCallerPatchedAllTypes.llbc` | `235c16310e970dafa081468fa17466b6ae43026907fc1df038e05d392ec2cf02` |
| `extraction/V5FriCallerPatchedAllTypes.pretty.llbc` | `a72270d0bce08ec930881cc9b6ae8231b7e8b7df96e84d358b31fe52b6068655` |
| `extraction/v5-fri-fixed-callbacks.patch` | `10f8a0d5e42f996968e31e982d9ecb2b4a46be911bafb9a0745743eb6b9139b0` |
| `generated/V5FriCaller/FunsRaw.lean.txt` | `304fa51aaf3f34dc8eab5aabd62d49abf7c581ea2422ffb3401384f8e50519fb` |
| `generated/V5FriCaller/Types.lean` | `8a9c03aeaa3a4fccb06b141276a78d0848089ac35f83f6a72ea69e76c984af73` |
| `proof/V5FriCallerParametric.lean` | `a1e1678fef7051200b559240dc71dfaab84efcb049ef33fe85b91a0a57d760ea` |
| `proof/V5FriCallerMerkleBridge.lean` | `8c175163521af742721215edefdb5a36e07e15b1e791175200f0db945dc759bd` |
| `proof/V5FriCallerAcceptedResolverBridge.lean` | `deaeb51487e6a42c986a5ff93069fb9c9d2a340e77489723f2719c5f89297a21` |

The source file has Git blob
`ca28d560e44e5e82e689321f32289831c889a0bd`. The extraction used Charon
commit `cb50ff16b9f1066b8a97dc06da704de2da2fa41c` and Aeneas commit
`b59d5188` with Lean 4.32.0.

The compilable type snapshot omits Aeneas's generated `discriminant`
attributes. Those attributes create globally named metadata helpers which
collide when the independent Merkle and FRI snapshots are imported together.
The normalization changes no datatype, constructor, or field; the raw LLBC
and generated caller body remain hash-pinned above.

## Replay

Set `AENEAS_LEAN_LIB` to the matching Aeneas Lean library and run:

```sh
AENEAS_LEAN_LIB=/path/to/aeneas/backends/lean/.lake/build/lib/lean \
  ./aeneas-verif/v5-fri-caller-exact-20260821/replay-lean432.sh
```

The replay verifies every recorded hash, checks that the replay-only patch
still applies to the recorded production source, compiles the type snapshot
and proof in a fresh directory, rejects proof shortcuts, and checks the
printed theorem dependencies.

After replaying the unchanged-Merkle and FRI-consumer bundles, run
`replay-merkle-bridge-lean432.sh` with the three replay output directories to
check the cross-snapshot caller theorem.

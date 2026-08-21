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

## Recorded files

| File | SHA-256 |
|---|---|
| `extraction/V5FriCallerPatchedAllTypes.llbc` | `235c16310e970dafa081468fa17466b6ae43026907fc1df038e05d392ec2cf02` |
| `extraction/V5FriCallerPatchedAllTypes.pretty.llbc` | `a72270d0bce08ec930881cc9b6ae8231b7e8b7df96e84d358b31fe52b6068655` |
| `extraction/v5-fri-fixed-callbacks.patch` | `10f8a0d5e42f996968e31e982d9ecb2b4a46be911bafb9a0745743eb6b9139b0` |
| `generated/V5FriCaller/FunsRaw.lean.txt` | `304fa51aaf3f34dc8eab5aabd62d49abf7c581ea2422ffb3401384f8e50519fb` |
| `generated/V5FriCaller/Types.lean` | `ac0381caf2872cbc078bdc7f7804bc5ecc759e3ef5059353c7257dd34f2d077c` |
| `proof/V5FriCallerParametric.lean` | `a1e1678fef7051200b559240dc71dfaab84efcb049ef33fe85b91a0a57d760ea` |

The source file has Git blob
`ca28d560e44e5e82e689321f32289831c889a0bd`. The extraction used Charon
commit `cb50ff16b9f1066b8a97dc06da704de2da2fa41c` and Aeneas commit
`b59d5188` with Lean 4.32.0.

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

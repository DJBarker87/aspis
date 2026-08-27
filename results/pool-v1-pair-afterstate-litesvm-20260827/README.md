# V7 Pool proof-carried afterstate LiteSVM evidence

This bundle isolates the executable one-terminal Pool private-transfer path
after a selected verifier has authenticated a proof-carried pair-tree
afterstate.  The Pool performs no Poseidon computation.  It checks registry
selection and sealed proof-account framing, invokes an SBF verifier transport
double, authenticates the immediate exact 688-byte `ASJA` return, and writes
the pair Pool state, chronological root history, nullifier marker and 200-byte
transition receipt atomically.

Two independent deterministic LiteSVM executions passed:

| case | source -> next sequence | history write | CU | transaction wire |
|---|---:|---|---:|---:|
| same page | 100 -> 101 | page 0, slot 101 | 150,223 | 873 bytes |
| rollover | 255 -> 256 | new page 1, slot 0 | 119,206 | 906 bytes |

Both runs preserve the retained membership anchor at sequence 50, match the
entire 1,000-byte Pool image to the verifier-provided next state, create the
one-shot marker, return `ASTR`, and produce byte-identical simulation and
execution metadata.  The rollover run additionally proves the full prior
8,256-byte page remains byte-exact.

These are not real-proof combined measurements.  The transport double does no
cryptography; it returns the framed `ASJA` body from its verifier-owned account.
The numbers therefore include the Pool prefix, selected-verifier CPI and
return transport, and Pool suffix, but must not be added to a frozen verifier
reference as though the result were an observed combined transaction.  The
real seven-C2-lane Tag-73 verifier integration remains the decisive CU gate.

The pair path is exposed only under the measurement feature
`pair-afterstate-evidence`.  Normal production builds do not recognize the
pair instruction.  Marker and rollover-page creation are also excluded: both
accounts are pre-created, exact-size, zeroed Pool-owned accounts.

Artifacts and toolchain:

- `aspis_pool.so`: 446,536 bytes,
  SHA-256 `d36b382cb673e35c1842c2db78020cb80a3fcad2a948e6d460a55a8db0203cac`.
- `aspis_pair_afterstate_transport_double.so`: 20,800 bytes,
  SHA-256 `f6be90dd1a7088ff9bc7ba95a88e52885c61f036fa4fffaa0ec951a2a9dbe056`.
- `solana-cargo-build-sbf 2.3.0`, platform-tools `v1.48`, SBF Rust `1.84.1`.
- Host Rust `1.93.0`, Cargo `1.93.0`, LiteSVM `0.16.0`.
- macOS 26.5 / Darwin 25.5.0 arm64.

The first SBF link found a 4,800-byte handler frame, 472 bytes over Solana's
4 KiB limit.  The authenticated 680-byte afterstate and the next 1,000-byte
Pool state were moved to the heap.  The final SBF link completed without any
stack-offset or frame-clobber diagnostic, and the focused eight pair tests pass.
Those focused tests retain the earlier direct coverage of two sequential live
updates, exact replay rejection before verifier dispatch, stale-afterstate
rejection with a fresh marker, and byte-exact Pool/history/marker rollback.

No RPC, deploy, signing-key retention, or network transaction was used.

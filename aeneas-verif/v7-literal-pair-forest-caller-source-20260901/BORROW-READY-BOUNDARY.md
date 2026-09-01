# V7 literal caller read-only account-data boundary

## Result

The caller-side data view is kernel checked for the production borrow-ready
entry state.  The strongest theorems are:

- `borrow_readonly_account_data_borrow_ready_exact`;
- `borrow_readonly_account_data_success_is_exact_view`;
- `readonly_data_guard_deref_is_exact`.

They establish that a successful view is byte-for-byte `account.data`, and
that dereferencing the modeled read-only guard returns exactly the same slice.
The definitions are executable and introduce no project axiom.

The exact remaining platform boundary is the dynamic check performed by
Solana's `AccountInfo::try_borrow_data` for arbitrary host states with an
outstanding mutable `RefCell` borrow.  The production accepted-path model starts
with transaction accounts in the borrow-ready state.  This boundary neither
asserts verifier acceptance nor hides parsing, authentication, transcript,
cryptography, result construction, or state-transition logic.

## Why literal Aeneas translation stops

Production Rust returns `Ref<'a, &'a mut [u8]>` from `try_borrow_data`, then
maps it to `Ref<'a, [u8]>`.  Current Aeneas retains a real nested mutable
write-back projection on both sides of the abstraction.  The first exact
failure is:

```text
SymbolicToPureValues.ml:878
AEndedProjBorrows ... loans != []
```

Ignoring those loans is unsound: they encode the `RefCell` borrow's nested
mutable provenance and backward return, not dead shared-loan bookkeeping.

The diagnostic
`toolchain/borrow-readonly-owned-result-probe.patch` consumes the exact guard
inside the helper and returns only `usize`.  This rules out guard escape as the
cause:

- Rust check: pass;
- Charon: pass, LLBC SHA-256
  `419e80a41b4df57d8bf5826424e2338a878307afc80c597331a4c6fb00a42e5f`;
- Aeneas: the same line-878 failure.

Implementing literal arbitrary-state closure therefore requires general Aeneas
support for mutable borrows nested in ADTs.  A one-line loan erasure is not an
acceptable translator patch.

## Focused evidence

| Gate | Unit | Invocation | Wall | Peak RSS | Swap | Result |
|---|---|---|---:|---:|---:|---|
| owned-result Charon | `aspis-v7-borrow-owned-charon-r3b` | `0788b89ab5cc4d9ea6a2653d6f3e6dfa` | 3:05.17 cold compile | 917,300 KiB | 0 | pass |
| owned-result Aeneas | `aspis-v7-borrow-owned-aeneas-r3` | `0e999169546b48e39a7ab54ed23b145f` | 0.89 s | 61,424 KiB | 0 | expected line-878 rejection |
| borrow-ready final Lean replay | `aspis-v7-borrow-ready-final-replay-r4c` | `a548d5b38be9404db29da60e2333d110` | 17.66 s | 2,745,948 KiB | 0 | pass |

The final theorem axiom union is exactly:

```text
propext
Classical.choice
Quot.sound
```

There is no `sorry`, `admit`, `sorryAx`, `native_decide`, project axiom, or
conclusion-shaped acceptance premise in the compiled bridge.

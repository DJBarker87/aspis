# V7 Pool atomic nullifier-marker lifecycle — 2026-08-30

## Decision

The eight-lane one-terminal Pool now creates or reserves the canonical
nullifier-marker PDA inside the same Pool instruction that invokes the selected
Tag-73 verifier and settles the lane transition. This closes the activation
blocker recorded at `eb405a030695090651509fe1aea6964c19705e88` without a
pre-reservation transaction, early nullifier disclosure, or any change to the
proof relation, transcript, ASQ8/ASF8/ASR8 codecs, proof bytes, query profile or
cryptographic assumptions.

The two new terminal accounts are placed immediately after the writable
marker:

1. a writable, System-owned signer that funds the marker; and
2. the exact read-only executable native System Program.

The normal wallet uses the transaction fee payer as the marker payer, so this
does not add a second signature.

## Exact terminal account layouts

| Operation | History path | Accounts |
|---|---:|---:|
| Private transfer | same page/genesis | 11 |
| Private transfer | rollover | 12 |
| Withdrawal | same page/genesis | 16 |
| Withdrawal | rollover | 17 |

The common suffix is:

```text
marker (writable)
marker payer (writable signer)
System Program (read-only executable)
registry
registry entry
selected verifier program
proof account
```

A withdrawal retains the existing exact five-account SPL suffix after the
proof account. All accounts must remain pairwise distinct.

## Fail-closed lifecycle

`process_pair_forest_terminal_with_verifier_v1` now performs this order:

1. decode the 320-byte ASQ8 request and authenticate master, checkpoint,
   selected lane, history page(s), registry/verifier/proof layout and account
   uniqueness;
2. authenticate the marker payer as writable, non-executable, System-owned and
   signing;
3. authenticate the System Program by exact address, native-loader owner,
   executable/read-only/nonsigner privileges;
4. derive and plan the exact marker PDA from the Pool and canonical nullifier;
5. for withdrawals, authenticate all custody accounts and construct the exact
   SPL transfer before any marker CPI;
6. immediately before verifier CPI, create or allocate the marker with the
   Pool PDA signer seeds;
7. replan the live account and require exact Pool owner, exact marker size,
   all-zero data, intended encoded payload and rent exemption;
8. invoke and authenticate the selected verifier and exact ASR8 result;
9. execute and check withdrawal custody, if any;
10. update only the selected lane/history page and write the consumed marker.

The accepted fresh account forms are deliberately narrow:

- zero-lamport, data-empty System-owned canonical PDA: one `CreateAccount`
  CPI;
- pre-funded, data-empty System-owned canonical PDA: rent top-up if needed,
  signed `Allocate`, then signed `Assign`; this prevents lamport dusting from
  becoming a marker-creation griefing attack;
- exact-size, rent-exempt, Pool-owned, all-zero canonical PDA: no System CPI.

Every wrong address, owner, size, privilege, nonzero image, occupied marker or
non-rent-exempt resulting account fails closed. A consumed marker rejects an
exact replay before another System CPI or verifier call.

## Atomic rollback boundary

Marker reservation intentionally occurs before verifier CPI. On Solana, every
System CPI and all later Pool/SPL writes are in the same top-level instruction
journal. A verifier error, malformed ASR8, failed withdrawal CPI, custody-delta
mismatch or later settlement error therefore rolls marker creation and payer
lamports back together with Pool state.

The Rust host test exposes the post-System-CPI intermediate state and then
models the outer Solana journal rollback to the exact original account images.
That proves the Pool call order and absence of pre-verifier Pool writes, but it
is not substituted for runtime evidence. A fresh SBF build plus LiteSVM or
validator replay must still demonstrate actual rollback before activation.

## Exact TxV1 sizes

The real transaction-v1 wallet builder and strict simulation preflight were
updated. ASQ8 remains exactly 320 bytes and the proof remains account-backed.
Adding the payer meta and System Program increases every terminal wire by
exactly 34 bytes because the payer is already the transaction fee payer.

| Operation | History | TxV1 wallet config | Strict simulation | Headroom from strict wire to 4,096 |
|---|---|---:|---:|---:|
| Private transfer | same page | 845 B | 833 B | 3,263 B |
| Private transfer | rollover | 878 B | 866 B | 3,230 B |
| Withdrawal | same page | 1,010 B | 998 B | 3,098 B |
| Withdrawal | rollover | 1,043 B | 1,031 B | 3,065 B |

For comparison, exact legacy/v0 serializations under the same full wallet
configuration are 823, 856, 988 and 1,021 bytes respectively. These numbers
are measurements from the serialization tests, not instruction-data
estimates.

## Focused adversarial coverage

`terminal_marker_creation_fails_closed_rolls_back_and_rejects_replay` covers:

- unsigned/spoofed payer;
- canonical System Program address under a spoofed loader;
- arbitrary marker substituted for the canonical PDA;
- pre-existing malformed Pool-owned marker bytes;
- insufficient marker-payer funds;
- successful zero-lamport marker creation followed by verifier failure and
  exact outer-journal rollback model;
- successful pre-funded marker top-up/allocate/assign and consumption;
- exact replay rejection before a second System CPI or verifier call.

The existing nullifier planner test
`wrong_address_owner_privileges_length_or_malformed_image_fail_closed` pins the
complete address/owner/privilege/length/image matrix. Existing terminal tests
continue to cover selected-lane/history mutation and authenticated SPL
withdrawal success/failure ordering.

Focused verification completed locally:

```text
NO_DNA=1 cargo test -q -p aspis-pool --lib \
  --features v7-pair-forest-one-tx-candidate
```

Result: 102 passed, zero failed.

The changed wallet TxV1 sizing, simulation-shape and adversarial-meta tests all
pass. A full 140-test wallet run had 139 passes and one deterministic failure
in the unchanged
`relayer_finality_join::finality_join_rejects_receipt_binding_slot_signature_and_failure_mismatches`
test: the implementation returned `StartupReceiptMismatch` where that existing
test expected `ProviderSetMismatch`. `git diff eb405a0` confirms this audit did
not change that module; it is not treated as evidence against or silently
fixed as part of the marker lifecycle.

`rustfmt --check` on the four changed Rust files and `git diff --check` are
green.

## CU and release status

No CU number is claimed from host tests or from an old binary. The fresh
zero-lamport path adds one System `CreateAccount` CPI; a dusted PDA can add a
top-up plus `Allocate` and `Assign`. Exact incremental and combined CU require
the changed Pool SBF artifact and the real one-terminal runtime harness.

Activation gates remaining for this lifecycle are:

1. reproducible SBF build of the changed Pool source;
2. real transfer and withdrawal, same-page and rollover CU measurements with a
   newly created marker;
3. validator/LiteSVM verifier-failure, SPL-failure and replay rollback evidence;
4. refresh of the terminal source/Aeneas bridge for the two-account layout,
   rent input and marker-creation branch.

The cryptographic Lean development does not change. The operational/source
bridge must add the exact call-order cases for fresh zero-lamport, pre-funded
and precreated-zero markers and keep Solana instruction rollback as an explicit
runtime boundary/evidence obligation.

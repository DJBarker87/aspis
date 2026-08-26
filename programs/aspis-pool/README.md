# Aspis Pool V1 Solana program

`aspis-pool` exposes a native Solana `process_instruction` entrypoint for
initialization, vault-backed deposits, private 1-to-2 spends, and withdrawals
with one change output. There is no public raw-append instruction. Every PDA is
derived from the `program_id` supplied by the runtime; this crate deliberately
does not contain `declare_id!` or a deployment key.

Status: this is a host-checked state/custody kernel, not the release Pool
binary. Initialization and deposit have focused LiteSVM evidence. The direct
private-spend route is retained as a semantic reference, but a transaction with
the mock verifier already exhausts the 1,400,000-CU limit. It therefore must
not be deployed as the production spend route. The public `ASPP`/`ASPF` route
uses a verifier-owned authorization receipt and a state-bound prepared-
settlement plan so the final transaction can atomically consume the nullifier,
update the tree/history, move custody and retire the plan without rerunning
proof verification or Poseidon tree construction. The exact composition is
SBF-build clean; validator/LiteSVM compute-unit evidence remains a release gate.

All integers are little-endian. Every fixed wire rejects the wrong magic,
version, transition kind, digest encoding, nonzero reserved bytes, noncanonical
M31 limbs, wrong length, and trailing bytes. All accounts supplied to one Pool
instruction must have distinct public keys, including accounts occupying
different semantic roles.

## Top-level instruction ABI

### Initialize: `ASIN`, version 1, exactly 184 bytes

```text
0..4      magic "ASIN"
4         version 1
5..8      zero reserved
8..40     asset mint pubkey
40..44    canonical M31 asset id
44..48    zero reserved
48..80    deployment domain
80..184   exact ASPP VerifierPolicyV1 image
```

Exact accounts:

```text
0  [signer,writable] payer (System-owned)
1  [writable]        canonical Pool state PDA
2  [writable]        canonical root-page-zero PDA
3  []                initialized legacy SPL Token mint
4  [writable]        canonical vault token-account PDA
5  [executable]      original SPL Token program
6  [executable]      System Program
```

The state, root page, and vault may be data-empty System-owned canonical PDAs,
in which case the processor funds/allocates/assigns them with signed System
CPIs. Exact zeroed program-owned state/page accounts and an already initialized,
empty canonical vault are also accepted. The vault is initialized with legacy
SPL Token `InitializeAccount3`; Token-2022 and extension accounts are excluded.
Pool/page bytes are written only after every creation and token CPI succeeds.
Success return data is exactly the 104-byte `ASIR` receipt:

```text
0..4    magic "ASIR"
4       version 1
5..8    zero reserved
8..40   Pool state PDA
40..72  root-page-zero PDA
72..104 vault token-account PDA
```

### Deposit: `ASDI`, version 1, 80..592 bytes

The existing exact deposit wire is unchanged: its 80-byte fixed request is
followed by the declared `0..512` opaque encrypted-note payload. Deposit amount
is a nonzero `u32` below the frozen 30-bit value limit. The program recomputes
the format-2 commitment from the owner-key digest, amount, Pool asset id, and
salt, then executes one legacy SPL Token `TransferChecked` and verifies the
exact source debit and vault credit before persisting one leaf/root.

Without root-page rollover, exact accounts are:

```text
0  [writable]         Pool state PDA
1  [writable]         current root page
2  []                 asset mint
3  [writable]         source token account
4  [signer]           direct source owner
5  [writable]         canonical vault token account
6  [executable]       original SPL Token program
```

At a root-page boundary, exact accounts are:

```text
0  [writable]         Pool state PDA
1  []                 full current root page
2  [writable]         canonical fresh next root-page PDA
3  []                 asset mint
4  [writable]         source token account
5  [signer]           direct source owner
6  [writable]         canonical vault token account
7  [executable]       original SPL Token program
8  [signer,writable]  payer (System-owned)
9  [executable]       System Program
```

Only rollover requires the payer/System accounts. Successful return data is
exactly the canonical 224-byte `ASPD` deposit receipt followed by precisely the
declared payload bytes (maximum 736 bytes). Failed deposits emit no Pool return
data.

### Private transfer: `ASPT`, version 1, exactly 432 bytes

```text
0..8      ASPT outer header
8..216    exact 208-byte ASPA historical-anchor envelope
216..432  exact 216-byte ASCP verifier statement
```

The statement is the exact byte string authenticated by the selected verifier:

```text
0..4      magic "ASCP"
4         statement version 1
5         private-transfer transition kind
6         canonical digest encoding version
7         zero reserved
8..40     Pool pubkey
40..72    deployment domain
72..80    anchor root sequence
80..112   canonical anchor root
112..144  canonical nullifier
144..148  canonical M31 asset id
148..152  zero reserved
152..184  recipient note commitment
184..216  change note commitment
```

The processor requires the envelope and statement to agree on all duplicated
fields, authenticates the retained historical root, selects the exact active
registry profile/release, validates a fresh nullifier-marker PDA, invokes the
selected verifier read-only, then atomically consumes the marker and appends
the recipient and change commitments in that order.

### Withdrawal: `ASWD`, version 1, exactly 432 bytes

```text
0..8      ASWD outer header
8..216    exact 208-byte ASPA historical-anchor envelope
216..432  exact 216-byte ASWP verifier statement
```

```text
0..4      magic "ASWP"
4         statement version 1
5         withdrawal transition kind
6         canonical digest encoding version
7         zero reserved
8..40     Pool pubkey
40..72    deployment domain
72..80    anchor root sequence
80..112   canonical anchor root
112..144  canonical nullifier
144..148  canonical M31 asset id
148..152  nonzero withdrawal amount below the value limit
152..184  destination legacy token-account pubkey
184..216  change note commitment
```

After proof acceptance, the program uses the canonical vault-authority PDA to
execute one legacy SPL Token `TransferChecked`, requires the exact vault debit
and destination credit, consumes the marker, and appends exactly one change
commitment. A verifier, token, marker, or append error produces no successful
Pool return data and the Solana runtime must roll back all CPIs/account changes.

### Prepare settlement: `ASPP`, version 1, exactly 456 bytes

The 24-byte `ASPP` header binds the transition kind and inclusive
`not_before_slot`/`expires_at_slot` interval. It is followed by one exact
432-byte `ASPT` or `ASWD` instruction whose nested kind must match. Preparation
authenticates the finalized 720-byte verifier-owned `ASRA`, the live registry
selection and exact source Pool/history images, performs the checked append,
then persists a 10,000-byte Pool-owned `ASPS` core and, only at rollover, an
8,504-byte `ASRS` shard. Their canonical PDA domains are:

```text
ASPS core: [b"aspis-settle-plan-v1", pool, statement_digest,
            source_sequence_le, plan_authority]
ASRS shard: [b"aspis-settle-roll-v1", core_plan_address]
```

The preparation account layout is documented in the focused prepared-
settlement checkpoint. It creates no marker and performs no custody transfer or
Pool/history mutation.

### Final prepared settlement: `ASPF`, version 1, exactly 224 bytes

```text
0..4      magic "ASPF"
4         version 1
5         transition kind
6         canonical digest encoding version
7         zero reserved
8..224    exact canonical 216-byte ASCP or ASWP statement
```

The common exact accounts are:

```text
0  [signer,writable] plan authority/refund recipient (System-owned)
1  [writable]        canonical Pool state PDA
2  [writable iff the first new root remains here] current root page
3  [writable]        canonical next root page, rollover only
+  [writable]        canonical nullifier-marker PDA
+  []                finalized verifier-owned ASRA
+  []                verifier-registry PDA
+  []                exact profile/release entry PDA
+  [writable]        exact 10,000-byte ASPS core PDA
+  [writable]        exact 8,504-byte ASRS shard PDA, rollover only
+  [executable]      System Program
```

A withdrawal alone appends this exact suffix:

```text
[]            asset mint
[writable]    canonical vault token account
[writable]    statement-bound destination token account
[]            canonical vault-authority PDA
[executable]  original SPL Token program
```

The processor rejects missing/trailing or aliased accounts and wrong signer,
writable, owner, executable, PDA or data-length states. It takes one `Clock`
slot, reauthenticates the finalized `ASRA` and live registry at that same slot,
then invokes the pure prepared-plan apply gate against the exact source
Pool/current/optional-next history images. After that succeeds it creates or
populates the marker, executes the authenticated legacy-token withdrawal (if
any) and proves the exact vault/destination deltas, copies the authenticated
next Pool/history images, populates the marker, tombstones/refunds the optional
shard and core, and only then emits the normal 200-byte `ASTR`. Solana rollback
makes any earlier CPI or write invisible on a later error; replay finds neither
a fresh marker nor live plan accounts.

## Spend account ABI

Both spend instructions begin with a compact page prefix:

```text
0  [writable] Pool state PDA
1  [writable iff also the mutable current page] anchor root page
2  current root page, only when different from the anchor page
+1 canonical fresh next root-page PDA, only when this append rolls over
```

A distinct historical anchor page is read-only. The current page is writable
only if the append places at least one root in it; a full current page is
read-only when all new roots land in the next page. No duplicate page meta is
permitted when anchor and current are the same account.

The private-transfer suffix is:

```text
[writable]         nullifier-marker PDA
[signer,writable]  System-owned payer
[executable]       System Program
[]                 verifier-registry PDA
[]                 exact profile/release entry PDA
[executable]       selected verifier program
[]                 selected-verifier-owned sealed proof account
```

Withdrawal appends this exact token suffix:

```text
[]            asset mint
[writable]    canonical vault token account
[writable]    statement-bound destination token account
[]            canonical vault-authority PDA
[executable]  original SPL Token program
```

Registry, entry, verifier, and proof accounts are always read-only. The proof
account is never forwarded to any program other than the registry-selected
verifier. Pool, history, marker, payer, System, vault, and destination accounts
are not forwarded to that verifier.

## Successful spend return data

Private transfer and withdrawal success replace the verifier's intermediate
return data with exactly one 200-byte `ASTR` receipt:

```text
0..4      magic "ASTR"
4         version 1
5         transition kind
6         output count (2 private, 1 withdrawal)
7         canonical digest encoding version
8..40     Pool pubkey
40..72    nullifier
72..104   recipient commitment (private) or change commitment (withdrawal)
104..136  change commitment (private) or destination token-account pubkey
136..140  zero (private) or withdrawal amount
140..144  zero reserved
144..152  first leaf index
152..160  second leaf index (private) or zero (withdrawal)
160..168  resulting root sequence
168..200  resulting root
```

The entrypoint clears return data before dispatch and again on every error, so
an intermediate verifier `ASVS` result cannot be mistaken for Pool success.

## Validation and mutation order

Before proof dispatch or any Pool mutation, spend paths validate the exact
instruction, account count/order/uniqueness, runtime-derived Pool and page
PDAs, owners/loader identities/privileges, current history, historical anchor,
tree capacity, marker freshness, optional rollover PDA, verifier/proof claim,
and (for withdrawal) the complete token transfer plan. The proof CPI happens
before root-page or marker creation. The append kernel computes and validates
the entire heap-backed next state and acquires every mutable Pool/history
borrow before its marker/token callback; after that callback succeeds, the
prevalidated fixed-size state/history persistence contains no fallible
operation. Keeping the 1,000-byte state off the instruction frame is required
by Solana's 4 KiB SBF stack limit and does not change its canonical wire image.

Initialization and rollover may perform earlier System/Token CPIs whose
failure atomicity is provided by Solana transaction rollback. Host unit tests
prove no Pool bytes change on rejected proof paths; an SVM integration test is
still required to evidence rollback after an already successful CPI followed
by a later outer error.

## Frozen state and PDA domains

```text
Pool state:       [b"aspis-pool-state-v1", asset_mint]
Root page:        [b"aspis-pool-root-page-v1", pool, page_number_le]
Nullifier marker: [b"aspis-pool-nullifier-v1", pool, canonical_nullifier]
Vault authority:  [b"aspis-pool-vault-authority-v1", pool]
Vault token:      [b"aspis-pool-vault-token-v1", pool]
```

The program retains the existing 1,000-byte `ASPK` version-2 state, 8,256-byte
`ASPR` root pages, 208-byte `ASNM` markers, depth-20 Poseidon tree, and pinned
empty-root table. No Tag-73, K1, verifier-routing, or statement cryptography is
changed by this entrypoint layer.

## Mandatory release boundaries

This crate is not by itself a mainnet release:

- No deployment key or program id has been selected. Release tooling must pin
  one build/client program id, derive every address against it, and verify the
  deployed executable identity. The binary intentionally trusts the runtime
  `program_id` instead of a source-level `declare_id!` constant.
- The 216-byte Pool statement wires are frozen, but this repository does not
  yet contain an approved verifier profile/release proving their complete
  semantics. Registry governance must admit only reviewed releases that prove
  exact 1-to-2 value conservation or withdrawal authorization/value
  conservation for these payloads. The V1 Pool ABI is fee-free and withdrawal
  always has one change output.
- Loader upgrade authority, deployed-code hash/reproducibility, registry
  governance creation/mutation, and client transaction construction remain
  release-system responsibilities.
- A focused `cargo-build-sbf` build succeeds without stack-offset/frame-clobber
  diagnostics. A pinned reproducible release build, validator/LiteSVM
  execution, account-lock behavior, transaction-size feasibility,
  CPI/return-data semantics, rollback after successful CPI, rent behavior for
  every initialization form, and compute-unit measurements remain integration
  gates.
- Token-2022, extensions, transfer fees/hooks, multisig/delegate deposits,
  wrapped-native vaults, vault delegates/close authorities, pause/migration,
  and arbitrary-output/raw-append instructions are intentionally unsupported.

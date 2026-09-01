# V7 Registry V2 immutable-deployment source bridge

This focused bundle closes the finite 256-bit projection and immutable
loader-v3 certificate boundary left by the preceding Registry V2 one-terminal
caller and literal `AccountInfo` bridges. It changes no production Rust,
cryptography, Pool state, wire format or deployment.

## What is kernel checked

The translated source projection preserves production's fail-closed branch
order for `authenticate_immutable_loader_v3_deployment_v2` after three named
Solana/source primitives return. Successful execution proves:

- the expected Program key, loader-v3 ownership, executable/readonly/nonsigner
  Program shape;
- loader-v3-owned, non-executable, readonly/nonsigner ProgramData shape;
- an exact 36-byte Program image and the `Program` loader-state variant;
- equality of the decoded link, supplied ProgramData account and derived PDA;
- data past the exact 45-byte ProgramData metadata prefix;
- the `ProgramData` variant with `upgrade_authority_address = None`;
- a nonzero SHA-256 result for the complete payload after that prefix;
- exact equality with the instruction's expected executable SHA-256;
- exact certificate output fields, without truncation or substitution.

The principal theorems are:

- `translated_immutable_deployment_success_is_exact`;
- `translated_deployment_source_root_success_is_exact`;
- `transaction_local_projection_iff_literal_256_fields`;
- `literal_256_fields_supply_fixed_caller_certificate_fields`.

The last two list every 32-byte Registry/Entry identity used by the fixed
caller and require equality reflection only for those concrete transaction
pairs. They do not assume a globally injective 256-bit-to-64-bit encoding,
which cannot exist. They also expose the production Entry policy binding as a
separate projected value because the earlier fixed caller type has no
`entry.policy_binding` field.

## Exact source/tool boundary

The literal production helper itself extracts cleanly with Charon 0.1.223.
Current Aeneas fails while giving back the nested shared `AccountInfo` borrow
abstraction (`SymbolicToPureValues.ml:878`) before reaching the certificate
logic. The failure is frozen in `evidence/production-helper-aeneas.stderr`.

Accordingly, the translated harness treats exactly three production results
as explicit input values:

1. `bincode::deserialize::<UpgradeableLoaderState>` for Program and
   ProgramData metadata;
2. `Pubkey::find_program_address` for the loader-v3 ProgramData PDA;
3. `solana_program::hash::hash(&programdata[45..])`.

The Lean theorem does not assume these values are correct and jump to its
conclusion. It executes and proves every subsequent account, length, variant,
link, PDA-equality, authority, nonzero-hash and expected-hash gate. Correctness
of those three primitives and the binding from their literal production calls
to the observation values remains explicit. Charon/Aeneas/compiler provenance
and Solana account-borrow/runtime semantics remain ordinary source-tool
boundaries.

Five focused production V2 tests independently exercise the real helper,
including loader link/owner/privilege/upgrade-authority/hash mutations and
write rollback. Their frozen output is in `evidence/production-v2-tests.*`.

## Replay

Run source hashes and Rust tests locally. Run extraction and Lean replay on a
Linux build host in a no-swap cgroup as required by repository policy:

```sh
./source-audit.sh
./replay-rust.sh

CHARON_BIN=/path/to/charon \
AENEAS_BIN=/path/to/aeneas \
./replay-extraction.sh

AENEAS_LEAN_BACKEND=/path/to/aeneas/backends/lean \
LEAN_BIN=/path/to/lean-4.31.0 \
./replay-lean.sh
```

Charon's raw LLBC includes the disposable absolute workspace path. The replay
therefore reports its run-specific hash and compares the Aeneas-generated Lean
and translation manifest byte-for-byte; the committed extraction artifact has
its own frozen hash in `REPLAY-RESULT.txt`.

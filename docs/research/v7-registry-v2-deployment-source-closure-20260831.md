# Registry V2 immutable-deployment source closure

Status: **finite projection and post-primitive certificate logic green; full
literal helper remains at one explicit Aeneas `AccountInfo` borrow boundary**.

At source revision `9a5fd7aec741242b840d934e4eaaeb3c41e6016c`, Charon extracts production
`authenticate_immutable_loader_v3_deployment_v2` without errors. Aeneas then
fails while giving back the nested shared `AccountInfo` borrow abstraction at
`SymbolicToPureValues.ml:878`, before the loader certificate logic can be
emitted.

The focused bridge therefore translates the exact control flow after three
named primitive outputs are available: loader-state bincode decoding,
loader-v3 ProgramData PDA derivation, and SHA-256 of the complete executable
payload after the 45-byte metadata prefix. Lean proves successful execution
forces every Program/ProgramData owner and privilege check, exact Program
length and variant, linked/derived/account PDA equality, revoked upgrade
authority, nonempty payload, nonzero full-payload hash, expected-hash equality,
and exact certificate output. These are values passed through checked control
flow, not conclusion-shaped theorem premises.

The same proof adds a finite 32-byte-to-`u64` correspondence for every Registry
V2 and Entry V2 identity consumed by the existing fixed one-terminal caller.
Each concrete comparison has its own equality-reflection obligation; no global
injectivity claim is made. The production Entry policy binding is carried as a
separate projected value because the earlier fixed caller type does not contain
an `entry.policy_binding` field.

The complete replay bundle is
`aeneas-verif/v7-registry-v2-deployment-certificate-source-20260831/`.
Its final clean Lean replay used 2,665,508 KiB peak RSS with zero swap and
reported exactly `propext`, `Classical.choice`, and `Quot.sound`. Five focused
production Registry V2 tests passed, including link, owner, privilege,
upgrade-authority and digest mutations with exact rollback.

The remaining source boundary is finite and explicit: bind the literal
production calls for bincode/PDA/SHA to the three observation values through a
toolchain capable of translating the shared `AccountInfo` borrow graph (or an
upstream-equivalent source factoring proved against those calls). No
cryptographic or Registry theorem needs weakening.

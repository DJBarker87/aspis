# V7 Tag-73 current parser accepted-source bridge

This bundle pins the production Tag-73 deferred parser at branch revision
`f45c21b1db2b05a60582fb84cae371e6bdc1a3ff` and connects literal translated
parser success to its exact byte layout.

## Result

The strongest theorem is
`current_parser_success_has_exact_fixed_reader_input` in
`proof/V7Tag73CurrentParserLayoutBridge.lean`.  From literal translated parser
success it proves:

- the selected frontier has at most 203 nodes;
- the complete proof body is exactly `19948 + 52 * frontierNodes` bytes;
- the returned fixed-field slice is the first 9,936 input bytes; and
- that returned slice has length exactly 9,936.

`deferred_parser_success_has_exact_layout` additionally pins every C1/C2 root,
work-nonce, query-section, and two-frontier slice.  The wrong/trailing-length
theorem is fail-closed.

This is the parser-side input required by the separately proved 641-QM31,
2,564-limb production reader theorem.

## Source and extraction boundary

The production `crates/aspis-core/src/v7_onefold.rs` SHA-256 is:

```text
6abb0376100611c5553258062480777187785579f402c9c1d3ce72379518258f
```

Pinned Charon 0.1.223 cannot select an inherent method as a standalone root.
`overlay/v7-current-parser-extraction-only.patch` therefore adds a free wrapper
only in the isolated extraction copy.  The wrapper directly calls the deployed
inherent method, and
`extracted_entry_is_exact_deferred_parser` proves their equality by `rfl`.
The overlay is never compiled into the production SBF.

The normalized LLBC SHA-256 is:

```text
ec9cd3a21e3adcb1e177014028aee64e59f915aeb9f309e93b4b3868f32b5bef
```

Toolchain identities:

```text
Charon: 0.1.223
Charon binary SHA-256: b2b0961a3c55aca64752b2fa4a4701ba0c06b860236979e5727c07de8ac2310c
Aeneas: d860ac47-tag73-variantfn-namespace-r1
Aeneas binary SHA-256: 017fc5685a79d4aa3aa19f9529d57fdf167c1387c9b1fee63a254994f5ff9d5a
```

The five core-library declarations emitted by Aeneas have transparent
definitions in `FunsExternal.lean`; the axiom template is excluded and is not
imported.

## NUC evidence

All runs used `MemorySwapMax=0`:

| Stage | Unit | Result | Peak RSS |
|---|---|---:|---:|
| current parser Charon extraction | `aspis-v7-current-parser-charon-r4` | pass, 2.15 s | 562,120 KiB |
| Aeneas translation | `aspis-v7-current-parser-aeneas-r5` | pass, 0.92 s | 212,112 KiB |
| generated Lean modules | `aspis-v7-current-parser-lean-r2` | pass, 9.23 s | 2,539,952 KiB |
| source bridge | `aspis-v7-current-parser-bridge-r1` | pass, 2.14 s | 2,503,388 KiB |
| exact layout and fixed-reader-input bridge | direct NUC replay after `aspis-v7-current-parser-layout-r7` | pass, 30.69 s | 6,876,104 KiB |

The printed axiom set is restricted to `propext`, `Classical.choice`, and
`Quot.sound`.  There is no `sorry`, `admit`, `sorryAx`, `native_decide`, or
project-specific axiom in imported proof source.

No production Rust, SBF, deployment, transaction, or on-chain account was
changed by this bundle.

The final axiom-printing replay and its exact environment are recorded in
`evidence/REPLAY-RESULT.txt`.

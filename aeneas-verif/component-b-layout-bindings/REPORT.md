# Component-B terminal/layout correspondence

## Verdict

The production-default V5 release has a proved deterministic correspondence
between the Component-B terminal, covector, and layout.

The principal theorem is
`ComponentBRelationClaimsLayoutInstantiation.extracted_component_b_relation_claims_layout_equalities`.
It executes the source-authentic terminal-covector builder, the source-authentic
1,024-row Component-B copy, and the source-authentic C2 constructor, then proves:

1. every relation-consumer covector row is the maintained
   `terminalWeights point 1` row;
2. every committed Component-B row agrees with the maintained `rowMessage`
   after multiplication by that terminal weight;
3. the maintained dense dot product is `tenRoundTerminal`; and
4. the actual Nat-indexed 1,024-row accumulation used by the extracted
   relation-claims loop is `tenRoundTerminal`.

There is no theorem equating the complete unweighted lane with
`rowMessage`: pad and pivot rows differ outside the terminal functional's
support.  The weighted statement is the exact consumer-facing obligation.

No opaque `faithful`, executable-correspondence, or Rust/model equality premise
remains. The theorem has three preconditions: canonical terminal-point words,
canonical mask words, and the exact successful execution equation of the
generated encoder. Only the last is executable, and it is the generated
function run itself rather than an abstract equality assumption.

The sampler, production host flow, and full V5 integration are joined in the
current-source Component-B and A/B/C proof suites indexed from
[`aeneas-verif/README.md`](../README.md).

## Recorded provenance

- Workspace HEAD during final replay:
  `27e8265d28de88e7967626a2d2432ef161fb4f49`
- Charon: `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`
- Aeneas: `b59d5188c082f704a418c7cb4e52ad69328002d1`
- Rust: `nightly-2026-06-01`, `rustc 1.98.0-nightly (14210df0e 2026-05-31)`
- Maintained proof replay: Lean `4.32.0`
- `crates/aspis-prover/src/v5_spend_messages.rs`:
  `87a5363df9891c8c6269943a1a7d76acad1a06ef13da61a68f9768c95afca629`
- `crates/aspis-prover/src/v5_sumcheck_mask.rs`:
  `26ed8e873da039503976fe08dcd26894b847c75007497d290fa74c4c9296319a`

Both LLBC files embed the current `v5_spend_messages.rs` bytes exactly.  Charon
reports `has_errors = false`.

## Source-authentic extractions

### Terminal covector and encoder

Source functions:

- `v5_structured_terminal_covector`,
  `crates/aspis-prover/src/v5_split_layer_zero.rs:153`;
- `V5StructuredBLane::encode`,
  `crates/aspis-prover/src/v5_spend_messages.rs:282`.

Command:

```text
cd crates/aspis-prover
charon cargo --preset=aeneas \
  --start-from='aspis_prover::v5_mask::split_layer_zero::v5_structured_terminal_covector,aspis_prover::v5_mask::spend_messages::_::encode' \
  --dest-file='aeneas-verif/component-b-layout-bindings/llbc/layout_full_v5.llbc' \
  -- --release --locked -p aspis-prover --features v5-mask
aeneas -backend lean \
  aeneas-verif/component-b-layout-bindings/llbc/layout_full_v5.llbc \
  -dest aeneas-verif/component-b-layout-bindings/generated/full-v5 \
  -max-heartbeats 200000 -max-recdepth 1000 \
  -abort-on-error -warnings-as-errors -no-progress-bar
```

Artifacts:

- LLBC: `8469d1d9d5dc1a942af8b2e2186b68c7d96d830e530776a86f3b4e93a7d490c9`
- raw Lean: `c504afa43519ccdbe134c575fa18f656dd8df6cc2be7b3b79392b8aa35e049a4`
- normalized Lean-4.32 module:
  `06c057b0788e2907323625828677bb394f463936d41d879bdfe68f00e7f3702e`

The earlier `.expect("fixed B message shape")` spelling introduced an Aeneas
string proof whose generated theorem closure contained a native decide axiom.
The source now uses an explicit `match` with the same unreachable error branch
(`v5_spend_messages.rs:308-311`).  Fresh extraction removes that axiom; the
encoder and all downstream integration theorems now have only the permitted
kernel base.

### Component-B row copy and C2 slot

Source functions:

- `component_b_message_values`, `v5_spend_messages.rs:341`;
- `assemble_v5_c2_messages`, `v5_spend_messages.rs:354`.

Command:

```text
cd crates/aspis-prover
charon cargo --preset=aeneas \
  --start-from='crate::v5_mask::spend_messages::component_b_message_values,crate::v5_mask::spend_messages::assemble_v5_c2_messages' \
  --dest-file='aeneas-verif/component-b-layout-bindings/c2-slot/llbc/component_b_c2_slot.llbc' \
  -- --release --locked -p aspis-prover --features v5-mask
aeneas -backend lean \
  aeneas-verif/component-b-layout-bindings/c2-slot/llbc/component_b_c2_slot.llbc \
  -dest aeneas-verif/component-b-layout-bindings/c2-slot/generated/raw \
  -max-heartbeats 200000 -max-recdepth 1000 \
  -abort-on-error -warnings-as-errors -no-progress-bar
```

Artifacts:

- LLBC: `8e956f2aa05c5223f153175daee04818170438a1ebc05319999dc89d0a67b614`
- raw Lean: `8655c4d548ed1099cc5d846a8409bad6ca90729142a32a6cddb899ee1e7c180e`
- normalized Lean-4.32 module:
  `d3fe91d5d20d9a2bea8a7b548bbf677cfd58e5916b794d049127be2e3492d365`

## Kernel theorem inventory

The source-facing leaves are:

- `ComponentBLayoutBindingsProof.extracted_terminal_covector_rows_eq_terminalWeights`;
- `ComponentBEncodedMessageBindingProof.extracted_encode_success_terminal_support`;
- `ComponentBEncodedMessageBindingProof.extracted_component_b_encode_weighted_rowMessage`;
- `ComponentBC2SlotProof.extracted_component_b_message_values_exact`;
- `ComponentBC2SlotProof.extracted_assemble_v5_c2_messages_slot_one`.

The relation-facing results are:

- `extracted_component_b_relation_claims_covectorRows`;
- `extracted_component_b_committed_rows_eq_encoded_lane`;
- `extracted_component_b_relation_claims_weightedMessageRows`;
- `extracted_component_b_relation_claims_layout_equalities`.

The three exported relation theorems printed by the final module depend
exactly on:

```text
[propext, Classical.choice, Quot.sound]
```

The same permitted closure holds for the source-facing encoder and terminal
theorems.  There is no `sorryAx`, `ofReduceBool`, native-decide axiom, declared
axiom, `sorry`, `admit`, `native_decide`, `unsafe`, or raised handwritten limit.

## Validation

- Lean 4.32 direct replay at default handwritten limits: pass.
- Final theorem axiom audit: pass.
- Targeted Rust test
  `component_b_copy_and_c2_slot_constructor_preserve_exact_order`: 1/1 pass.
- `cargo check --release --locked -p aspis-prover --features v5-mask`: pass
  (workspace-pre-existing warnings remain).
- `rustfmt --check` on `v5_spend_messages.rs` and
  `v5_sumcheck_mask.rs`: pass.
- Forbidden-token scan: pass.
- `git diff --check` / no-index whitespace checks: pass.

The final Lean replay reports only pre-existing `unusedSimpArgs` linter
warnings in the long Aeneas loop-invariant proof. The final integration,
encoder binding, normalized generated modules, relation bridge, and C2 proof
compile without warnings.

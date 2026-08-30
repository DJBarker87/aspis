# Component-B deterministic pipeline integration

## Result

Lean 4.32 theorem
`ComponentBDeterministicPipelineCapstone.sampled_mask_to_c2_relation_and_tenRoundTerminal`
proves the deterministic source-authentic pipeline:

1. successful generated `V5SumcheckMask::sample`;
2. the authentic generated mixing/evaluation helper, returning the same
   existential `mixed` and `terminal`;
3. the maintained `terminalCovector` and `tenRoundTerminal` recurrence;
4. the authentic generated terminal-covector builder;
5. the authentic structured-B encoder, actual 1,024-row copy, and generated
   C2 constructor with exact `[Hcopy, copied, componentC]` order;
6. the maintained terminal-weighted Component-B row relation;
7. both the maintained dense dot product and the actual Nat-indexed source
   accumulation.

The theorem additionally proves that transporting either maintained relation
sum into the evaluator's authenticated exact tower gives exactly the returned
generated `terminal`. It states only the weighted row equality:
no unweighted full-lane equality is claimed at pad or pivot rows.

## Principal theorem interface

The executable premises are:

- one successful actual sampler run;
- totality of the supplied `Qm31WordSource.next_word` implementation;
- canonical point, total-claim, eta, and real-round inputs required by the
  already-proved generated arithmetic;
- one successful actual `V5StructuredBLane::encode` run for the same sampled
  mask and supplied pads/pivot pad;
- the supplied H-copy and Component-C vectors.

The existential conclusion includes the exact helper/builder/copy/assembly
runs, endpoint equality, terminal canonicality, covector length/canonicality,
pointwise terminal-weighted row equality, maintained dot/source-sum
equalities, and exact-tower equalities to the generated evaluator terminal.
The `encodeRun` premise is an ordinary successful-execution input, not an
opaque correspondence premise.

## New bridge theorems

- `point_canonical_for_layout`
- `sampled_mask_canonical_for_encoder`
- `exactTail_eq_layoutMaskTails`
- `relationExactToLayout_tailEvaluation`
- `relationExactToLayout_chainContributions`
- `relationExactToLayout_tenRoundTerminal`
- `relation_tenRoundTerminal_to_generated_terminalCovector`
- `sampled_mask_to_c2_relation_and_tenRoundTerminal`

The exact-tower bridge follows the maintained `List.foldl` recurrence.  It is
not a `Faithful` predicate, opaque transport assumption, or parallel model.

## Lean-4.32 compatibility normalization

The two validated bundles contain colliding Lean module/declaration names. The
new bundle retains two mechanically checked normalizations:

- `generated/ComponentBLayoutBindingsGenerated.lean` is the accepted layout
  generated module with exactly four declarations omitted because the larger
  authentic sampler extraction already declares them:
  `M31.neg`, `CM31.neg`, `QM31.ZERO`, and `QM31.neg`.
- `generated/MultilinearEvalFormula.lean` contains the two previously audited
  theorem bodies under their distinct original namespaces, with one combined
  import header.  This preserves both meanings of the colliding module name.

`replay-lean432.sh` reconstructs both normalizations from the authenticated source
files and byte-compares them before compiling.

## Authentication

- Charon: `cb50ff16b9f1066b8a97dc06da704de2da2fa41c`
- Aeneas: `b59d5188c082f704a418c7cb4e52ad69328002d1`
- Lean: `4.32.0`
- unified sampler/mixing/evaluator LLBC SHA-256:
  `e2f683b62a7827e6b30c66cbb5038ee069db4979fe56508997e307e64d678bf4`
- layout LLBC SHA-256:
  `cd367c196b0e4cb0b5fac92a4b761008a81851e8fbcc9022ecf83c93333c590d`
- C2 copy/constructor LLBC SHA-256:
  `8e956f2aa05c5223f153175daee04818170438a1ebc05319999dc89d0a67b614`
- current `v5_sumcheck_mask.rs` SHA-256:
  `26ed8e873da039503976fe08dcd26894b847c75007497d290fa74c4c9296319a`
- current `v5_mask.rs` SHA-256:
  `a1516a5ab348d1e374d908844545054f1fd5647ea12ff56cff273cb1b2b7d05c`
- integration proof SHA-256:
  `9ffcb3bcf1eb63f33959e28414cdebc5d77b96b9e2198def9bc3303a39175866`
- clean replay log SHA-256:
  `93eafde98212887cad93acd1774738b8222e0a1033407e534832307f7b4d64cc`

The source LLBC/raw Lean artifacts remain in the two consumed source bundles;
their exact paths and hashes are checked by the replay script.  The retained
`olean-deps/` objects are hash-pinned Lean-4.32 replay dependencies for the
already-proved relation/MLE chain.

## Verification

Clean command:

```sh
AENEAS432_BACKEND=$AENEAS_LEAN_BACKEND \
COMPONENT_B_PIPELINE_REPLAY_OUT=<temporary> \
  aeneas-verif/component-b-mask/deterministic-pipeline-current-20260722/replay-lean432.sh
```

Result: PASS.  Eight new exported theorems were audited with `#print axioms`.
Every theorem depends only on
`{propext, Classical.choice, Quot.sound}`.  The replay rejects `sorryAx`,
`ofReduceBool`, forbidden proof tokens, raised heartbeat limits, and raised
recursion limits.  Compilation used Lean default limits.

## Residual scope

This theorem proves deterministic algebra and authentic layout execution.  It
does not prove sampler uniformity, Fiat-Shamir/transcript binding, PCS
authentication, selector least-good enforcement, deployed-v4 equivalence, v5
freeze, or zero knowledge.  Those assumptions remain explicitly outside this
local theorem.

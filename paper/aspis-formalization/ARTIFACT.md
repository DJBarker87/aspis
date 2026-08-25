# Artifact guide for the Aspis paper

This guide maps the mathematical names in the paper to exact repository
artifacts. Internal release labels and Lean declaration names are kept here so
that the manuscript remains readable.

Paper title: **Aspis: End-to-End Formal Verification of a Transparent Private Spend
on Solana**

Development repository: <https://github.com/DJBarker87/aspis>

Frozen V5 publication tag:
[`aspis-v5-formalization-paper-v1`](https://github.com/DJBarker87/aspis/tree/aspis-v5-formalization-paper-v1)

Formal source baseline: `a561d9a304a6c86fb037c974c4198b4eb94ecb61`

Deployed-program source: `06788d44d30ea8cbd391899dddaf6f0acc6e4a3f`

The publication tag points to the repository revision containing this guide,
the manuscript source, and the generated PDF. The formal replay reads the
tracked source baseline, while the deployment bundle retains its earlier clean
build source. The moving development branch is not the publication identity.

## 1. Main theorem and clean replay

Paper result: **End-to-end accepted-execution theorem**

- Lean file:
  `aeneas-verif/v5-result-aware-source-link-20260821/proof/V5AcceptedOneRunDeterministicFinal.lean`
- Lean declaration:
  `AspisV5AcceptedOneRunDeterministicFinal.accepted_composite_security_conclusion_for_any_terminal_evaluator`
- Replay script: `aeneas-verif/scripts/replay-accepted-path-lean432.sh`
- Pinned Aeneas revision:
  `b59d5188c082f704a418c7cb4e52ad69328002d1`
- Recorded closure size: 331 tracked Lean modules

From the repository root:

```sh
aeneas-verif/scripts/replay-accepted-path-lean432.sh
```

The script resolves the import closure from tracked files, prepares the pinned
Aeneas environment, rejects `sorry`, `admit`, `native_decide`, `unsafe`, and
`ofReduceBool` in the staged proof closure, builds all required formal and
generated modules, and prints the final theorem's axioms. Set
`ASPIS_KEEP_ACCEPTED_REPLAY_WORK=1` to preserve its temporary manifest and log.

A fast manifest-only check is:

```sh
ASPIS_ACCEPTED_RESOLVE_ONLY=1 \
  aeneas-verif/scripts/replay-accepted-path-lean432.sh
```

## 2. Paper theorem map

| Paper name | Lean declaration | Source file |
| --- | --- | --- |
| Trace soundness for the spend relation | `AspisV5AcceptedSpendRelation.extracted_trace_implies_spend_relation` | `AspisFormal/AspisFormal/V5AcceptedSpendRelation.lean` |
| Circle generator order | `AspisCircleGroupOrder.orderOf_g` | `AspisFormal/AspisFormal/CircleGroupOrder.lean` |
| Coherent four-fold extraction | `AspisV5FriReleasedAdaptiveExtraction.accepted_ideal_fri_extracts_initial_candidate_or_counted` | `AspisFormal/AspisFormal/V5FriReleasedAdaptiveExtraction.lean` |
| Bounded distinct-query distribution | `AspisV5BoundedQuerySamplerUniformity.deployed_q18_conditioned_uniform` | `AspisFormal/AspisFormal/V5BoundedQuerySamplerUniformity.lean` |
| Exact query miss ratio | `AspisV5WithoutReplacementQuerySoundness.ideal_miss_probability_eq_descFactorial_ratio` | `AspisFormal/AspisFormal/V5WithoutReplacementQuerySoundness.lean` |
| Complete byte transcript | `AspisV5TranscriptConnection.source_shaped_helper_composition_exact` | `AspisFormal/AspisFormal/V5TranscriptConnection.lean` |
| Five authenticated opening sections | `AspisV5MerkleRustBridge.exactV5Run_yieldsForest` | `AspisFormal/AspisFormal/V5MerkleRustBridge.lean` |
| Authenticated value consumption | `AspisV5MerkleConsumedValueBridge.rustObservation_exposes_only_authenticated_fri_values` | `AspisFormal/AspisFormal/V5MerkleConsumedValueBridge.lean` |
| Main accumulator equality | `AspisV5AcceptedSnapshotMainDotExact.accepted_snapshot_main_dot_exact` | `aeneas-verif/v5-result-aware-source-link-20260821/proof/V5AcceptedSnapshotMainDotExact.lean` |
| Compact accumulator equality | `AspisV5AcceptedDeterministicRelationTail.accepted_snapshot_compact_dot_exact` | `aeneas-verif/v5-result-aware-source-link-20260821/proof/V5AcceptedDeterministicRelationTail.lean` |
| End-to-end accepted execution | `AspisV5AcceptedOneRunDeterministicFinal.accepted_composite_security_conclusion_for_any_terminal_evaluator` | `aeneas-verif/v5-result-aware-source-link-20260821/proof/V5AcceptedOneRunDeterministicFinal.lean` |
| Conditional work-normalized soundness | `AspisV5UnifiedSecurityExperiment.work_normalized_accepted_false_probability_le_two_pow_neg_100_of_released_core` | `AspisFormal/AspisFormal/V5UnifiedSecurityExperiment.lean` |
| Protocol budget arithmetic | `AspisV5HundredBitSecurityMargin.corrected_selected_release_core_le_seven_tenths` | `AspisFormal/AspisFormal/V5HundredBitSecurityMargin.lean` |
| Fixed-victim classification | `AspisV5FixedVictimTheftGame.fixed_victim_attack_implies_mathematical_failure` | `AspisFormal/AspisFormal/V5FixedVictimTheftGame.lean` |
| Exact modeled spend state | `AspisV5TheftStateTransitionReduction.v5_source_success_exact_state` | `AspisFormal/AspisFormal/V5TheftStateTransitionReduction.lean` |
| Fixed-schedule witness independence | `AspisV5DeployedZeroKnowledgeBridge.encoded_concrete_fixed_schedule_view_is_witness_independent` | `AspisFormal/AspisFormal/V5DeployedZeroKnowledgeBridge.lean` |

Use `rg` to resolve a declaration if its namespace changes during maintenance:

```sh
rg -n '^theorem <declaration_name>' AspisFormal aeneas-verif
```

## 3. Formal claim boundary

The final translated-execution theorem derives, from any successful call:

- parsed proof body and live-statement digest;
- exact Fiat-Shamir transcript and six ordered work checks;
- eighteen distinct query positions;
- five authenticated opening sections and all values consumed later;
- four FRI folds, coordinate calculations, and the final four coefficients;
- seventy-six decoded claims, four prepared claims, and fifty-eight relation
  fields;
- four relation rounds, the twelve-component main accumulator, the
  four-component compact accumulator, and both final dot products.

The two formal composition tasks that remain are:

1. identify every field of the translated Rust live statement with the
   abstract `V5PublicStatement` used by the false-acceptance and theft games;
2. embed the deterministic successful-call classification in the causal
   `WorkNormalizedV5AdversarialExperiment` used for the numerical bound.

The assumptions ledger is in `docs/assumptions-ledger.md`.

## 4. Mainnet and build evidence

Primary bundle:
`release/aspis-v5-tag67-mainnet-v1/`

RPC archive:
`release/aspis-v5-tag67-mainnet-rpc-archive-v1/`

Frozen program candidate:
`release/aspis-v5-tag67-frozen-candidate-v1/`

Recorded identities:

| Artifact | Identity |
| --- | --- |
| Program source commit | `06788d44d30ea8cbd391899dddaf6f0acc6e4a3f` |
| Program source tree | `9b6bdfddb3c213addc2bb705c8130cce4fb2c351` |
| Program bytes | 1,258,496 |
| Program SHA-256 | `4cf3c1d5ddd47efa68875c0070247e007083c5c9bb2d5988db0d644a609edf40` |
| Program identifier | `7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue` |
| Proof bytes | 75,358 |
| Proof SHA-256 | `330414df587974684643a6062d092db0519d746f0c7efe4ed2108775b685feaf` |
| Public statement bytes | 768 |
| Public statement SHA-256 | `0cdc34bc7f835640cff76d1085df9ba966df9f39eb228f3002f927cf30958113` |
| Spend transaction | `EJviPgF12i9iK2CveVaQSMeFQqDMFPQ1iPRUYEwNQE3zGquTUZNJXPZEENorcQtsnQj1orFmH1TPsgdbR3vJ2fE` |
| Finalized slot | 435,019,536 |
| Compute units | 1,334,452 of 1,356,912 |

Offline checks from the repository root:

```sh
release/aspis-v5-tag67-frozen-candidate-v1/verify.sh
release/aspis-v5-tag67-mainnet-v1/verify.sh
python3 release/aspis-v5-tag67-mainnet-rpc-archive-v1/verify.py
python3 tools/check_release_facts.py
```

The clean source rebuild is separate because it needs the pinned Solana SBF
toolchain. Its environment variables and checks are documented by:

```sh
sed -n '1,260p' release/verify-v5-source-rebuild.sh
```

## 5. Build the paper

Requirements: `latexmk`, PDFLaTeX, BibTeX, and the LaTeX packages named in the
root source file.

From `paper/aspis-formalization`:

```sh
mkdir -p ../../output/pdf
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=../../output/pdf aspis-formalization.tex
```

The final PDF is `output/pdf/aspis-formalization.pdf`. Check its metadata,
fonts, and page rendering before submission:

```sh
pdfinfo output/pdf/aspis-formalization.pdf
pdffonts output/pdf/aspis-formalization.pdf
```

The arXiv upload should contain the root TeX source, `sections/`,
`references.bib`, and any generated bibliography required by the selected
submission workflow. Build products and repository artifacts stay out of the
source archive.

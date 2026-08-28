# Tag-73 exact measured K1.2--K1.6 assembly

Date: 2026-08-28

## Result

`AspisFormal.K1.V7Tag73ExactMeasuredK16Assembly` adds the event-level
capstone

```text
exact_tag73_measured_k16_aok_raw
```

It composes the existing exact K1.2 and K1.6 theorems with the concrete
deployed-schedule events for the intermediate stages:

- K1.3: q16, one-fold, joint query batching and later relation-alpha;
- K1.4: the restoration-wide width-29 event; and
- K1.5: the eight fixed algebraic families plus the restored-gamma residual.

The theorem no longer accepts an abstract K1.3, K1.4 or K1.5 measure-bound
object.  Its remaining probability inputs are inequalities for the literal
sets defined by the exact Tag-73 source model.  K1.2's numerical Merkle term
is constructed internally from the proved adaptive two-tree classifier.

No independence premise and no proof-of-work normalization is introduced.

## Exact remaining formal inputs

| Input | Status / permitted boundary |
| --- | --- |
| `ExactTag73K12SourceObligations` | deterministic accepted-source facts; the translated two-tree caller bridge proves the opening predicate, while final capstone wiring still has to supply the exact caller instance and prefix coverage |
| `initialEncoderExact` | concrete decoder instantiation equality; its circle-code theorem is an explicitly permitted external theorem boundary |
| `ExactTag73K13SourceObligations` | maintained relation-tail composition exists; the final Aeneas namespace/value projection remains |
| q16 event inequality | causal 512-slot router, exact first-cap-203 distribution and semantic count are proved; the literal accepted-event-to-router inclusion remains to be instantiated |
| one-fold event inequality | exact published one-fold bad set and causal sampler law are proved; instantiate the permitted published circle theorem at the exact Tag-73 encoder parameters |
| joint-query-batch inequality | degree-at-most-16 root theorem is proved; connect the exact rho sampler coordinates to the literal event |
| later relation-alpha inequality | three degree-six repair events are proved; connect the exact later-alpha sampler coordinates |
| width-29 inequality | restoration-wide width-29 root cap is proved; instantiate its exact causal ordinary-sampler/source bridge |
| eight fixed K1.5 event inequalities | exact caps and actual-law adapters are proved; finish the deterministic compiler-coordinate/source inclusions |
| restored-gamma inequality | variable-prefix gamma law and scheduler-native provider are proved; finish the exact compiler coordinate equivalence and concrete residual inclusion |
| Poseidon faithfulness | explicitly permitted primitive interface |
| runtime/fuel facts | concrete arithmetic certificates, not cryptographic assumptions |

SHA-256 behavior, the published circle theorem, Poseidon faithfulness and the
Solana runtime remain the explicitly permitted external boundaries.  K1.6's
classical-ROM compiler is already kernel-checked and does not import a BCS
coefficient as an axiom.

## Focused replay evidence

The NUC used the pinned Lean workspace and a cgroup with
`MemorySwapMax=0`.  A one-time cold dependency build was needed because the
cached workspace did not yet contain the restored K1 modules; no unchanged
full replay was repeated afterward.

| Run | Result | Wall | Maximum RSS | Swap |
| --- | ---: | ---: | ---: | ---: |
| Three direct dependencies | PASS, 9,010 cached/cold jobs | 4:19.95 | 8,140,424 KiB | 0 |
| `V7Tag73ExactMeasuredK16Assembly.lean` | PASS | 2.87 s | 6,706,000 KiB | 0 |

The final `#print axioms` output is exactly:

```text
propext
Classical.choice
Quot.sound
```

There is no `sorry`, `admit`, `sorryAx`, project-specific axiom, or hidden
aggregate K1.x premise in the compiled theorem.

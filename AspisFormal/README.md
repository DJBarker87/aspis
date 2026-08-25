# Aspis formal development

This Lean 4 project contains the mathematical security development for the
Aspis transparent private-spend verifier. The companion `aeneas-verif/`
project connects the successful deployed Rust proof-checking path to these
models.

Start with the accessible overview in
[`docs/formal-verification.md`](../docs/formal-verification.md). The exact map
from paper theorem names to Lean declarations is in
[`paper/aspis-formalization/ARTIFACT.md`](../paper/aspis-formalization/ARTIFACT.md).

## Main result

The final source theorem begins with any successful translated verifier call
and derives, from that same execution:

- proof parsing and public-statement digest;
- the exact transcript and six ordered work checks;
- 18 distinct query positions;
- five authenticated opening sections and their consumed values;
- four FRI folds and the final polynomial;
- 76 decoded claims, four prepared claims, and the 58-field relation message;
- all four relation rounds;
- the 12-component main accumulator, the compact accumulator, and both final
  dot products.

The corresponding declaration is:

```text
AspisV5AcceptedOneRunDeterministicFinal.
  accepted_composite_security_conclusion_for_any_terminal_evaluator
```

Its clean replay resolves 331 tracked Lean modules and passed on 24 August
2026 with Lean 4.32 and the pinned Aeneas revision.

## Mathematical results

| Area | Checked result |
| --- | --- |
| Private-spend relation | Extracted arithmetic, Poseidon2, and depth-20 Merkle rows produce a complete one-input, one-output spend witness, relative to the stated Poseidon2 implementation interface. |
| Value conservation | Field balance plus the 30-bit range bounds implies integer conservation without modular wraparound. |
| Field and domains | M31 arithmetic, the degree-four extension, circle generator order, distinct released domains, stored evaluation order, and encoder identities. |
| Low-degree test | One coherent initial decoder candidate survives all four radix-four folds, or a prefix-timed counted event occurs. |
| Query sampler | The bounded first-occurrence sampler is uniform over ordered 18-element schedules on success, with the exact without-replacement miss probability. |
| Relation | Exact candidate and verifier-weight folds preserve their dot product; causal challenge counting bounds repair of false claims. |
| Transcript | Exact byte payloads, SHA-256 operation order, work placement, and challenge consumption. |
| Merkle openings | Exact five-section parsing, topology, frontier use, full input consumption, and authentication of every value consumed by FRI. |
| Security experiment | One finite accepted-false experiment, an exact failure ledger, a conditional protocol budget below `0.7 * 2^-100`, and the final conditional `2^-100` composition. |
| Theft and state | Fixed-victim and observed-history classifications, exact modeled marker and pool update, replay rejection, rollback in the state model, and cleanup preservation. |
| Hiding | Exact witness independence for the finite masking model, bounded retry, complete modeled byte inventory, and an explicit conditional deployed-view hybrid. |

## Security statement

Lean proves the event inclusion

```text
accepted false
  ⊆ protocol failure ∪ 18 named external events
```

and the resulting union bound in one probability space. If deterministic
implementation and runtime correspondences hold, the remaining external sum
contains six cryptographic or credential events. The checked numerical endpoint
is:

```text
protocol budget ≤ 0.7 * 2^-100
external budget ≤ 0.3 * 2^-100
--------------------------------
total budget    ≤       2^-100
```

This is work-normalized accounting. The separate raw analysis removes the
37-bit work credit after the grind has completed and retains a dominant
70-to-71-bit term plus explicit primitive, credential, statement, and runtime
terms.

## Composition boundary

Two formal steps remain between the deterministic accepted-call theorem and a
fully instantiated deployed probability theorem:

1. identify every field of the translated live Rust statement with the
   abstract `V5PublicStatement` used by the false-acceptance and theft games;
2. place the successful-call classification inside the causal
   `WorkNormalizedV5AdversarialExperiment`, including its oracle-query and
   repeated-attempt law.

Published circle decoding and Fiat-Shamir theorems, SHA-256 and Poseidon2
security, translator and proof-assistant correctness, compiler correctness,
and Solana runtime behavior remain explicit interfaces. See
[`docs/assumptions-ledger.md`](../docs/assumptions-ledger.md).

## Build

```sh
cd AspisFormal
lake exe cache get
lake build
```

The accepted deployed-path replay is the stronger publication gate for the
end-to-end theorem:

```sh
aeneas-verif/scripts/replay-accepted-path-lean432.sh
```

CI runs that replay in
[`lean.yml`](../.github/workflows/lean.yml). Parameter and constant bindings
back to Rust are checked by
[`param-binding.yml`](../.github/workflows/param-binding.yml) and
[`poseidon-binding.yml`](../.github/workflows/poseidon-binding.yml).

The audited theorem closure contains no `sorry`, project axiom,
`native_decide`, or compiled-evaluation shortcut. Its axiom report contains
only `propext`, `Classical.choice`, and `Quot.sound` from Lean's standard
logical foundations.

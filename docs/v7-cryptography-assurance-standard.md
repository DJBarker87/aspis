# Aspis research cryptography assurance standard

This is the reusable process distilled from the V5/V6/V7 work.

## Assurance layers

1. **Protocol declaration**
   - exact message/challenge order;
   - exact profile and byte grammar;
   - explicit non-goals.

2. **Pure algebra**
   - fields, encoders, commitments and relations;
   - deterministic correctness;
   - no probabilities.

3. **Published-theorem interfaces**
   - exact predicates only;
   - finite substitutions checked in Lean;
   - unresolved applicability marked `BLOCKED`.

4. **Deterministic extraction**
   - accepted proof outside named failures yields a witness/candidate;
   - no security arithmetic yet.

5. **Failure-event inclusion**
   - false acceptance implies one listed event;
   - event inventory precedes numerical ledger.

6. **Finite security ledger**
   - rational/integer bounds;
   - exact work placement;
   - exact Fiat–Shamir round count;
   - named external primitive allowance.

7. **Complete-view hiding**
   - staged affine view;
   - rank/translation theorem;
   - simulator and ROM programming;
   - salt terms only for hash-input hiding.

8. **Reference implementation**
   - literal, slow, readable;
   - KATs and adversarial fixtures.

9. **Optimized implementation**
   - differential equality to reference;
   - isolated and cumulative CU measurements;
   - canonical parsing and full byte consumption.

10. **Source correspondence**
    - Charon/Aeneas extraction;
    - one accepted top-level execution;
    - shared witnesses through the complete theorem.

11. **Release provenance**
    - clean reproducible binary;
    - exact proof and RPC evidence;
    - state deltas and cleanup;
    - honest claim/assumption table.

## Forbidden shortcuts

- “the paper applies” without a predicate.
- “formally verified” when only arithmetic is formal.
- choosing separate successful executions for separate verifier components.
- treating a Merkle-committed word as a codeword.
- treating compact-query conditioning as independent.
- relying on a proof-carried retry counter.
- security decimals without exact inequalities.
- claiming zero knowledge from salted Merkle roots alone.
- presenting projected CU as measured CU.
- silently changing profile widths.

## Branch gate labels

- `EXPLORATORY`
- `ALGEBRA-CLOSED`
- `THEOREM-AUDIT-PASS`
- `HOST-REFERENCE-PASS`
- `FORMAL-EXTRACTION-PASS`
- `SBF-SLICE-PASS`
- `HIDING-PASS`
- `COMPLETE-SECURITY-PASS`
- `SOURCE-BRIDGE-PASS`
- `RELEASE-CANDIDATE`

A branch may only advance one label when the corresponding checked artefacts
exist.

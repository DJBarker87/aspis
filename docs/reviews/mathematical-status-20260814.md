# Mathematical security status (14 August 2026)

This is an internal, hostile review of the mathematical claims for the
q18/g37 case study and V5. It is not an external audit.

## Short answer

The review found no concrete forgery, inflation attack, broken field
calculation, or false group identity. The 30-bit value arithmetic, M31 circle
facts, QM31 field construction, finite probability calculations, and several
masking results are in good shape.

The main problem is that those results do not yet form a complete proof of the
deployed V5 system. Lean checks many important pieces, but some of the hardest
links are still passed into the final theorems as assumptions.

Aspis should therefore be described as a research system with conditional
security. It is not currently justified to describe deployed V5 as a proved
100-bit zero-knowledge payment system.

## The old and new systems are different

| Property | q18/g37 case study | Deployed V5 |
| --- | --- | --- |
| Batched lanes | 29 lanes, highest power 28 | 19 lanes (16 base plus 3 extension), highest power 18 |
| Batch challenge | Historical calculation | Chosen from the nonzero extension field, so the denominator is `|K| - 1` |
| Number of challenge rounds | Historical calculation uses the safe cap 32 | Exactly 30 after the initial committed data is excluded |
| Security number | Conditional 100.161-bit work-normalized, per-query result | Conditional work-normalized result of at most `2^-100` error, if all V5 assumptions hold |

The old 29-lane calculation gives a slightly larger error than the correct V5
19-lane calculation, so it can be used as a safe upper bound. It must not be
presented as an exact description of V5. The fractional 100.161-bit number
belongs to q18/g37, not V5.

The 100.161-bit number is also not a raw `2^-100` chance of forgery at every
query budget. It is success probability divided by the number of random-oracle
queries. The paper's raw-advantage table shows the difference.

## What is still assumed in the V5 soundness theorem

The final V5 calculation is valid only if all of the following statements are
true:

- the listed failure cases cover every way a false proof could be accepted;
- the values opened by the prover really belong to the claimed code;
- the cited coding and Fiat--Shamir papers apply to this exact mixed M31/QM31
  protocol;
- each separately hashed proof-of-work value justifies the work reduction
  later used for its challenge;
- Rust samples challenges and orders transcript messages exactly as the Lean
  model says;
- the Merkle tree and polynomial commitments have the assumed security;
- the three schedule branches are bounded as claimed; and
- the six proof-of-work checks match the six terms in the calculation, with
  none omitted or counted twice.

Lean proves that these statements imply the claimed error bound. It does not
prove the statements themselves. Closing them is the largest remaining piece
of the soundness work.

## The exact spend rules

The production public statement contains:

```text
pool, sequence, current anchor, nullifier, output commitment,
next anchor, asset, fee, deployment domain
```

The nullifier is:

```text
H_nullifier(nullifier_key || input_salt)
```

It does not include the note commitment, deployment domain, or program id.
The proof is tied to a deployment because the deployment domain is a separate
public field included in the transcript. Reusing the same nullifier key and
input salt on another deployment produces the same public nullifier and is
therefore linkable.

Mask values and proof-generation randomness are not part of the secret witness
to the spend relation. They are fresh prover randomness. Current V5 range
checks split the two 30-bit values into six 10-bit limbs and prove their bits
are Boolean. The historical q18/g37 construction used the lookup-table range
check described in the paper.

## What Lean proves about the spend rules

Lean derives the range, balance, and asset rules from the arithmetic
constraints. Its hash and Merkle theorem starts by assuming a detailed
hash/Merkle witness and an assumption that the Poseidon2 model matches the
intended function.

`V5AcceptedSpendRelation.lean` now proves the deterministic next step: if
soundness extraction supplies a normalized package containing the arithmetic
residuals, typed hash inputs, all eleven two-round transitions for each
Poseidon2 permutation, both Merkle paths with shared bits and siblings, and
the exact six public-field matches, then those data satisfy the complete spend
relation (assuming the deployed Poseidon2 functions match the Lean model).
That package is already a structured interpretation of the trace, not raw
proof bytes.

There is still no finished theorem showing that every proof accepted by the
deployed V5 verifier produces those extracted rows. Therefore the project does
not yet have a complete theorem of the form:

```text
deployed V5 verifier accepts
    => the complete private-spend relation is true
```

The missing work is the cryptographic and implementation step from Tag-67
bytes and account state to an authenticated extracted trace: polynomial
commitment and FRI extraction, Fiat--Shamir, copy and LogUp constraints,
public-input binding, byte decoding, and the Rust-to-trace connection. This is
a high-severity formal-proof gap, although the review found no concrete proof
that exploits it.

## What the Rust-to-Lean work proves

The Rust-to-Lean work checks useful selected functions. The final Lean theorem
collects results for Components A, B, C and the Tag-67 work checks.

However, the Component-B and Component-C proofs start with assumptions that
the relevant Rust calls returned successfully, that inputs had the required
lengths and field encodings, and that selected folded values, coefficients,
and challenges equal the Lean values. There is no theorem showing that an
ordinary accepted production proof automatically supplies all of those facts.

The familiar transcript-hash equation is the only extra equality in the
Tag-67 work-checking theorem. It is not the only assumption in the entire
Rust-to-Lean argument.

## Zero knowledge

The Component-B and Component-C masking theorems are real mathematical
results. The final V5 hiding theorem still assumes that production randomness,
sampling, value projection, transcript construction, commitments,
serialization, compilation, and hashes behave as the simpler Lean model says.

There is no end-to-end theorem that starts with the deployed V5 prover and
concludes that its published proof reveals nothing beyond the public
statement. V5 must not yet be described as having proved deployed zero
knowledge.

## Theft resistance

The wrong-secret reduction has been repaired. It no longer assumes that the
compressing nullifier hash is globally one-to-one. The generic theorem is also
instantiated with the exact V5 public-field match and complete spend relation,
so the nullifier equality is now derived from that relation. For a fixed
target-nullifier preimage and prover execution, Lean proves:

```text
Pr[accepted prover execution yields the wrong extracted secret]
    <= Pr[the extractor fails]
       + Pr[the attacker produces a different input with the same nullifier]
```

The second term is a fixed-target second-preimage event. The reduction is
valid, but a security claim must either sample the target note in a defined
game or assume a bound that holds uniformly for every valid target. The Lean
theorem is not yet a complete computational theft game: it does not define
efficient algorithms, sample the target note, model the attacker's full view,
or connect its abstract acceptance predicate to the deployed verifier. The
extractor's input is a complete execution record that may include the prover
and random-oracle query transcript; the theorem does not claim that public
proof bytes reveal a witness.

The known-answer Poseidon2 tests show that Rust and Lean produce the expected
outputs on selected test inputs. They do not prove that Poseidon2 is secure or
give a 124-bit second-preimage bound.

The on-chain marker gives an exact but narrower guarantee: after one accepted
transition uses a public nullifier, later transactions using that nullifier
are rejected. Lean now proves one part of the separate route: if extraction
returns the exact fixed victim leaf with a different valid owner/note opening,
then extraction failed or the combined owner-and-note commitment has a target
second preimage. Showing that an alternative leaf or path reaches the victim
anchor still needs a Merkle-binding reduction. A different-nullifier attack is
not a second preimage of the nullifier hash, because a second preimage has the
same output.

The logical flaw in the old injectivity formulation is fixed. Deployed theft
resistance remains conditional and has no finished numerical bound. It still
needs deployed extraction or simulation extraction, fixed-target bounds for
the nullifier and combined owner-and-note commitment, Merkle binding for an
alternative leaf or path, and the complete game and code-to-model connection.
This remains important before real value is placed in the system.

## Correct S-two references

For the 24 March 2026 revision of S-two (ePrint 2026/532):

- Theorem 5 covers the circle FFT;
- Theorem 7 covers Johnson-radius circle-code list decoding;
- Theorem 19 gives the circle-FRI round error results;
- Theorem 21 gives the corrected batch-evaluation proof; and
- Theorem 22 gives the bounded-query Fiat--Shamir formula used here.

Any draft calling Theorem 5 the batch theorem or Theorem 6 the Fiat--Shamir
theorem is wrong for that revision.

The review found no published attack that directly breaks the chosen
Johnson-radius parameters. The unresolved question is whether Aspis's exact
circle code, extension-field lanes, challenge sampling, and transcript satisfy
the cited theorems' conditions.

## The demonstration witness

The mainnet transaction did not use the older seed-zero fixture. Its mainnet
artifact builder is written to sample every secret digest from
operating-system randomness, discard candidates until the nullifier PDA has
bump 255, build the production trace, and run the full host verifier before
writing the artifact. The secret witness then fell out of scope and was not
included in the release. The code does not establish secure memory erasure of
the `SpendWitness`, so no such claim is made.

This was still a demonstration note rather than a user's funded private asset.
The archived 75,358-byte proof now has a regression test that feeds the exact
proof and statement through the released verifier callback. It passes, and
changing any one of the nine public fields makes it fail. Together with the
generation record and finalized on-chain acceptance, this is strong evidence
that the published bytes are the intended proof for the published statement,
not an unrelated transaction. It is not a substitute for the missing general
acceptance-to-relation theorem. The absence of the witness is expected for a
private proof, but it also means an outsider cannot now reveal it and rerun the
relation directly.

## Safe claims today

- No defect is known in the checked finite arithmetic or per-spend balance
  result. A sequence-wide total-value theorem still needs Merkle binding.
- The q18/g37 calculator produces the stated conditional, work-normalized
  number.
- The V5 calculation correctly uses 19 lanes, a nonzero batch challenge, six
  separate work checks, and 30 challenge rounds.
- Lean proves meaningful facts about selected Rust functions when its stated
  assumptions hold.
- The exact compiled V5 program completed the recorded mainnet transaction and
  atomic state change.

Those facts do not yet prove deployed V5 soundness, zero knowledge, or theft
resistance from end to end.

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

The post-review module `V5DeployedFalseAcceptance.lean` now removes an
ambiguity in how that conditional calculation is read. It defines false
acceptance for one public statement, takes three named failure predicates, and
proves their union bound. Lean does not yet prove that those predicates are
the actual deployed selector-0, selector-1, and selector-2 failures. If that
connection, accepted-run extraction, Poseidon2 faithfulness, the existing
width, round, transcript, commitment, and Fiat--Shamir premises, and the three
branch bounds all hold, Lean proves a work-normalized false-acceptance
probability at most `2^-100`. The ordinary probability is at most
`min(1, T / 2^100)` for query budgets `1 <= T <= 2^128`. This is a precise
conditional theorem rather than a completed deployed proof.

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
compressing nullifier hash is one-to-one. The nullifier equality is derived
from the exact V5 spend relation. For a fixed victim and prover execution, the
new `V5FixedVictimTheftGame.lean` classifies an accepted attack into these
mathematical failures:

1. witness extraction fails;
2. the attacker recovers the victim's credential;
3. a different secret/randomness pair produces the victim's nullifier;
4. a different opening produces the victim's note commitment; or
5. a different leaf at the victim's exact position reaches the same root.

`ApplicationMerkleBinding.lean` proves that the fifth case exposes a concrete
Poseidon2 node-hash collision. It also includes a test theorem showing that
two different positions under one parent are both legitimate openings. This
matters: a different Merkle path is not automatically an attack or a hash
collision; the relevant theft case is a different leaf at the victim's
position under the victim's root.

The chain-level theorem adds three more possible failures: two nullifiers map
to the same marker PDA, Solana locking/rollback/state behavior fails, or the
victim setup did not create one unambiguous target note. Lean proves that the
deployed attack probability is at most the sum of these eight events if the
deployed attack is connected to this mathematical game.

This is a complete case split for the attack event defined in the Lean model,
not a theorem that every real attack fits that event and not a numerical
theft-resistance result. The deployed connection remains a premise. So do
extraction after the attacker has observed other proofs, concrete security
bounds for the Poseidon2 nullifier, note commitment and tree hash, PDA
security, and the Solana runtime statements. Known-answer Poseidon2 tests only
show agreement on selected inputs; they do not prove primitive security.

The on-chain marker still gives a narrower deterministic guarantee: after one
accepted transition uses a public nullifier, another transaction with that
same nullifier is rejected. A different-nullifier attack is not a second
preimage of the nullifier hash because a second preimage has the same output.

No finished numerical theft bound is claimed. The remaining deployed and
cryptographic steps are high priority before real user value is protected.

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

The recorded pre-execution runner source required bump 255 to stay inside the
measured compute budget, and the landed transaction used it. The immutable
lifecycle evidence does not pin the exact executed runner commit. The exact
deployed program derived the PDA from the nullifier and checked the supplied
address, but did not require the numeric bump to be 255; that program check was
added later. This does not change the proof bytes, the accepted statement, or
same-nullifier replay protection.

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

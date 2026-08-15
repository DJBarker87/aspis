# Mathematical security status (14 August 2026)

This is an internal, hostile review of the mathematical claims for the
q18/g37 case study and V5. It is not an external audit.

## Short answer

The review found no concrete forgery, inflation attack, broken field
calculation, or false group identity. The 30-bit value arithmetic, M31 circle
facts, QM31 field construction, finite probability calculations, and several
masking results are in good shape.

The principal remaining problem is no longer an unidentified hole in the
circle-code mathematics. It is the final connection from several outer Rust
control-flow functions to the maintained Lean models, followed by explicit
bounds for the named cryptographic and runtime assumptions.

Aspis should therefore be described as a research system with conditional
security. It is not currently justified to describe deployed V5 as a proved
100-bit zero-knowledge payment system.

## The old and new systems are different

| Property | q18/g37 case study | Deployed V5 |
| --- | --- | --- |
| Batched lanes | 29 lanes, highest power 28 | 19 lanes (16 base plus 3 extension), highest power 18 |
| Batch challenge | Historical calculation | Chosen from the nonzero extension field, so the denominator is `|K| - 1` |
| Number of challenge rounds | Historical calculation uses the safe cap 32 | Exactly 30 after the initial committed data is excluded |
| Security number | Conditional 100.161-bit work-normalized, per-query result | About 71 raw bits for the dominant completed-grind batching event; a checked core below `0.7 * 2^-100` after charging for the 37-bit grind |

The old 29-lane calculation gives a slightly larger error than the correct V5
19-lane calculation, so it can be used as a safe upper bound. It must not be
presented as an exact description of V5. The fractional 100.161-bit number
belongs to q18/g37, not V5.

The 100.161-bit number is also not a raw `2^-100` chance of forgery at every
query budget. It is success probability divided by the number of random-oracle
queries. The paper's raw-advantage table shows the difference.

## What is still assumed in the V5 soundness theorem

The mathematical argument now follows one initial decoder candidate through
all four folds and handles the challenge-dependent family of nearby
candidates without multiplying the error by the 240-candidate list cap. Lean
checks the exact released field, circle code, distance, agreement threshold,
list parameters, batching degree, and nonzero challenge space needed by the
cited decoding result.

The main project-specific gaps are five production-code connections:

1. the enclosing Rust loop that places 76 decoded values into four rows;
2. the complete transcript driver;
3. the one-section Merkle parser, topology, and hash caller;
4. the five-section Merkle driver and remainder threading; and
5. the final construction of the candidate eligibility, support, message, and
   record data consumed by the correlated-agreement proof.

The published decoding result itself, Fiat--Shamir/random-oracle reasoning,
SHA-256 and Poseidon2 security, compilation, and Solana behavior remain
external assumptions. The paper-to-Lean interpretation is reviewed and the
parameter substitution is machine-checked; Lean does not reprove the cited
paper.

The dominant raw batching event has roughly 71 bits of security once a grind
has completed. Charging for the released 37-bit grind gives a modeled core of
about 100.56 bits; Lean proves the conservative statement that this core is at
most `0.7 * 2^-100`. The remaining external events must together fit the
reserved `0.3 * 2^-100` budget. This is a 100-bit work-normalized target, not a
128-bit target and not a raw `2^-100` probability per completed proof.

The query sampler is also less abstract than before. Lean now proves the exact
finite probability for 18 uniform distinct positions landing in a fixed set of
at most 6,082 positions out of 131,072. A second finite proof shows that the
ideal 64-draw first-occurrence sampler is uniform over ordered 18-position
schedules after conditioning on success. It also proves that, without
conditioning, success with all queries in the fixed set is bounded by the same
ratio when draw exhaustion rejects. Those results do not yet show that the SHA
transcript has the ideal draw law, that the Rust loop matches the finite model,
or that FRI failure produces the required fixed set. The final 32-bit work
reduction also remains a separate premise.

For a future wire format, independent sampling with replacement is a sensible
simplification. Lean checks the cardinality calculation: the 18-draw ratio,
after division by the same separately justified `2^32` work factor, is still
at most `2^-111`. It does not justify that work factor or a joint probability
experiment. V5 itself must not be silently changed: the sampling rule is part
of its transcript, proof layout, verifier, and published release identity.

V5 used distinct queries so all 18 checks hit different fibres and the Merkle
opening code could work with one sorted list of 18 different leaf indices. A
with-replacement version must say how repeated queries are represented and how
the Good-A/Good-B schedule tests treat them. That is manageable in a new wire
format. At these parameters a repeat among 18 draws occurs only about 0.12% of
the time, and the security difference is about 0.035 bit, so the extra V5
sampler machinery buys very little.

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

The general chain-level theorem conservatively adds three more possible
failures: two nullifiers map to the same marker PDA, Solana
locking/rollback/state behavior fails, or the victim setup did not create one
unambiguous target note. Lean proves that the deployed attack probability is
at most the sum of these eight events if the deployed attack is connected to
this mathematical game.

`V5NullifierMarkerReplay.lean` now narrows the PDA case. In the explicit
sequential marker model, a successful spend writes the public nullifier into
its derived address. A later spend at that address rejects whether it carries
the same nullifier or a different nullifier. This proves a useful state-model
fact, but it is not yet connected to the fixed-victim theft game. That theorem
still includes PDA aliasing. The exact Rust-to-model connection, the
attack-game reduction, and Solana locking, rollback, and finalized marker
persistence remain external.

This is a complete case split for the attack event defined in the Lean model,
not a theorem that every real attack fits that event and not a numerical
theft-resistance result. The deployed connection remains a premise. So do
extraction after the attacker has observed other proofs, concrete security
bounds for the Poseidon2 nullifier, note commitment and tree hash, and the
Solana runtime statements. Known-answer Poseidon2 tests only show agreement on
selected inputs; they do not prove primitive security.

The marker result is deliberately narrow. It prevents a second accepted use
after the first marker has committed. It does not stop a fraudulent first
spend that reaches an empty marker; that still depends on proof soundness and
the fixed-victim cryptographic argument. A different-nullifier attack is not a
second preimage of the nullifier hash because a second preimage has the same
output.

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

The formulas and theorem numbers are not the main remaining problem. The
published protocol and Aspis differ in several exact places:

- Theorem 21 runs FRI on both the original function and an out-of-domain
  quotient. V5 has no quotient word, commitment, or opening. It runs FRI on
  the ordinary 19-column batch and handles two claimed out-of-domain values
  through a separate degree-six coefficient-relation sumcheck. The two checks
  share fold challenges and final coefficients. The new Lean modules prove
  the candidate-relative relation algebra for this custom construction, but no
  cited theorem supplies the remaining raw Merkle/FRI extraction, matching,
  and false-spend implication.
- S-two's query experiment uses independent uniform points. V5 keeps the first
  18 distinct positions from at most 64 draws.
- S-two Theorem 19 analyzes its multi-domain folding-with-insertion cascade.
  V5 performs four radix-four folds of one combined word. The repository has
  not yet proved that V5 is an exact specialization of that cascade.
- S-two's grinding condition applies directly to the verifier randomness for
  that round. V5 checks a separate domain-separated work hash, absorbs the
  nonce, and then obtains the later challenge through another hash call.
- S-two says the mixed-domain Merkle adaptation can be made, but does not give
  its formal proof. V5 authenticates five salted trees with its own mixed
  radix-four/binary layout.

These differences are not known attacks, and the review found no published
attack that directly breaks the chosen Johnson-radius parameters. They still
prevent the S-two theorem from establishing the V5 probability bound without
additional arguments.

The relation-specific work is now considerably stronger than a degree-six root
count. `V5RelationSumcheckSoundness.lean` proves that for one fixed candidate,
false data in the incoming claim or either staged value can cancel through the
two sequential mixes on at most a `2 / |K|` fraction of mix pairs, even though
the second value may depend on the first mix. Over all twelve challenges, with
later rounds allowed to depend on completed earlier rounds, the fixed-candidate
repair event has mass at most `32 / |K|`.

`V5FriRelationCandidateBridge.lean` connects that scalar count to the exact
arity-four candidate fold and the verifier's dual weight fold.
`V5Tag67RelationListInclusion.lean` then proves the decisive deterministic
candidate statement: accepted relation checks, a final coefficient match, and
a candidate-relative false claim imply membership in the counted event. For a
fixed family of at most 240 candidates chosen before the twelve
challenges, the union is bounded by `32 * 240 / |K|`.

`V5FriListCap.lean` independently checks the four list-bound calculations, not
just the first layer. The Guruswami--Sudan multiplicities are `10`, `10`, `9`,
and `6`, and every resulting expression is strictly below 240. The actual
Guruswami--Sudan theorem connecting those expressions to the V5 decoder lists
remains external.

`V5FriCoherentCandidateExtraction.lean` closes the deterministic FRI
selection step. Accepted ideal FRI either hits one of six explicit failures
(the small consistency set, four exact fold-reduction failures, or an
oversized initial list) or yields one member of one initial list whose exact
four folds reach the published final polynomial. This avoids a `240^4` choice:
later layers are the folds of that one initial member.

`V5Tag67CandidateTraceExtraction.lean` closes the deterministic semantic
step. A false no-witness statement makes every initial-list member have a
scalar mismatch unless one of six named failures occurs: the four-claim batch
equation, a four-claim batch collision, 19-lane recombination, public-field
binding, arithmetic residuals, or hash/Merkle residuals.

`V5Tag67ModeledRelationAcceptanceBridge.lean` proves that success of the pure
relation-verifier model gives the four shared boundary checks and the final
dot-product check for every list member. `V5Tag67AcceptedFalseInclusion.lean`
then proves the combined split: a raw accepted false execution is in a raw
relation-model failure, a raw FRI-model failure, an explicit FRI failure, an
explicit candidate/trace failure, or the single-list repair event.

Later modules replace this coarse five-way status with the actual
width-nineteen candidate-family event, projected residual failures, and exact
released accounting. The challenge-dependent family proof avoids a factor of
240, and the released parameters and circle-code side conditions are checked
in `V5Width19S2ApplicabilityAudit.lean`.

The updated arithmetic separates raw probability from attack work. The
dominant completed-grind batching event is about 71 raw bits. Charging for the
37-bit grind gives a modeled core of about 100.56 bits; the maintained Lean
endpoint proves the conservative bound `0.7 * 2^-100` and reserves
`0.3 * 2^-100` for externally bounded events. The remaining gaps are the five
production-code connections listed near the start of this review and the
named cryptographic, compiler, and runtime assumptions.

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

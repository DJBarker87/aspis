# Profile-21 post-delta tau seam reduction

Status: **selected candidate; not quotable until the literal tag-50 verifier,
adversarial seam teeth, final Johnson ledger, and mined proof all pass.**

Date: 2026-07-13.

## Selected wire and causal order

The profile-21 extension is

```text
source_nonce_u64 || logical_U[35] || tau_QM31.
```

Its physical position in the prefix does not change its Fiat--Shamir order:

1. commit the salted C1/C2 roots containing the ordinary word and X/F;
2. finish round zero and sample `alpha0`;
3. check and absorb the dedicated source-g38 nonce;
4. sample nonzero `delta`;
5. disclose and absorb logical `U`;
6. disclose and absorb `tau`, then absorb the translated W1 root;
7. sample and check every ordinary W1 OOD claim, sumcheck and later fold;
8. absorb the final polynomial, check final g38, and sample distinct q16;
9. authenticate and check

   ```text
   W1(q) - Fold_alpha0(W0)(q) = Enc(U)(q) = F(q) + delta X(q).
   ```

For an honest proof, if `Lambda` is the exact public post-alpha0 relation
covector, then

```text
tau = Lambda(phi(U)).
```

The verifier adds the disclosed `tau` to the running round-zero claim before
adding either round-one OOD mixture. It then retains the ordinary round-one
boundary equality unchanged. It deliberately does not recompute the
35-coordinate dot product on SBF.

The retired `tX,muF` fields and their message-only target equation are absent.
They are unnecessary once both literal q16 equalities are paid for.

## Completeness

The prover computes `U=F+delta X` in the frozen logical source basis and
constructs

```text
W1 = Fold_alpha0(W0) + Enc(phi(U)).
```

Linearity gives the displayed honest `tau`. Therefore adding it before the
round-one OOD mixtures produces exactly the same running claim as the former
explicit verifier dot. All later relation boundaries, OOD claims, folds and
q equations are unchanged.

An implementation differential must compare the old explicit
`Lambda(phi(U))` with the serialized honest `tau` at random QM31 schedules.

## Soundness handoff

Condition on the already-charged ordinary and source list/MCA events. Let
`p0` and `p1` be the decoded ordinary polynomials for W0 and W1, and let `u`
be the degree-below-35 polynomial disclosed by logical U. After one arity-four
fold, `p1-Fold_alpha0(p0)` has degree below 256. Define

```text
d = p1 - Fold_alpha0(p0) - u.
```

The ordinary relation proof with the disclosed seam scalar has two cases.

- If `d=0`, its honest linear relation forces
  `tau=Lambda(phi(U))`, except under an already-charged relation/sumcheck/PCS
  failure.
- If `d!=0`, it has at most 255 roots on the 32,768-point W1 line domain.
  Passing all distinct q16 seam checks therefore costs at most

  ```text
  C(255,16) / C(32768,16).
  ```

  This is 112.7781654706 raw bits, or 150.7781654706 bits under the selected
  final-g38 normalization. Ordinary received-word/list disagreement remains
  charged to the existing main q16 row rather than being assumed away.

Independently, if the pre-delta X/F combination is not the disclosed `u`, the
existing dimension-35 polynomial-generator MCA and source q16 events apply to
`F+delta X-u`. The C2 root is fixed before source g38 and delta; U, tau, W1,
all later roots and the final polynomial are fixed before final g38 and q16.

For a conservative ledger the 150.778-bit seam-polynomial row may be added as
a separate union term. At the current precision it does not change the
selected union (`107.288354146078` bits), factor-33 result
(`102.243960026720` bits), or factor-40 sensitivity
(`101.966426051191` bits). The obsolete degree-one target-collision row may be
removed once no target equation remains.

## Why boundary inference is rejected

Simply skipping the round-one boundary check is not equivalent. The claimed
round-one OOD values enter the verifier through the running claim. If that
claim is discarded and replaced by the round-one polynomial evaluation, the
values themselves are no longer constrained by the acceptance equation.
That would invalidate the current OOD/list ledger. A separately disclosed
post-delta `tau` preserves the OOD additions and boundary check exactly.

## Privacy accounting

For honest proofs, `tau` is a deterministic public linear function of the
already-disclosed U and the public verifier schedule. It is therefore a
derived view coordinate, not an independent mask observation. A complete-view
simulator computes the same value from simulated U. The final affine-rank
replay must quotient this exact identity rather than adding a new row.

The source mask basis and its layout fingerprint remain separate obligations.
The selected universal candidate carries natural coefficient 18 at root zero
and coefficients 0 through 17 at root one. Its all-q proof and generated
fingerprint must land before the complete HVZK claim can turn green.

## Required teeth

- honest explicit-dot versus serialized-tau equality at fresh random QM31
  schedules;
- tau byte, U byte, translated-W1 root and round-one boundary corruptions;
- a relation-consistent wrong translated polynomial that is rejected by the
  literal q seam;
- preservation of both round-one OOD-value corruptions;
- transcript-order KAT proving source g38 precedes delta and U/tau/W1 precede
  every later OOD challenge and final q;
- regenerated layout/basis fingerprints and final literal SBF measurement.

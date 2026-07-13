# Profile-21 joint auxiliary-tail claim

Status: **design frozen for an exact rank gate; not an acceptance path.**  This
candidate removes the masked X/F switch only if the log-10 complete-View rank
gate below is green.  No CU or soundness credit is taken before that result.

## Public claim surface

Partition the 28 committed columns into

```text
S = C0,...,C15                 semantic trace columns
U = M0,...,M9,H,G              auxiliary hiding/copy columns
```

The terminal constraint needs all three point values for `S`, but it uses only
the value at `z` for every column in `U`.  The current wire nevertheless sends
all three values for all 28 columns.  The proposed wire sends, before the
point/column batching challenges,

```text
{ f_j(z), f_j(succ(z)), f_j(xor12(z)) : j in S }   48 QM31
{ f_j(z) : j in U }                                12 QM31
```

After `kappa` and `gamma` it sends one joint tail claim

```text
A = kappa   * sum_{j in U} gamma^j f_j(succ(z))
  + kappa^2 * sum_{j in U} gamma^j f_j(xor12(z)).
```

Thus 24 raw auxiliary tail values become one QM31 value: 84 statement values
become 61.  `G(z)` remains explicit for the masked zerocheck terminal, and
`H(z)` plus every `M_i(z)` remain explicit for the copy and mask terms.  No
semantic evaluator is allowed to read an omitted value.

## Fiat--Shamir order

The causal order is:

1. commit all layer-zero words and finish the masked sumcheck, deriving `z`;
2. absorb the 60 raw values above;
3. sample `kappa`;
4. check and absorb the existing batch work witness, then sample `gamma`;
5. absorb `A` and sample a fresh nonzero z/tail separator `tau`;
6. check and absorb a dedicated group-batching work witness, then sample a
   fresh nonzero group separator `delta`;
7. begin the OOD/relation/fold transcript, with every later root and query
   derived from a state that contains `A`, `tau`, and `delta`.

The prover must not choose a raw semantic claim after `kappa`, a raw column
claim after `gamma`, or `A` after `tau`.  Zero `tau` or `delta` values are
rejected (or charged as separate `1/|QM31|` events, but rejection is simpler).

The main batch work nonce remains before `gamma`, which is the challenge whose
within-group polynomial-generator/MCA term it amplifies.  The second work
witness must follow `A,tau` and precede `delta`: at rate 1/512 the unground
two-word correlated-agreement term is only about 75.12 bits, while g38 raises
it to about 113.12 bits.  The retiring masked-switch source nonce can occupy
this position, so the candidate does not add a work-nonce check relative to
profile 21.  The local degree-two `tau,delta` claim-collision term is charged
separately and receives no backward work credit.

## Post-claim separation of the four claim classes

A single relation target without an additional separator is unsound: because
`A` follows `kappa,gamma`, a malicious prover could use it to cancel false
successor/XOR claims in `S`.  The candidate prevents that with two fresh
post-claim challenges.

Define

```text
F_S = sum_{j in S} gamma^j f_j
F_U = sum_{j in U} gamma^j f_j
F_* = delta F_S + F_U.
```

The ordinary relation opens `F_*` with point weights
`[tau,kappa,kappa^2]`.  Its claimed initial value is therefore

```text
delta * (tau S_z + kappa S_succ + kappa^2 S_xor)
  + tau U_z
  + A,
```

where each symbol denotes the corresponding `gamma`-weighted sum.  This is a
single ordinary committed codeword and a single ordinary three-point linear
functional; it is not a matrix-valued fold or a selective post-commitment
coefficient splice.

For discrepancies from the committed words, put

```text
Z_S = sum_{j in S} gamma^j e_{z,j}
T_S = sum_{j in S} gamma^j (kappa e_{succ,j} + kappa^2 e_{xor,j})
Z_U = sum_{j in U} gamma^j e_{z,j}
E_A = A - kappa F_U(succ(z)) - kappa^2 F_U(xor12(z)).
```

All four quantities are fixed before `tau,delta`.  The relation discrepancy is

```text
D(tau,delta) = delta tau Z_S + delta T_S + tau Z_U + E_A.
```

The four coefficient classes occupy the distinct monomials
`{delta*tau,delta,tau,1}`.  If any coefficient is nonzero, `D` is a nonzero
total-degree-at-most-two polynomial, so the local separator failure is at
most `2/|QM31|`.  This is the guard that a plain `{G(z),A}` or plain joint `A`
construction lacks.

If all four coefficients vanish while a raw claim is false, the earlier
challenges supply the usual polynomial-identity terms.  The `S` tail error is
of degree at most two in `kappa` and at most 15 in `gamma`; the two z groups
have degree at most 27 in `gamma`.  The final ledger must charge the exact
sequential union rather than silently folding these events into the FRI query
term.

For nonzero `delta`, proximity batching is explicitly two level.  First form
the two ordinary gamma-batched words `F_S,F_U`; then use the standard two-word
generator

```text
(delta, 1).
```

The gamma generator is applied separately to `S` and `U` (the same gamma may
be used, with the two MCA errors unioned), and `delta` then performs ordinary
random-linear correlated agreement between their outputs.  This avoids an
adaptive squared-coefficient generator.  The circle-code transport and the
complete Johnson ledger must be rerun for this two-level generator and the new
transcript order; this paragraph is not permission to use a capacity
conjecture.

## Decisive hiding gate

The rank gate is the literal log-10, q16, rate-1/512 profile-21 View with no X,
F, U-switch, or translated W1:

- `S` conditions on its layer-zero cells and all three terminal values;
- all twelve `U` sources are eliminated jointly against their layer-zero
  cells, twelve z values, and the one scalar `A`;
- semantic PCS columns carry scale `delta gamma^j`;
- auxiliary PCS columns carry scale `gamma^j`;
- every row PCS tail is rebuilt with point weights
  `[tau,kappa,kappa^2]`;
- the full 1,080-M31 masked-sumcheck quotient, all later query values, OOD
  values, relation coefficients, final coefficients, conservative semantic
  differences, and legal-sumcheck directions remain in the View.

The required result is exact containment, with source columns, pivot rows,
pre-normalization pivot values, and a minor fingerprint.  Per-column aggregate
tests are insufficient: `A` is one joint row across all twelve auxiliary
oracles.  A log-11 affine-slice result is also insufficient; this candidate's
claim is precisely that the existing log-10 randomness closes after removing
23 unnecessary observations.

## Expected structural delta if and only if the gate is green

The candidate would retire the two X/F C2 lanes, repurpose their source work
witness as the post-`A` two-group work witness, remove the 35-QM31 disclosed U
vector, the translated W1 seam, and their q-query co-opening checks.  It also
narrows the shared C2 private leaf and removes 23 QM31 statement fields.  Those
are structural six-figure candidates; none is booked until an integrated
verifier with the complete corruption and privacy teeth is measured.

Required tests include random off-domain identity comparison against the
uncompressed 84-value relation, independent mutations of every retained raw
claim and `A`, challenge-order teeth for `kappa/gamma/A/tau/delta`, the existing
padding/cross-residual corpus, and same-statement/two-witness distinguishing
tests over the compressed transcript and receipt.

# Profile-21 fresh-W1 mask audit

Date: 2026-07-13

Status: **conditionally viable for argument soundness at Johnson; refuted as a
standalone complete ambient-HVZK construction.**  The mask starts after
`alpha0`, so it has zero image in the already transmitted round-zero relation
polynomial `p0`.  It can hide the later continuation only.  A complete privacy
claim therefore needs either an independently bound early mask or a
language-specific proof that honest same-statement witness differences have
zero projection onto the residual `p0` quotient.

This is an interface audit, not an implementation.  It makes no production
edits and does not promote the repository's still-open exact
circle/fold/BCS Johnson transport theorem.

## Candidate and exact seam equation

After the first ordinary circle fold, let

```text
w = W1 = Fold_alpha0(W0),
m = M,
L = exact post-alpha0 first-line relation functional,
r = running folded relation target before the fresh mask.
```

`M` must be an independently sampled word in the **same ordinary line code**
as `W1` (or a pinned linear subcode).  A widened private Merkle root commits
both `w` and `m`.  The prover then serializes

```text
tau_M = L(m),
```

and, after the pre-beta work check, the verifier samples uniform nonzero
`beta` and defines

```text
C1 = w + beta*m,
r1 = r + beta*tau_M.
```

The exact functional is not a plain coefficient sum.  In the current code it
is the covector exposed by `first_later_weights`; it depends on `z`, `kappa`,
both round-zero OOD mixers and `alpha0`.  The executable reference operation
is `profile21_first_later_full_target`, not the older eta-power diagnostic.

For a committed candidate define

```text
e0 = r - L(w),
eM = tau_M - L(m).
```

The next relation is consistent exactly when

```text
e0 + beta*eM = 0.                              (fresh-W1 seam)
```

If `(e0,eM) != (0,0)`, this affine polynomial has at most one root in
`QM31*`.  In particular, if the base seam is correct (`e0=0`) and `tau_M` is
wrong (`eM!=0`), no nonzero beta accepts.  If both errors are nonzero, at most
one beta cancels them.  The conservative per-attempt target-binding term is
therefore

```text
1 / (|QM31|-1),
```

before the positioned-work accounting.  This conclusion is conditional on
the ordinary relation proof actually checking the next target against the
polynomial built from `C1`; merely updating a host-side scalar is not a
check.

The root is only a commitment.  It does not prove `w=Fold(W0)` or that `m` is
low degree.  Those are respectively the sampled transition check and the
joint-code reduction below.

## Mandatory transcript order and grinding

The accepted causal order is:

1. Bind `W0`, complete the round-zero OOD messages and sumcheck, check the
   round-zero fold work, sample `alpha0`, and compute the normalized fold.
2. Commit and absorb one widened salted root containing `(W1,M)`.
3. Serialize and absorb canonical `tau_M=L(M)`.
4. Check and absorb the retained dedicated **g38** work nonce against this
   exact transcript state.
5. Draw up to three independent exact-uniform QM31 challenges, consuming the
   next transcript words, and take the first nonzero value as `beta`.  Abort
   if all three are zero.  Conditional on success this is exactly uniform on
   `QM31*`; the honest abort probability is `|QM31|^-3`, about `2^-372`.
6. Form the virtual `C1=W1+beta*M` and target `r+beta*tau_M`; only now sample
   the first line OOD point and continue the ordinary sumcheck/fold schedule.
7. Bind every later root and the final polynomial, check and absorb final
   work, and only then derive the distinct query positions.
8. At each query authenticate both components of the widened root, verify the
   literal normalized `W1=Fold_alpha0(W0)` equation, derive `C1` from the
   authenticated `W1,M`, and apply the ordinary `C1 -> W2` transition check.

The current profile-21 order cannot be reused verbatim: its source g38 occurs
before the disclosed source and translated root.  For this candidate the
dedicated work must move after **both** the widened root and `tau_M` and before
`beta`.

That position matters in the ROM work/success metric.  Every fresh beta trial
obtained by changing the root, `tau_M`, or the valid nonce now costs expected
`2^38` hash queries.  Thus a beta-derived event with per-attempt error
`epsilon_beta` is charged as `epsilon_beta/2^38` per unit adversarial work.
For the affine seam term this is about `162` raw work bits
(`log2(|QM31|-1)+38`), with the complete system still capped by the separate
SHA-256/ROM assumption.  Post-beta or pre-root work gives no such credit.

### Exact adaptive counterexamples

If `tau_M` is chosen after beta, a prover with committed errors and
`beta!=0` sets

```text
tau_M = L(M) - e0/beta,
```

so the fresh-W1 seam is identically satisfied despite a false base seam.  If
the widened root is chosen after beta, the prover can instead choose `M` (and
then `tau_M`) to cancel the discrepancy.  Both variants have success one and
are unsound.

If the root and `tau_M` precede beta but no pre-beta work is retained, the
one-root argument remains an information-theoretic per-attempt bound, but a
Fiat--Shamir prover can reselect the cheap root/tau prefix until its beta is
the cancelling root.  It therefore fails the selected work-normalized
security budget even though the single-attempt algebra is correct.

## What Johnson MCA does and does not certify

For fixed received words `(w,m)` and post-commitment beta, later FRI sees only
`c=w+beta*m`.  Testing `c` alone at one fixed beta does not prove that `m` is
a codeword.  For example, choose a far word `m`, a codeword `c`, and a desired
`beta0`, and set `w=c-beta0*m`; at `beta=beta0` the combined word is exactly
`c`.  Commitment-before-beta converts this from a deterministic attack into
the random-linear-combination event; it does not eliminate the need to charge
that event.

The correct reduction treats `(W1,M)` as two attached functions under the
degree-one polynomial generator

```text
Gen(beta) = (1,beta).
```

At the Johnson radius, polynomial-generator mutual correlated agreement can
give common agreement with line-code words `p_W1,p_M`; linearity then gives
`p_C1=p_W1+beta*p_M`.  The ordinary list/fold commutation carries that same
choice through the later folds, while the common q set checks the literal
`W0 -> W1` and derived `C1 -> W2` transitions.

Restricting beta from `QM31` to `QM31*` changes a theorem failure bound
`epsilon` to at most `epsilon/(1-1/|QM31|)`.  The ledger must use the theorem's
actual list/generator numerator over `|QM31|-1`; it must not replace the MCA
row by the elementary `1/(|QM31|-1)` seam row.  Keep the two rows separate
unless one written reduction proves they are the same bad event.  Both
beta-derived rows receive the positioned g38 work credit.

Because `M` is introduced only after the circle-to-line fold, this design does
not require a new *circle-code switch for M*.  It still requires an extension
of the exact Aspis candidate theorem: the widened `(W1,M)` root must be two
attached line functions in the same S-two/WHIR reduction, the `(1,beta)` MCA
event must be instantiated for the exact line code, and common-list folding,
four-slot query sampling, private-Merkle authentication and BCS state
restoration must be carried through the production transcript.  The generic
Johnson MCA primitive does not, by itself, prove those candidate-specific
steps.  The repository already labels that transport open in
`docs/aspis-soundness-note.md` section 16.4.

Verdict on the soundness interface: **conditionally viable; no new
capacity conjecture is needed, but the existing open Johnson transport does
not disappear.**

## Wrong-tau binding

No direct full-word evaluation of `L(M)` is required if all of the following
hold:

* the widened root and canonical tau bytes precede g38 and beta;
* `beta` is nonzero and exact-uniform conditional on no abort;
* the relation coefficients are literally `W1+beta*M`;
* the carried target is literally `r+beta*tau_M`; and
* the existing relation proof binds those coefficients to that target.

Then the affine seam equation supplies the binding.  At q, however, both
`W1` and `M` must be authenticated from the widened root.  Authenticating
only their derived sum permits a prover to substitute components without
changing `C1`.

Canonical field parsing, root lane order, beta retry order and challenge
labels need teeth.  The three nonzero attempts must consume fresh transcript
words; rehashing the same rejected word is not exact rejection sampling.

## Soundness-ledger delta

The frozen ledger must add or update these rows:

| event | required charge |
| --- | --- |
| `(W1,M)` degree-one powers/MCA | theorem list/generator numerator over `|QM31|-1`, with pre-beta g38 in the work metric |
| fresh-W1 target combo | `1/(|QM31|-1)`, with pre-beta g38 in the work metric |
| three-zero beta abort | completeness `|QM31|^-3`; no soundness credit |
| widened-root binding | SHA-256 collision/second-preimage assumption and updated private-Merkle EPRO label count |
| sampled `W0 -> W1` transition | existing common-q miss event; no second independent q credit |
| later FRI/OOD/relation | unchanged shape, but applied to virtual `C1` and covered by the exact attached-function transport |
| Fiat--Shamir restoration | one additional beta public-coin round unless this candidate replaces an already counted round; recompute the factor from the literal transcript |
| proof bytes / CU | widened leaves, two authenticated components per q, one tau scalar, one work nonce, beta sampling and derived-C1 arithmetic |

Do not credit the final pre-q work against beta: it is too late.  Do not count
the same g38 as both an unqualified additive security term and a separate
query-work term; its position determines which challenge it prices.

## Complete simulator view

The public view added or changed by this candidate includes:

* the widened salted `W1/M` root and its transcript position;
* public `tau_M`, the valid g38 nonce, the three-attempt beta schedule and the
  chosen beta;
* every later line OOD value, relation polynomial, fold challenge/root and
  terminal coefficient computed from `C1`;
* at q, the raw authenticated `W1` and `M` leaf symbols, their salts and
  multiproof frontier, plus the derived `C1` symbols;
* serialized proof-account bytes, logs, abort/retry behavior and the final
  atomic mutation (or receipt, if any).

`tau_M` consumes a linear observation of the mask and is not entropy.  The q
openings of `M` consume further mask rank.  Moreover, because both `W1` and
`M` are opened, the derived value is not a one-time pad for the queried W1
symbol:

```text
W1(q) = C1(q) - beta*M(q).
```

The mask can still randomize unopened later linear forms, but an exact-view
rank calculation must include tau, all opened M symbols, all later messages
and duplicate-query quotienting.  It needs an all-q minor/certificate, not a
single sampled schedule.

The Fiat--Shamir challenge is conditioned on a root that depends on `M`.
Consequently fixed-schedule affine rank alone is not a computational-HVZK
simulator.  The existing private-Merkle/EPRO random-oracle hybrid must be
extended to the widened leaf and must simulate the joint distribution of
`(root,tau_M,g38,beta,later transcript,q openings)`, including failed beta
attempts and any prover restart metadata.

## Decisive privacy obstruction

The current strict-root1 rank audit has exact rank

```text
1140 / 1144 M31.
```

Its four-M31 deficit is one QM31 direction in the already transmitted
round-zero relation polynomial `p0`.  It supplies every missing later-opening
pivot.  Since fresh `M` is sampled, committed and injected only after
`alpha0`, every M column is identically zero in the p0 observation row.  No
choice of the line-code basis, tau or nonzero beta can change that causal
zero.

This gives a direct distinguishing counterexample in the ambient affine
model: take two centers whose difference is the nonzero residual p0 quotient
direction.  Their p0 views occupy distinct affine cosets, while all fresh-M
randomness has zero projection onto that quotient.  The later continuation
may be perfectly randomized and the p0 distinguisher still succeeds.

Therefore:

* **fresh W1 alone:** complete ambient HVZK is refuted;
* **fresh W1 plus a separately bound pre-alpha0 mask:** possible, but the
  exact joint observation map must be rerun and reach full containment;
* **fresh W1 under exact-language semantics:** open; it becomes sufficient
  only if a theorem proves that every valid same-statement witness difference
  has zero residual p0 projection.

Neither Merkle salting nor the beta challenge repairs this field-view hole.

## Implementation gates

Before integration, the candidate needs:

1. a note-level attached-function theorem for `(W1,M)` at the exact line code
   and Johnson radius, with the exact list numerator and g38 placement;
2. transcript KAT and weakening teeth for root/tau/work/beta ordering,
   noncanonical tau, zero-beta attempts, lane swaps and unauthenticated M;
3. a wrong-tau and false-base-seam adversarial corpus;
4. an exact-view affine containment run including p0, tau, all later messages,
   q openings and atomic public data, plus an all-q certificate;
5. the private-Merkle/EPRO simulator update for the widened root; and
6. a labelled CU/proof-size measurement that does not infer savings from the
   mask dimension alone.

## Sources and code anchors

* `crates/aspis-prover/src/state_only_circle_relation.rs`, especially
  `fold`, `inject_profile21_first_later_u`, and
  `profile21_first_later_full_target`.
* `crates/aspis-prover/src/state_only_profile21.rs`, round-zero causal loop.
* `crates/aspis-core/src/state_only_prefix.rs`, profile-21 verifier transcript
  schedule.
* `docs/stage2-mask-code-alternatives.md`, strict-root1 rank and early-p0
  obstruction.
* `docs/aspis-soundness-note.md` section 16.4, exact missing transport theorem.
* Arnon--Chiesa--Fenzi--Yogev, *WHIR*, ePrint 2024/1586, sections 4.2--4.3.
* Gruen, *Vortex*, ePrint 2024/185, correlated-agreement reduction.

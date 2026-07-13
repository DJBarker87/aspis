# Profile 22: private-salted profile-20 freeze

Date: 2026-07-13

Status: **byte-exact builder, host verifier, append-only SBF verifier, and both
atomic mutation paths are integrated and literally measured. Production
mutation remains disabled: the complete-system soundness and complete-view
HVZK gates are still open, and the committed diagnostic fixture is unmined.**

## Purpose

Profile 22 is the minimum private-Merkle successor to atomic profile 20.  It
keeps profile 20's width-28 statement/relation word, rate `1/512`, q16 query
geometry, four arity-four folds, OOD schedule, and terminal predicate. It
changes the profile domain separator, the five Merkle leaf/opening formats,
and raises the batch and final work predicates to the profile-22-specific g38
freeze.

There is no source switch and no `X`, `F`, `U`, `tau`, `delta`, source root,
source work, translated first-later word, or source-query equation.

## Frozen wire

The header uses append-only profile id `22` under the existing `V4_S2`
header version.  All remaining prefix offsets and fields are byte-identical
to profile 20:

```text
log rows                  10
log blowup                 9
query count               16
batch grinding            38 bits
fold grinding        [39, 35, 31, 27] bits
final grinding            38 bits
prefix length          6,736 bytes
generator width           28 = 26 C1 + 2 C2
```

The new profile id and g38 final-work byte are absorbed in the existing
`PROFILE` header record. From that domain-separated initial state onward, the
Fiat--Shamir labels, prover messages, challenge order, retry rules, and query
sampling are exactly the ordinary profile-20 schedule; only the two work
thresholds differ. Salts are never transcript messages; each root already
binds its private leaf records.

The five committed sections, in consensus order, are:

| section | binary depth | tree tag | value bytes | private record bytes |
|---|---:|---|---:|---:|
| C1 layer zero | 17 | existing C1 tag | 416 | 448 |
| C2 layer zero | 17 | existing C2 tag | 128 | 160 |
| W1 | 15 | existing line-1 tag | 64 | 96 |
| W2 | 13 | existing line-2 tag | 64 | 96 |
| W3 | 11 | existing line-3 tag | 64 | 96 |

Every opened record is `value || 32-byte salt`.  The aggregate suffix is the
five canonical private minimal-subtree openings in the table order, with one
shared transcript-derived circle/line index object.  Trailing bytes, wrong
section order, wrong depth, wrong tag, wrong width, noncanonical field bytes,
salt mutations, value mutations, frontier mutations, and root mutations are
all rejecting teeth.

## Entropy and crash rule

The prover consumes `StateOnlyAttemptSecrets`: one public 256-bit mask nonce,
one independent private field-mask seed, and one independent private leaf-salt
seed.  The durable nonce ledger must burn the public nonce before either the
field masks or a private salt can be derived.  A failed build or crash burns
the attempt.

Profile-22 salts use a new attempt-binding domain, independent of the retired
profile-21 switch-basis binding.  The binding includes the hiding context,
profile id, fixed depths, fixed value widths, and tree tags.  Each leaf salt
then additionally binds its tree tag and leaf index.  The same public nonce is
globally non-reusable in the durable wallet ledger.

## Soundness and privacy boundary

The authenticated values and every PCS equation are unchanged from profile
20.  Replacing `H(tag || value)` by `H(private-domain || tag || value || salt)`
does not change the relation, MCA, fold, OOD, or q16 soundness terms; it changes
only the Merkle binding reduction and proof bytes.

With batch g38, final g38, and fold work `[39,35,31,27]`, the frozen soundness
ledger is 102.4649 bits at factor 31 and 102.0972 bits at factor 40. Raising
these thresholds changes mining time only; verifier CU and proof length are
unchanged.

Private salting is necessary but is not, by itself, the complete HVZK proof.
No hiding claim is credited here until the corrected physical affine-view
rank artifact, private-Merkle/EPRO simulator, retry/side-channel argument, and
same-wire distinguisher suite are all green.

The current machine-readable gates are intentionally red:

- `profile22_no_source_soundness_epro.json` reports
  `complete_system_claim_quotable = false`. Its Johnson numeric ledger is
  green and does not invoke a capacity conjecture, but the production claim
  still needs every work record mined and checked plus the remaining
  transcript/physical-containment obligations.
- `profile22_universal_affine_privacy.json` reports the
  root-neutral-sumcheck all-schedule lemma open. Fixed-q16 physical replay is
  green; it is not promoted to a complete-view simulator theorem.
- the complete-view surface includes proof-account framing, roots, opened
  `value || salt` records, frontier nodes, transcript/work inputs, logs,
  mutation account images, rent/payer deltas, timing, and failed attempts.

None of the diagnostic feature gates below changes either boolean.

## Literal integrated measurements

The committed fixture is 56,686 bytes with SHA-256
`77736f0ea30ae9e2516537213e7dce386c9be69e3c772e5b50f03c57892136f8`.
It is deliberately unmined: the production host and SBF APIs reject the same
bytes, while the local diagnostic-only build bypasses only the six PoW
predicates. The bypass requires
`diagnostic-unmined-profile22-acceptance`; it is not implied by
`profile22-mutation-candidate` and is absent from every production-capable
binary.

Append-only tag 56 executes one parser/transcript/terminal/relation/private-
opening/q16 verifier call. On `solana-test-validator 2.3.0` it consumes
1,157,676 CU, leaving 242,324 CU below the 1.4M instruction limit. The
overlap-free ledger is:

```text
transaction setup       1,569
proof load                485
parse                   1,829
transcript            152,038
terminal              382,178
relation              183,649
private openings      184,928
layer-zero queries    156,973
later queries          93,477
completion                219
wrapper return            272
post-marker                 59
                      -------
total                1,157,676
```

Append-only tag 57 is the production-PoW mutation wrapper and contains no
diagnostic selector. It remains fail-closed in default builds. Append-only tag
58 is the nondefault local-validator measurement arm. Its two literal totals
are:

| marker path | total CU | increment over tag 56 | headroom |
|---|---:|---:|---:|
| program-owned zeroed | 1,167,381 | 9,705 | 232,619 |
| canonical System-create | 1,169,714 | 12,038 | 230,286 |

Both ledgers reconcile exactly. Proof corruption rejects without mutation;
production tag 57 rejects the unmined fixture without mutation; the pool
sequence advances once, the anchor and exact marker image are written, a
duplicate is rejected without a second write, and the two-signer System-path
race commits exactly one transaction. The feature SBF build emits no
over-limit stack-frame warning. These results are recorded in
`atomic_state_only_profile22_acceptance.json` and
`atomic_state_only_profile22_mutation.json`.

## Module and integration plan

New files, to keep the old profile-20 and profile-21 wires immutable:

- `crates/aspis-core/src/state_only_profile22_openings.rs`: fixed five-section
  private parser/verifier for widths `[416,128,64,64,64]`.
- `crates/aspis-prover/src/state_only_profile22_openings.rs`: matching
  aggregate serializer.
- `crates/aspis-prover/src/state_only_profile22.rs`: atomic builder using the
  ordinary width-28 relation and private trees from the first commitment.
- `crates/aspis-statement/src/state_only_profile22.rs`: complete atomic host
  verifier over the ordinary relation and private openings.
- `crates/aspis-prover/src/state_only_profile22.rs`: byte shape, replay, KAT,
  and adversarial root/value/salt/frontier/trailing-byte teeth in its test
  module.
- `crates/aspis-prover/examples/profile22_fixture.rs`: deterministic,
  explicitly insecure diagnostic-fixture generator.
- `programs/aspis-verifier/src/lib.rs`: append-only tags 56--58, all
  fail-closed without their nondefault candidate feature. The tag-56 unmined
  selector additionally requires its separate diagnostic-only feature.
- `xtask/src/onchain.rs`: literal tag-56 acceptance and tag-58 atomic mutation
  harnesses with overlap-free ledgers and rollback/concurrency teeth.

Minimal shared-file edits:

- register profile id/shape 22 in `state_only_prefix.rs` and the existing
  header builder;
- export the three new modules from crate `lib.rs` files;
- add a profile-22 leaf-salt derivation method to `state_only_entropy.rs`;
- no old tag or existing profile parser is repurposed. Production tag 57 must
  not be enabled until both independent proof gates are green and a mined KAT
  passes the no-bypass production host and SBF entrypoints.

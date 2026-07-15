# Profile 23: D-after-G root-neutral liveness, soundness and EPRO ledger

**Status (`2026-07-14`): the q18 minimum-q-degree root-neutral polynomial
minor, complete Good23 predicate, cap17/q3 builder, proof-independent numeric
soundness ledger, and complete-view computational hiding in the declared
SHA-256 ROM/EPRO fixed-channel model are green. The canonically mined q18
proof, production host/SBF KATs, and local one-transaction release certificate
are also green with `36/36` gates. The `2026-07-13` q16/cap16 release is
superseded historical evidence.**

The candidate generator order is fixed as

```text
semantic[0..15], mask-only[16..25], H[26], G[27], D[28].
```

`D` is one new full-domain QM31 lane with the zero factor. Three post-final-
nonce q18 candidates are tried inside each of at most seventeen public attempts.
The verifier receives one selector byte and verifies only the selected tuple.

## Exact root neutrality

Let the layer-zero batch be

```text
R(gamma) = sum_j gamma^j C_j + gamma^27 G + gamma^28 D.
```

For a source change `U` in a semantic or mask lane `j`, pair it with

```text
Delta G = -gamma^(j-27) U = -gamma^(-(27-j)) U.
```

For a source change `V` in `D`, pair it with

```text
Delta G = -gamma V.
```

Both pairs make `Delta R(gamma)` identically zero. The executable checks this
pointwise for all 10,610 candidate sources, not only for the 1,404 columns
eventually selected into the minor.

The frozen result is:

| quantity | result |
|---|---:|
| serialized terminal rows | 336 M31 |
| terminal projection rank under root neutrality | 324 |
| D terminal projection rank | 12 |
| terminal-conditioned sumcheck rank | 1,080 |
| root-neutral conditioned sumcheck rank | 1,076 / 1,076 |
| joint rank | 1,404 / 1,404 |
| degree-one q columns | 1,068 |
| degree-two q columns | 336 |
| q total degree | 31,320 |
| safe gamma-coordinate degree | 80,688 |
| root-neutral z degree | 41,040 |
| minor fingerprint | `0x6b3838662fbf34db` |

The q18 basis is selected in minimum-degree order: all semantic and D
degree-one candidates precede mask-only degree-two candidates. The 1,100
degree-one candidates have exact rank 1,068, so no alternate basis in this
source family restores the cap16 liveness bound; cap17 is the smallest proved
fix.

The gamma degree deliberately uses the safe M31 scalar clearing rule. A
coordinate of `gamma^-e` is written over `Norm(gamma)^e`, and the whole M31
column is scaled by that norm. Multiplication by `gamma^e` is not a legal
scalar column rescaling in the M31 source module; using it would silently turn
one M31 source into a QM31-valued source without its coordinate mates.

The complete `Good` determinant retains two additional independent raw
12-M31 terminal certificates:

```text
remaining G/D terminal direction   12*10 = 120 z-degree
H1 inactive-padding terminal       12*10 = 120 z-degree
```

Therefore the complete-view bound is `41,040 + 120 + 120 = 41,280`, not the
root-neutral-minor-only `41,040` and not the intermediate one-certificate
`41,160`.

## Query-domain guard and q3 liveness

The ledger exhaustively visits all `2^17` implemented log-19 fibers and checks

```text
query_root(q) = 2*x(q)^2 - 1
              = line_domain_x_for_circle(19, 1, q).
```

All 131,072 roots are distinct and none equals one. Consequently distinct
fiber sampling already gives distinct polynomial roots, and the probe's
`root != 1` precondition is automatic on this coset. No extra degree-16 anchor
guard is booked.

With `p=2^31-1`, `N=131072`, `q=18`, and three candidates,

```text
rho_q = 31320 / (131072 - 17)
      = 0.23898363282591278

d_cont = 41280 + 80688 = 121968

beta = d_cont/p + rho_q^3
     = 0.013705910239932412.
```

One attempt therefore has `6.189058045848226` bits of failure probability.
Seventeen independent public attempts give

```text
-log2(beta^17) = 105.21398677941984 bits.
```

Including the bounded construction abort gives

```text
Pr[public abort] <= 17*(128/p^6) + beta^17,
```

which gives a `105.21398677941983`-bit public-abort floor. The bounded q18
sampler's cap17/q3 union is separately `550.9238900176506` bits and is not
the limiting term.

## Term-by-term soundness changes

The inherited rate-1/512 Johnson/MCA ledger changes only these algebraic
terms:

| term | Profile 23 change | bits |
|---|---|---:|
| polynomial batch | degree `27 -> 28` for width 29 | 107.31602011435538 |
| final q18 miss | multiply only this event by 3 | 110.18373913364348 |
| nonzero gamma / three-point batch | numerator `29 -> 30` | 119.09310940170425 |
| inactive-copy gamma claim | numerator `27 -> 28` | 119.19264507525517 |

Every other event is inherited unchanged and is listed individually in the
JSON artifact. Their exact union is

```text
selected event union                106.70203348730290 bits
BCS at T=1                          101.65763936794444 bits
BCS at T=2^128                      106.70203180861958 bits
selected factor-40 diagnostic       101.38010539241553 bits
```

The refined selector calculation is retained as a diagnostic. The
conservative unselected event union is `106.79080600295417` bits;
reconstructing the same work-normalized BCS endpoints and then applying a
whole-ledger factor three gives the authorizing release floor
`100.16144938287455` bits. The
`105.21398677941984` figure is only the cap17 rank-exhaustion subterm and must
not be presented as whole-protocol soundness.

The work-normalized BCS statement is explicit:

```text
epsilon_BCS(T)/T
  <= (1 + R/T)*epsilon_round + 3*(T + 1/T)/2^lambda,
R = 32, lambda = 256, 1 <= T <= 2^128.
```

Both interval endpoints are checked. In particular, at `T=1` the round-error
multiplier is `1+R=33`, not 32. For the conservative ledger the endpoint floors are
`101.74641188359571` bits at `T=1` and `106.79080421773332` bits at
`T=2^128`. The prover-selected selector byte is a new message boundary after
the final nonce and before q18; the current ledger does not merge it away.

The factor-3 union applies only to the final query-miss event. Multiplying the
whole soundness ledger by three is a valid but needlessly pessimistic bound.

## Distinct EPRO input inventory

`D` has 1,024 QM31 coefficients, hence 4,096 M31 field-expander outputs. At
two random-oracle inputs per output, the field-expander inventory becomes

```text
2*(22850 + 4096) = 53892 inputs.
```

The transcript inventory is the number of **distinct random-oracle inputs**
that must be programmed or collision-accounted, not the number of literal
SHA invocations made by an unoptimised replay. The current host code may
replay the common pre-query transcript for each selector; those identical
inputs occur more than once operationally but enter this EPRO set once.

The distinct-input inventory is:

```text
Profile-22 base                                      601
two extra q streams * 8 blocks * (squeeze+advance)   32
three candidate-label-44 absorbs                       3
dedicated D-claims label-43 absorb                      1
                                                     ---
                                                     637
```

The last input is mandatory under the implemented dedicated label. The
earlier provisional count 636 omitted it.

Thus

```text
C = 3*305152 + 53892 + 8 + 637 = 969993.
```

At `Q_H <= 2^128` and seventeen attempts:

| EPRO term | bits |
|---|---:|
| one-sided real-vs-simulator leading no-prequery term | 104.02492234825198 |
| programming collision lower bound | 209.04984478399368 |
| six-work-nonce exhaustion lower bound | 193635243.91255844 |

These are the numeric EPRO terms only. The inherited affine and PRG hybrids
retain their separately stated assumptions.

The Profile-23 specialization now closes those assumptions for the declared
computational model: Good23 gives an exact complete non-hash field simulator
with `epsilon_aff=0`; SHA-256 expansion is inside the same programmable random
oracle; and the fixed-boundary controller gives the declared one-event public
channel. The one-sided real-vs-simulator complete-view bound is dominated by
`2^-104.02492234825198`. The written two-witness reduction passes through that
simulator and therefore has the conservative pairwise floor
`103.02492234825198` bits. This is not statistical HVZK, a standard-model
SHA-256 PRG claim, or protection for filesystem/timing/power/thermal/memory
channels or remote-prover traffic; `epsilon_side=0` excludes them. The exact
statement and
assumptions are pinned in
`docs/stage2-profile23-computational-hvzk-closure.md` and
`results/stage2/profile23_computational_hvzk_closure.json`.

## What is and is not closed

This work closes the fixed numeric polynomial-kernel witness, the executable
three-minor complete-`Good` product provenance, and the exact Profile-23
liveness, Johnson-event, BCS-factor and EPRO arithmetic. The formerly
quarantined typed `D`/q3 prover-verifier path is integrated. The host worker
now retains one common attempt, evaluates all three post-final schedules with
the exact complete-`Good` predicate, serializes only the least good branch,
retries only an exact all-bad result up to cap 17, and exposes one opaque
candidate or one opaque failure. A distinct Profile-23 fixed-release edge
publishes exactly one proof/abort result at the selected boundary. Valid
end-to-end proofs for
selectors 0, 1 and 2 now build and verify.

This soundness/EPRO artifact did not by itself enable a default production
tag. The separate fail-closed release evaluation now records `released=true`,
`status=released_all_required_gates_green`, and `36/36` passing gates in
`results/stage2/profile23_one_transaction_release.json`. It binds a
64,447-byte q18 proof with SHA-256
`d4f529964d1cf9ccd9c5568b694796ba54191c6be38d341c66efa08c830cdc3d`,
a canonical statement sidecar with SHA-256
`947a608c93487a634f37119bead8d61fe29e9cb6883493465d6fb35af27883c2`,
canonical public-input digest
`b2d150dfcb6432c1b6f2e3892ee45a9aa5f393809d97c8292fea975b3da35fa3`,
and a fresh 921,848-byte default SBF with SHA-256
`97c45a9abef97607a2fc6ed245829210046b234044b6738599d2bce0c367d04a`.
Production tag59 is `1,303,642 CU`; tag65 is `1,338,471 CU` on the
program-owned path and `1,340,803 CU` on canonical System creation, leaving
`59,197 CU` of maximum-path headroom.

The authorizing conservative soundness floor is
`100.16144938287455` bits. The q18 complete-view
pairwise-witness floor is `103.02492234825198` bits in the declared SHA-256
ROM/EPRO fixed-release-channel model; the corresponding real-vs-simulator
bound is `104.02492234825198` bits. These theorem facts do not broaden the
claim beyond their assumptions or side-channel exclusions.

The intended certificate scope is atomic verification and mutation using a
finalized, pre-uploaded proof account. Production tag59 and tag65 require the
all-zero authority sentinel in bytes `8..40` of the unchanged 40-byte header;
proof-account creation, chunk upload, and `FinalizeProof` are excluded.
Append-only tag 62 seals proof accounts and tag 63 initializes pools.
The certificate is local release evidence, not mainnet or external-audit
evidence. The finalized mainnet execution and current audit status are
recorded separately in
[`profile23-mainnet-demo.md`](profile23-mainnet-demo.md) and the
[prepublication security review](reviews/profile23-prepublication-security-review.html).

## Superseded q16 production evidence (`2026-07-13`)

The earlier q16 release passed 30/30 gates. Its 61,599-byte mined proof,
6,870,048-byte default SBF, and `1,207,123 CU` worst production path with
`192,877 CU` headroom are retained as historical engineering evidence only.
Its selected Johnson floor was `101.30230658283051` bits. The q16 unmined
diagnostic CU rows (`1,195,306`, `1,205,006`, and `1,207,339 CU`) and its
`141.00 s` fresh-attempt privacy run are likewise historical. None transfers
to q18.

The xtask acceptance and mutation commands accept both
`ASPIS_PROFILE23_PROOF` and `ASPIS_PROFILE23_STATEMENT` so q18 mined bytes can
be retested without replacing the committed unmined theorem fixture.

## Reproduction

```bash
NO_DNA=1 cargo run -q -p aspis-prover \
  --example profile23_soundness_epro_ledger -- --calculation-only

NO_DNA=1 cargo run -q --release -p aspis-prover \
  --example profile23_complete_good_product

NO_DNA=1 cargo test --release -p aspis-prover --lib \
  state_only_good23::tests::frozen_profile23_fixture_runs_exact_good23_on_all_selectors \
  -- --ignored --nocapture
```

Machine-readable result:
`results/stage2/profile23_d_after_g_soundness_epro.json`.

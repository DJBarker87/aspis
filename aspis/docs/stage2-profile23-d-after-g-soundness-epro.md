# Profile 23: D-after-G root-neutral liveness, soundness and EPRO ledger

**Status (`2026-07-13`): the fixed root-neutral polynomial minor, complete
Good23 predicate, cap-16/q3 builder, fixed-release path, numeric soundness,
complete-view computational hiding in the declared SHA-256 ROM/EPRO fixed-
channel model, and production KATs are green. Profile 23 is now released as
the default one-transaction production path after all `30/30` release gates
passed. This earlier soundness/EPRO artifact did not itself change or enable
the production wire.**

The candidate generator order is fixed as

```text
semantic[0..16], mask-only[16..26], H[26], G[27], D[28].
```

`D` is one new full-domain QM31 lane with the zero factor. Three post-final-
nonce q16 candidates are tried inside each of at most sixteen public attempts.
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
pointwise for all 10,617 processed sources, not only for the 1,404 columns
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
| degree-one q columns | 1,024 |
| degree-two q columns | 380 |
| q total degree | 28,544 |
| gamma inverse exponent sum | 23,105 |
| safe gamma-coordinate degree | 92,436 |
| root-neutral z degree | 41,040 |
| minor fingerprint | `0xb7472b1f2b1d03e7` |

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

With `p=2^31-1`, `N=131072`, `q=16`, and three candidates,

```text
rho_q = 28544 / (131072 - 15)
      = 0.21779836254454168

d_cont = 41280 + 92436 = 133716

beta = d_cont/p + rho_q^3
     = 0.010393777091336816.
```

One attempt therefore has `6.588136165878648` bits of failure probability.
Sixteen independent public attempts give

```text
-log2(beta^16) = 105.41017865405837 bits.
```

Including the bounded construction abort gives

```text
Pr[public abort] <= 16*(128/p^6) + beta^16,
```

which rounds to the same `105.41017865405837`-bit floor. The bounded q16
sampler's cap-16/q3 union is separately `588.7966767164355` bits and is not
the limiting term.

## Term-by-term soundness changes

The inherited rate-1/512 Johnson/MCA ledger changes only these algebraic
terms:

| term | Profile 23 change | bits |
|---|---|---:|
| polynomial batch | degree `27 -> 28` for width 29 | 108.31602011435538 |
| final q16 miss | multiply only this event by 3 | 107.31692409651947 |
| nonzero gamma / three-point batch | numerator `29 -> 30` | 119.09310940170425 |
| inactive-copy gamma claim | numerator `27 -> 28` | 119.19264507525517 |

Every other event is inherited unchanged and is listed individually in the
JSON artifact. Their exact union is

```text
event union                         106.62423467771788 bits
after BCS boundary factor 32        101.62423467771788 bits
after conservative factor 40        101.30230658283051 bits
```

The refined analysis above applies the factor three only to the final q16
miss and retains `101.30230658283051` bits after factor 40. The acceptance
artifact also pins the coarser whole-ledger-times-three sensitivity floor,
recomputed from Profile 23's own terms and 32 BCS boundaries, at
`100.80652861422749` bits. The selected `101.30230658283051`-bit result is the
headline; the coarse result is a deliberately pessimistic sensitivity. The
`105.41017865405837` figure is only the cap-16
rank-exhaustion subterm and must not be presented as whole-protocol soundness.

The BCS factor is 32 rather than Profile 22's 31. The prover-selected selector
byte is a new message boundary after the final nonce and before q16. It may be
merged away only by a compiler theorem for a combined final-nonce/selector
record; the current ledger does not assume that theorem.

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

At `Q_H <= 2^128` and sixteen attempts:

| EPRO term | bits |
|---|---:|
| one-sided real-vs-simulator leading no-prequery term | 104.11238518950232 |
| programming collision lower bound | 209.22477047196247 |
| six-work-nonce exhaustion lower bound | 48,408,806.06128344 |

These are the numeric EPRO terms only. The inherited affine and PRG hybrids
retain their separately stated assumptions.

The Profile-23 specialization now closes those assumptions for the declared
computational model: Good23 gives an exact complete non-hash field simulator
with `epsilon_aff=0`; SHA-256 expansion is inside the same programmable random
oracle; and the fixed-boundary controller gives the declared one-event public
channel. The one-sided real-vs-simulator complete-view bound is dominated by
`2^-104.11238518950232`. The written two-witness reduction passes through that
simulator and therefore has the conservative pairwise floor
`103.11238518950232` bits. This is not statistical HVZK, a standard-model
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
retries only an exact all-bad result up to cap 16, and exposes one opaque
candidate or one opaque failure. A distinct Profile-23 fixed-release edge
publishes exactly one proof/abort result at the selected boundary. Valid
end-to-end proofs for
selectors 0, 1 and 2 now build and verify.

This soundness/EPRO artifact did not by itself enable a default production
tag. Its overlap-free unmined diagnostic measurements remain historical
evidence: `1,195,306 CU` for read-only tag 59, `1,205,006 CU` for a
program-owned mutation marker, and `1,207,339 CU` for canonical System marker
creation. The fresh-attempt privacy regression is green in `141.00 s`, and
the declared computational-HVZK theorem is closed.

The later production integration completed the gates that were outside this
artifact's scope. `results/stage2/profile23_one_transaction_release.json`
records `released=true` with all `30/30` required gates green. The
certificate's one-transaction scope is atomic verification and mutation using
a finalized, pre-uploaded proof account. Production tags 59 and 60 require the
all-zero authority sentinel in bytes `8..40` of the unchanged 40-byte header;
proof-account creation, chunk upload, and `FinalizeProof` are excluded.
Append-only tag 62 seals the proof account, append-only tag 63 initializes the
pool, and the frozen program id is
`7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue`. The
released mined proof is
`results/stage2/proofs/atomic_state_only_profile23_v3_mined.bin`, `61,599`
bytes, SHA-256
`35c4e79316bf4a2af1951e5d2f41b6ebb4ebb7bd1e91a3ba93c52e549bfe7949`.
The manifest-default production SBF is `6,870,048` bytes, SHA-256
`6b64baf559dcddbd6f9b1af1205effeb6afae6a5746a44421e8826251fe4cffb`.

Same-binary production tag 59 is `1,202,939 CU`. Literal production tag 60
measures `1,204,792 CU` for the program-owned zeroed mutation account and
`1,207,123 CU` for canonical System-owned account creation. The worst measured
production path therefore has `192,877 CU` of
headroom under the `1,400,000 CU` cap. The release certificate pins the
selected Johnson soundness floor at `101.30230658283051` bits and records the
Profile-23-own whole-ledger-times-three/BCS32 sensitivity at
`100.80652861422749` bits. It also pins the complete-view pairwise-witness
computational-hiding floor at `103.11238518950232` bits in the declared
SHA-256 ROM/EPRO fixed-release-channel model. The corresponding
real-vs-simulator bound is `104.11238518950232` bits. These release facts do
not broaden either theorem beyond its stated assumptions or
local-side-channel exclusions.

The xtask acceptance and mutation commands accept `ASPIS_PROFILE23_PROOF` so
the released mined bytes can be tested without replacing the committed
historical unmined KAT.

## Reproduction

```bash
NO_DNA=1 cargo run -q -p aspis-prover \
  --example profile23_soundness_epro_ledger

NO_DNA=1 cargo run -q --release -p aspis-prover \
  --example profile22_root_neutral_polynomial_kernel_rank -- \
  results/stage2/proofs/atomic_state_only_profile22_v3_unmined.bin \
  52e96f99756fe8fd2d8b7a700019b143d7eb549af1bf1ae987e99a75cadcd4c9

NO_DNA=1 cargo run -q --release -p aspis-prover \
  --example profile23_complete_good_product

NO_DNA=1 cargo test -q -p aspis-prover --lib \
  state_only_good23::tests

NO_DNA=1 cargo test -q -p aspis-prover --lib \
  state_only_profile22_release::tests

NO_DNA=1 cargo check -q -p aspis-prover \
  --example profile23_production_miner
```

Machine-readable result:
`results/stage2/profile23_d_after_g_soundness_epro.json`.

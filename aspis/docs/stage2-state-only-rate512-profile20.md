# State-only rate-1/512 profile 20

Date: `2026-07-13`

Status: **exact verifier measurement green; Johnson/BCS PCS row green;
baseline complete-view hiding rank red.** This is a diagnostic profile, not a
complete-system security claim. Atomic mutation is not included and the
unmined fixture bypasses only PoW acceptance predicates.

## Exact object and measurement

Profile 20 keeps the same width-28, 1,024-coefficient message and four
arity-four folds. It evaluates on the log-19 circle domain:

```text
message coefficients       1,024
circle symbols            524,288
four-symbol fibers        131,072
rate                         1/512
queries                         16
layer depths       17; 15, 13, 11
batch/query work              36/36 bits
fold work             [39,35,31,27] bits
```

The exact unmined proof is
`results/stage2/proofs/state_only_width28_global_inactive_p20_unmined.bin`:

```text
proof bytes                    54,604
prefix / suffix           6,736 / 47,868
SHA-256       b8122b19ecf6604c3d1db7eaab871996
              93fd80d05579bbeeefe1c6a82ca81e34
deployed verifier .so       4,720,360 bytes
```

The literal integrated instruction completed at **1,165,013 CU**. The
overlap-subtracted ledger is **1,164,948 CU**, leaving **235,052 CU** below
the 1.4M cap:

```text
transaction setup        1,279
proof load                 404
parse                    1,411
transcript             151,616
terminal               335,209
relation               225,230
Merkle openings        180,139
query arithmetic       269,349
verifier return            252
post-marker                 59
                      ---------
total                 1,164,948
```

The query bucket reconciles as `2,202` shared setup + `162,991` layer-zero
+ `104,156` later-layer CU = `269,349`. The segmented query run contains an
additional `9,734` CU duplicate power setup which the integrated verifier
reuses from the relation phase and the ledger therefore subtracts.

Machine-readable measurements are in
`results/stage2/state_only_width28_global_inactive.json`.

## Theorem-derived Johnson row

This row uses the March 24, 2026 revision of S-two, ePrint 2026/532,
Theorem 19 and Lemma 4, as pinned by
`docs/stage2-johnson-transport-closure-2026-07-12.md`. It is not extrapolated
from the rate-1/16 or rate-1/32 measurements.

Let `Q=|QM31|=(2^31-1)^4`, `rho=1/512`, and

```text
alpha = (1 + 1/(2*10))*sqrt(rho) = 0.04640388251536719.
```

The complete-fiber agreement cap is therefore

```text
A = floor(alpha * 131072) = 6082.
```

For each folded line code with output-domain size `n` and dimension `k`,
S-two uses

```text
rho_i = (k-1)/n
m_i   = max(ceil(sqrt(rho_i)/(2*(alpha-sqrt(rho_i)))), 3)
ell_i = (m_i+1/2)/sqrt(rho_i)
eps_i = 3*ell_i*((2*ell_i^4/3)*rho_i+1)*n/Q.
```

The generator evaluates that formula directly. It also asserts that the same
function reproduces the pinned rate-1/16 table before deriving profile 20:

| round | `(n,k)` | `m_i` | `ell_i` | unground bits | work | normalized bits |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 0 | `(131072,256)` | 10 | 238.0532812332 | 75.5299426923 | 39 | 114.5299426923 |
| 1 | `(32768,64)` | 9 | 216.6597801103 | 78.2262818045 | 35 | 113.2262818045 |
| 2 | `(8192,16)` | 6 | 151.9017226148 | 82.8581350802 | 31 | 113.8581350802 |
| 3 | `(2048,4)` | 3 | 91.4476170639 | 88.8406480138 | 27 | 115.8406480138 |

The largest list parameter is `238.0533`. The OOD calculation pins the
conservative integer cap `L_ood=240`: this is one larger than
`ceil(238.0533)=239`. With root caps `[1024,255,63,15]`, two OOD samples per
round, and sample space `Q-(2^31-1)^2`, the OOD union is `213.1000183949`
bits.

The exact remaining critical rows are:

```text
powers-generator batching, before/after work  70.3684875342 / 106.3684875342
q16 hypergeometric query, after work                         106.9018865972
union of four normalized fold rows                          112.0797907885
conservative all-round union                                105.4867589959
minus log2(31) BCS factor                                   100.5325626855
margin over 100 bits                                          0.5325626855
```

These values are generated in
`results/stage2/rate16_hardened_soundness.json`. The scalar circle-FFT
subcode, powers-generator batching, arity-four folds and WHIR list/fold
commutation use the proven Johnson transport in the pinned note. The artifact
still sets `complete_system_claim_quotable=false`: the hiding reserve is not
instantiated by profile 20 and atomic mutation has not been composed.

## Hiding result

The exact q16/domain-19 FullShared baseline rank gate gives:

```text
masked zerocheck              1080 / 1080 M31
complete PCS View              712 / 780 M31
baseline deficit                68 M31 = 17 QM31
valid-witness containment       true
```

Thus lower query count removes 52 of the previous 120 missing M31 directions
but does **not** make the current ad-hoc mask complete. Profile 20 alone is not
HVZK.

The separate masked-switch research map reaches `780/780`, adding 64 pivots
in later openings and four in relation coefficients. That result is recorded
in `results/stage2/state_only_masked_switch_joint_rank.json`, but it remains
non-production until the early channel is binding, the circle code-switch
handoff has a proven proximity reduction, the Fiat--Shamir order is fixed,
and its verifier CU is measured.

## Commands and teeth

```text
NO_DNA=1 ASPIS_STATE28_REUSE_PROOFS=1 cargo run --release -p aspis-xtask -- stage2-state-only-width28
NO_DNA=1 cargo run --release -p aspis-xtask -- stage2-rate16-soundness
NO_DNA=1 cargo test -p aspis-core state_only_prefix::tests
NO_DNA=1 cargo test --release -p aspis-prover --test state_only_circle_openings rate512_q16_width28_roundtrip
```

The parser replays all three profile headers and transcript schedules. The
rate-1/512 opening test corrupts an authenticated leaf after a full log-19
roundtrip. Static rate-1/512 normalization tables are generated from the
circle-domain formulas; selected first/last/interior entries are checked
against dynamic group arithmetic.

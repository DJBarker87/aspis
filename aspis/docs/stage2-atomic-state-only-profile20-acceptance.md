# Atomic state-only profile-20 acceptance

Date: 2026-07-13

Status: **acceptance-complete and read-only on SBF; 1,179,451 CU. Atomic
complete-view hiding rank, mined PoW, and account mutation remain disabled.**

Append-only instruction tag 46 verifies the actual same-private-path atomic-v3
proof. The 56,044-byte proof contains the transcript-bound masked degree-27
terminal, the exact 183-link atomic copy polynomial, the three-point relation,
all Merkle openings, and every profile-20 q16 query. The verifier computes the
atomic statement digest itself; no expected terminal is provided as
instruction data.

The fixture pins:

- proof SHA-256
  `fdd1097f702b411b6bcd26d0e195322d7683ff93ec4cb70828b9459fe7cef007`;
- statement digest
  `52e96f99756fe8fd2d8b7a700019b143d7eb549af1bf1ae987e99a75cadcd4c9`;
- profile 20, rate `1/512`, 16 queries;
- Solana test validator 2.3.0.

## Literal reconciled ledger

| phase | CU |
| --- | ---: |
| transaction setup and public decode | 1,549 |
| proof load | 484 |
| parse | 1,804 |
| transcript | 151,952 |
| atomic terminal | 384,716 |
| relation | 183,481 |
| Merkle openings | 185,774 |
| query arithmetic | 269,366 |
| verifier return | 266 |
| post-last-marker | 59 |
| **literal total** | **1,179,451** |

The buckets sum exactly to the single simulation total and leave 220,549 CU
under 1.4M. This is not an overlap-subtracted or segmented estimate.

## Terminal reserve

The first internal breakdown measured the terminal at 484,442 CU and tag 46
at 1,279,180 CU, including identical marker overhead. Its largest atomic-only
excess was affine copy-pattern evaluation: 82,582 CU versus 19,425 CU in the
non-atomic baseline.

The live evaluator computes five shared eight-limb QM31 dots, then reconstructs
all fifteen generated affine tuple patterns by exact field identities. Four
M31 coefficient products per routing limb are reduced together. Finally, the
selected rank-103 `(bits 9..4, bits 3..0)` routing basis reuses the semantic
selector tensor already required by the same terminal. The generated rank-74
basis remains the minimum-rank independent reference, but building its second
selector tensor costs more in the integrated instruction.

The measured progression, with marker overhead present at every endpoint, is:

| exact implementation | literal CU |
| --- | ---: |
| pre-rewrite instrumented terminal | 1,279,180 |
| five-dot pattern reconstruction | 1,217,906 |
| rank-74 routing with lazy M31 reduction | 1,189,233 |
| shared semantic/rank-103 routing | **1,179,451** |

The final pattern phase is 21,328 CU, prepared selectors fall from 66,973 to
35,501 CU, and the selected shared routing phase is 107,910 CU. The rank-74
lazy routing phase is lower in isolation at 79,334 CU, but its second selector
expansion loses 9,782 CU end-to-end. The total exact saving from the first
instrumented endpoint is **99,729 CU**. No proof byte, root, challenge,
transcript label, or acceptance equation changes.

Guards:

- optimized versus generated pattern evaluator at 64 fresh random QM31 points;
- shared semantic tensor versus the selected rank-103 routing partition at 64
  fresh random QM31 points;
- exact active/inactive selector membership over all 1,024 rows plus 64 random
  off-domain points;
- diagnostic versus production terminal at 64 fresh random QM31 points;
- rank-74 routing versus the independent 183-link walk at 64 random QM31
  points;
- all sixteen C1 opening corruptions plus independent `h1`, `lambda`, and
  `chi` teeth;
- eight full-proof corruption offsets and all eight atomic public fields on
  host;
- changed pool revision rejected on SBF.

The terminal suite is 7/7 green. Generated constants remain derived from the
registry and pinned to registry fingerprint `0xa5249dda67f75888` and active-row
fingerprint `0xfc90f89be110b6f5`.

## Deliberate nonclaims

The proof uses an unmined diagnostic nonce. The verifier absorbs the nonce and
runs all downstream Fiat--Shamir work, but diagnostic mode bypasses the PoW
predicate; production mode rejects this fixture. Tag 46 accepts only a
read-only proof account and has no state-transition path. The separately
measured mutation closure costs 9,729--12,062 CU over this endpoint, but its
default tag remains fail-closed until profile-21 complete-view hiding closes.

The actual prover uses the pinned atomic mask inventory, but this artifact does
not claim HVZK until the atomic full-transcript-view rank and the profile-21
external masked-switch containment are measured. It also does not authorize
pool or nullifier mutation. Those gates remain separate on purpose.

Machine-readable artifact:
`results/stage2/atomic_state_only_profile20_acceptance.json`.

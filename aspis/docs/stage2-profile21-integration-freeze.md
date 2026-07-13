# Profile-21 one-transaction integration freeze

Date: 2026-07-13

Status: **source-target reduction repaired; integration resumed; not a fit,
soundness, or privacy claim.**
The current conservative bridge, including the harder canonical System-owned
nullifier-creation path, is 1,375,491 CU. Only append-only tag 50 running the
literal profile-21 wire, all teeth, and the atomic mutation may replace that
bridge. The bridge remains provisional because it does not yet include the
measured production-covector combo check.

## Frozen statement and wiring

Profile 21 uses the atomic state-v3 trace and generated registry, not the old
state-only-v4 102-link layout. Two Poseidon2 x^5 rounds are composed inside
each transition constraint. The intermediate round state is virtual and is
never a copy-helper endpoint. Every value that crosses a composed-pair,
sponge, Merkle, public-digest, or semantic boundary remains committed:

- rows 0 through 10 are committed inputs to composed two-round transitions;
- row 11 is the committed final boundary used by continuations and public
  bindings;
- row 12 is the committed absorption boundary; and
- relation-free rows and cells are mask sources only, never semantic or copy
  endpoints.

The atomic migration regenerated the layout rather than inheriting the
state-only-v4 constants. Its exact copy inventory is 183 terms, 143 tag
groups, tuple width 17, 210 active rows, and 814 inactive rows. The selected
runtime routing uses the rank-103 tensor because it shares the already-live
semantic selector tensor; the independently generated rank-74 tensor and the
direct 183-link walk remain identity guards. The live registry, active-row,
relation-free-mask and layout/factor fingerprints are respectively:

```text
0xa5249dda67f75888
0xfc90f89be110b6f5
0x0fdabd401816cc99
0x9e4d2fcd4cf9fe01
```

The shared q16 source-basis fingerprint is `0xceb35dd3ee50e051`.
Any layout or source-basis change must regenerate the corresponding values
and hard-fail if compiled constants retain an old fingerprint.

## Main algebra recount

The committed main PCS remains the exact width-28 atomic hiding layout:

| object | frozen value |
| --- | ---: |
| semantic C1 columns | 16 |
| mask-only C1 columns | 10 |
| main C2 columns | 2 (`h1,G`) |
| main gamma width `k'` | 28 |
| gamma collision degree | 27 |
| terminal points | 3 (`z,succ(z),xor12(z)`) |
| atomic theta lanes / degree | 25 / 24 |
| copy terms / tuple width | 183 / 17 |
| zerocheck rounds / individual degree | 10 / 27 |
| transmitted zerocheck coefficients | 270 QM31 |

The degree-27 taxonomy is exact: two composed x^5 rounds contribute degree
25, the active selector contributes one, and the outer equality factor
contributes one. It is not trace degree, univariate total degree, gamma
degree, or FRI degree. The local zerocheck collision term is `270/|QM31|`.
The scalar main generator remains ordinary; no QM31 fiber-packing or
matrix-valued generator is introduced.

The auxiliary switch source is separate from the main gamma generator. It is
a dimension-35 ordinary line code committed before its target and delta
challenges. Physically, X/F values share the early C2 Merkle leaf/root, which
widens that leaf from 128 to 256 bytes, but they do not become extra main
gamma columns.

## Universal source basis

The source coefficient space is frozen as the direct sum

```text
R = (x^2 + 1) P_<16
M = span{1, x, x^18, ..., x^34}.
```

Natural-line-to-monomial conversion is triangular and invertible. For every
accepted tuple of 16 distinct M31 query abscissae, evaluation on R is

```text
diag(q_i^2 + 1) * Vandermonde(q_0,...,q_15).
```

Because M31 is 3 mod 4, every `q_i^2+1` is nonzero. This proves the q
randomness block is universally full rank, not merely full rank on one
fixture. Generated natural-basis constants, their fingerprint, and an
independent production-abscissa identity walk are required in the parser
freeze.

The current exact replays are:

```text
masked zerocheck                         1080 / 1080 M31
baseline atomic PCS                       712 / 780 M31
conditioned profile-21 PCS                780 / 780 M31
switch variables / observations / kernel    70 / 52 / 18 QM31
q randomness and q co-opening               16 / 16 QM31
U one-time-pad                               35 / 35 QM31
```

This proves the fixed-schedule affine field view. It does not, by itself,
simulate Merkle roots or Fiat--Shamir conditioning.

## Selected direct binding and transcript

The selected verifier discloses the 35 coefficients of U and evaluates them
literally at all q16 positions with the four-query fused QM31-by-M31 kernel.
At every query it checks

```text
Enc(U)(q) = F(q) + delta X(q)
          = W1(q) - Fold_alpha0(W0)(q).
```

The no-direct attached-function construction and the eight-round
batch-evaluation sumcheck are rejected. The latter measured 39.7K CU more
than the literal direct check. There is no production U tree.

Literal q binding is necessary but not sufficient. The current switch
diagnostic absorbs `tX,muF` computed under a power-vector target. Production
needs the different covector produced by the complete round-zero relation.
Production serializes U in logical coordinates and adds the exact check
`L(U_message)=muF+delta*tX`. The frozen `phi(U)` is used for the full relation
injection and source-code evaluation. If the source word equality is false, the source
MCA/q event catches it. If it is true, any nonzero pre-delta target-error pair
has at most one nonzero-delta root. This uses the existing degree-one ledger
event and needs no extra PCS. No parser API may treat the two fields as
trusted, and no final CU total may omit the combo check.

The causal order is frozen:

1. settle the external zerocheck and main early commitments;
2. commit the shared C2/X/F root;
3. derive the source covector from the authenticated round-zero relation,
   compute and absorb only `tX` and `muF`;
4. check and absorb source pre-delta g38;
5. sample nonzero delta, disclose logical U, commit translated W1, and inject
   full `phi(U)` into the existing first-later relation;
6. perform the ordinary later OOD/fold rounds, commit W2 and W3, bind the
   final polynomial, and check final g38;
7. sample 16 distinct queries; and
8. authenticate main and X/F openings and enforce both literal equalities.

There is no profile-21 beta cross-equation and no serialized or absorbed
virtual-W0 scalar: the isolated beta values lacked an authenticated base-fold
operand and are omitted. The authenticated W0 contribution is consumed only
through the unchanged round-zero relation, the translated-W1 commitment and
the direct q equalities. Main pre-gamma work is also g38. A root, target,
delta, final-work, or q
sample moved earlier than its dependency is a transcript failure. Every such
swap has a dedicated negative tooth.

## Private-Merkle wire

Affine masks hide the opened field values. Separately, every logical leaf in
every selected tree has a private 32-byte salt derived from an independent,
domain-separated leaf-salt seed and a durably burned attempt nonce:

```text
leaf = SHA256(leaf-domain || tree-tag || fixed-width-value || salt).
```

This is a computational bounded-query ROM construction, not statistical
HVZK and not “Merkle salting alone.” The selected five-tree inventory is:

| tree | logical leaves |
| --- | ---: |
| C1 | 131,072 |
| shared C2/XF | 131,072 |
| translated W1 | 32,768 |
| W2 | 8,192 |
| W3 | 2,048 |
| total | 305,152 |

The actual q16 schedule opens 16 distinct leaves in each tree, so exactly 80
salts, or 2,560 bytes, are serialized. The leaf-hash micro A/B conservatively
books zero CU for salt hashing. Sharing X/F into the C2 root widens 16 leaf
hashes by 128 bytes and costs 1,027 CU, while deleting the separate X/F tree
saves 31,930 CU. The exact overlap-safe net saving is 30,903 CU.

Production requires distinct field-mask and leaf-salt PRG domains, OS entropy,
a burned nonce reserved before derivation, no retry transcript leakage, and
zeroization. Fixture entropy and unmined work bypasses are diagnostics only.

## Soundness ledger

At rate 1/512, q16, the selected literal source binding justifies separate
dimension-35 source MCA and source-query events. With g38 at main pre-gamma,
source pre-delta, and final pre-q, the conservative event union is
107.2883541461 bits. After the factor-33 loss it is
102.2439600267 bits; a factor-40 sensitivity is 101.9664260512 bits.

This is Johnson-proven arithmetic, not a capacity conjecture. It is still not
a complete production claim until the exact parser/equations and mined work
are integrated. The machine-readable source is
`results/stage2/profile21_soundness_hvzk_audit.json`.

## Atomic mutation and CU gate

The exact profile-20 verifier plus atomic transition is already measured:

| path | exact CU |
| --- | ---: |
| program-owned zero marker | 1,189,180 |
| canonical System-owned PDA creation | 1,191,513 |

Before discovering the target-binding seam, the isolated literal switch
increment was `246,560 - 31,679 = 214,881 CU`. After the exact shared-root
saving, the provisional arithmetic was:

```text
program-owned: 1,189,180 + 214,881 - 30,903 = 1,373,158 CU
System-owned:  1,191,513 + 214,881 - 30,903 = 1,375,491 CU
```

This remains provisional: neither formula includes the production target
combo dot/check. The harder bridge has 24,509 CU of arithmetic room. It is not margin because
the parser, salted leaf wire, relation splice, changed transcript, production
work predicates and mutation wrapper have not yet been measured as one
instruction.

Append-only tag 50 is the read-only candidate integration boundary. Tags 51
and 52 are reserved for the production and local unmined atomic mutation
wrappers respectively. Default builds remain fail-closed. A
diagnostic-unmined feature may bypass only work
predicates for measurement; it must execute and absorb every work witness and
must never expose a writable mutation path. The production feature has no
bypass and must reject the unmined fixture before any CPI or write.

## Acceptance gates

Tag 50 may become the production path only when one frozen proof passes all of
the following:

1. literal end-to-end SBF measurement below 1,400,000 CU on the canonical
   System-owned marker path;
2. exact phase markers whose sum reconciles to the total, with no naive
   cross-artifact addition;
3. all parser, transcript-order, source-basis, direct-U, OOD, fold, Merkle,
   zerocheck, copy, padding, lambda, corruption, rollback, duplicate, and race
   teeth;
4. the production target-combo equation using the real covector and logical U,
   with `phi(U)` injected into the full relation and its soundness reduction,
   privacy effect and CU included;
5. production g38 witnesses at all three frozen positions;
6. all-schedule affine containment or the reviewed witness-independent
   `Good(schedule)` availability policy;
7. the private-Merkle/Fiat--Shamir EPRO simulator and bounded-query privacy
   ledger covering proof bytes, logs, retries and account images; and
8. real OS entropy, durable nonce burning, retry suppression and zeroization.

Until then, tag 50 and the complete shielded-spend claim remain fail-closed.

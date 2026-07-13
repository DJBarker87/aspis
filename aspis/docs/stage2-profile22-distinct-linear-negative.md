# Profile-22 distinct-linear zero-width probe: negative evidence

Date: 2026-07-13

## Outcome

Changing only the public dense-linear factor family on the existing 27 mask
sources does not close Profile 22.

The strongest control, distinct families with the old
`1 + L_family^26` G shape, repairs the ordinary exact raw-quotiented
sumcheck rank to `1080/1080`.  It still leaves the new literal direct-sum
guard red:

```text
mask view       4036
physical target 4040  (not contained)
legal target    4040  (not contained)
```

Its exact root-neutral/D=0 sumcheck image is only `1072/1080`.  Therefore it
does not remove the one-coordinate tail/native-X obligation either.

Replacing G by the missing restricted-line degree 23 is worse on the frozen
schedule: ordinary sumcheck rank is `1069/1080`, the mask view is `4025`, the
physical target is `4032`, and the legal target is `4040`.

This is a host-only negative result.  No production factor, commitment leaf,
proof byte, generator width, Fiat--Shamir position, verifier predicate, or
layout fingerprint changed.

## Exact frozen object

- proof: `results/stage2/proofs/atomic_state_only_profile22_v3_unmined.bin`
- statement digest:
  `52e96f99756fe8fd2d8b7a700019b143d7eb549af1bf1ae987e99a75cadcd4c9`
- query count: 16
- queries:
  `[88314,41687,47121,93656,480,21886,42281,106043,59427,89961,1516,23076,42616,79414,55632,92200]`
- source inventory: 16 semantic M31 lanes, 10 mask-only M31 lanes,
  one QM31 G lane
- raw-opening minor rank: `2244` in every completed replay
- generator width and gamma positions: frozen

## Factor family construction

The host mirror uses the production dense family formula

```text
L_f(z) = sum_v [3 + 22v + f(17 + 8v)] z_v.
```

The 26 M31 lanes retain the frozen exponents and tower rotations:

```text
semantic: 0,2,4,6,8,10,12,14,16,18,20,22,24,26,13,25
mask-only: 1,3,5,7,9,11,15,17,19,21
```

Three predeclared bijections from lanes `j=0..26` to families `1..=27` were
tested, with no subset search:

1. `lane_plus_one`: `f(j)=j+1`;
2. `affine_7j_plus_3_mod_27`: `f(j)=1+((7j+3) mod 27)`;
3. `reverse_27_minus_j`: `f(j)=27-j`.

Two G factors were compared:

- `G=L_f^23`, which makes the restricted-line degree multiset exactly
  `0..=26`;
- `G=1+L_f^26`, which retains the historical G shape and duplicates degree
  26 while using a distinct family.

All bounded family slopes are nonzero in every round.  This removes the
known same-family affine-offset collision as an explanation, but it does not
make the coupled source image surjective.

## Exact ranks

| assignment | G factor | raw | ordinary SC | mask view | physical augmented | physical contained | legal augmented | legal contained | joint PCS |
|---|---:|---:|---:|---:|---:|---|---:|---|---:|
| lane plus one | `L^23` | 2244 | 1069/1080 | 4025 | 4032 | no | 4040 | no | 712/780 |
| affine permutation | `L^23` | 2244 | 1069/1080 | 4025 | 4032 | no | 4040 | no | 712/780 |
| reverse | `L^23` | 2244 | 1069/1080 | 4025 | 4032 | no | 4040 | no | 712/780 |
| lane plus one | `1+L^26` | 2244 | 1080/1080 | 4036 | 4040 | no | 4040 | no | 712/780 |
| affine permutation | `1+L^26` | 2244 | 1080/1080 | 4036 | 4040 | no | 4040 | no | 712/780 |
| reverse | `1+L^26` | 2244 | 1080/1080 | 4036 | 4040 | no | 4040 | no | 712/780 |

The three assignment permutations give identical ranks for each G choice.
This is evidence that merely moving these factors among distinct dense
families does not attack the remaining source/direct-sum obstruction.

### Exact D=0/root-neutral controls

The lane-plus-one assignment was replayed through the separate exact
root-neutral reduction:

| G factor | mask-only D=0 rank | total D=0 rank | target | complete |
|---|---:|---:|---:|---|
| `L^23` | 884 | 1061 | 1080 | no |
| `1+L^26` | 976 | 1072 | 1080 | no |

The other assignments were not replayed after both ordinary assignment
families produced identical ranks and the predeclared stop rule fired.

## Stop rule and deliberately unrun scans

The frozen schedule is a necessary test.  Once all degree-23 variants were
sumcheck-deficient and all degree-26 variants retained the literal
`4036 -> 4040` deficit, further schedule scans were stopped.

Accordingly, affine-degenerate, terminal-certificate, Boolean-z,
consecutive-q16, and same-coset-q16 replays were not run for this candidate.
The ordered shared-family-to-distinct prefix scan was also not run.  This is
not a theorem that every prefix or schedule has the same rank; it is a
bounded engineering stop after the candidate failed the frozen necessary
conditions.

## CU and theorem consequences

No verifier CU delta is claimed.  The predeclared condition for costing the
distinct evaluator was elimination of the known deficits with zero added
lanes.  No tested assignment satisfies that condition.

Had a factor schedule passed these gates, production adoption would still
have required an all-parser-valid-schedule, source-aware containment theorem
for the exact raw/sumcheck/PCS map, including the D=0 branch.  Finite rank
replays cannot supply that theorem.  The production factor fingerprint and
soundness ledger would then need to be re-pinned, even though commitment
width and the PCS generator width would remain unchanged.

## Reproduction

```bash
NO_DNA=1 cargo test -q -p aspis-prover \
  --example profile22_distinct_linear_probe \
  deterministic_assignments_are_bijections -- --nocapture

NO_DNA=1 cargo run --release -q -p aspis-prover \
  --example profile22_distinct_linear_probe -- \
  actual lane g23 26 both

NO_DNA=1 cargo run --release -q -p aspis-prover \
  --example profile22_distinct_linear_probe -- \
  actual lane g26 26 both
```

Replace `lane` by `affine` or `reverse`, and use view `containment`, to
replay the remaining completed matrix entries.

# Profile-21 one-variable affine-slice closure

Date: 2026-07-13

Status: **red.** Adding one Boolean message variable and masking with a single
affine kernel `(s-c)R` does not contain the complete same-statement view. This
is a host-only diagnostic and enables no production path.

## Construction and exact result

For each logical coefficient, the statement is duplicated with physical pair

```text
D = (1, 1).
```

The rank diagnostic can evaluate the inserted variable at a fixed `c in
QM31`, so the
slice covector is

```text
L_c = (1-c, c).
```

The fresh direction uses

```text
K_c = (-c, 1-c),
L_c K_c = (1-c)(-c) + c(1-c) = 0.
```

The implementation multiplies the pair by `c` in QM31 before serializing the
result into `[1,i,u,iu]` M31 coordinates. C1 remains an M31-valued duplicated
lane. Thus the extension-field control is not an accidental coordinate-wise
base-field approximation.

At the canonical inserted coordinate `b=0`, all three independent controls
give the same ranks:

| slice | SC | G raw | affine raw kernel | baseline | +G | +G+H | +semantic/legal |
|---|---:|---:|---:|---:|---:|---:|---:|
| `c=2` | 1080 | 268 | 4096 | 712 | 808 | 808 | 812 |
| `c=3` | 1080 | 268 | 4096 | 712 | 808 | 808 | 812 |
| `c=u` | 1080 | 268 | 4096 | 712 | 808 | 808 | 812 |

The extension control is `u=[0,0,1,0]`, so it is outside M31. It is a rank
stress test only, not a promotable protocol parameter. Without explicitly
enforcing the duplicate-lift subcode, restricting arbitrary M31 C1
coefficients at `c` outside M31 produces a QM31-valued logical word and no
longer reduces to the original M31 witness statement. Production candidates
therefore keep every slice coordinate in M31. In every tested case
the four missing pivots are exactly `1084..1087`. H adds no direction after G;
the H, semantic and legal-minor fingerprints are invariant across all three
controls.

## Why changing `c` cannot repair the deficit

The joint PCS coordinate layout has 268 serialized H-raw coordinates followed
by the PCS tail. For q16 the tail begins with 192 later openings and eight OOD
values, followed by four seven-coefficient relation polynomials. Hence

```text
268 + 4*(192 + 8 + 4) = 1084.
```

Pivots `1084..1087` are therefore the four M31 coordinates of `c4` in the
first relation polynomial. Its boundary equation is

```text
B4(h) = 4(c0 + c4).
```

Condition on the authenticated raw values and the two OOD values. Every fresh
`K_c` direction has zero initial claim because `L_c K_c=0`; after subtracting
the conditioned OOD contribution, its first-round boundary carry is also
zero. G and H can differ only by nonzero fixed batching scalars at this point,
which is why their conditioned tail images coincide and H adds rank zero.

The conservative semantic perturbation instead leaves one unrestricted QM31
boundary-carry direction. Once the already-covered `c0` coordinate is
eliminated, that direction appears precisely as the serialized `c4` pivots
`1084..1087`. The boundary functional is therefore a separating functional:
it vanishes on every member of the one-variable affine kernel family for any
`c`. The `c=2` and `c=3` controls cover the sound base-field scope; `c=u`
confirms that merely rotating into the larger tower field does not repair the
rank. The functional is nonzero on the missing semantic
direction. Rotating `c` changes the chosen kernel basis but cannot change this
separation.

This algebraic obstruction, together with the base-field and genuine-QM31
controls, closes the one-variable family. A q18 replay cannot turn a failed
q16 complete-view containment into containment and is not credited.

## Reproduction and evidence

The exact implementation is
`crates/aspis-prover/src/state_only_hiding_rank/state_only_affine_slice_rank.rs`.
The checkpointable runner is
`crates/aspis-prover/examples/profile21_affine_slice_lift_rank.rs`. Compact
evidence, including fingerprints and guards, is frozen in
`results/stage2/profile21_one_variable_affine_closure.json`.

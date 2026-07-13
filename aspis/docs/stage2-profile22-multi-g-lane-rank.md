# Profile 22 multi-G lane fallback rank probe

Date: 2026-07-13

Status: **host-only structural fallback; exact selected-schedule ranks green at
26 additional lanes; production cost screen decisively red.**  No proof wire,
transcript tag, verifier, factor fingerprint, or production acceptance path is
changed.  This note makes no soundness or HVZK claim.

## Bounded object

The host rank diagnostic now accepts an explicit list of at most 27 additional
full-domain QM31 mask lanes.  Each lane has:

- its own raw q16 and three-point opening block;
- an explicit zerocheck factor of degree at most 26; and
- the next consecutive generator coefficient, beginning at `gamma^28` after
  production H and G.

The implementation records the production-width masked-sumcheck rank and the
rank after every lane prefix.  The complete conservative physical and legal
containment replay runs only when the final prefix reaches 1,080.  This is
diagnostic algebra only; serializers and the verifier remain untouched.

The search was deliberately finite.  It did not enumerate subsets.  Three
16-lane screens were fixed before their respective runs:

1. `1 + L_f^26` for `f=1..15,17`;
2. `L_17^e` for `e=0..15`; and
3. the diagonal `L_f^e` for the preceding family/exponent order.

The only extension was the algebraically complete, still finite power basis
`L_17^e` for every allowed `e=0..26`.  No further family or combinatorial
search was performed.

## Exact affine-degenerate ranks

The schedule is the already frozen nonzero-gamma counterexample

```text
z = [-(32+i)/9, 1, 1, 1, 1, 1, 0, 1, i, u].
```

The family-only degree-26 screen saturates:

```text
lanes   0    1    2    3    4    5    6    7..16
rank  916  928  940  952  964  976  980      980
```

The fixed-family degree screen is:

```text
lane count  0,   1,   2,   3,   4,   5,   6,   7,   8,   9,
rank       916, 922, 928, 934, 940, 946, 952, 958, 964, 970,

lane count 10,  11,  12,  13,  14,  15,  16,  17,  18,  19,
rank       976, 982, 988, 996,1004,1010,1016,1022,1028,1034,

lane count 20,  21,  22,  23,  24,  25,  26,  27
rank      1040,1046,1052,1060,1068,1076,1080,1080.
```

The diagonal screen through lane 16 has the same prefix ranks as the
fixed-family degree screen.  Thus the first successful prefix in the complete
ordered degree family is exactly 26 lanes, factors `L_17^0..L_17^25`, at
generator exponents `gamma^28..gamma^53`.

The exact 26-lane affine replay reports:

```text
masked sumcheck                  1080 / 1080 M31
selected PCS image                712 M31
declared ambient PCS              780 M31
physical augmented image          712 M31
legal-sumcheck augmented image    712 M31
physical contained               true
legal contained                  true
```

The exact frozen-schedule replay has rank 1,080 at prefix zero and remains
1,080 for all 26 added prefixes.  It reports the same `712/780`, physical
`712`, legal `712`, and both containment booleans true.

These are exact M31 ranks for two schedules.  They do not prove an
all-schedule theorem, code proximity, MCA, fold/list commutation, or a
production masking construction.

## Wire and cost screen

If the 26 lanes were hypothetically placed in the existing shared C2 tree,
the direct byte geometry would be:

```text
C2 value width                         128 -> 1,792 bytes
q16 opened values per lane             16*4*16 = 1,024 bytes
three claimed evaluations per lane     3*16    =    48 bytes
increment per lane                                  1,072 bytes
26-lane proof increment                            27,872 bytes
current profile-22 proof                56,686 -> 84,558 bytes
outer generator width                        28 -> 54 lanes
```

This assumes one shared root, the same 16 leaf salts and frontier, and one
unchanged masked-sumcheck transcript.  Any separate roots, targets, or work
records make it larger.  The wider generator also changes the batching
numerator and transcript/profile fingerprint; its soundness ledger and MCA
instantiation would have to be recompiled.  No such recompilation is claimed
here.

The prior measured screening anchors are:

```text
System-create total                         1,169,714 CU
exact recorded headroom                       230,286 CU
planning headroom used in this task        approximately 232,000 CU
entire fused three-lane q16 helper kernel       60,968 CU
128-byte shared-C2 widening over q16             1,027 CU
entire current parser                            1,832 CU
```

Even an optimistic amortized arithmetic screen charges only one third of the
entire three-lane kernel per lane and no terminal-factor reserve:

```text
ceil(26 * 60,968 / 3) + 13 * 1,027 + 1,832
= 528,390 + 13,351 + 1,832
= 543,573 CU.
```

That already exceeds 232K by 311,573 CU (and the exact 230,286 headroom by
313,287 CU).  It is not a measured lower bound, merely a deliberately favorable
screen.

Using the conservative convention already applied to the one-lane liveness
bridge—charge the entire three-lane kernel, entire parser, and a 5,000-CU
handling reserve for every added lane—gives:

```text
26 * 60,968                          = 1,585,168 CU
13 * 1,027 shared-leaf widening     =    13,351 CU
26 * 1,832 parser charge            =    47,632 CU
26 * 5,000 handling reserve         =   130,000 CU
total incremental screen            = 1,776,151 CU
projected System-create total        = 2,945,865 CU
```

This exceeds the 232K planning headroom by 1,544,151 CU.  No on-chain
integration was built or measured, but both screens are sufficiently far
above the cap to retire this 26-lane shape as a one-transaction fallback.

## Commands

```sh
NO_DNA=1 cargo build --release -q -p aspis-prover \
  --example state_only_hiding_rank_gate

# Complete bounded degree scan on the affine-degenerate schedule.
NO_DNA=1 target/release/examples/state_only_hiding_rank_gate \
  results/stage2/proofs/atomic_state_only_profile22_v3_unmined.bin \
  52e96f99756fe8fd2d8b7a700019b143d7eb549af1bf1ae987e99a75cadcd4c9 \
  atomic-multi-g-powers17-all-bad-affine

# Exact minimum-prefix affine replay.
NO_DNA=1 target/release/examples/state_only_hiding_rank_gate \
  results/stage2/proofs/atomic_state_only_profile22_v3_unmined.bin \
  52e96f99756fe8fd2d8b7a700019b143d7eb549af1bf1ae987e99a75cadcd4c9 \
  atomic-multi-g-powers17-26-bad-affine

# Same 26 factors on the frozen schedule.
NO_DNA=1 target/release/examples/state_only_hiding_rank_gate \
  results/stage2/proofs/atomic_state_only_profile22_v3_unmined.bin \
  52e96f99756fe8fd2d8b7a700019b143d7eb549af1bf1ae987e99a75cadcd4c9 \
  atomic-multi-g-powers17-26
```

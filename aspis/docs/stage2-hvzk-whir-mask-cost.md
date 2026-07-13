# Upstream HVZK-WHIR mask cost mapped to state-only q29

Status: isolated verifier model and SBF probe only. Nothing in this note is a
production hiding integration or a circle-HVZK theorem.

## Pinned upstream object

The source audited is Plonky3 commit
`6b6a3b4d40fca2187d368c9dc1fca417c84ae8c3`:

- `whir/src/pcs/zk/config.rs` derives the oracle randomness, mask-code shapes,
  chronological groups, and `mask_queries`;
- `whir/src/pcs/zk/verifier/mod.rs` fixes the order sumcheck commitment,
  code-switch commitment, OOD answers, queries, and the next sumcheck;
- `whir/src/pcs/zk/code_switch.rs` defines the switch-mask covector;
- `whir/src/pcs/zk/base_case/verifier.rs` verifies the target identity, source
  spot checks, and paired carried/fresh mask spot checks.

With four arity-four fold batches there are three code switches. The exact
internal chronological group widths are

```text
[2, 1, 2, 1, 2, 1, 2]
```

and their sum is 11 mask codewords. The four width-two groups are PCS-internal
sumcheck masks. The three width-one groups are code-switch masks.

Aspis has two distinct sumchecks which must not be conflated:

- the PCS-internal relation has individual degree six, so a generalized
  upstream mask needs `ell_zk >= 7`;
- the external state-only zerocheck has individual degree 27, so its separate
  ten-mask group needs `ell_zk >= 28`.

For q29 source randomness and two private OOD answers, each switch-mask
message has length `29 + 2 = 31`.

## Spot-check soundness counts

The upstream configuration does not use the raw Reed--Solomon root count. It
uses `SecurityAssumption::queries` with the selected proximity regime and
three union bits for its eight base-case branches. Adding the external
zerocheck group raises the whole-system branch count to nine and therefore
four union bits. The resulting integer counts happen to be unchanged from a
103-bit target in the rows below.

For a mask inverse-rate exponent `r`, the proven Johnson agreement used by the
upstream code is

```text
sqrt(2^-r) * 1.05,
```

so one query contributes `r/2 - log2(1.05)` bits. At 104 branch-unioned target
bits the counts are:

| mask rate | conditional root count | upstream Johnson count |
|---|---:|---:|
| 1/16 | 26 | 54 |
| 1/32 | 21 | 43 |
| 1/64 | 18 | 36 |
| 1/256 | 13 | 27 |

The root column is not a malicious-prover theorem for the upstream verifier.
A Merkle root authenticates an arbitrary word; it does not establish that the
word is a Reed--Solomon codeword. The raw root count is valid only if a
separate codeword-validity invariant is proved. The Johnson column is the
configuration's conservative proven-regime count.

## Timing-safe batching candidate

The measured candidate makes only these transcript-order changes:

1. precommit the challenge-independent internal sumcheck masks and external
   zerocheck masks in one common padded group;
2. keep all three switch masks sequential, because their messages contain
   randomness folded at earlier challenges;
3. group the fresh base-case blinds after all carried groups exist;
4. after all roots and all coefficient reveals are bound, sample a fresh
   `eta`, then derive the shared mask-query positions;
5. check one `eta`-linear combination of the 21 mask-code identities per
   position, embedding shorter coefficient vectors with high-degree zeros.

The batching collision term is at most `20 / |QM31|`. It must be added to the
full soundness union. The candidate is algebraically sound for the identity
checks because `eta` is sampled after every identity is fixed and before the
positions are sampled. It is still a protocol change and has not been
integrated.

This reduces mask trees from 16 carried/fresh trees to five: one independent
precommit tree, three sequential switch trees, and one fresh tree. The fresh
main source blind remains a sixth root.

## SBF measurements

Command:

```text
NO_DNA=1 cargo run --release -p aspis-xtask -- stage2-hvzk-whir-mask-probe
```

Artifact: `results/stage2/hvzk_whir_mask_probe.json`. Wire tag 41 is a
no-account, measurement-only instruction. It cannot authorize state.

The CU totals are overlap-subtracted isolated models:

```text
control
+ (Merkle phase - control)
+ (spot-check arithmetic - control)
+ (target identity - control)
+ (transcript phase - control).
```

The spot-check phase measures one query and extrapolates by the exact loop
count. The Merkle phase measures one tree of each exact width/depth and
reconciles the multiplicities. These are executable SBF primitive costs, not
an integrated production-verifier total.

| mask rate | regime | q | upstream scalar CU | timing-batched CU | timing-batched bytes |
|---|---|---:|---:|---:|---:|
| 1/16 | conditional root | 26 | 11,408,374 | 2,223,294 | 63,872 |
| 1/16 | Johnson proven | 54 | 36,148,890 | 4,651,814 | 126,656 |
| 1/32 | conditional root | 21 | 8,424,970 | 1,877,432 | 60,752 |
| 1/32 | Johnson proven | 43 | 24,968,496 | 3,676,271 | 117,168 |
| 1/64 | conditional root | 18 | 6,865,390 | 1,679,589 | 59,488 |
| 1/64 | Johnson proven | 36 | 18,929,152 | 3,093,302 | 108,512 |
| 1/256 | conditional root | 13 | 4,561,896 | 1,353,636 | 53,328 |
| 1/256 | Johnson proven | 27 | 12,354,841 | 2,389,418 | 94,000 |

Even the conditional 1/256 root row consumes 1,353,636 CU before the new
source-side work. It is therefore not a path to a complete 1.4M-CU verifier.

## Dedicated mask-query PoW

A dedicated nonce can be placed after `eta` and all reveals but before the
mask positions. Verification adds one measured hash, 138 CU, and eight proof
bytes. Honest work is `2^g` expected trials. Johnson-proven timing-batched
results are:

| mask rate | PoW | q | mask verifier CU | incremental bytes |
|---|---:|---:|---:|---:|
| 1/16 | 20 | 44 | 3,720,867 | 106,664 |
| 1/16 | 40 | 34 | 2,870,250 | 86,664 |
| 1/32 | 20 | 35 | 2,987,436 | 99,352 |
| 1/32 | 40 | 27 | 2,321,081 | 72,088 |
| 1/64 | 20 | 29 | 2,504,978 | 86,104 |
| 1/64 | 40 | 22 | 1,971,731 | 70,088 |
| 1/256 | 20 | 22 | 2,004,711 | 79,688 |
| 1/256 | 40 | 17 | 1,634,357 | 64,888 |

Thus a 40-bit dedicated grind plus a 1/256 mask code still leaves the mask
verifier alone above the transaction cap.

## Source-rate repair

Appending 29 private coefficients changes the actual source-code dimensions.
The current leaf domains do not preserve rate 1/32:

```text
dimensions       [285, 93, 45, 33]
current domains  [8192, 2048, 512, 128]
```

The candidate padded domains are:

```text
[16384, 4096, 2048, 2048]
```

Their exact rates are approximately
`[0.017395, 0.022705, 0.021973, 0.016113]`, all below 1/32. This restores the
rate premise needed by the q29 Johnson calculation. It does not replace the
round-by-round work and union ledger.

The isolated source-side price is:

| component | CU delta |
|---|---:|
| larger source Merkle frontiers | 38,207 |
| re-encode the 33-coefficient final-source reveal at 29 positions | 392,979 |
| authenticate the fresh-main mask tree | 21,626 |
| total new source-side work | 452,812 |

The larger source frontiers add 12,032 proof bytes. Existing source leaf bytes
and already-required source queries are not double-counted.

## Ruling

The upstream HVZK-WHIR construction is a useful correctness reference, but a
literal or lightly batched port is not a one-transaction hiding solution for
Aspis. The best proven row measured here is 1/256 plus a dedicated 40-bit
grind:

```text
1,634,357 mask CU + 452,812 source-side CU = 2,087,169 CU
```

before the existing statement terminal, relation, ordinary query arithmetic,
or atomic mutation. The raw-root row is both conditional and, after adding
the source side, also above 1.4M.

This closes the direct-port avenue as a fit optimization. Any viable upstream-
style replacement needs another structural theorem/algorithm that removes the
coefficient-reveal re-encoding work, not another Merkle or field microkernel.

## Direct CM31 multiplicative-subgroup RS decision row

A separate theorem-surface option is to replace the circle source word with an
ordinary multiplicative-subgroup Reed--Solomon word over CM31. At state-only
width 16 and q29, each source leaf then opens four CM31 slots per column rather
than four M31 slots:

| object | circle M31 | direct CM31 RS |
|---|---:|---:|
| layer-zero C1 leaf bytes | 256 | 512 |
| opened leaf-byte delta at q29 | - | +7,424 |
| conservative layer-zero arithmetic proxy | - | +95,470 CU |
| SHA leaf-hash proxy | - | +3,693 CU |
| combined verifier delta proxy | - | +99,163 CU |

The arithmetic number is the measured q36 width17-to-width33 delta from
`layer0_dot_width_probe.json`, scaled only by `29/36`. It deliberately prices
the second CM31 limb as 16 additional independent M31 columns. A dedicated
mixed `QM31 x CM31` kernel should improve that conservative proxy. The hash
number derives four additional SHA-256 compression blocks per q29 leaf from
the measured 382-CU twelve-block leaf-hash delta in
`m31_circle_basis_probe.json`.

Ordinary subgroup RS is the code family used by upstream Hiding-WHIR, so this
option has a materially cleaner theorem path than circle code-switching. That
is not yet a transfer proof: the exact QM31/CM31 subgroup, interleaved source
encoding, code-switch diagram, and state-only adapter still need to be pinned.
The row is a decision proxy, not a soundness or integrated-CU claim.

## Minimal one-switch repair

The rank analysis leaves a narrower candidate than the full 21-mask port: one
width-one code-switch mask only. Its frozen shape is:

```text
message length       31 = q29 source randomness + two OOD pads
encoding randomness  29
mask domain           2048 (rate parameter 1/32, depth 11)
queries               29
```

The main q29 positions and existing g36 work can be reused only if the carried
root, fresh root, 60-coefficient reveal, and target claim are all fixed before
that nonce and the shared position squeeze. Under that ordering,

```text
29 * (5/2 - log2(1.05)) + 36 = 106.458709491 bits,
```

which clears a 104-bit branch-unioned target in the Johnson regime. This is a
positioning condition, not permission to credit a nonce sampled earlier.

Exact tag-41 costs are:

| one-switch component | CU |
|---|---:|
| two carried/fresh Merkle trees | 85,237 |
| ordinary scalar spot checks | 720,057 |
| specialized single-word spot checks | 659,669 |
| target identity | 18,323 incremental |
| transcript | 2,431 incremental |
| ordinary reconciled total | 825,307 |
| specialized reconciled total | 764,919 |

The standalone proof increment is 17,136 bytes. The isolated switch identity
does not need the full Construction-7.2 fresh-main/source identity; adding it
would cost another 392,979 CU for source re-encoding alone.

There is also an explicit shared-root lower bound. If the carried lane is
packed into an already-required later-fold root at the same causal commitment
point, and the fresh OTP lane shares a base root committed before gamma, the
paths and roots are not incremental. Adding one 16-byte lane to a 64-byte leaf
costs 233 CU over all q29 leaf hashes. Keeping both lane deltas, all identity
arithmetic, and reveal transcript work gives:

```text
680,315 CU and 1,904 proof bytes.
```

That row is valid only when both existing trees expose the required mask-domain
rows and the commitment order is unchanged. If either root is sampled at the
wrong time or has an incompatible domain, the standalone 764,919-CU row is
the applicable measurement.

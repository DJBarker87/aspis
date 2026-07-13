# Atomic profile-20 mutation closure

Date: 2026-07-13

Status: **the exact account-transition closure is implemented and measured on
both marker paths. Default tag 47 remains fail-closed because profile-20
complete-view hiding is not closed.**

The committed 56,044-byte profile-20 proof is intentionally unmined and is
used only in a nondefault local-validator diagnostic binary. Its SHA-256 is
`fdd1097f702b411b6bcd26d0e195322d7683ff93ec4cb70828b9459fe7cef007`.
The default SBF build exposes no unmined mutation bypass:

- append-only tag 47 has no diagnostic flag and returns
  `ATOMIC_ERROR_VERIFIER_NOT_INTEGRATED` in default builds;
- its nondefault `profile20-mutation-candidate` arm calls the production PoW
  verifier and rejects the unmined fixture before any CPI or write;
- append-only tag 48 is compiled only with
  `diagnostic-unmined-mutation` and exists solely to measure the exact kernel
  on a local validator.

## Literal measurements

Both results are one-instruction simulations with complete marker ledgers.
No segmented or overlap-subtracted number appears in either total.

| bucket | program-owned zero marker | System-owned create |
| --- | ---: | ---: |
| transaction setup | 1,988 | 1,988 |
| account validation | 7,258 | 6,806 |
| statement decode and digest | 894 | 894 |
| exact profile-20 verifier | 1,177,627 | 1,177,627 |
| marker ready / System CPI | 206 | 2,991 |
| mutable-state recheck | 741 | 741 |
| final account copies | 279 | 279 |
| post-marker bookkeeping | 187 | 187 |
| **literal total** | **1,189,180** | **1,191,513** |
| headroom below 1.4M | 210,820 | 208,487 |
| incremental over read-only tag 46 | 9,729 | 12,062 |

The System path is the canonical zero-lamport, empty, System-owned PDA path.
The program signs `create_account`, allocates 72 bytes, assigns ownership, then
reacquires and rechecks both mutable accounts before copying their final
images. The program-owned path begins with the same canonical PDA already
owned by the verifier and exactly zeroed.

## Transition teeth

Both paths pass all of the following:

- corrupt a sumcheck byte, reject, and compare the pool and nullifier account
  images byte-for-byte with the pre-instruction images;
- accept the clean diagnostic proof, increment the pool sequence exactly once,
  replace the anchor, and write the exact pool/nullifier marker tuple;
- retry with the updated anchor and identical nullifier, reject before a
  second proof verification/write, and preserve both post-state images;
- on the System-owned path, submit two differently signed transactions against
  the same writable pool and canonical nullifier PDA and require exactly one
  commit. Solana writable locks serialize the pair; the loser observes stale
  state or the consumed marker.

The transition kernel orders work as:

```text
validate accounts and prestate
derive canonical statement and digest
verify complete proof
create marker PDA if absent
reacquire and recheck pool plus marker
copy marker image
copy pool image
```

No fallible state operation remains after the final images are prepared.
Transaction rollback is an additional outer guarantee; the kernel also keeps
direct host-test mutation atomic.

## Budget consequence

Using the latest fused-switch increment (214,881 CU) and the conservative
overlap-safe shared-X/F saving (30,903 CU), the mutation-inclusive bridge is:

```text
program-owned: 1,189,180 + 214,881 - 30,903 = 1,373,158
System-create:  1,191,513 + 214,881 - 30,903 = 1,375,491
```

These are explicitly non-integrated bridges, leaving 26,842 and 24,509 CU.
The final tag-50/tag-51 literal must replace them because parser, transcript,
and code-generation overlap can move the endpoint. Mutation itself is no
longer an unknown six-figure plank; it is a measured 9.7--12.1K CU increment.
The remaining production gate is the profile-21 complete-view/private-Merkle
splice and its mined PoW, not the account kernel.

Machine-readable artifact:
`results/stage2/atomic_state_only_profile20_mutation.json`.

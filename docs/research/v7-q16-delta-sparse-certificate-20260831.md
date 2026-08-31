# V7 q16 delta sparse-certificate milestone (2026-08-31)

## Scope and base

This milestone repairs the generated cap-203 compact-frontier delta certificate
without changing the recurrence, cap, count, or probability statement.

- branch base: `b3d1fd4ef003c6811281a2f616f71e65a92b778f`
- V6 generator: `tools/generate_v6_compact_frontier_tail.py`
- V7 generator: `tools/generate_v7_compact_frontier_delta.py`
- public V7 module: `AspisFormal.V7CompactFrontierDeltaCertificate`
- expected delta:
  `6915291501979218758486550434503151696943423928716542558271246420848672768`

No V6 generated file or theorem was changed.  The V7 generator remains
untrusted; Lean must kernel-check every generated theorem.

## Why the historical monolith was invalid

The historical 5,227-line V7 delta source assumed that the V6 tail certificate
exported a full recurrence table.  The current V6 certificate deliberately
exports only its exact sparse dependency closure.

The old direct build was stopped after 4:54:17 when process RSS jumped from
about 10.7 GiB to 16,287,832 KiB.  Its buffered output then exposed early
errors that had accumulated while Lean continued elaborating:

- `certificate_1_1_0` existed;
- `AspisV6CompactFrontierTailCertificate.certificate_1_2_2` did not exist;
- later attributes referenced many other nonexistent historical cells; and
- the resulting recurrence goals were unsolved.

A two-line fail-fast Lean probe reproduced the first missing symbol in 2.62s.
Therefore the monolithic run is classified as invalid evidence and must never
be rerun unchanged.

## Sparse symbol boundary

The new generator first scans every generated V6 source and compares the
declarations against the V6 generator's exact dependency closure.  Generation
fails before writing output if those sets differ.

The frozen boundary is:

| Set | Cells |
|---|---:|
| Exact extant V6 sparse inventory | 753 |
| V6 cells actually reused by V7 | 652 |
| New local V7 delta cells | 412 |
| Final V7 cells | 6 (frontiers 204 through 209) |

The generator stops dependency traversal whenever an extant V6 cell is
reached.  Every remaining cell uses the same proved
`frontierCoeff_succ_eq_supported` recurrence as the V6 certificate.  It emits
19 depth aggregators and bounded per-depth chunks; it never emits the old
653-theorem monolith.

The generated manifest records the full reused/local symbol lists, their
SHA-256 surfaces, every generated-source hash, and per-depth chunk bounds.

Preflight commands:

```sh
python3 tools/generate_v6_compact_frontier_tail.py --check \
  AspisFormal/AspisFormal/V6CompactFrontierTailCertificate.lean
python3 tools/generate_v7_compact_frontier_delta.py --check-symbols \
  AspisFormal/AspisFormal/V7CompactFrontierDeltaCertificate.lean
python3 tools/generate_v7_compact_frontier_delta.py --check \
  AspisFormal/AspisFormal/V7CompactFrontierDeltaCertificate.lean
```

Results:

```text
V6 split certificate: PASS (520 generated parts, 753 recurrence cells)
V7 sparse symbol manifest: PASS (412 local, 652 reused V6 symbols)
V7 split delta certificate: PASS (326 generated parts)
```

Key source hashes before commit:

```text
7870de94b2fc531597dcddc639bbd2464fb6c7139d0e0566543113021805100f  tools/generate_v7_compact_frontier_delta.py
b1530375cc72836238787974e515a46937fb3baab9a1edf3372c9efc1ca93caa  AspisFormal/AspisFormal/V7CompactFrontierDeltaCertificate.lean
f82158ba9042a4b1e9bfffcd0a3fcb7ad16bc561b9248b0d431c93064a3b9cfc  AspisFormal/AspisFormal/V7CompactFrontierDeltaCertificate/manifest.json
7b1ecd41f01b35652fe28329b3759549925a382b201538c90d297f5172016f1a  AspisFormal/AspisFormal/V7CompactFrontierDeltaCertificate/Depth00.lean
cc1aa42af5bb6be290a215256605b99f3d46dc7db5487595af4c6a920318b80a  AspisFormal/AspisFormal/V7CompactFrontierDeltaCertificate/Depth01.lean
```

## Focused NUC Depth00/Depth01 gate

Task root:

```text
/home/dombarker/project-offloads/aspis-v7-q16-delta-sparse-b3d1fd4-20260831-r1
```

The first run failed in 0.08s because the task artifact root shadowed the
package cache.  No theorem was evaluated.  The replacement added a task-owned
symlink overlay (994 `.olean`, 993 `.ilean`) while excluding every V7 delta
output.  No shared cache file was changed.

Replacement unit:

```text
aspis-v7-q16-delta-depth01-b3d-r2.service
invocation ca8ca9b1df1b4da4945dd6f4adec55d0
MemoryHigh=10G
MemoryMax=12G
MemorySwapMax=0
```

| Target | Exit | Wall | Max process RSS | Swaps |
|---|---:|---:|---:|---:|
| `Depth00.lean` | 0 | 2.46s | 6,143,248 KiB | 0 |
| `Depth01.lean` | 0 | 2.50s | 6,143,816 KiB | 0 |

Artifact hashes:

```text
69096c5b850f02078ece7e44c32aa7b754a6586d472a3e641490b5439009036b  Depth00.olean
31964b3c11b27d13cf65086b2688fd2f9bdb837abe9d078b918be44e7ad47eea  Depth00.ilean
523ac6cf2bb9498213d5e56081e1db215bb80df994872c0ba1974e334fc37065  Depth01.olean
a94174c9554a0da8e63b3accf7408b30358480b0a423f040e089c103c2b1a877  Depth01.ilean
```

Depth00 and Depth01 are import/re-export modules and introduce no theorem, so
there is no new `#print axioms` surface at this gate.  The first local theorem
is in `Depth02Chunk000`; its focused kernel build is the next gate.  Only after
that theorem and its Depth02 aggregator are green should later depths be
compiled serially.  The final delta sum, V7 compact-frontier certificate, and
q16 count bridge remain pending.

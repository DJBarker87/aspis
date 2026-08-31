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
| Exact V6 sparse-support inventory | 304 |
| V6 support theorems actually reused by V7 | 88 |
| New local V7 delta cells | 412 |
| Final V7 cells | 6 (frontiers 204 through 209) |

The generator stops dependency traversal whenever an extant V6 cell is
reached.  Every remaining cell uses the same proved
`frontierCoeff_succ_eq_supported` recurrence as the V6 certificate.  It emits
19 depth aggregators and bounded per-depth chunks; it never emits the old
653-theorem monolith.

The generated manifest records the full reused/local symbol lists, their
SHA-256 surfaces, every generated-source hash, and per-depth chunk bounds.  It
also requires the exact `support_0_1` through `support_18_16` grid and qualifies
every generated support reference against that 304-theorem inventory.

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
V7 sparse symbol manifest: PASS (412 local, 652 reused V6 cells, 88 reused support theorems)
V7 split delta certificate: PASS (326 generated parts)
```

Key source hashes at this milestone:

```text
f27faff42522a25b84a8032198c3be65ba36d9e2e57a9203020ecc65ce6bf2ad  tools/generate_v7_compact_frontier_delta.py
b1530375cc72836238787974e515a46937fb3baab9a1edf3372c9efc1ca93caa  AspisFormal/AspisFormal/V7CompactFrontierDeltaCertificate.lean
49672277125d43cf06b1f8ee3bae0363028b40b33a1afe7a18995800c224bf5d  AspisFormal/AspisFormal/V7CompactFrontierDeltaCertificate/manifest.json
7b1ecd41f01b35652fe28329b3759549925a382b201538c90d297f5172016f1a  AspisFormal/AspisFormal/V7CompactFrontierDeltaCertificate/Depth00.lean
cc1aa42af5bb6be290a215256605b99f3d46dc7db5487595af4c6a920318b80a  AspisFormal/AspisFormal/V7CompactFrontierDeltaCertificate/Depth01.lean
53ec9b28479cea19bcc3bdb557357eaed86ff11bf4a35120d396f65bcc3fa311  AspisFormal/AspisFormal/V7CompactFrontierDeltaCertificate/Depth02Chunk000.lean
f006083c4392a941d4dcdb432fd62bb0b420beab2c4559b7463f7720cfe796b7  AspisFormal/AspisFormal/V7CompactFrontierDeltaCertificate/Depth02.lean
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
there is no new `#print axioms` surface at this gate.

## Focused Depth02 local-cell gate

The first Depth02 attempt failed fast and usefully.  Unit
`aspis-v7-q16-delta-depth02-b3d-r3.service`, invocation
`6ff9f1af999d4dab915d96c8def1628b`, stopped in 2.54s because the inherited V6
proof text referred to unqualified `support_1_1`.  No Depth02 artifact was
written.  The generator was corrected to derive the exact 304-theorem support
inventory and qualify only references present in it; this is a source change,
not an unchanged rerun.

Replacement unit:

```text
aspis-v7-q16-delta-depth02-b3d-r4.service
invocation 41c2306d64db46cb830eb9e42d99fc36
MemoryHigh=10G
MemoryMax=12G
MemorySwapMax=0
```

| Target | Exit | Wall | Max process RSS | Swaps |
|---|---:|---:|---:|---:|
| `Depth02Chunk000.lean` | 0 | 2.77s | 6,179,716 KiB | 0 |
| `Depth02.lean` | 0 | 2.59s | 6,143,924 KiB | 0 |
| Depth02 axioms probe | 0 | 2.47s | 6,135,180 KiB | 0 |

The unit's cgroup peak was 642.6 MiB and its swap peak was zero.  Process RSS
above includes shared read-only dependency mappings, so both measurements are
reported rather than conflated.

Artifact hashes:

```text
dc5d70c980bd7607cc0974acb42a22a4b6ad2f5d046be48b120637edb1198e33  Depth02Chunk000.olean
3e85e088417a20ddacd04c6de8c89bdeb7c2c79eb5fccb5b49c568e16f9e5dd7  Depth02Chunk000.ilean
14e885d61a9140fedfaac3813a33962b4c76f54d28ca02dfee8261afc423a405  Depth02.olean
f29883d25680a92a52c63f385c54251a2e624802e76f8c953d2d0fd3562924ff  Depth02.ilean
```

The first local theorem reports exactly:

```text
[propext, Classical.choice, Quot.sound]
```

Depth02 is therefore green.  The next legitimate gate is
`Depth03Chunk000.lean`, followed by the Depth03 aggregator only if that chunk
passes.  The final delta sum, V7 compact-frontier certificate, and q16 count
bridge remain pending.

## Focused Depth03 local-cell gate

The Depth03 fail-fast symbol manifest passed before execution.  The bounded
serial unit was:

```text
aspis-v7-q16-delta-depth03-b3d-r5.service
invocation c2edc94b464340c488aa18a0c2eb2362
MemoryHigh=10G
MemoryMax=12G
MemorySwapMax=0
```

| Target | Exit | Wall | Max process RSS | Swaps |
|---|---:|---:|---:|---:|
| `Depth03Chunk000.lean` | 0 | 3.24s | 6,182,576 KiB | 0 |
| `Depth03.lean` | 0 | 2.47s | 6,144,488 KiB | 0 |
| Depth03 axioms probe | 0 | 2.65s | 6,135,932 KiB | 0 |

The cgroup peak was 648.3 MiB with zero swap.  Both local theorems,
`certificate_3_2_0` and `certificate_3_2_1`, report exactly:

```text
[propext, Classical.choice, Quot.sound]
```

Artifact hashes:

```text
5a87a243519de5d9182c8a3eb0c554add78aa9303c50dd6db2f528d9fdfab607  Depth03Chunk000.olean
679b9956c2b7cf26c056d5eb2d1590924f2e418f4c7ddca707c0214dbbcb21dc  Depth03Chunk000.ilean
fe4abfbcd96a3288f5bdee16cb7f3b941cf7e30e69b5665df42e6458889ee9ad  Depth03.olean
6498f9337a212af4e1ed4f003f7936b897edb8320cfe80ec1b8b1ea15c8c7a9d  Depth03.ilean
```

Depth03 is green.  The next legitimate gate is `Depth04Chunk000.lean` then
the Depth04 aggregator only.  No multi-depth or monolithic run has been used.

## Focused Depth04 local-cell gate

The Depth04 symbol manifest passed before the serial run.  The unit was
`aspis-v7-q16-delta-depth04-b3d-r6.service`, invocation
`c5294905ef064344b7cc97a0c89662da`, with `MemoryHigh=10G`, `MemoryMax=12G`,
and `MemorySwapMax=0`.

| Target | Exit | Wall | Max process RSS | Swaps |
|---|---:|---:|---:|---:|
| `Depth04Chunk000.lean` | 0 | 3.24s | 6,185,292 KiB | 0 |
| `Depth04.lean` | 0 | 2.53s | 6,144,740 KiB | 0 |
| Depth04 axioms probe | 0 | 2.51s | 6,136,116 KiB | 0 |

All three local theorems report exactly
`[propext, Classical.choice, Quot.sound]`.

```text
4696cb389a6e4a369695991c9f85869c2cf31ba1e87a2a27086b7bb5bdfa1680  Depth04Chunk000.olean
433b6cc089eb2813c6f47345957ff4d6e728e97ab099c7fa8fe30c5a187d1bdd  Depth04Chunk000.ilean
bfcb6aae860a45c90c1cd0867857695a476f127c3490cbce98fc843e6e9e3a94  Depth04.olean
4fd12fdacb43226b28c2b7ce39b6f59858ded13dcdd9cad01265213c01855083  Depth04.ilean
```

Depth04 is green.  The next legitimate gate is `Depth05Chunk000.lean` then
the Depth05 aggregator only.

## Focused Depth05 local-cell gate

The Depth05 symbol manifest passed before the serial run.  Unit
`aspis-v7-q16-delta-depth05-b3d-r7.service`, invocation
`07535ff117de400aa90ccd60f24999db`, used the same 10G/12G/zero-swap limits.

| Target | Exit | Wall | Max process RSS | Swaps |
|---|---:|---:|---:|---:|
| `Depth05Chunk000.lean` | 0 | 3.54s | 6,189,292 KiB | 0 |
| `Depth05.lean` | 0 | 2.47s | 6,145,252 KiB | 0 |
| Depth05 axioms probe | 0 | 2.47s | 6,137,152 KiB | 0 |

All four local theorems report exactly
`[propext, Classical.choice, Quot.sound]`.

```text
dba608873383867054647c64296da71c1f034881e9156b843e880357a7ebbd64  Depth05Chunk000.olean
d23dbf161f59b3e9d85e56fc3b2c9bed6c51d4477adbdd903fd2a66fbb1e1bfc  Depth05Chunk000.ilean
a7791d2ce6dd94098b42d7e2e999e9e56c971cca2d8475709a419714eda95f79  Depth05.olean
f661ea50cee530fa9d5ca22cfb64347ec607b3d8892c24067ce20ecae86a78be  Depth05.ilean
```

Depth05 is green.  The next legitimate gate is `Depth06Chunk000.lean` then
the Depth06 aggregator only.

## Focused Depth06 local-cell gate

The Depth06 symbol manifest passed before the serial run.  Unit
`aspis-v7-q16-delta-depth06-b3d-r8.service`, invocation
`d2dab58a51204d47810ca185bd801e10`, used the same 10G/12G/zero-swap limits.

| Target | Exit | Wall | Max process RSS | Swaps |
|---|---:|---:|---:|---:|
| `Depth06Chunk000.lean` | 0 | 4.49s | 6,204,016 KiB | 0 |
| `Depth06.lean` | 0 | 2.53s | 6,146,124 KiB | 0 |
| Depth06 axioms probe | 0 | 2.67s | 6,138,208 KiB | 0 |

All seven local theorems report exactly
`[propext, Classical.choice, Quot.sound]`.

```text
fc442e37b117901388e3f2b3597fd8521c409839249619704bef4ced34477dc3  Depth06Chunk000.olean
ee1b778c8b941e80c502a3ce60a98707a6329907d5cde979531b5d66a6d0347b  Depth06Chunk000.ilean
81efc1cdc567cb58efb56eeb8e89be8112bb9bfe248068449c44a1ea620fbed0  Depth06.olean
e2d06fc91afb17370e8e1429731f99a8e43cc5e6b2432ebb13e0d617e401b772  Depth06.ilean
```

Depth06 is green.  Depth07 contains two bounded chunks; the next legitimate
gate is `Depth07Chunk000.lean` only, before any decision about Chunk001 or its
aggregator.

## Focused Depth07 Chunk000 gate

The first narrowed runner, r9, failed before elaboration in 0.03s because it
omitted `cd $SOURCE_FORMAL`; Lean correctly rejected an input outside its root
directory.  It wrote no artifact.  The cwd-corrected r10 unit was
`aspis-v7-q16-delta-depth07-chunk000-b3d-r10.service`, invocation
`c3e2a5a86b0a4a22bbbcc9597db66abc`, under the same 10G/12G/zero-swap limits.

| Target | Exit | Wall | Max process RSS | Swaps |
|---|---:|---:|---:|---:|
| `Depth07Chunk000.lean` | 0 | 5.49s | 6,214,572 KiB | 0 |
| Chunk000 axioms probe | 0 | 2.50s | 6,138,520 KiB | 0 |

All eight Chunk000 theorems report exactly
`[propext, Classical.choice, Quot.sound]`.

```text
3c4d3ccb7f7201819c5401024a432cc8431225b7fd36acceee71c2a01c0ac415  Depth07Chunk000.olean
4599ce5317c4d8cca14974d2483dca7fa50639ce7260f7b27c84a3d9ceea677b  Depth07Chunk000.ilean
```

Chunk000 is independently green.  Chunk001 and the Depth07 aggregator remain
unbuilt.

## Focused Depth07 Chunk001 gate

The independent Chunk001 unit was
`aspis-v7-q16-delta-depth07-chunk001-b3d-r11.service`, invocation
`f57873be2dd241379495e7d76ab0ee4f`, under the same 10G/12G/zero-swap limits.

| Target | Exit | Wall | Max process RSS | Swaps |
|---|---:|---:|---:|---:|
| `Depth07Chunk001.lean` | 0 | 3.33s | 6,191,160 KiB | 0 |
| Chunk001 axioms probe | 0 | 2.48s | 6,138,608 KiB | 0 |

Both Chunk001 theorems report exactly
`[propext, Classical.choice, Quot.sound]`.

```text
39d7dd5be119f34d2719d54e98d3ae1d84fbe6c90c5ba7a00e598b06ba44697f  Depth07Chunk001.olean
72f5694f8cc1f1e882a5c0bdbc4cfd91d1645f79081019fbc9b02d04d3d99d7d  Depth07Chunk001.ilean
```

Both Depth07 chunks are independently green.  The small Depth07 aggregator is
the next gate and has not yet been run.

## Focused Depth07 aggregator gate

After both chunks were independently green, unit
`aspis-v7-q16-delta-depth07-aggregator-b3d-r12.service`, invocation
`cbfa16076d1341ea9db2c28969db2dfb`, built only the aggregator and its axioms
probe under the same 10G/12G/zero-swap limits.

| Target | Exit | Wall | Max process RSS | Swaps |
|---|---:|---:|---:|---:|
| `Depth07.lean` | 0 | 2.49s | 6,147,892 KiB | 0 |
| Depth07 axioms probe | 0 | 2.64s | 6,139,620 KiB | 0 |

All ten re-exported local theorems report exactly
`[propext, Classical.choice, Quot.sound]`.

```text
ad52f0f57b84d4f06173d0490c6ed6407edeb85293c0b532ad7977359d745b2e  Depth07.olean
34001dcd3829dffc6f93eb9c7adacfdec9b422c1cdb3028f50162d8530b18e10  Depth07.ilean
```

Depth07 is fully green.  No Depth08 target was started in this gate.

## Focused Depth08 Chunk000 gate

The frozen manifest describes Depth08 as 12 local cells in three chunks, with
at most eight cells and recurrence cost 89 per chunk.  Only Chunk000 was run.
Unit `aspis-v7-q16-delta-depth08-chunk000-b3d-r13.service`, invocation
`e6aa3893f5294d4cb8aa6b869fdd09d5`, used the same 10G/12G/zero-swap limits.

| Target | Exit | Wall | Max process RSS | Swaps |
|---|---:|---:|---:|---:|
| `Depth08Chunk000.lean` | 0 | 6.33s | 6,223,856 KiB | 0 |
| Chunk000 axioms probe | 0 | 2.49s | 6,140,732 KiB | 0 |

All eight Chunk000 theorems report exactly
`[propext, Classical.choice, Quot.sound]`.

```text
c478c1eb4eabc472e5224cbafcb9aa596d9666a9754a79568979c941428bb344  Depth08Chunk000.olean
f80f165947bc17ae39b7b016d014251c698cb4aac5d119dc0b710c1bbdcff062  Depth08Chunk000.ilean
```

Chunk000 is independently green.  Depth08 Chunk001, Chunk002, and the
aggregator remain unbuilt.

## Focused Depth08 Chunk001 gate

Unit `aspis-v7-q16-delta-depth08-chunk001-b3d-r14.service`, invocation
`12cc9754aa3d49949c4c593d85618b56`, ran only Chunk001 and its axioms probe
under the same 10G/12G/zero-swap limits.

| Target | Exit | Wall | Max process RSS | Swaps |
|---|---:|---:|---:|---:|
| `Depth08Chunk001.lean` | 0 | 3.90s | 6,193,612 KiB | 0 |
| Chunk001 axioms probe | 0 | 2.46s | 6,139,668 KiB | 0 |

Both theorems report exactly `[propext, Classical.choice, Quot.sound]`.

```text
44120bfcd08e758eea3d8725ece29dce13915f5c47e2c9bf9929767c4ab73ca7  Depth08Chunk001.olean
fa0763ad206e6152ac320bfb9515a84ca3d7c86d8d9387236635767a0c851134  Depth08Chunk001.ilean
```

Chunk001 is independently green.  Chunk002 and the Depth08 aggregator remain
unbuilt.

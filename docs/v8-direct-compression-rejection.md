# V8 direct compression rejection

**Decision:** **REJECTED—do not revisit absent a genuinely different
cryptographic proof system.**

The direct V8-A experiment is complete. Ordinary lossless compression does
not reduce the selected V7 proof: the best output in the exhaustive audited
parameter matrix is 30,508 bytes, four bytes larger than the 30,504-byte
input. This closes the direct `Compress(frozen V7)` branch. V8 continues on
the native proof-system track.

## Frozen V7 input

The experiment used the exact production proof that finalized on devnet. It
did not regenerate, remine, reinterpret, or modify the proof.

| Fact | Frozen value |
|---|---:|
| Proof body | 30,504 bytes |
| Formal maximum body | 30,504 bytes |
| Proof SHA-256 | `e8e15ce268447b92ac1344292bc879dcb0bf7534621ce077d8790097975dcecb` |
| Merkle digest | 26 bytes / 208 bits |
| Generic collision level | 104 bits |
| Query count | 16 |
| Query record | 621 bytes |
| C1 values per query | 403 bytes |
| C2 values per query | 186 bytes |
| C2 disclosure | Complete C2 fibre; no omitted-value reconstruction |
| Private salt | 32 bytes |
| Frontier cap / actual frontier | 203 / 203 nodes per tree |
| Compact counter | 4 |
| Work schedule | 35 / 31 / 34 bits |
| Finalized devnet CU | 1,257,959 |
| Headroom below 1.3M | 42,041 CU |

The exact body decomposition is 9,936 fixed packed-field bytes, 52 root
bytes, 24 work-nonce bytes, 9,936 query bytes, and 10,556 frontier bytes:

```text
9,936 + 52 + 24 + (16 * 621) + (2 * 203 * 26) = 30,504
```

This corrects the superseded draft facts of 27-byte digests, 606-byte query
records, omitted C2, and a 30,672-byte maximum. None applies to the selected
V7 wire.

## What the cited `zip` construction means

The audited source is Giacomo Fenzi and Yuwen Zhang, *zip: Reducing Proof
Sizes for Hash-Based SNARGs*, [IACR ePrint 2025/1446](https://eprint.iacr.org/2025/1446),
archive version `20250808:232705` dated 8 August 2025. The source was accessed
on 25 August 2026.

Construction 2.2 is a literal lossless wrapper. For a base prover/verifier
pair `(P0, V0)` it defines:

```text
P(x, w): Compress(P0(x, w))
V(x, z): V0(x, Decompress(z))
```

Its defining condition is
`Decompress(Compress(bytes)) = bytes`. It introduces no new cryptographic
verification layer, field arithmetic, recursion, or hash proof. Acceptance
after decompression is acceptance by the unchanged base verifier. The paper
benchmarks ordinary zstd, zip, and gzip utilities; it explicitly presents
compression as a way to expose serialization inefficiency.

The V8-A experiment therefore did not build a new cryptographic verifier. It
performed an exact lossless round trip and then called the production V7
read-only verifier with every work check enabled.

## Codec matrix

The input's measured byte entropy is **7.993428 bits per byte**, already very
close to the 8-bit maximum. The following matrix exhaustively swept the stated
ordinary-codec parameter ranges:

- Brotli qualities 0–11 and windows 10–24;
- zstd levels 1–22;
- LZ4 levels 1–12;
- gzip levels 1–9;
- xz levels 0–9, both ordinary and extreme;
- bzip2 levels 1–9;
- ZIP's maximum ordinary deflate setting.

| Rank | Codec and best setting | Bytes | Ratio | Change |
|---:|---|---:|---:|---:|
| 1 | Brotli q0, window 15; q1 tied | 30,508 | 100.013113% | +4 |
| 2 | zstd level 1, no checksum | 30,513 | 100.029504% | +9 |
| 3 | LZ4 level 12, no frame CRC | 30,519 | 100.049174% | +15 |
| 4 | Apple gzip level 9, deterministic header | 30,532 | 100.091791% | +28 |
| 5 | xz level 0 | 30,568 | 100.209809% | +64 |
| 6 | ZIP level 9, stripped metadata | 30,626 | 100.399948% | +122 |
| 7 | bzip2 level 9 | 30,975 | 101.544060% | +471 |

The exact primary commands and pinned tool versions were:

```sh
proof=/Users/dominic/ZK-v7/results/spend/v7-devnet-20260825-fullc2/v7-proof.bin

# brotli 1.2.0; exhaustive-matrix best, tied with finalized q1
brotli -q 0 -w 15 -c "$proof" > output.br       # 30,508 bytes
brotli -q 1 -c "$proof" > output-q1.br          # 30,508 bytes

# Zstandard CLI 1.5.7
zstd -q -1 --no-check -c < "$proof" > output.zst # 30,513 bytes

# Apple gzip 479
gzip -n -9 -c "$proof" > output.gz              # 30,532 bytes

# xz 5.8.3 / liblzma 5.8.3
xz -0 -c "$proof" > output.xz                   # 30,568 bytes
```

The remaining best-setting commands were:

```sh
lz4 -q -12 --no-frame-crc -c "$proof" > output.lz4 # 30,519 bytes
zip -X -j -9 output.zip "$proof"                    # 30,626 bytes
bzip2 -9 -c "$proof" > output.bz2                   # 30,975 bytes
```

The LZ4, ZIP, and bzip2 version strings were not pinned in the finalized
artifact and are deliberately not invented here. Their command lines and
results are retained as independently measured matrix entries. Only the
winning tied Brotli q1 case was promoted to the finalized evidence bundle.

## Exact round trip and verifier acceptance

The finalized q1 compressed artifact is 30,508 bytes with SHA-256:

```text
d2e71b945d4d5c30204fc72b79c134f3f8add38885e01d1d4c00aa5a6c979c41
```

Decompression produced 30,504 bytes byte-for-byte equal to the frozen proof,
with the original SHA-256:

```text
e8e15ce268447b92ac1344292bc879dcb0bf7534621ce077d8790097975dcecb
```

Every matrix candidate round-tripped to that same proof hash. For the
finalized q1 artifact, the exact production V7 read-only verifier then
accepted the decompressed bytes with `check_pow = true`, compact counter 4,
frontier 203, and all three work witnesses checked. This is the exact
Construction 2.2 acceptance path, not a file-equality-only test.

The finalized evidence is
`results/v8/v8-a-frozen-v7-brotli-q1-20260825/v8-a-compression-experiment.json`,
SHA-256
`0ace48577f022f32a9b3b2b2f59220ec28e00798bb804244cf621839c2bfddf0`.

Measured q1 costs were 8 ms and 1,966,080 bytes maximum resident set for
compression, and 6 ms and 1,720,320 bytes maximum resident set for
decompression. The complete harness, including production host verification,
finished in 0.47 seconds with 6,963,200 bytes maximum resident set.

## Gate result

| V8 target | Limit | q1 miss |
|---|---:|---:|
| 18 KiB gold | 18,432 bytes | 12,076 bytes |
| Preferred release | 18,500 bytes | 12,008 bytes |
| Five total lifecycle transactions | 18,937 bytes | 11,571 bytes |
| Five proof-bearing transactions | 19,095 bytes | 11,413 bytes |
| Five uploads plus separate verification | 19,375 bytes | 11,133 bytes |

No size gate passes. The output falls in the plan's `>20,500` rejection band
and is larger than V7 itself.

## Archived decision and next track

This result rejects ordinary lossless wrapping, including further tuning of
the same codec families. It does not claim that information-theoretic proof
compression is impossible, nor does it reject a specialized native encoding
backed by a reconstruction theorem. It says the remaining 11–12 KiB cannot
come from a generic file-codec wrapper around this already packed proof.

V8's active route is now a native cryptographic redesign: a materially
different PCS/IOPP or another proof system that changes which evidence must be
transmitted and checked. A future proposal may reuse the V8 name only if it
preserves the spend semantics and security target while meeting the byte and
CU gates.

**REJECTED—do not revisit absent a genuinely different cryptographic proof
system.**

#!/usr/bin/env swift

import CryptoKit
import Foundation
import Metal

private let kernelSource = #"""
#include <metal_stdlib>
using namespace metal;

constant uint K[64] = {
    0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
    0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
    0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
    0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
    0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
    0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
    0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
    0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2
};

inline uint rotr(uint x, uint n) { return (x >> n) | (x << (32 - n)); }

inline uint small_sigma0(uint x) { return rotr(x, 7) ^ rotr(x, 18) ^ (x >> 3); }
inline uint small_sigma1(uint x) { return rotr(x, 17) ^ rotr(x, 19) ^ (x >> 10); }
inline uint big_sigma0(uint x) { return rotr(x, 2) ^ rotr(x, 13) ^ rotr(x, 22); }
inline uint big_sigma1(uint x) { return rotr(x, 6) ^ rotr(x, 11) ^ rotr(x, 25); }
inline uint choose(uint x, uint y, uint z) { return z ^ (x & (y ^ z)); }
inline uint majority(uint x, uint y, uint z) { return (x & y) | (z & (x | y)); }

// Rotating the variable names between invocations makes one compression
// round require only the two state writes mandated by SHA-256. Eight rounds
// restore the a...h orientation. The 16-word scalar schedule avoids the
// private-memory traffic of a 64-word per-thread array.
#define SHA_ROUND(A,B,C,D,E,F,G,H,I,W) do {                            \
    uint t1 = (H) + big_sigma1(E) + choose((E),(F),(G)) + K[(I)] + (W); \
    uint t2 = big_sigma0(A) + majority((A),(B),(C));                   \
    (D) += t1;                                                         \
    (H) = t1 + t2;                                                     \
} while (0)

#define EXPAND(W0,W1,W9,W14) \
    (W0) += small_sigma0(W1) + (W9) + small_sigma1(W14)

#define EXPAND_AND_COMPRESS_16(BASE) do { \
    EXPAND(w0,w1,w9,w14);    SHA_ROUND(a,b,c,d,e,f,g,h,(BASE)+0,w0);  \
    EXPAND(w1,w2,w10,w15);   SHA_ROUND(h,a,b,c,d,e,f,g,(BASE)+1,w1);  \
    EXPAND(w2,w3,w11,w0);    SHA_ROUND(g,h,a,b,c,d,e,f,(BASE)+2,w2);  \
    EXPAND(w3,w4,w12,w1);    SHA_ROUND(f,g,h,a,b,c,d,e,(BASE)+3,w3);  \
    EXPAND(w4,w5,w13,w2);    SHA_ROUND(e,f,g,h,a,b,c,d,(BASE)+4,w4);  \
    EXPAND(w5,w6,w14,w3);    SHA_ROUND(d,e,f,g,h,a,b,c,(BASE)+5,w5);  \
    EXPAND(w6,w7,w15,w4);    SHA_ROUND(c,d,e,f,g,h,a,b,(BASE)+6,w6);  \
    EXPAND(w7,w8,w0,w5);     SHA_ROUND(b,c,d,e,f,g,h,a,(BASE)+7,w7);  \
    EXPAND(w8,w9,w1,w6);     SHA_ROUND(a,b,c,d,e,f,g,h,(BASE)+8,w8);  \
    EXPAND(w9,w10,w2,w7);    SHA_ROUND(h,a,b,c,d,e,f,g,(BASE)+9,w9);  \
    EXPAND(w10,w11,w3,w8);   SHA_ROUND(g,h,a,b,c,d,e,f,(BASE)+10,w10); \
    EXPAND(w11,w12,w4,w9);   SHA_ROUND(f,g,h,a,b,c,d,e,(BASE)+11,w11); \
    EXPAND(w12,w13,w5,w10);  SHA_ROUND(e,f,g,h,a,b,c,d,(BASE)+12,w12); \
    EXPAND(w13,w14,w6,w11);  SHA_ROUND(d,e,f,g,h,a,b,c,(BASE)+13,w13); \
    EXPAND(w14,w15,w7,w12);  SHA_ROUND(c,d,e,f,g,h,a,b,(BASE)+14,w14); \
    EXPAND(w15,w0,w8,w13);   SHA_ROUND(b,c,d,e,f,g,h,a,(BASE)+15,w15); \
} while (0)

inline bool valid_head(uint h0, uint h1, uint bits) {
    if (bits == 0) return true;
    if (bits <= 32) return (h0 >> (32 - bits)) == 0;
    return h0 == 0 && (h1 >> (64 - bits)) == 0;
}

kernel void mine_pow(
    constant uint *state [[buffer(0)]],
    constant ulong &base [[buffer(1)]],
    constant uint &trials [[buffer(2)]],
    constant uint &bits [[buffer(3)]],
    constant uint &gridWidth [[buffer(4)]],
    device ulong *results [[buffer(5)]],
    constant uint *prestate [[buffer(6)]],
    uint gid [[thread_position_in_grid]]) {
    results[gid] = ~ulong(0);
    // Keep the hot-loop nonce as two 32-bit limbs. Apple GPUs execute the
    // increment and byte extraction more cheaply than a 64-bit multiply/add
    // plus eight 64-bit shifts for every candidate.
    if (ulong(gid) > ~ulong(0) - base) return;
    ulong firstNonce = base + ulong(gid);
    uint nonceLo = uint(firstNonce);
    uint nonceHi = uint(firstNonce >> 32);
    for (uint trial = 0; trial < trials; ++trial) {
        uint w0=state[0], w1=state[1], w2=state[2], w3=state[3];
        uint w4=state[4], w5=state[5], w6=state[6], w7=state[7];
        uint w8 = 0x03000000u | (nonceLo & 0xffu) << 16
                                   | ((nonceLo >> 8) & 0xffu) << 8
                                   | ((nonceLo >> 16) & 0xffu);
        uint w9 = (nonceLo >> 24) << 24
                  | (nonceHi & 0xffu) << 16
                  | ((nonceHi >> 8) & 0xffu) << 8
                  | ((nonceHi >> 16) & 0xffu);
        uint w10 = (nonceHi >> 24) << 24 | 0x00800000u;
        uint w11=0, w12=0, w13=0, w14=0, w15=328;
        uint a=prestate[0], b=prestate[1], c=prestate[2], d=prestate[3];
        uint e=prestate[4], f=prestate[5], g=prestate[6], h=prestate[7];
        SHA_ROUND(a,b,c,d,e,f,g,h,8,w8);
        SHA_ROUND(h,a,b,c,d,e,f,g,9,w9);
        SHA_ROUND(g,h,a,b,c,d,e,f,10,w10);
        SHA_ROUND(f,g,h,a,b,c,d,e,11,w11);
        SHA_ROUND(e,f,g,h,a,b,c,d,12,w12);
        SHA_ROUND(d,e,f,g,h,a,b,c,13,w13);
        SHA_ROUND(c,d,e,f,g,h,a,b,14,w14);
        SHA_ROUND(b,c,d,e,f,g,h,a,15,w15);
        EXPAND_AND_COMPRESS_16(16);
        EXPAND_AND_COMPRESS_16(32);
        EXPAND_AND_COMPRESS_16(48);
        uint h0 = a + 0x6a09e667u;
        uint h1 = b + 0xbb67ae85u;
        if (valid_head(h0, h1, bits)) {
            // Each gid visits candidates in increasing order. The host takes
            // the minimum across gids after the fixed chunk completes, so
            // the emitted nonce is independent of GPU scheduling.
            results[gid] = (ulong(nonceHi) << 32) | ulong(nonceLo);
            return;
        }
        if (trial + 1u < trials) {
            uint nextLo = nonceLo + gridWidth;
            uint carry = uint(nextLo < nonceLo);
            // Preserve the old exact end-of-u64 behavior: a lane terminates
            // instead of wrapping to nonce zero.
            if (carry != 0u && nonceHi == 0xffffffffu) return;
            nonceLo = nextLo;
            nonceHi += carry;
        }
    }
}
"""#

struct Options {
    var state: [UInt8] = []
    var bits: UInt32 = 0
    var start: UInt64 = 0
    // 65,536 long-lived lanes keep Apple GPUs saturated without the large
    // result buffer and scheduling overhead of the old one-million-lane
    // default.  More trials amortize dispatch while retaining a small chunk
    // relative to the high-difficulty production searches.
    var threads: UInt32 = 1 << 16
    var trials: UInt32 = 4096
    var maxHashes: UInt64? = nil
    var checkpoint: String? = nil
    var resume = false
}

func fail(_ message: String) -> Never {
    FileHandle.standardError.write(Data("aspis-pow-metal: \(message)\n".utf8))
    exit(2)
}

func require<T>(_ value: T?, _ message: String) -> T {
    guard let value else { fail(message) }
    return value
}

func parseHex(_ value: String) -> [UInt8]? {
    guard value.count == 64 else { return nil }
    var bytes: [UInt8] = []
    bytes.reserveCapacity(32)
    var index = value.startIndex
    for _ in 0..<32 {
        let next = value.index(index, offsetBy: 2)
        guard let byte = UInt8(value[index..<next], radix: 16) else { return nil }
        bytes.append(byte)
        index = next
    }
    return bytes
}

func parseOptions() -> Options {
    var options = Options()
    let arguments = Array(CommandLine.arguments.dropFirst())
    var index = 0
    while index < arguments.count {
        let argument = arguments[index]
        func value() -> String {
            guard index + 1 < arguments.count else { fail("missing value after \(argument)") }
            index += 1
            return arguments[index]
        }
        switch argument {
        case "--state": options.state = require(parseHex(value()), "--state must be 64 hex characters")
        case "--bits": options.bits = require(UInt32(value()), "invalid --bits")
        case "--start": options.start = require(UInt64(value()), "invalid --start")
        case "--threads": options.threads = require(UInt32(value()), "invalid --threads")
        case "--trials": options.trials = require(UInt32(value()), "invalid --trials")
        case "--max-hashes": options.maxHashes = require(UInt64(value()), "invalid --max-hashes")
        case "--checkpoint": options.checkpoint = value()
        case "--resume": options.resume = true
        default: fail("unknown argument \(argument)")
        }
        index += 1
    }
    guard options.state.count == 32 else { fail("--state is required") }
    guard options.bits <= 63 else { fail("--bits must be at most 63") }
    guard options.threads > 0 && options.trials > 0 else { fail("thread and trial counts must be nonzero") }
    if options.resume, let checkpoint = options.checkpoint,
       let saved = try? String(contentsOfFile: checkpoint, encoding: .utf8),
       let value = UInt64(saved.trimmingCharacters(in: .whitespacesAndNewlines)) {
        options.start = value
    }
    return options
}

func validDigest(state: [UInt8], nonce: UInt64, bits: UInt32) -> Bool {
    var message = state
    message.append(0x03)
    var littleEndian = nonce.littleEndian
    withUnsafeBytes(of: &littleEndian) { message.append(contentsOf: $0) }
    let digest = SHA256.hash(data: Data(message))
    let bytes = Array(digest)
    let head = bytes[0..<8].reduce(UInt64(0)) { ($0 << 8) | UInt64($1) }
    return bits == 0 || head < (UInt64(1) << (64 - bits))
}

private let sha256FirstEightK: [UInt32] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
    0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
]

func rotateRight(_ value: UInt32, _ count: UInt32) -> UInt32 {
    (value >> count) | (value << (32 - count))
}

// SHA-256 rounds 0...7 consume only the 32-byte transcript state.  Compute
// that nonce-independent prefix once on the CPU and pass it through constant
// memory, leaving the GPU kernel with rounds 8...63 for every candidate.
func sha256PrestateAfterEightRounds(_ words: [UInt32]) -> [UInt32] {
    var a: UInt32 = 0x6a09e667
    var b: UInt32 = 0xbb67ae85
    var c: UInt32 = 0x3c6ef372
    var d: UInt32 = 0xa54ff53a
    var e: UInt32 = 0x510e527f
    var f: UInt32 = 0x9b05688c
    var g: UInt32 = 0x1f83d9ab
    var h: UInt32 = 0x5be0cd19
    for i in 0..<8 {
        let bigSigma1 = rotateRight(e, 6) ^ rotateRight(e, 11) ^ rotateRight(e, 25)
        let choice = (e & f) ^ ((~e) & g)
        let temp1 = h &+ bigSigma1 &+ choice &+ sha256FirstEightK[i] &+ words[i]
        let bigSigma0 = rotateRight(a, 2) ^ rotateRight(a, 13) ^ rotateRight(a, 22)
        let majority = (a & b) ^ (a & c) ^ (b & c)
        let temp2 = bigSigma0 &+ majority
        h = g; g = f; f = e; e = d &+ temp1
        d = c; c = b; b = a; a = temp1 &+ temp2
    }
    return [a, b, c, d, e, f, g, h]
}

func writeCheckpoint(_ path: String, next: UInt64) {
    let url = URL(fileURLWithPath: path)
    do {
        try FileManager.default.createDirectory(at: url.deletingLastPathComponent(), withIntermediateDirectories: true)
        try Data("\(next)\n".utf8).write(to: url, options: .atomic)
    } catch {
        fail("checkpoint write failed: \(error)")
    }
}

var options = parseOptions()
guard let device = MTLCreateSystemDefaultDevice() else { fail("Metal device unavailable") }
let library: MTLLibrary
do { library = try device.makeLibrary(source: kernelSource, options: nil) }
catch { fail("Metal kernel compilation failed: \(error)") }
guard let function = library.makeFunction(name: "mine_pow") else { fail("mine_pow kernel unavailable") }
let pipeline: MTLComputePipelineState
do { pipeline = try device.makeComputePipelineState(function: function) }
catch { fail("pipeline creation failed: \(error)") }
guard let queue = device.makeCommandQueue() else { fail("command queue unavailable") }

var words = [UInt32](repeating: 0, count: 8)
for i in 0..<8 {
    words[i] = UInt32(options.state[4*i]) << 24 | UInt32(options.state[4*i+1]) << 16
             | UInt32(options.state[4*i+2]) << 8 | UInt32(options.state[4*i+3])
}
let prestate = sha256PrestateAfterEightRounds(words)
guard let stateBuffer = device.makeBuffer(bytes: words, length: 32, options: .storageModeShared),
      let prestateBuffer = device.makeBuffer(bytes: prestate, length: 32, options: .storageModeShared),
      let baseBuffer = device.makeBuffer(length: 8, options: .storageModeShared),
      let trialsBuffer = device.makeBuffer(length: 4, options: .storageModeShared),
      let bitsBuffer = device.makeBuffer(length: 4, options: .storageModeShared),
      let widthBuffer = device.makeBuffer(length: 4, options: .storageModeShared),
      let resultBuffer = device.makeBuffer(
          length: Int(options.threads) * MemoryLayout<UInt64>.stride,
          options: .storageModeShared
      )
else { fail("Metal buffer allocation failed") }

trialsBuffer.contents().storeBytes(of: options.trials, as: UInt32.self)
bitsBuffer.contents().storeBytes(of: options.bits, as: UInt32.self)
widthBuffer.contents().storeBytes(of: options.threads, as: UInt32.self)
let hashesPerChunk = UInt64(options.threads) * UInt64(options.trials)
let started = Date()
var base = options.start
var tested: UInt64 = 0

while true {
    if let limit = options.maxHashes, tested >= limit {
        let elapsed = Date().timeIntervalSince(started)
        let rate = String(format: "%.2f", Double(tested) / elapsed / 1_000_000)
        let duration = String(format: "%.3f", elapsed)
        FileHandle.standardError.write(Data("aspis-pow-metal: benchmark tested=\(tested) rate=\(rate) MH/s elapsed=\(duration)s\n".utf8))
        exit(3)
    }
    baseBuffer.contents().storeBytes(of: base, as: UInt64.self)
    guard let command = queue.makeCommandBuffer(), let encoder = command.makeComputeCommandEncoder() else {
        fail("command allocation failed")
    }
    encoder.setComputePipelineState(pipeline)
    encoder.setBuffer(stateBuffer, offset: 0, index: 0)
    encoder.setBuffer(baseBuffer, offset: 0, index: 1)
    encoder.setBuffer(trialsBuffer, offset: 0, index: 2)
    encoder.setBuffer(bitsBuffer, offset: 0, index: 3)
    encoder.setBuffer(widthBuffer, offset: 0, index: 4)
    encoder.setBuffer(resultBuffer, offset: 0, index: 5)
    encoder.setBuffer(prestateBuffer, offset: 0, index: 6)
    let groupWidth = min(pipeline.maxTotalThreadsPerThreadgroup, 32)
    encoder.dispatchThreads(MTLSize(width: Int(options.threads), height: 1, depth: 1),
                            threadsPerThreadgroup: MTLSize(width: groupWidth, height: 1, depth: 1))
    encoder.endEncoding()
    command.commit()
    command.waitUntilCompleted()
    guard command.status == .completed else { fail("Metal command failed: \(String(describing: command.error))") }
    let remainingThroughMax = UInt64.max - base
    let candidatesThisChunk = remainingThroughMax >= hashesPerChunk - 1
        ? hashesPerChunk
        : remainingThroughMax + 1
    let testedUpdate = tested.addingReportingOverflow(candidatesThisChunk)
    tested = testedUpdate.overflow ? UInt64.max : testedUpdate.partialValue
    let candidates = resultBuffer.contents().bindMemory(
        to: UInt64.self,
        capacity: Int(options.threads)
    )
    var nonce = UInt64.max
    for gid in 0..<Int(options.threads) {
        nonce = min(nonce, candidates[gid])
    }
    if nonce != UInt64.max {
        guard validDigest(state: options.state, nonce: nonce, bits: options.bits) else {
            fail("GPU nonce failed independent CryptoKit SHA-256 check")
        }
        if let checkpoint = options.checkpoint {
            try? FileManager.default.removeItem(atPath: checkpoint)
        }
        let elapsed = Date().timeIntervalSince(started)
        let rate = String(format: "%.2f", Double(tested) / elapsed / 1_000_000)
        let duration = String(format: "%.3f", elapsed)
        FileHandle.standardError.write(Data("aspis-pow-metal: found bits=\(options.bits) nonce=\(nonce) tested<=\(tested) rate=\(rate) MH/s elapsed=\(duration)s\n".utf8))
        print("nonce=\(nonce)")
        exit(0)
    }
    guard candidatesThisChunk == hashesPerChunk else { fail("u64 nonce space exhausted") }
    let next = base.addingReportingOverflow(hashesPerChunk)
    guard !next.overflow else { fail("u64 nonce space exhausted") }
    base = next.partialValue
    if let checkpoint = options.checkpoint { writeCheckpoint(checkpoint, next: base) }
    let elapsed = Date().timeIntervalSince(started)
    let rate = String(format: "%.2f", Double(tested) / elapsed / 1_000_000)
    let duration = String(format: "%.1f", elapsed)
    FileHandle.standardError.write(Data("aspis-pow-metal: bits=\(options.bits) next=\(base) tested=\(tested) rate=\(rate) MH/s elapsed=\(duration)s\n".utf8))
}

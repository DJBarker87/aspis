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
    uint gid [[thread_position_in_grid]]) {
    results[gid] = ~ulong(0);
    for (uint trial = 0; trial < trials; ++trial) {
        ulong offset = ulong(gid) + ulong(trial) * ulong(gridWidth);
        // The host normally dispatches full contiguous chunks.  This guard
        // makes the final partial u64 chunk exact instead of wrapping to
        // nonce zero if the entire nonce space contains no success.
        if (offset > ~ulong(0) - base) return;
        ulong nonce = base + offset;
        uint w[64];
        for (uint i = 0; i < 8; ++i) w[i] = state[i];
        w[8] = 0x03000000u | uint((nonce      ) & 0xffu) << 16
                              | uint((nonce >>  8) & 0xffu) << 8
                              | uint((nonce >> 16) & 0xffu);
        w[9] = uint((nonce >> 24) & 0xffu) << 24
             | uint((nonce >> 32) & 0xffu) << 16
             | uint((nonce >> 40) & 0xffu) << 8
             | uint((nonce >> 48) & 0xffu);
        w[10] = uint((nonce >> 56) & 0xffu) << 24 | 0x00800000u;
        w[11] = 0; w[12] = 0; w[13] = 0; w[14] = 0; w[15] = 328;
        for (uint i = 16; i < 64; ++i) {
            uint s0 = rotr(w[i - 15], 7) ^ rotr(w[i - 15], 18) ^ (w[i - 15] >> 3);
            uint s1 = rotr(w[i - 2], 17) ^ rotr(w[i - 2], 19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16] + s0 + w[i - 7] + s1;
        }
        uint a=0x6a09e667, b=0xbb67ae85, c=0x3c6ef372, d=0xa54ff53a;
        uint e=0x510e527f, f=0x9b05688c, g=0x1f83d9ab, h=0x5be0cd19;
        for (uint i = 0; i < 64; ++i) {
            uint S1 = rotr(e,6) ^ rotr(e,11) ^ rotr(e,25);
            uint ch = (e & f) ^ ((~e) & g);
            uint temp1 = h + S1 + ch + K[i] + w[i];
            uint S0 = rotr(a,2) ^ rotr(a,13) ^ rotr(a,22);
            uint maj = (a & b) ^ (a & c) ^ (b & c);
            uint temp2 = S0 + maj;
            h=g; g=f; f=e; e=d+temp1; d=c; c=b; b=a; a=temp1+temp2;
        }
        uint h0 = a + 0x6a09e667u;
        uint h1 = b + 0xbb67ae85u;
        if (valid_head(h0, h1, bits)) {
            // Each gid visits candidates in increasing order. The host takes
            // the minimum across gids after the fixed chunk completes, so
            // the emitted nonce is independent of GPU scheduling.
            results[gid] = nonce;
            return;
        }
    }
}
"""#

struct Options {
    var state: [UInt8] = []
    var bits: UInt32 = 0
    var start: UInt64 = 0
    var threads: UInt32 = 1 << 20
    var trials: UInt32 = 512
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
guard let stateBuffer = device.makeBuffer(bytes: words, length: 32, options: .storageModeShared),
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
    let groupWidth = min(pipeline.maxTotalThreadsPerThreadgroup, 256)
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

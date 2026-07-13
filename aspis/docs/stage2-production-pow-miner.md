# Production PoW miner for profile 21

Status: **canonical-minimum CPU and Metal implementations are byte-exact;
final profile-21 mining is deliberately not started until its transcript and
proof bytes are frozen.  The protocol-specific EPRO theorem is tracked in the
profile-21 privacy closure and is not implied by this engineering artifact.**

## Canonical predicate

Every work witness uses the existing verifier predicate, unchanged:

```text
digest = SHA256(transcript_state[32] || 0x03 || nonce_u64_le)
accept iff u64_be(digest[0..8]) < 2^(64-bits).
```

The Metal kernel specializes this 41-byte message to one SHA-256 block. The
padding word is 328 bits. It neither changes transcript absorption nor lowers
any difficulty. A returned GPU nonce is checked once with CryptoKit in the
runner and again with `Transcript::grinding_ok` in Rust before proof
construction can use it.

Minimum-nonce semantics are an honest-prover rule, not an additional verifier
predicate.  Both bundled miners now return

```text
K = min { k in [0,2^64) : grinding_ok(state,k,bits) }.
```

The CPU workers share an atomic minimum and do not retire until every worker's
next residue-class candidate is at least that minimum.  Each Metal dispatch
finishes a complete contiguous chunk, returns the first success in each GPU
thread's increasing stream, and the host selects the global minimum.  Earlier
completed chunks contain no success.  Thus CPU scheduling and GPU scheduling
cannot change `K`.  The consensus verifier still checks only validity, so a
custom `ASPIS_POW_MINER` is trusted honest-prover code and must implement this
canonical rule for the privacy theorem to apply.

## Sequential work records

For the rate-1/512 q16 state-only schedule plus the selected switch, the work
records are causally distinct and cannot be shared:

| Record | Bits | Bound state and position |
|---|---:|---|
| batch | 38 | after all statement-evaluation rows, before gamma |
| fold 0 | 39 | after layer-0 OOD values and relation sumcheck, before alpha0 |
| switch source | 38 | after alpha0 and `(tX,muF)`, before delta |
| fold 1 | 35 | after layer-1 root/OOD/sumcheck, before alpha1 |
| fold 2 | 31 | after layer-2 root/OOD/sumcheck, before alpha2 |
| fold 3 | 27 | after layer-3 root/OOD/sumcheck, before alpha3 |
| final query | 38 | after the final tensor polynomial/translated continuation, before q16 |

The first, four fold, and final records are the current profile-20 order. The
source record is the new profile-21 pre-delta requirement. The profile-21
implementation must retain this table as a schedule test when its wire
offsets freeze. Label 36 is reserved for the source nonce; label 39 is
reserved if the switch final-position record is encoded separately rather
than reusing the existing final-query work position.

## Implemented paths

- `aspis-prover::pow` is the sole prover search entry point. It replaces the
  previously single-threaded batch search as well as the earlier ad-hoc
  multithreaded fold/final search.
- `build_state_only_masked_switch(..., MaskedSwitchPowMode::Mine)` now mines
  the isolated source and final g36 records through that same entry point;
  the existing diagnostic builder remains byte-compatible and emits zeros.
- Without configuration it searches on all available CPU cores. Progress is
  silent by default and is enabled only with `ASPIS_POW_PROGRESS=1`.
- With `ASPIS_POW_MINER` it invokes the configured canonical runner. With
  `ASPIS_POW_CHECKPOINT_DIR` each transcript state gets its own full-state,
  difficulty-qualified checkpoint. Completed searches remove their stale
  checkpoint.
- The Metal runner dispatches 2^20 threads with 512 candidates per thread by
  default. Every completed approximately 2^29-candidate chunk advances the
  checkpoint and prints elapsed work and throughput. Interruption loses at
  most the current chunk.
- The bounded first-Good Profile23 worker uses the unpublished-attempt entry
  point: it suppresses child stderr, emits no progress, and creates no
  checkpoint, so only the fixed-boundary `Proof`/`Abort` release is public.

Build and test on Apple Silicon:

```sh
./tools/build-aspis-pow-metal.sh
ASPIS_POW_MINER="$PWD/target/release/aspis-pow-metal" \
  cargo test -p aspis-prover \
  pow::tests::configured_metal_miner_matches_canonical_predicate \
  --release -- --ignored --nocapture
```

For the final frozen proof:

```sh
mkdir -p results/stage2/pow-checkpoints
ASPIS_POW_MINER="$PWD/target/release/aspis-pow-metal" \
ASPIS_POW_CHECKPOINT_DIR="$PWD/results/stage2/pow-checkpoints" \
  <the frozen profile-21 proof command>
```

## Measured throughput and estimate

On the 10-core Apple M3 / Metal 4 host, one 2^29-candidate no-hit benchmark
ran at **579.51 MH/s**. The generic sha2 path measured **7.059 MH/s on one CPU
core**; eight-core scaling is only a fallback estimate, not a replacement for
the Metal measurement.

At 579.51 MH/s, expected search times are 474.33 seconds for each 38-bit
record, 948.66 seconds for 39 bits, 59.29 seconds for 35 bits, 3.71 seconds
for 31 bits, and 0.23 seconds for 27 bits. The seven-record expected total is
**2,434.87 seconds = 40.58 minutes**. Grinding is geometric, so this is an
expectation, not a deadline or upper bound.

## Guards

- CPU KAT pins the minimum 16-bit nonce `100214` for a fixed transcript and
  exercises both the sequential and scheduler-independent parallel paths.
- The ignored Metal/Rust integration test requires that exact same global
  minimum `100214`, independently checks every earlier nonce in Rust, and then
  checks the ordinary verifier predicate.
- The Metal executable independently rehashes a returned candidate with
  CryptoKit before printing it.
- The Metal kernel rejects offsets beyond `u64::MAX` in its final partial
  chunk; a no-success tail fails closed instead of wrapping to nonce zero.
- Proof verification remains the final independent check of every serialized
  nonce. No diagnostic PoW bypass is allowed for the mined artifact.

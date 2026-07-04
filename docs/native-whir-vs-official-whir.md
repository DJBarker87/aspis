# Native WHIR vs Official WHIR

## Scope
Nearest-comparable upstream PCS runs only. Local proofs remain M31/CM31/QM31 with SHA-256 and a fixed narrow v0 relation; official WHIR runs use the current upstream CLI over Goldilocks2 with Blake3 because upstream does not currently expose M31 or SHA-256.

## Official Repo
- path: `/tmp/whir-ref`
- git head: `0aeaa7f337c743d9ddfcb9d909628d6491e3355c`
- dirty: `false`

## Global Notes
- This is a comparison harness, not a proof-equivalence oracle.
- The current upstream CLI no longer exposes the README's older `--type` or `--fold_type` flags; the harness records the upstream commit and parses the real current CLI output.
- Official proof size is reported from upstream stdout in KiB and converted to an estimated byte count; it is not a byte-exact serialization export.
- Official runs are bounded by a 180 second timeout by default so the harness cannot hang indefinitely on one upstream profile.

## Profiles
### whir-m31-dev-v0
- local proof bytes: Some(4108)
- local host prove ns: Some(2311792)
- local on-chain verify CU: Some(96118)
- official proof size: Some(22.3) KiB (~Some(22835) bytes)
- official completed/timed_out/exit_success: true/false/true
- official prover total ns: Some(172100000)
- official verifier ns/rep: Some(11300000)
- official security line: Some(96.0) bits using Some("list decoding")
- local fold stages: 4, official initial+round stages: 5
- official stdout: `/Users/dominic/ZK/results/native-whir/official-whir/whir-m31-dev-v0.stdout.txt`
- official stderr: `/Users/dominic/ZK/results/native-whir/official-whir/whir-m31-dev-v0.stderr.txt`
  - Official run uses Goldilocks2 as the nearest upstream PCS field embedding, not M31 -> CM31 -> QM31.
  - Official run uses Blake3 because the current upstream CLI does not expose SHA-256.
  - Local verifier cost is on-chain CU; official verifier cost is host wall-clock time from the upstream binary.
  - Stage-count mismatch: local fold stages=4, official reported initial+round stages=5.

### whir-m31-solana-v0
- local proof bytes: Some(18316)
- local host prove ns: Some(25763625)
- local on-chain verify CU: Some(326021)
- official proof size: None KiB (~None bytes)
- official completed/timed_out/exit_success: false/true/false
- official prover total ns: None
- official verifier ns/rep: None
- official security line: Some(128.0) bits using Some("list decoding")
- local fold stages: 6, official initial+round stages: 7
- official stdout: `/Users/dominic/ZK/results/native-whir/official-whir/whir-m31-solana-v0.stdout.txt`
- official stderr: `/Users/dominic/ZK/results/native-whir/official-whir/whir-m31-solana-v0.stderr.txt`
  - Official run uses Goldilocks2 as the nearest upstream PCS field embedding, not M31 -> CM31 -> QM31.
  - Official run uses Blake3 because the current upstream CLI does not expose SHA-256.
  - Local verifier cost is on-chain CU; official verifier cost is host wall-clock time from the upstream binary.
  - Official run timed out after 180 seconds; partial stdout/stderr were preserved.
  - Stage-count mismatch: local fold stages=6, official reported initial+round stages=7.

_Generated 2026-04-19T22:04:20.243088+00:00 from `cargo xtask compare-official-whir`._
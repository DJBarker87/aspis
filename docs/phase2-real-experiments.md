# Phase 2 Real Verifier Experiments

## Goal
Run the actual Anchor/Winterfell `verify_stark` instruction that exists in this repo, preserve the same public digest binding across proof variants, and measure whether a commitment-preserving row-interpolant sidecar buys verifier CU once the proof has at least one recursive FRI layer.

## Actual Program Path
- Program id: `CECNRbDxFQVfWiQwvG8qcSGPGSk8eLWraBCERcdL5DKT`.
- Build target: `third_party/solana-pqzk-fullchain/programs/stark-pqc-verifier`.
- Execution path: `phase2_init_chat_msg` -> `phase2_write_chat_msg_chunk` -> `verify_stark`.
- `phase2_*` is a feature-gated loader used only to populate the exact `ChatMsg` account consumed by the production verifier instruction.
- This is a real transparent verifier path, but it is Winterfell/FRI over `f128`, not a native WHIR/M31 verifier.

## Archived Trace-8 Reference
- Archived repo baseline: mean verify CU 1104506.47, proof bytes 4211, trace length 8, recursive FRI layers 0.
- Local sanity run `trace8_raw_rows`: mean verify CU 1157699.

## Run Config
- payload_chunk_size=640, verify_repetitions=3, heap_frame_bytes_requested=262144.
- baseline_trace_len=8, baseline_num_queries=30, experimental_trace_len_candidates=[16, 32, 64, 128, 256, 512, 1024], experimental_query_count_candidates=[30, 24, 20, 16, 12, 8, 6, 4, 2], chosen_experimental_trace_len=64, chosen_experimental_num_queries=30.
- production_max_chat_payload_bytes=10068, phase2_loader_max_chat_payload_bytes=65536, cipher_hex=`000102030405060708090a0b0c0d0e0f101112131415161718191a1b`, nonce_hex=`1032547698badcfe13579bdf`, kem_len=0.

## Variants
- `trace8_raw_rows`: group=sanity, trace_len=8, include_interpolants=false, proof_bytes=4437, fri_layers=0, predicted_verify_cu=1114365.0.
- `trace64_q30_raw_rows`: group=fold_experiment, trace_len=64, include_interpolants=false, proof_bytes=13354, fri_layers=1, predicted_verify_cu=1580246.3.
- `trace64_q30_raw_rows_plus_interpolants`: group=fold_experiment, trace_len=64, include_interpolants=true, proof_bytes=15210, fri_layers=1, predicted_verify_cu=1593412.4.

## Measured Results
- `trace8_raw_rows`: verify=1157699 CU, pipeline_total=1177074 CU, init_chat_msg=1868 CU, write_chat_msg_total=17507 CU, proof_bytes=4437, fri_layers=0.
- `trace64_q30_raw_rows`: verify=1400000 CU (failed to complete under current tx CU cap), pipeline_total=1457359 CU, init_chat_msg=2570 CU, write_chat_msg_total=54789 CU, proof_bytes=13354, fri_layers=1.
- `trace64_q30_raw_rows_plus_interpolants`: verify=1400000 CU (failed to complete under current tx CU cap), pipeline_total=1465704 CU, init_chat_msg=2584 CU, write_chat_msg_total=63120 CU, proof_bytes=15210, fri_layers=1.

## Fold Experiment Winner
- Baseline `trace64_q30_raw_rows` verify=1400000 CU, pipeline_total=1457359 CU.
- Winner `trace64_q30_raw_rows` verify=1400000 CU, pipeline_total=1457359 CU.
- Delta vs baseline: verify 0 CU, pipeline_total 0 CU, proof bytes 0.

## Predicted vs Measured
- `trace8_raw_rows`: predicted_verify_cu=1114365.0, measured_verify_cu=1157699, abs_error=43334.0, rel_error=3.74%.
- `trace64_q30_raw_rows`: predicted_verify_cu=1580246.3, measured_verify_cu=1400000, abs_error=180246.3, rel_error=12.87%.
- `trace64_q30_raw_rows_plus_interpolants`: predicted_verify_cu=1593412.4, measured_verify_cu=1400000, abs_error=193412.4, rel_error=13.82%.

## Notes
- This measures the actual Anchor/Winterfell `verify_stark` instruction present in the repo. It is a real transparent verifier path, but it is still Winterfell/FRI over f128 rather than a native WHIR/M31 verifier. At least one measured verify variant hit the transaction CU cap before completion; those rows are preserved as lower-bound CU observations and marked as failed-to-complete.
- The archived `trace_len=8` proof has zero recursive FRI layers, so the row-interpolant sidecar is a semantic no-op there. This runner chooses the smallest larger trace length that actually creates recursive FRI work within the verifier payload cap.
- The production ChatMsg payload cap in this repo is 10068 bytes. The phase2-only loader used for measurement allows up to 65536 bytes so a full-security recursive proof can be staged without changing `verify_stark` itself.
- The `phase2_*` loader bypasses signature verification only to stage identical `ChatMsg` bytes for each variant. `verify_stark` itself is unmodified and remains the measured verifier instruction.
- Because the repo does not contain a native WHIR/M31 verifier, this report should be read as a real-program fold-packaging experiment on the available Winterfell/FRI verifier, not as a complete replacement for the missing M31 end-to-end path.

_Generated 2026-04-19T18:12:20.698192+00:00 UTC from `cargo xtask phase2-real-experiments`._
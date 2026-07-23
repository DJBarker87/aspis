-- Normalized from the pinned Aeneas output archived at
-- research-archive-v5-production-closure-2026-07-22.
import V5TranscriptRecords

open Aeneas Aeneas.Std Result ControlFlow Error

namespace aspis_verifier

/-- [aspis_core::transcript::label::M31_CIRCLE_ROUND_ROOT]
    Source: `crates/aspis-core/src/transcript.rs`, line 73. -/
@[global_simps, irreducible, rust_const
  "aspis_core::transcript::label::M31_CIRCLE_ROUND_ROOT"]
def aspis_core.transcript.label.M31_CIRCLE_ROUND_ROOT : Std.U8 := 12#u8

/-- [aspis_core::transcript::label::M31_CIRCLE_C2_ROOT]
    Source: `crates/aspis-core/src/transcript.rs`, line 76. -/
@[global_simps, irreducible, rust_const
  "aspis_core::transcript::label::M31_CIRCLE_C2_ROOT"]
def aspis_core.transcript.label.M31_CIRCLE_C2_ROOT : Std.U8 := 13#u8

/-- [aspis_verifier::v5_cu_probe::real_v5_round_root_absorb_input]
    Source: `programs/aspis-verifier/src/v5_cu_probe.rs`. -/
def v5_cu_probe.real_v5_round_root_absorb_input
    (layer : Std.Usize) (root : Array Std.U8 32#usize)
    (publicFsSalt : Array Std.U8 32#usize) :
    Result (Std.U8 × Array Std.U8 65#usize) := do
  let record ←
    v5_cu_probe.real_v5_round_root_record layer root publicFsSalt
  ok (aspis_core.transcript.label.M31_CIRCLE_ROUND_ROOT, record)

/-- [aspis_verifier::v5_cu_probe::real_v5_c2_root_absorb_input]
    Source: `programs/aspis-verifier/src/v5_cu_probe.rs`. -/
def v5_cu_probe.real_v5_c2_root_absorb_input
    (root : Array Std.U8 32#usize)
    (publicFsSalt : Array Std.U8 32#usize) :
    Result (Std.U8 × Array Std.U8 64#usize) := do
  let record ← v5_cu_probe.real_v5_c2_root_record root publicFsSalt
  ok (aspis_core.transcript.label.M31_CIRCLE_C2_ROOT, record)

end aspis_verifier

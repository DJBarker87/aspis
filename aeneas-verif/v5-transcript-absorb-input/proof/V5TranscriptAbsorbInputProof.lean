import V5TranscriptAbsorbInputCore
import V5TranscriptRecordsProof

open Aeneas Aeneas.Std Result ControlFlow

namespace AspisV5TranscriptAbsorbInput

open aspis_verifier

theorem extracted_round_root_absorb_input_exact
    (layer : Std.Usize)
    (layerByte : Std.U8)
    (root publicFsSalt : Array Std.U8 32#usize)
    (hlayer : layer.val = layerByte.val) :
    v5_cu_probe.real_v5_round_root_absorb_input layer root publicFsSalt
      ⦃ output =>
        output.1 = 12#u8 ∧
        output.2.val =
          AspisV5TranscriptRecords.roundRootRecordModel
            layerByte root publicFsSalt ⦄ := by
  have hrecord := AspisV5TranscriptRecords.extracted_round_root_record_exact
    layer layerByte root publicFsSalt hlayer
  unfold v5_cu_probe.real_v5_round_root_absorb_input
  cases hcall : v5_cu_probe.real_v5_round_root_record
      layer root publicFsSalt with
  | fail error =>
      rw [hcall] at hrecord
      simp [Std.WP.spec, Std.WP.theta] at hrecord
  | ok record =>
      rw [hcall] at hrecord
      simpa [aspis_core.transcript.label.M31_CIRCLE_ROUND_ROOT,
        Std.WP.spec, Std.WP.theta, Std.WP.wp_return] using hrecord
  | div =>
      rw [hcall] at hrecord
      simp [Std.WP.spec, Std.WP.theta] at hrecord

theorem extracted_c2_root_absorb_input_exact
    (root publicFsSalt : Array Std.U8 32#usize) :
    v5_cu_probe.real_v5_c2_root_absorb_input root publicFsSalt
      ⦃ output =>
        output.1 = 13#u8 ∧
        output.2.val =
          AspisV5TranscriptRecords.c2RootRecordModel root publicFsSalt ⦄ := by
  have hrecord := AspisV5TranscriptRecords.extracted_c2_root_record_exact
    root publicFsSalt
  unfold v5_cu_probe.real_v5_c2_root_absorb_input
  cases hcall : v5_cu_probe.real_v5_c2_root_record root publicFsSalt with
  | fail error =>
      rw [hcall] at hrecord
      simp [Std.WP.spec, Std.WP.theta] at hrecord
  | ok record =>
      rw [hcall] at hrecord
      simpa [aspis_core.transcript.label.M31_CIRCLE_C2_ROOT,
        Std.WP.spec, Std.WP.theta, Std.WP.wp_return] using hrecord
  | div =>
      rw [hcall] at hrecord
      simp [Std.WP.spec, Std.WP.theta] at hrecord

theorem extracted_round_and_c2_absorb_labels_are_distinct :
    (12#u8 : Std.U8) ≠ 13#u8 := by
  decide

#print axioms extracted_round_root_absorb_input_exact
#print axioms extracted_c2_root_absorb_input_exact
#print axioms extracted_round_and_c2_absorb_labels_are_distinct

end AspisV5TranscriptAbsorbInput

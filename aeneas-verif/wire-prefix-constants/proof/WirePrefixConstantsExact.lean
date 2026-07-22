import WirePrefixConstants

open Aeneas Aeneas.Std Result

private theorem add_23_32 : 23#usize + 32#usize = ok 55#usize := by
  change UScalar.add 23#usize 32#usize = ok 55#usize
  rcases System.Platform.numBits_eq with h | h <;>
    norm_num [UScalar.add, UScalar.tryMk, UScalar.tryMkOpt,
      UScalar.check_bounds, UScalar.ofNatCore, UScalar.val, h]

private theorem add_55_32 : 55#usize + 32#usize = ok 87#usize := by
  change UScalar.add 55#usize 32#usize = ok 87#usize
  rcases System.Platform.numBits_eq with h | h <;>
    norm_num [UScalar.add, UScalar.tryMk, UScalar.tryMkOpt,
      UScalar.check_bounds, UScalar.ofNatCore, UScalar.val, h]

private theorem add_87_16 : 87#usize + 16#usize = ok 103#usize := by
  change UScalar.add 87#usize 16#usize = ok 103#usize
  rcases System.Platform.numBits_eq with h | h <;>
    norm_num [UScalar.add, UScalar.tryMk, UScalar.tryMkOpt,
      UScalar.check_bounds, UScalar.ofNatCore, UScalar.val, h]

private theorem add_103_4480 : 103#usize + 4480#usize = ok 4583#usize := by
  change UScalar.add 103#usize 4480#usize = ok 4583#usize
  rcases System.Platform.numBits_eq with h | h <;>
    norm_num [UScalar.add, UScalar.tryMk, UScalar.tryMkOpt,
      UScalar.check_bounds, UScalar.ofNatCore, UScalar.val, h]

private theorem add_16_3 : 16#usize + 3#usize = ok 19#usize := by
  change UScalar.add 16#usize 3#usize = ok 19#usize
  rcases System.Platform.numBits_eq with h | h <;>
    norm_num [UScalar.add, UScalar.tryMk, UScalar.tryMkOpt,
      UScalar.check_bounds, UScalar.ofNatCore, UScalar.val, h]

private theorem mul_4_19 : 4#usize * 19#usize = ok 76#usize := by
  change UScalar.mul 4#usize 19#usize = ok 76#usize
  rcases System.Platform.numBits_eq with h | h <;>
    norm_num [UScalar.mul, UScalar.tryMk, UScalar.tryMkOpt,
      UScalar.check_bounds, UScalar.ofNatCore, UScalar.val, h]

private theorem mul_76_16 : 76#usize * 16#usize = ok 1216#usize := by
  change UScalar.mul 76#usize 16#usize = ok 1216#usize
  rcases System.Platform.numBits_eq with h | h <;>
    norm_num [UScalar.mul, UScalar.tryMk, UScalar.tryMkOpt,
      UScalar.check_bounds, UScalar.ofNatCore, UScalar.val, h]

private theorem add_4583_1216 : 4583#usize + 1216#usize = ok 5799#usize := by
  change UScalar.add 4583#usize 1216#usize = ok 5799#usize
  rcases System.Platform.numBits_eq with h | h <;>
    norm_num [UScalar.add, UScalar.tryMk, UScalar.tryMkOpt,
      UScalar.check_bounds, UScalar.ofNatCore, UScalar.val, h]

private theorem mul_3_16 : 3#usize * 16#usize = ok 48#usize := by
  change UScalar.mul 3#usize 16#usize = ok 48#usize
  rcases System.Platform.numBits_eq with h | h <;>
    norm_num [UScalar.mul, UScalar.tryMk, UScalar.tryMkOpt,
      UScalar.check_bounds, UScalar.ofNatCore, UScalar.val, h]

private theorem add_5799_48 : 5799#usize + 48#usize = ok 5847#usize := by
  change UScalar.add 5799#usize 48#usize = ok 5847#usize
  rcases System.Platform.numBits_eq with h | h <;>
    norm_num [UScalar.add, UScalar.tryMk, UScalar.tryMkOpt,
      UScalar.check_bounds, UScalar.ofNatCore, UScalar.val, h]

private theorem add_5847_16 : 5847#usize + 16#usize = ok 5863#usize := by
  change UScalar.add 5847#usize 16#usize = ok 5863#usize
  rcases System.Platform.numBits_eq with h | h <;>
    norm_num [UScalar.add, UScalar.tryMk, UScalar.tryMkOpt,
      UScalar.check_bounds, UScalar.ofNatCore, UScalar.val, h]

private theorem sub_4_1 : 4#usize - 1#usize = ok 3#usize := by
  change UScalar.sub 4#usize 1#usize = ok 3#usize
  rcases System.Platform.numBits_eq with h | h <;>
    norm_num [UScalar.sub, UScalar.val, h] <;>
    apply UScalar.eq_of_val_eq <;> norm_num [h, UScalar.val]

private theorem add_2_3 : 2#usize + 3#usize = ok 5#usize := by
  change UScalar.add 2#usize 3#usize = ok 5#usize
  rcases System.Platform.numBits_eq with h | h <;>
    norm_num [UScalar.add, UScalar.tryMk, UScalar.tryMkOpt,
      UScalar.check_bounds, UScalar.ofNatCore, UScalar.val, h]

private theorem mul_5_32 : 5#usize * 32#usize = ok 160#usize := by
  change UScalar.mul 5#usize 32#usize = ok 160#usize
  rcases System.Platform.numBits_eq with h | h <;>
    norm_num [UScalar.mul, UScalar.tryMk, UScalar.tryMkOpt,
      UScalar.check_bounds, UScalar.ofNatCore, UScalar.val, h]

private theorem add_5863_160 : 5863#usize + 160#usize = ok 6023#usize := by
  change UScalar.add 5863#usize 160#usize = ok 6023#usize
  rcases System.Platform.numBits_eq with h | h <;>
    norm_num [UScalar.add, UScalar.tryMk, UScalar.tryMkOpt,
      UScalar.check_bounds, UScalar.ofNatCore, UScalar.val, h]

private theorem sub_6423_6023 : 6423#usize - 6023#usize = ok 400#usize := by
  change UScalar.sub 6423#usize 6023#usize = ok 400#usize
  rcases System.Platform.numBits_eq with h | h <;>
    norm_num [UScalar.sub, UScalar.val, h] <;>
    apply UScalar.eq_of_val_eq <;> norm_num [h, UScalar.val]

private theorem cast_u8_4_to_usize :
    UScalar.cast .Usize 4#u8 = 4#usize := by
  apply UScalar.eq_of_val_eq
  rw [UScalar.cast_val_eq]
  rcases System.Platform.numBits_eq with h | h <;> norm_num [h]

namespace AspisV5WirePrefixConstantsExact

theorem header_bytes :
    aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_HEADER_BYTES = 23#usize := by
  simp [aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_HEADER_BYTES]

theorem c1_root_offset :
    aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_C1_ROOT_OFFSET = 23#usize := by
  simp [aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_C1_ROOT_OFFSET,
    aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_HEADER_BYTES]

theorem c2_root_offset :
    aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_C2_ROOT_OFFSET = ok 55#usize := by
  unfold aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_C2_ROOT_OFFSET
    aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_C1_ROOT_OFFSET
    aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_HEADER_BYTES
  exact add_23_32

theorem initial_claim_offset :
    aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_INITIAL_CLAIM_OFFSET = ok 87#usize := by
  unfold aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_INITIAL_CLAIM_OFFSET
    aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_C2_ROOT_OFFSET
    aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_C1_ROOT_OFFSET
    aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_HEADER_BYTES
  simp only [add_23_32, bind_tc_ok]
  exact add_55_32

theorem sumcheck_offset :
    aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_SUMCHECK_OFFSET = ok 103#usize := by
  unfold aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_SUMCHECK_OFFSET
    aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_INITIAL_CLAIM_OFFSET
    aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_C2_ROOT_OFFSET
    aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_C1_ROOT_OFFSET
    aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_HEADER_BYTES
  simp only [add_23_32, bind_tc_ok, add_55_32]
  exact add_87_16

theorem sumcheck_bytes :
    aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_SUMCHECK_BYTES = 4480#usize := by
  simp [aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_SUMCHECK_BYTES]

theorem claims_offset :
    aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_CLAIMS_OFFSET = ok 4583#usize := by
  unfold aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_CLAIMS_OFFSET
    aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_SUMCHECK_OFFSET
    aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_INITIAL_CLAIM_OFFSET
    aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_C2_ROOT_OFFSET
    aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_C1_ROOT_OFFSET
    aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_HEADER_BYTES
    aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_SUMCHECK_BYTES
  simp only [add_23_32, bind_tc_ok, add_55_32, add_87_16]
  exact add_103_4480

theorem total_lanes :
    aspis_prover.v5_mask.spend_messages.V5_TOTAL_LANES = ok 19#usize := by
  unfold aspis_prover.v5_mask.spend_messages.V5_TOTAL_LANES
    aspis_prover.v5_mask.spend_messages.V5_C1_LANES
    aspis_prover.v5_mask.spend_messages.V5_C2_LANES
    aspis_prover.v5_mask.V5_SEMANTIC_C1_LANES
    aspis_prover.v5_cu_envelope.V5_C1_COLUMNS
  exact add_16_3

theorem claims_bytes :
    aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_CLAIMS_BYTES = ok 1216#usize := by
  unfold aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_CLAIMS_BYTES
  rw [total_lanes]
  simp only [mul_4_19, bind_tc_ok]
  exact mul_76_16

theorem terminals_offset :
    aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_TERMINALS_OFFSET = ok 5799#usize := by
  unfold aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_TERMINALS_OFFSET
  rw [claims_offset, claims_bytes]
  exact add_4583_1216

theorem prefix_bytes :
    aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_BYTES = 6423#usize := by
  simp [aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_BYTES]

theorem terminal_bytes :
    aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_TERMINAL_BYTES = ok 48#usize := by
  unfold aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_TERMINAL_BYTES
  exact mul_3_16

theorem inactive_claim_offset :
    aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_INACTIVE_CLAIM_OFFSET = ok 5847#usize := by
  unfold aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_INACTIVE_CLAIM_OFFSET
  rw [terminals_offset, terminal_bytes]
  exact add_5799_48

theorem reserve_offset :
    aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_RESERVE_OFFSET = ok 5863#usize := by
  unfold aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_RESERVE_OFFSET
  rw [inactive_claim_offset]
  exact add_5847_16

theorem pcs_rounds :
    aspis_prover.v5_mask.spend_messages.V5_PCS_ROUNDS = ok 4#usize := by
  unfold aspis_prover.v5_mask.spend_messages.V5_PCS_ROUNDS
    aspis_prover.aspis_core.circle_fri.FIXED_ARITY4_ROUNDS
  simp [cast_u8_4_to_usize]

theorem later_layers :
    aspis_prover.v5_mask.spend_messages.V5_LATER_LAYERS = ok 3#usize := by
  unfold aspis_prover.v5_mask.spend_messages.V5_LATER_LAYERS
  rw [pcs_rounds]
  exact sub_4_1

theorem public_salt_count :
    aspis_prover.v5_mask.real_host_proof.V5_PUBLIC_FS_SALT_COUNT = ok 5#usize := by
  unfold aspis_prover.v5_mask.real_host_proof.V5_PUBLIC_FS_SALT_COUNT
  rw [later_layers]
  exact add_2_3

theorem public_salts_offset :
    aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_PUBLIC_FS_SALTS_OFFSET =
      ok 5863#usize := by
  unfold aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_PUBLIC_FS_SALTS_OFFSET
  exact reserve_offset

theorem public_salts_bytes :
    aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_PUBLIC_FS_SALTS_BYTES =
      ok 160#usize := by
  unfold aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_PUBLIC_FS_SALTS_BYTES
  rw [public_salt_count]
  unfold aspis_prover.v5_mask.real_host_proof.V5_PUBLIC_FS_SALT_BYTES
  exact mul_5_32

theorem zero_reserve_offset :
    aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_ZERO_RESERVE_OFFSET =
      ok 6023#usize := by
  unfold aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_ZERO_RESERVE_OFFSET
  rw [public_salts_offset, public_salts_bytes]
  exact add_5863_160

theorem zero_reserve_bytes :
    aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_ZERO_RESERVE_BYTES = ok 400#usize := by
  unfold aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_ZERO_RESERVE_BYTES
  rw [zero_reserve_offset]
  unfold aspis_prover.v5_mask.real_host_proof.V5_REAL_PREFIX_BYTES
  exact sub_6423_6023

#print axioms header_bytes
#print axioms c1_root_offset
#print axioms c2_root_offset
#print axioms initial_claim_offset
#print axioms sumcheck_offset
#print axioms sumcheck_bytes
#print axioms claims_offset
#print axioms total_lanes
#print axioms claims_bytes
#print axioms terminals_offset
#print axioms prefix_bytes
#print axioms terminal_bytes
#print axioms inactive_claim_offset
#print axioms reserve_offset
#print axioms pcs_rounds
#print axioms later_layers
#print axioms public_salt_count
#print axioms public_salts_offset
#print axioms public_salts_bytes
#print axioms zero_reserve_offset
#print axioms zero_reserve_bytes

end AspisV5WirePrefixConstantsExact

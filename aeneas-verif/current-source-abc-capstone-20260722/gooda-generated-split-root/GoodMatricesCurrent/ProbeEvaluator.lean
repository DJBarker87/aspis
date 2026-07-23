import GoodMatricesCurrent.SourceExtractedTerminalFieldAll
import AspisFormal.V5GoodGateDotBatching

open Aeneas Aeneas.Std Result ControlFlow Error
open aspis_verifier

#check core.convert.num.FromU64U32.from
#check Std.U64.wrapping_mul_val_eq
#check Std.U64.wrapping_add_val_eq
#check Std.Usize.xor
#check UScalar.xor
#check Array.index_usize_spec
#check Array.update_spec
#check GoodMatricesCurrent.SourceExtractedField.authentic_reduce_u64_word_spec
#check GoodMatricesCurrent.SourceExtractedField.local_reduce_u64_exact_spec
#check v5_cu_probe.good_gate_probe.KERNEL_DEGREE
#check core.cmp.min
#check core.cmp.OrdUsize
#check Std.Usize.wrapping_xor
#check Std.Usize.bitxor
#check HBitXor.hXor
#check Std.Array.getElem?_eq_getElem
#check List.getElem_replicate
#check List.getElem_replicate'
#check Fin.prod_univ_succ
#check Fin.prod_univ_castSucc
#check Finset.prod_filter
#check Finset.prod_filter_of_ne
#check Finset.filter_congr_decidable

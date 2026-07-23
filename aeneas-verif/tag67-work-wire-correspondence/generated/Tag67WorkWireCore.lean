-- Normalized from the pinned Aeneas output archived at
-- research-archive-v5-production-closure-2026-07-22.
import Aeneas.Std
import Aeneas.Tactic.RustAttributes

open Aeneas Aeneas.Std Result ControlFlow Error

namespace aspis_verifier

namespace aspis_core.transcript.label

@[global_simps, irreducible, rust_const
  "aspis_core::transcript::label::GRIND_NONCE"]
def GRIND_NONCE : Std.U8 := 5#u8

@[global_simps, irreducible, rust_const
  "aspis_core::transcript::label::M31_CIRCLE_FOLD_POW_NONCE"]
def M31_CIRCLE_FOLD_POW_NONCE : Std.U8 := 20#u8

@[global_simps, irreducible, rust_const
  "aspis_core::transcript::label::M31_PAYMENT_BATCH_POW_NONCE"]
def M31_PAYMENT_BATCH_POW_NONCE : Std.U8 := 28#u8

end aspis_core.transcript.label

namespace v5_cu_probe

@[global_simps, irreducible]
def V5_CU_PROBE_ACCOUNT_MAGIC : Array Std.U8 8#usize :=
  Array.make 8#usize [65#u8, 86#u8, 53#u8, 67#u8, 85#u8, 80#u8, 48#u8, 56#u8]

@[global_simps, irreducible]
def V5_CU_PROBE_RELATION_FINAL_OFFSET_EXACT : Std.Usize := 11048#usize

@[global_simps, irreducible]
def V5_CU_PROBE_BATCH_NONCE_OFFSET_EXACT : Std.Usize := 11080#usize

@[global_simps, irreducible]
def V5_CU_PROBE_FINAL_NONCE_OFFSET_EXACT : Std.Usize := 19127#usize

@[global_simps, irreducible]
def V5_CU_PROBE_QUERY_SELECTOR_OFFSET_EXACT : Std.Usize := 19135#usize

structure V5WorkWireProjection where
  fold_nonces : Array Std.U64 4#usize
  batch_nonce : Std.U64
  final_nonce : Std.U64
  query_selector : Std.U8

def v5_work_wire_magic_is_valid (data : Slice Std.U8) : Result Bool := do
  let i := Slice.len data
  if i >= 8#usize then
    let i1 ← Slice.index_usize data 0#usize
    let i2 ← Array.index_usize V5_CU_PROBE_ACCOUNT_MAGIC 0#usize
    if i1 = i2 then
      let i3 ← Slice.index_usize data 1#usize
      let i4 ← Array.index_usize V5_CU_PROBE_ACCOUNT_MAGIC 1#usize
      if i3 = i4 then
        let i5 ← Slice.index_usize data 2#usize
        let i6 ← Array.index_usize V5_CU_PROBE_ACCOUNT_MAGIC 2#usize
        if i5 = i6 then
          let i7 ← Slice.index_usize data 3#usize
          let i8 ← Array.index_usize V5_CU_PROBE_ACCOUNT_MAGIC 3#usize
          if i7 = i8 then
            let i9 ← Slice.index_usize data 4#usize
            let i10 ← Array.index_usize V5_CU_PROBE_ACCOUNT_MAGIC 4#usize
            if i9 = i10 then
              let i11 ← Slice.index_usize data 5#usize
              let i12 ← Array.index_usize V5_CU_PROBE_ACCOUNT_MAGIC 5#usize
              if i11 = i12 then
                let i13 ← Slice.index_usize data 6#usize
                let i14 ← Array.index_usize V5_CU_PROBE_ACCOUNT_MAGIC 6#usize
                if i13 = i14 then
                  let i15 ← Slice.index_usize data 7#usize
                  let i16 ← Array.index_usize V5_CU_PROBE_ACCOUNT_MAGIC 7#usize
                  ok (i15 = i16)
                else ok false
              else ok false
            else ok false
          else ok false
        else ok false
      else ok false
    else ok false
  else ok false

def v5_work_wire_u64 (data : Slice Std.U8) (offset : Std.Usize) : Result Std.U64 := do
  let i ← Slice.index_usize data offset
  let i1 ← lift (Std.Usize.wrapping_add offset 1#usize)
  let i2 ← Slice.index_usize data i1
  let i3 ← lift (Std.Usize.wrapping_add offset 2#usize)
  let i4 ← Slice.index_usize data i3
  let i5 ← lift (Std.Usize.wrapping_add offset 3#usize)
  let i6 ← Slice.index_usize data i5
  let i7 ← lift (Std.Usize.wrapping_add offset 4#usize)
  let i8 ← Slice.index_usize data i7
  let i9 ← lift (Std.Usize.wrapping_add offset 5#usize)
  let i10 ← Slice.index_usize data i9
  let i11 ← lift (Std.Usize.wrapping_add offset 6#usize)
  let i12 ← Slice.index_usize data i11
  let i13 ← lift (Std.Usize.wrapping_add offset 7#usize)
  let i14 ← Slice.index_usize data i13
  ok (core.num.U64.from_le_bytes
    (Array.make 8#usize [i, i2, i4, i6, i8, i10, i12, i14]))

def project_v5_work_wire (data : Slice Std.U8) : Result V5WorkWireProjection := do
  let i ← v5_work_wire_u64 data V5_CU_PROBE_RELATION_FINAL_OFFSET_EXACT
  let i1 ← lift (Std.Usize.wrapping_add V5_CU_PROBE_RELATION_FINAL_OFFSET_EXACT 8#usize)
  let i2 ← v5_work_wire_u64 data i1
  let i3 ← lift (Std.Usize.wrapping_add V5_CU_PROBE_RELATION_FINAL_OFFSET_EXACT 16#usize)
  let i4 ← v5_work_wire_u64 data i3
  let i5 ← lift (Std.Usize.wrapping_add V5_CU_PROBE_RELATION_FINAL_OFFSET_EXACT 24#usize)
  let i6 ← v5_work_wire_u64 data i5
  let i8 ← v5_work_wire_u64 data V5_CU_PROBE_BATCH_NONCE_OFFSET_EXACT
  let i9 ← v5_work_wire_u64 data V5_CU_PROBE_FINAL_NONCE_OFFSET_EXACT
  let i10 ← Slice.index_usize data V5_CU_PROBE_QUERY_SELECTOR_OFFSET_EXACT
  ok {
    fold_nonces := Array.make 4#usize [i, i2, i4, i6]
    batch_nonce := i8
    final_nonce := i9
    query_selector := i10
  }

def v5_batch_work_difficulty : Result Std.U8 := ok 37#u8

def v5_fold_work_difficulty (round : Std.Usize) : Result (Option Std.U8) := do
  match round.val with
  | 0 => ok (some 34#u8)
  | 1 => ok (some 33#u8)
  | 2 => ok (some 30#u8)
  | 3 => ok (some 25#u8)
  | _ => ok none

def v5_final_work_difficulty : Result Std.U8 := ok 32#u8

def v5_fold_work_record
    (round : Std.Usize) (nonce : Std.U64) : Result (Array Std.U8 9#usize) := do
  let bytes ← lift (core.num.U64.to_le_bytes nonce)
  let i ← lift (UScalar.cast .U8 round)
  let i1 ← Array.index_usize bytes 0#usize
  let i2 ← Array.index_usize bytes 1#usize
  let i3 ← Array.index_usize bytes 2#usize
  let i4 ← Array.index_usize bytes 3#usize
  let i5 ← Array.index_usize bytes 4#usize
  let i6 ← Array.index_usize bytes 5#usize
  let i7 ← Array.index_usize bytes 6#usize
  let i8 ← Array.index_usize bytes 7#usize
  ok (Array.make 9#usize [i, i1, i2, i3, i4, i5, i6, i7, i8])

def v5_batch_work_record (nonce : Std.U64) : Result (Array Std.U8 8#usize) :=
  ok (core.num.U64.to_le_bytes nonce)

def v5_final_work_record (nonce : Std.U64) : Result (Array Std.U8 8#usize) :=
  ok (core.num.U64.to_le_bytes nonce)

def v5_fold_work_absorb_input
    (round : Std.Usize) (nonce : Std.U64) :
    Result (Std.U8 × Array Std.U8 9#usize) := do
  let record ← v5_fold_work_record round nonce
  ok (aspis_core.transcript.label.M31_CIRCLE_FOLD_POW_NONCE, record)

def v5_batch_work_absorb_input
    (nonce : Std.U64) : Result (Std.U8 × Array Std.U8 8#usize) := do
  let record ← v5_batch_work_record nonce
  ok (aspis_core.transcript.label.M31_PAYMENT_BATCH_POW_NONCE, record)

def v5_final_work_absorb_input
    (nonce : Std.U64) : Result (Std.U8 × Array Std.U8 8#usize) := do
  let record ← v5_final_work_record nonce
  ok (aspis_core.transcript.label.GRIND_NONCE, record)

def v5_relation_final_zero_tail_is_valid_loop.body
    (relationFinal : Slice Std.U8) (offset : Std.Usize) :
    Result (ControlFlow Std.Usize Bool) := do
  if offset < 64#usize then
    let i ← Slice.index_usize relationFinal offset
    if i != 0#u8 then ok (done false)
    else
      let offset1 ← lift (Std.Usize.wrapping_add offset 1#usize)
      ok (cont offset1)
  else ok (done true)

def v5_relation_final_zero_tail_is_valid_loop
    (relationFinal : Slice Std.U8) (offset : Std.Usize) : Result Bool := do
  loop (fun offset1 =>
    v5_relation_final_zero_tail_is_valid_loop.body relationFinal offset1) offset

def v5_relation_final_zero_tail_is_valid
    (relationFinal : Slice Std.U8) : Result Bool := do
  let i := Slice.len relationFinal
  if i != 64#usize then ok false
  else v5_relation_final_zero_tail_is_valid_loop relationFinal 40#usize

def v5_query_selector_is_valid (selected : Std.U8) : Result Bool :=
  ok (selected < 3#u8)

end v5_cu_probe

end aspis_verifier

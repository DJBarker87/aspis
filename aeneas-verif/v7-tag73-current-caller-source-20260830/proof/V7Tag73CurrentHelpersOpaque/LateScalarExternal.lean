import V7Tag73CurrentHelpersOpaque.FunsExternal

open Aeneas Aeneas.Std Result ControlFlow Error

def core.num.trailingZerosNat : Nat → Nat → Nat
  | _, 0 => 0
  | value, fuel + 1 =>
    if value % 2 = 0 then 1 + core.num.trailingZerosNat (value / 2) fuel
    else 0

@[rust_fun "core::num::{u16}::trailing_zeros"]
def core.num.U16.trailing_zeros (value : Std.U16) : Result Std.U32 :=
  .ok ⟨BitVec.ofNat 32 (core.num.trailingZerosNat value.bv.toNat 16)⟩

@[rust_fun "core::num::{u64}::trailing_zeros"]
def core.num.U64.trailing_zeros (value : Std.U64) : Result Std.U32 :=
  .ok ⟨BitVec.ofNat 32 (core.num.trailingZerosNat value.bv.toNat 64)⟩

@[rust_fun "core::num::{u64}::count_ones"]
def core.num.U64.count_ones (value : Std.U64) : Result Std.U32 :=
  .ok ⟨value.bv.cpop.zeroExtend 32⟩

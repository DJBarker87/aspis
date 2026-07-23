-- Normalized from the pinned Aeneas output archived at
-- research-archive-v5-production-closure-2026-07-22.
import Aeneas.Std
import Aeneas.Tactic.RustAttributes

open Aeneas Aeneas.Std Result ControlFlow Error

namespace aspis_core

def transcript.digest_has_leading_zero_bits
  (digest : Array Std.U8 32#usize) (bits : Std.U8) : Result Bool := do
  if bits = 0#u8
  then ok true
  else
    let i ← Array.index_usize digest 0#usize
    let i1 ← Array.index_usize digest 1#usize
    let i2 ← Array.index_usize digest 2#usize
    let i3 ← Array.index_usize digest 3#usize
    let i4 ← Array.index_usize digest 4#usize
    let i5 ← Array.index_usize digest 5#usize
    let i6 ← Array.index_usize digest 6#usize
    let i7 ← Array.index_usize digest 7#usize
    let head ←
      lift (core.num.U64.from_be_bytes
        (Array.make 8#usize [i, i1, i2, i3, i4, i5, i6, i7]))
    let i8 ← lift (UScalar.cast .U32 bits)
    let i9 ← lift (Std.U32.wrapping_sub 64#u32 i8)
    let i10 ← lift (Std.U64.wrapping_shl 1#u64 i9)
    ok (head < i10)

end aspis_core

import V5OpeningAssembly.Funs

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V5OpeningAssemblyProof

open V5OpeningAssemblyGenerated

abbrev Opening :=
  V5OpeningAssemblyGenerated.aspis_core.state_only_private_openings.StateOnlyPrivateOpening

/-- The extracted final assembly step preserves every parser result, the four
index arrays, the consumed-byte calculation, and the exact returned remainder. -/
theorem assemble_v5_private_openings_exact
    (parsed : Array (Option Opening) 5#usize)
    (indices :
      V5OpeningAssemblyGenerated.aspis_core.circle_line_merkle.CircleLineQueryIndices)
    (proofBytesLen : Std.Usize) (remainder : Slice Std.U8)
    (c1 c2 later0 later1 later2 : Opening)
    (h0 : Array.index_usize parsed 0#usize = ok (some c1))
    (h1 : Array.index_usize parsed 1#usize = ok (some c2))
    (h2 : Array.index_usize parsed 2#usize = ok (some later0))
    (h3 : Array.index_usize parsed 3#usize = ok (some later1))
    (h4 : Array.index_usize parsed 4#usize = ok (some later2)) :
    V5OpeningAssemblyGenerated.private_openings.assemble_v5_private_openings
        parsed indices proofBytesLen remainder =
      ok
        ({
          c1 := c1
          c2 := c2
          later := Array.make 3#usize [later0, later1, later2]
          indices := indices
          bytes_consumed :=
            Std.Usize.wrapping_sub proofBytesLen (Slice.len remainder)
        }, remainder) := by
  unfold V5OpeningAssemblyGenerated.private_openings.assemble_v5_private_openings
  simp [h0, h1, h2, h3, h4, core.option.Option.unwrap, Std.lift]

#print axioms assemble_v5_private_openings_exact

end V5OpeningAssemblyProof

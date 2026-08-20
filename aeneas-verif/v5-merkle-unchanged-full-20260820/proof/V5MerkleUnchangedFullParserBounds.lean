import V5MerkleUnchangedFullRadixCompat
import V5MerkleUnchangedFullParserBridge

/-! Machine-word room implied by a successful released opening parse. -/

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisV5MerkleUnchangedFullParserBounds

open V5MerkleUnchangedCompat
variable [HashContext]

open V5MerkleUnchangedFull
open AspisV5MerkleUnchangedFullParserBridge

/-- Once the fixed record prefix is at least one digest wide, the parser's
checked end offset leaves enough machine-word room for every subsequent
32-byte frontier read.  This avoids assuming a runtime allocation limit. -/
theorem raw_parser_frontier_has_digest_room
    (proofBytes : Slice Std.U8) (expectedCount valueWidth : Std.Usize)
    (opening : aspis_core.state_only_private_openings.StateOnlyPrivateOpening)
    (remainder : Slice Std.U8)
    (raw : ExactRawParserOutput proofBytes expectedCount valueWidth opening
      remainder)
    (prefixRoom : 32 ≤
      2 + expectedCount.val * (valueWidth.val + 32) + 4) :
    opening.frontier.val.length + 32 < UScalar.size .Usize := by
  rcases raw with ⟨frontierCount, hcount, hwidth, hcountOffset,
    hrecordsOffset, hrecords, hrecordsLength, hfrontierCountOffset,
    hfrontierOffset, hfrontier, hfrontierLength, hend, hendBound,
    hremainder⟩
  have hproofBound : proofBytes.val.length ≤ Std.Usize.max := by
    exact proofBytes.property
  have hendMax :
      2 + expectedCount.val * (valueWidth.val + 32) + 4 +
        frontierCount * 32 ≤ Std.Usize.max := by
    rw [← hend]
    exact hendBound.trans hproofBound
  have hroomMax : opening.frontier.val.length + 32 ≤ Std.Usize.max := by
    rw [hfrontierLength]
    omega
  apply lt_of_le_of_lt hroomMax
  rcases System.Platform.numBits_eq with hbits | hbits
  · norm_num [UScalar.size, Usize.size, Usize.max, Usize.numBits, hbits]
  · norm_num [UScalar.size, Usize.size, Usize.max, Usize.numBits, hbits]

/-- All released calls have 18 records, so their record prefix is much wider
than the 32 bytes required by `raw_parser_frontier_has_digest_room`. -/
theorem released_raw_parser_frontier_has_digest_room
    (proofBytes : Slice Std.U8) (expectedCount valueWidth : Std.Usize)
    (opening : aspis_core.state_only_private_openings.StateOnlyPrivateOpening)
    (remainder : Slice Std.U8)
    (raw : ExactRawParserOutput proofBytes expectedCount valueWidth opening
      remainder)
    (queryCount : expectedCount.val = 18) :
    opening.frontier.val.length + 32 < UScalar.size .Usize := by
  apply raw_parser_frontier_has_digest_room proofBytes expectedCount valueWidth
    opening remainder raw
  rw [queryCount]
  omega

#print axioms raw_parser_frontier_has_digest_room
#print axioms released_raw_parser_frontier_has_digest_room

end AspisV5MerkleUnchangedFullParserBounds

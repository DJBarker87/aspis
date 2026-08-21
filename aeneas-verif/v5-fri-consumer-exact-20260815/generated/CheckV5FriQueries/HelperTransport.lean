import CheckV5FriQueries.Types
import FriArithmetic.Funs
import AspisCoreCm31Multiplicative
import V5FriByteDecoderSource.Funs
import V5FriHelperTransparent.Funs

open Aeneas Aeneas.Std Result ControlFlow Error

namespace V5FriConsumerExact.HelperTransport

namespace Consumer

abbrev M31 := V5FriConsumerExact.aspis_core.field.M31
abbrev CM31 := V5FriConsumerExact.aspis_core.field.CM31
abbrev QM31 := V5FriConsumerExact.aspis_core.field.QM31
abbrev Prepared :=
  V5FriConsumerExact.aspis_core.field.PreparedQm31Multiplier
abbrev FoldDenominator :=
  V5FriConsumerExact.aspis_core.circle_fri.FoldDenominator
abbrev CircleFriError :=
  V5FriConsumerExact.aspis_core.circle_fri.CircleFriError
abbrev CircleQueryLeaf :=
  V5FriConsumerExact.aspis_core.circle_query.CircleQueryLeaf
abbrev CircleQueryError :=
  V5FriConsumerExact.aspis_core.circle_query.CircleQueryError

end Consumer

namespace Arithmetic

abbrev CM31 := V5FriArithmeticExact.field.CM31
abbrev QM31 := V5FriArithmeticExact.field.QM31
abbrev Prepared := V5FriArithmeticExact.field.PreparedQm31Multiplier
abbrev FoldDenominator := V5FriArithmeticExact.circle_fri.FoldDenominator
abbrev CircleFriError := V5FriArithmeticExact.circle_fri.CircleFriError
abbrev CircleQueryLeaf := V5FriArithmeticExact.circle_query.CircleQueryLeaf
abbrev CircleQueryError := V5FriArithmeticExact.circle_query.CircleQueryError

end Arithmetic

namespace Multiplicative

abbrev CM31 := AspisCoreCM31Multiplicative.field.CM31
abbrev QM31 := AspisCoreCM31Multiplicative.field.QM31
abbrev Prepared :=
  AspisCoreCM31Multiplicative.field.PreparedQm31Multiplier

end Multiplicative

namespace Source

abbrev M31 := V5FriHelperTransparent.aspis_core.field.M31
abbrev CM31 := V5FriHelperTransparent.aspis_core.field.CM31
abbrev QM31 := V5FriHelperTransparent.aspis_core.field.QM31
abbrev Prepared :=
  V5FriHelperTransparent.aspis_core.field.PreparedQm31Multiplier
abbrev FoldDenominator :=
  V5FriHelperTransparent.aspis_core.circle_fri.FoldDenominator
abbrev CircleFriError :=
  V5FriHelperTransparent.aspis_core.circle_fri.CircleFriError
abbrev CircleQueryLeaf :=
  V5FriHelperTransparent.aspis_core.circle_query.CircleQueryLeaf
abbrev CircleQueryError :=
  V5FriHelperTransparent.aspis_core.circle_query.CircleQueryError

end Source

namespace Decoder

abbrev CM31 := V5FriByteDecoderSource.aspis_core.field.CM31
abbrev QM31 := V5FriByteDecoderSource.aspis_core.field.QM31

end Decoder

def mapResult {A B : Type} (f : A → B) : Result A → Result B
  | .fail error => .fail error
  | .div => .div
  | .ok value => .ok (f value)

def mapArray {A B : Type} {N : Std.Usize} (f : A → B)
    (values : Array A N) : Array B N :=
  ⟨values.val.map f, by simpa using values.property⟩

def toArithmeticCM31 (value : Consumer.CM31) : Arithmetic.CM31 :=
  ⟨value.a, value.b⟩

def fromArithmeticCM31 (value : Arithmetic.CM31) : Consumer.CM31 :=
  ⟨value.a, value.b⟩

def toArithmeticQM31 (value : Consumer.QM31) : Arithmetic.QM31 :=
  ⟨toArithmeticCM31 value.c0, toArithmeticCM31 value.c1⟩

def fromArithmeticQM31 (value : Arithmetic.QM31) : Consumer.QM31 :=
  ⟨fromArithmeticCM31 value.c0, fromArithmeticCM31 value.c1⟩

def toArithmeticPrepared (value : Consumer.Prepared) : Arithmetic.Prepared :=
  ⟨value.components⟩

def toMultiplicativeCM31 (value : Consumer.CM31) : Multiplicative.CM31 :=
  ⟨value.a, value.b⟩

def fromMultiplicativeCM31 (value : Multiplicative.CM31) : Consumer.CM31 :=
  ⟨value.a, value.b⟩

def toMultiplicativeQM31 (value : Consumer.QM31) : Multiplicative.QM31 :=
  ⟨toMultiplicativeCM31 value.c0, toMultiplicativeCM31 value.c1⟩

def fromMultiplicativeQM31 (value : Multiplicative.QM31) : Consumer.QM31 :=
  ⟨fromMultiplicativeCM31 value.c0, fromMultiplicativeCM31 value.c1⟩

def fromMultiplicativePrepared
    (value : Multiplicative.Prepared) : Consumer.Prepared :=
  ⟨value.components⟩

def toSourceCM31 (value : Consumer.CM31) : Source.CM31 :=
  ⟨value.a, value.b⟩

def fromSourceCM31 (value : Source.CM31) : Consumer.CM31 :=
  ⟨value.a, value.b⟩

def toSourceQM31 (value : Consumer.QM31) : Source.QM31 :=
  ⟨toSourceCM31 value.c0, toSourceCM31 value.c1⟩

def fromSourceQM31 (value : Source.QM31) : Consumer.QM31 :=
  ⟨fromSourceCM31 value.c0, fromSourceCM31 value.c1⟩

def fromDecoderCM31 (value : Decoder.CM31) : Consumer.CM31 :=
  ⟨value.a, value.b⟩

def fromDecoderQM31 (value : Decoder.QM31) : Consumer.QM31 :=
  ⟨fromDecoderCM31 value.c0, fromDecoderCM31 value.c1⟩

def toSourcePrepared (value : Consumer.Prepared) : Source.Prepared :=
  ⟨value.components⟩

def fromSourcePrepared (value : Source.Prepared) : Consumer.Prepared :=
  ⟨value.components⟩

def fromArithmeticFoldDenominator :
    Arithmetic.FoldDenominator → Consumer.FoldDenominator
  | .CircleY => .CircleY
  | .CircleX => .CircleX
  | .LineFirstPairX => .LineFirstPairX
  | .LineSecondPairX => .LineSecondPairX
  | .LineSecondFoldX => .LineSecondFoldX

def fromArithmeticCircleFriError :
    Arithmetic.CircleFriError → Consumer.CircleFriError
  | .CircleIndexOutOfRange => .CircleIndexOutOfRange
  | .CircleFiberOutOfRange => .CircleFiberOutOfRange
  | .InvalidLineLayer => .InvalidLineLayer
  | .InvalidLineFoldLayer => .InvalidLineFoldLayer
  | .LineIndexOutOfRange => .LineIndexOutOfRange
  | .LineFiberOutOfRange => .LineFiberOutOfRange
  | .QueryOutOfRange => .QueryOutOfRange
  | .InvalidBitReverseLength => .InvalidBitReverseLength
  | .BitReverseIndexOutOfRange => .BitReverseIndexOutOfRange
  | .ZeroDenominator denominator =>
      .ZeroDenominator (fromArithmeticFoldDenominator denominator)
  | .InvalidInverseBackend => .InvalidInverseBackend

def fromArithmeticCircleQueryLeaf :
    Arithmetic.CircleQueryLeaf → Consumer.CircleQueryLeaf
  | .C1 => .C1
  | .C2 => .C2
  | .Later layer => .Later layer

def fromArithmeticCircleQueryError :
    Arithmetic.CircleQueryError → Consumer.CircleQueryError
  | .QueryOutOfRange query => .QueryOutOfRange query
  | .LeafLength leaf expected actual =>
      .LeafLength (fromArithmeticCircleQueryLeaf leaf) expected actual
  | .NonCanonicalM31 offset => .NonCanonicalM31 offset
  | .NonCanonicalQm31 leaf offset =>
      .NonCanonicalQm31 (fromArithmeticCircleQueryLeaf leaf) offset
  | .C1KernelInvariant => .C1KernelInvariant
  | .LayerValueMismatch layer offset => .LayerValueMismatch layer offset
  | .TerminalValueMismatch index => .TerminalValueMismatch index
  | .Fold error => .Fold (fromArithmeticCircleFriError error)

def fromArithmeticQueryResult :
    core.result.Result Unit Arithmetic.CircleQueryError →
      core.result.Result Unit Consumer.CircleQueryError
  | .Ok unit => .Ok unit
  | .Err error => .Err (fromArithmeticCircleQueryError error)

def fromSourceFoldDenominator :
    Source.FoldDenominator → Consumer.FoldDenominator
  | .CircleY => .CircleY
  | .CircleX => .CircleX
  | .LineFirstPairX => .LineFirstPairX
  | .LineSecondPairX => .LineSecondPairX
  | .LineSecondFoldX => .LineSecondFoldX

def fromSourceCircleFriError :
    Source.CircleFriError → Consumer.CircleFriError
  | .CircleIndexOutOfRange => .CircleIndexOutOfRange
  | .CircleFiberOutOfRange => .CircleFiberOutOfRange
  | .InvalidLineLayer => .InvalidLineLayer
  | .InvalidLineFoldLayer => .InvalidLineFoldLayer
  | .LineIndexOutOfRange => .LineIndexOutOfRange
  | .LineFiberOutOfRange => .LineFiberOutOfRange
  | .QueryOutOfRange => .QueryOutOfRange
  | .InvalidBitReverseLength => .InvalidBitReverseLength
  | .BitReverseIndexOutOfRange => .BitReverseIndexOutOfRange
  | .ZeroDenominator denominator =>
      .ZeroDenominator (fromSourceFoldDenominator denominator)
  | .InvalidInverseBackend => .InvalidInverseBackend

def fromSourceCircleQueryLeaf :
    Source.CircleQueryLeaf → Consumer.CircleQueryLeaf
  | .C1 => .C1
  | .C2 => .C2
  | .Later layer => .Later layer

def fromSourceCircleQueryError :
    Source.CircleQueryError → Consumer.CircleQueryError
  | .QueryOutOfRange query => .QueryOutOfRange query
  | .LeafLength leaf expected actual =>
      .LeafLength (fromSourceCircleQueryLeaf leaf) expected actual
  | .NonCanonicalM31 offset => .NonCanonicalM31 offset
  | .NonCanonicalQm31 leaf offset =>
      .NonCanonicalQm31 (fromSourceCircleQueryLeaf leaf) offset
  | .C1KernelInvariant => .C1KernelInvariant
  | .LayerValueMismatch layer offset => .LayerValueMismatch layer offset
  | .TerminalValueMismatch index => .TerminalValueMismatch index
  | .Fold error => .Fold (fromSourceCircleFriError error)

def fromSourceQueryResult :
    core.result.Result Unit Source.CircleQueryError →
      core.result.Result Unit Consumer.CircleQueryError
  | .Ok unit => .Ok unit
  | .Err error => .Err (fromSourceCircleQueryError error)

/-- The consumer extraction left this production call external.  Reuse the
independent Charon/Aeneas extraction of the same unchanged Rust decoder and
transport only its duplicate record type. -/
def fromLeBytes (bytes : Slice Std.U8) : Result (Option Consumer.QM31) :=
  mapResult (Option.map fromDecoderQM31)
    (V5FriByteDecoderSource.aspis_core.field.QM31.from_le_bytes bytes)

def square (input : Consumer.QM31) : Result Consumer.QM31 :=
  mapResult fromSourceQM31
    (V5FriHelperTransparent.square (toSourceQM31 input))

def mul (left right : Consumer.QM31) : Result Consumer.QM31 :=
  mapResult fromSourceQM31
    (V5FriHelperTransparent.mul
      (toSourceQM31 left) (toSourceQM31 right))

def preparedNew (input : Consumer.QM31) : Result Consumer.Prepared :=
  mapResult fromSourcePrepared
    (V5FriHelperTransparent.prepare (toSourceQM31 input))

def circle (values : Array Consumer.QM31 4#usize)
    (alphaPowers : Array Consumer.Prepared 3#usize)
    (inv2x inv2y : Consumer.M31) : Result Consumer.QM31 :=
  mapResult fromSourceQM31
    (V5FriHelperTransparent.circle
      (mapArray toSourceQM31 values)
      (mapArray toSourcePrepared alphaPowers) inv2x inv2y)

def line (incoming outgoing : Slice Std.U8) (index : Std.Usize)
    (layer : Std.U8) (inverses : Array Consumer.M31 3#usize)
    (alphaPowers : Array Consumer.Prepared 3#usize) :
    Result (core.result.Result Unit Consumer.CircleQueryError) :=
  mapResult fromSourceQueryResult
    (V5FriHelperTransparent.line
      incoming outgoing index layer inverses
      (mapArray toSourcePrepared alphaPowers))

def terminal (incoming : Slice Std.U8)
    (finalPolynomial : Array Consumer.QM31 4#usize) (index : Std.Usize)
    (inverses : Array Consumer.M31 3#usize) (finalX : Consumer.M31)
    (alphaPowers : Array Consumer.Prepared 3#usize) :
    Result (core.result.Result Unit Consumer.CircleQueryError) :=
  mapResult fromSourceQueryResult
    (V5FriHelperTransparent.terminal
      incoming (mapArray toSourceQM31 finalPolynomial) index inverses
      finalX (mapArray toSourcePrepared alphaPowers))

end V5FriConsumerExact.HelperTransport

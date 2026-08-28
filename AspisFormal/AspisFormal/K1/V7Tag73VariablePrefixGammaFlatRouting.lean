import AspisFormal.K1.V7Tag73VariablePrefixGammaFactorization

/-!
# Adaptive flat-to-routed coordinates for the variable-prefix gamma sampler

The chronological production tape has twelve possible squeeze outputs.  A
reached ordinary call consumes between one and four of those blocks, and the
next call begins immediately afterwards.  The routed representation instead
stores every reached call in a four-block window.  This file gives the honest
adaptive coordinate permutations: padding for reached windows is taken only
from the unread suffix, and windows after the stopping call remain arbitrary.

Output and duplex-advance digests are moved by the same permutation.  No
unreached ordinary window is required to decode.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace AspisK1.V7Tag73VariablePrefixGammaFlatRouting

open AspisK1.V7Tag73TranscriptSchedule
open AspisK1.V7Tag73SamplerDecoder
open AspisK1.V7Tag73SamplerDecoderExact
open AspisK1.V7Tag73SamplerExactValue
open AspisK1.V7Tag73SecureCircleMap
open AspisK1.V7Tag73IncrementalSamplerControl
open AspisK1.V7Tag73DeployedDecoderFiberCap
open AspisK1.V7Tag73EightRetryDecoderBridge
open AspisK1.V7Tag73EightRetrySamplerLaw
open AspisK1.V7Tag73RawNonzeroSamplerLaw
open AspisK1.V7Tag73RawNonzeroSamplerFactorization
open AspisK1.V7Tag73VariablePrefixGammaSampler
open AspisK1.V7Tag73VariablePrefixGammaFactorization
open AspisV5ComponentCRejectionSampler
open AspisV5ComponentCStoppingTimeSampler
open AspisV5ComponentCQM31TowerExact

noncomputable section

/-! ## Branch-specific coordinate permutations -/

/-- Fixed four-block windows, in attempt-major order, have twelve coordinates. -/
def threeByFourIndexEquiv : Fin 3 × Fin 4 ≃ Fin 12 :=
  finProdFinEquiv.trans (finCongr (by norm_num))

/-- If the first call stops, fixed four-block chunking is already the correct
routing. -/
def stop0IndexEquiv : Fin 3 × Fin 4 ≃ Fin 12 :=
  threeByFourIndexEquiv

/-- Coordinate routing when the first call consumes `firstUsed` blocks and
the second consumes `secondUsed`.  The original chronological order is

`C0 ++ C1 ++ P0 ++ P1 ++ later`,

and routed order is `C0 ++ P0 ++ C1 ++ P1 ++ later`.
-/
def stop1ToIndex (firstUsed secondUsed : Nat)
    (firstPositive : 0 < firstUsed) (firstBound : firstUsed ≤ 4)
    (secondPositive : 0 < secondUsed) (secondBound : secondUsed ≤ 4)
    (coordinate : Fin 3 × Fin 4) : Fin 12 := by
  if attemptZero : coordinate.1.val = 0 then
    exact if before : coordinate.2.val < firstUsed then
      ⟨coordinate.2.val, by omega⟩
    else
      ⟨secondUsed + coordinate.2.val, by omega⟩
  else if attemptOne : coordinate.1.val = 1 then
    exact if before : coordinate.2.val < secondUsed then
      ⟨firstUsed + coordinate.2.val, by omega⟩
    else
      ⟨4 + coordinate.2.val, by omega⟩
  else
    exact ⟨8 + coordinate.2.val, by omega⟩

@[simp] theorem stop1ToIndex_val (firstUsed secondUsed : Nat)
    (firstPositive : 0 < firstUsed) (firstBound : firstUsed ≤ 4)
    (secondPositive : 0 < secondUsed) (secondBound : secondUsed ≤ 4)
    (coordinate : Fin 3 × Fin 4) :
    (stop1ToIndex firstUsed secondUsed firstPositive firstBound
      secondPositive secondBound coordinate).val =
      if coordinate.1.val = 0 then
        if coordinate.2.val < firstUsed then coordinate.2.val
        else secondUsed + coordinate.2.val
      else if coordinate.1.val = 1 then
        if coordinate.2.val < secondUsed then firstUsed + coordinate.2.val
        else 4 + coordinate.2.val
      else 8 + coordinate.2.val := by
  simp only [stop1ToIndex]
  split_ifs <;> rfl

def stop1FromIndex (firstUsed secondUsed : Nat)
    (firstPositive : 0 < firstUsed) (firstBound : firstUsed ≤ 4)
    (secondPositive : 0 < secondUsed) (secondBound : secondUsed ≤ 4)
    (coordinate : Fin 12) : Fin 3 × Fin 4 := by
  if first : coordinate.val < firstUsed then
    exact (0, ⟨coordinate.val, by omega⟩)
  else if second : coordinate.val < firstUsed + secondUsed then
    exact (1, ⟨coordinate.val - firstUsed, by omega⟩)
  else if firstPadding : coordinate.val < secondUsed + 4 then
    exact (0, ⟨coordinate.val - secondUsed, by omega⟩)
  else if secondPadding : coordinate.val < 8 then
    exact (1, ⟨coordinate.val - 4, by omega⟩)
  else
    exact (2, ⟨coordinate.val - 8, by omega⟩)

def stop1IndexEquiv (firstUsed secondUsed : Nat)
    (firstPositive : 0 < firstUsed) (firstBound : firstUsed ≤ 4)
    (secondPositive : 0 < secondUsed) (secondBound : secondUsed ≤ 4) :
    Fin 3 × Fin 4 ≃ Fin 12 where
  toFun := stop1ToIndex firstUsed secondUsed firstPositive firstBound
    secondPositive secondBound
  invFun := stop1FromIndex firstUsed secondUsed firstPositive firstBound
    secondPositive secondBound
  left_inv coordinate := by
    rcases coordinate with ⟨attempt, block⟩
    fin_cases attempt
    · by_cases before : block.val < firstUsed
      · have routedValue :
            (stop1ToIndex firstUsed secondUsed firstPositive firstBound
              secondPositive secondBound (0, block)).val = block.val := by
          simp [stop1ToIndex, before]
        change stop1FromIndex firstUsed secondUsed firstPositive firstBound
            secondPositive secondBound
            (stop1ToIndex firstUsed secondUsed firstPositive firstBound
              secondPositive secondBound (0, block)) = (0, block)
        apply Prod.ext <;> apply Fin.ext <;>
          simp only [stop1FromIndex] <;> simp [routedValue, before]
      · have routedValue :
            (stop1ToIndex firstUsed secondUsed firstPositive firstBound
              secondPositive secondBound (0, block)).val =
                secondUsed + block.val := by
          simp [stop1ToIndex, before]
        change stop1FromIndex firstUsed secondUsed firstPositive firstBound
            secondPositive secondBound
            (stop1ToIndex firstUsed secondUsed firstPositive firstBound
              secondPositive secondBound (0, block)) = (0, block)
        apply Prod.ext <;> apply Fin.ext <;>
          simp only [stop1FromIndex] <;> simp [routedValue] <;>
          split_ifs <;> simp <;> omega
    · by_cases before : block.val < secondUsed
      · have routedValue :
            (stop1ToIndex firstUsed secondUsed firstPositive firstBound
              secondPositive secondBound (1, block)).val =
                firstUsed + block.val := by
          simp [stop1ToIndex, before]
        change stop1FromIndex firstUsed secondUsed firstPositive firstBound
            secondPositive secondBound
            (stop1ToIndex firstUsed secondUsed firstPositive firstBound
              secondPositive secondBound (1, block)) = (1, block)
        apply Prod.ext <;> apply Fin.ext <;>
          simp only [stop1FromIndex] <;> simp [routedValue] <;>
          split_ifs <;> simp <;> omega
      · have routedValue :
            (stop1ToIndex firstUsed secondUsed firstPositive firstBound
              secondPositive secondBound (1, block)).val = 4 + block.val := by
          simp [stop1ToIndex, before]
        change stop1FromIndex firstUsed secondUsed firstPositive firstBound
            secondPositive secondBound
            (stop1ToIndex firstUsed secondUsed firstPositive firstBound
              secondPositive secondBound (1, block)) = (1, block)
        apply Prod.ext <;> apply Fin.ext <;>
          simp only [stop1FromIndex] <;> simp [routedValue] <;>
          split_ifs <;> simp <;> omega
    · have routedValue :
          (stop1ToIndex firstUsed secondUsed firstPositive firstBound
            secondPositive secondBound (2, block)).val = 8 + block.val := by
        simp [stop1ToIndex]
      change stop1FromIndex firstUsed secondUsed firstPositive firstBound
          secondPositive secondBound
          (stop1ToIndex firstUsed secondUsed firstPositive firstBound
            secondPositive secondBound (2, block)) = (2, block)
      apply Prod.ext <;> apply Fin.ext <;>
        simp only [stop1FromIndex] <;> simp [routedValue] <;>
        split_ifs <;> simp <;> omega
  right_inv coordinate := by
    change stop1ToIndex firstUsed secondUsed firstPositive firstBound
        secondPositive secondBound
        (stop1FromIndex firstUsed secondUsed firstPositive firstBound
          secondPositive secondBound coordinate) = coordinate
    by_cases first : coordinate.val < firstUsed
    · have unrouted : stop1FromIndex firstUsed secondUsed firstPositive
          firstBound secondPositive secondBound coordinate =
            (0, ⟨coordinate.val, by omega⟩) := by
        simp [stop1FromIndex, first]
      rw [unrouted]
      apply Fin.ext
      rw [stop1ToIndex_val]
      simp [first]
    · by_cases second : coordinate.val < firstUsed + secondUsed
      · have unrouted : stop1FromIndex firstUsed secondUsed firstPositive
            firstBound secondPositive secondBound coordinate =
              (1, ⟨coordinate.val - firstUsed, by omega⟩) := by
          simp [stop1FromIndex, first, second]
        rw [unrouted]
        apply Fin.ext
        rw [stop1ToIndex_val]
        simp
        split_ifs <;> omega
      · by_cases firstPadding : coordinate.val < secondUsed + 4
        · have unrouted : stop1FromIndex firstUsed secondUsed firstPositive
              firstBound secondPositive secondBound coordinate =
                (0, ⟨coordinate.val - secondUsed, by omega⟩) := by
            simp [stop1FromIndex, first, second, firstPadding]
          rw [unrouted]
          apply Fin.ext
          rw [stop1ToIndex_val]
          simp
          split_ifs <;> omega
        · by_cases secondPadding : coordinate.val < 8
          · have unrouted : stop1FromIndex firstUsed secondUsed firstPositive
                firstBound secondPositive secondBound coordinate =
                  (1, ⟨coordinate.val - 4, by omega⟩) := by
              simp [stop1FromIndex, first, second, firstPadding, secondPadding]
            rw [unrouted]
            apply Fin.ext
            rw [stop1ToIndex_val]
            simp
            split_ifs <;> omega
          · have unrouted : stop1FromIndex firstUsed secondUsed firstPositive
                firstBound secondPositive secondBound coordinate =
                  (2, ⟨coordinate.val - 8, by omega⟩) := by
              simp [stop1FromIndex, first, second, firstPadding, secondPadding]
            rw [unrouted]
            apply Fin.ext
            rw [stop1ToIndex_val]
            simp
            omega

/-- Coordinate routing when all three calls are reached.  Chronological order
is `C0 ++ C1 ++ C2 ++ P0 ++ P1 ++ P2`, while routed order is
`C0 ++ P0 ++ C1 ++ P1 ++ C2 ++ P2`.
-/
def stop2ToIndex (firstUsed secondUsed thirdUsed : Nat)
    (firstPositive : 0 < firstUsed) (firstBound : firstUsed ≤ 4)
    (secondPositive : 0 < secondUsed) (secondBound : secondUsed ≤ 4)
    (thirdPositive : 0 < thirdUsed) (thirdBound : thirdUsed ≤ 4)
    (coordinate : Fin 3 × Fin 4) : Fin 12 := by
  if attemptZero : coordinate.1.val = 0 then
    exact if before : coordinate.2.val < firstUsed then
      ⟨coordinate.2.val, by omega⟩
    else
      ⟨secondUsed + thirdUsed + coordinate.2.val, by omega⟩
  else if attemptOne : coordinate.1.val = 1 then
    exact if before : coordinate.2.val < secondUsed then
      ⟨firstUsed + coordinate.2.val, by omega⟩
    else
      ⟨thirdUsed + 4 + coordinate.2.val, by omega⟩
  else
    exact if before : coordinate.2.val < thirdUsed then
      ⟨firstUsed + secondUsed + coordinate.2.val, by omega⟩
    else
      ⟨8 + coordinate.2.val, by omega⟩

@[simp] theorem stop2ToIndex_val (firstUsed secondUsed thirdUsed : Nat)
    (firstPositive : 0 < firstUsed) (firstBound : firstUsed ≤ 4)
    (secondPositive : 0 < secondUsed) (secondBound : secondUsed ≤ 4)
    (thirdPositive : 0 < thirdUsed) (thirdBound : thirdUsed ≤ 4)
    (coordinate : Fin 3 × Fin 4) :
    (stop2ToIndex firstUsed secondUsed thirdUsed firstPositive firstBound
      secondPositive secondBound thirdPositive thirdBound coordinate).val =
      if coordinate.1.val = 0 then
        if coordinate.2.val < firstUsed then coordinate.2.val
        else secondUsed + thirdUsed + coordinate.2.val
      else if coordinate.1.val = 1 then
        if coordinate.2.val < secondUsed then firstUsed + coordinate.2.val
        else thirdUsed + 4 + coordinate.2.val
      else if coordinate.2.val < thirdUsed then
        firstUsed + secondUsed + coordinate.2.val
      else 8 + coordinate.2.val := by
  simp only [stop2ToIndex]
  split_ifs <;> rfl

def stop2FromIndex (firstUsed secondUsed thirdUsed : Nat)
    (firstPositive : 0 < firstUsed) (firstBound : firstUsed ≤ 4)
    (secondPositive : 0 < secondUsed) (secondBound : secondUsed ≤ 4)
    (thirdPositive : 0 < thirdUsed) (thirdBound : thirdUsed ≤ 4)
    (coordinate : Fin 12) : Fin 3 × Fin 4 := by
  if first : coordinate.val < firstUsed then
    exact (0, ⟨coordinate.val, by omega⟩)
  else if second : coordinate.val < firstUsed + secondUsed then
    exact (1, ⟨coordinate.val - firstUsed, by omega⟩)
  else if third : coordinate.val < firstUsed + secondUsed + thirdUsed then
    exact (2, ⟨coordinate.val - firstUsed - secondUsed, by omega⟩)
  else if firstPadding : coordinate.val < secondUsed + thirdUsed + 4 then
    exact (0, ⟨coordinate.val - secondUsed - thirdUsed, by omega⟩)
  else if secondPadding : coordinate.val < thirdUsed + 8 then
    exact (1, ⟨coordinate.val - thirdUsed - 4, by omega⟩)
  else
    exact (2, ⟨coordinate.val - 8, by omega⟩)

def stop2IndexEquiv (firstUsed secondUsed thirdUsed : Nat)
    (firstPositive : 0 < firstUsed) (firstBound : firstUsed ≤ 4)
    (secondPositive : 0 < secondUsed) (secondBound : secondUsed ≤ 4)
    (thirdPositive : 0 < thirdUsed) (thirdBound : thirdUsed ≤ 4) :
    Fin 3 × Fin 4 ≃ Fin 12 where
  toFun := stop2ToIndex firstUsed secondUsed thirdUsed firstPositive firstBound
    secondPositive secondBound thirdPositive thirdBound
  invFun := stop2FromIndex firstUsed secondUsed thirdUsed firstPositive firstBound
    secondPositive secondBound thirdPositive thirdBound
  left_inv coordinate := by
    rcases coordinate with ⟨attempt, block⟩
    fin_cases attempt
    · by_cases before : block.val < firstUsed
      · have routedValue :
            (stop2ToIndex firstUsed secondUsed thirdUsed firstPositive
              firstBound secondPositive secondBound thirdPositive thirdBound
              (0, block)).val = block.val := by
          simp [stop2ToIndex, before]
        change stop2FromIndex firstUsed secondUsed thirdUsed firstPositive
            firstBound secondPositive secondBound thirdPositive thirdBound
            (stop2ToIndex firstUsed secondUsed thirdUsed firstPositive
              firstBound secondPositive secondBound thirdPositive thirdBound
              (0, block)) = (0, block)
        apply Prod.ext <;> apply Fin.ext <;>
          simp only [stop2FromIndex] <;> simp [routedValue, before]
      · have routedValue :
            (stop2ToIndex firstUsed secondUsed thirdUsed firstPositive
              firstBound secondPositive secondBound thirdPositive thirdBound
              (0, block)).val = secondUsed + thirdUsed + block.val := by
          simp [stop2ToIndex, before]
        change stop2FromIndex firstUsed secondUsed thirdUsed firstPositive
            firstBound secondPositive secondBound thirdPositive thirdBound
            (stop2ToIndex firstUsed secondUsed thirdUsed firstPositive
              firstBound secondPositive secondBound thirdPositive thirdBound
              (0, block)) = (0, block)
        apply Prod.ext <;> apply Fin.ext <;>
          simp only [stop2FromIndex] <;> simp [routedValue] <;>
          split_ifs <;> simp <;> omega
    · by_cases before : block.val < secondUsed
      · have routedValue :
            (stop2ToIndex firstUsed secondUsed thirdUsed firstPositive
              firstBound secondPositive secondBound thirdPositive thirdBound
              (1, block)).val = firstUsed + block.val := by
          simp [stop2ToIndex, before]
        change stop2FromIndex firstUsed secondUsed thirdUsed firstPositive
            firstBound secondPositive secondBound thirdPositive thirdBound
            (stop2ToIndex firstUsed secondUsed thirdUsed firstPositive
              firstBound secondPositive secondBound thirdPositive thirdBound
              (1, block)) = (1, block)
        apply Prod.ext <;> apply Fin.ext <;>
          simp only [stop2FromIndex] <;> simp [routedValue] <;>
          split_ifs <;> simp <;> omega
      · have routedValue :
            (stop2ToIndex firstUsed secondUsed thirdUsed firstPositive
              firstBound secondPositive secondBound thirdPositive thirdBound
              (1, block)).val = thirdUsed + 4 + block.val := by
          simp [stop2ToIndex, before]
        change stop2FromIndex firstUsed secondUsed thirdUsed firstPositive
            firstBound secondPositive secondBound thirdPositive thirdBound
            (stop2ToIndex firstUsed secondUsed thirdUsed firstPositive
              firstBound secondPositive secondBound thirdPositive thirdBound
              (1, block)) = (1, block)
        apply Prod.ext <;> apply Fin.ext <;>
          simp only [stop2FromIndex] <;> simp [routedValue] <;>
          split_ifs <;> simp <;> omega
    · by_cases before : block.val < thirdUsed
      · have routedValue :
            (stop2ToIndex firstUsed secondUsed thirdUsed firstPositive
              firstBound secondPositive secondBound thirdPositive thirdBound
              (2, block)).val = firstUsed + secondUsed + block.val := by
          simp [stop2ToIndex, before]
        change stop2FromIndex firstUsed secondUsed thirdUsed firstPositive
            firstBound secondPositive secondBound thirdPositive thirdBound
            (stop2ToIndex firstUsed secondUsed thirdUsed firstPositive
              firstBound secondPositive secondBound thirdPositive thirdBound
              (2, block)) = (2, block)
        apply Prod.ext <;> apply Fin.ext <;>
          simp only [stop2FromIndex] <;> simp [routedValue] <;>
          split_ifs <;> simp <;> omega
      · have routedValue :
            (stop2ToIndex firstUsed secondUsed thirdUsed firstPositive
              firstBound secondPositive secondBound thirdPositive thirdBound
              (2, block)).val = 8 + block.val := by
          simp [stop2ToIndex, before]
        change stop2FromIndex firstUsed secondUsed thirdUsed firstPositive
            firstBound secondPositive secondBound thirdPositive thirdBound
            (stop2ToIndex firstUsed secondUsed thirdUsed firstPositive
              firstBound secondPositive secondBound thirdPositive thirdBound
              (2, block)) = (2, block)
        apply Prod.ext <;> apply Fin.ext <;>
          simp only [stop2FromIndex] <;> simp [routedValue] <;>
          split_ifs <;> simp <;> omega
  right_inv coordinate := by
    change stop2ToIndex firstUsed secondUsed thirdUsed firstPositive firstBound
        secondPositive secondBound thirdPositive thirdBound
        (stop2FromIndex firstUsed secondUsed thirdUsed firstPositive firstBound
          secondPositive secondBound thirdPositive thirdBound coordinate) =
      coordinate
    by_cases first : coordinate.val < firstUsed
    · have unrouted : stop2FromIndex firstUsed secondUsed thirdUsed
          firstPositive firstBound secondPositive secondBound thirdPositive
          thirdBound coordinate = (0, ⟨coordinate.val, by omega⟩) := by
        simp [stop2FromIndex, first]
      rw [unrouted]
      apply Fin.ext
      rw [stop2ToIndex_val]
      simp [first]
    · by_cases second : coordinate.val < firstUsed + secondUsed
      · have unrouted : stop2FromIndex firstUsed secondUsed thirdUsed
            firstPositive firstBound secondPositive secondBound thirdPositive
            thirdBound coordinate =
              (1, ⟨coordinate.val - firstUsed, by omega⟩) := by
          simp [stop2FromIndex, first, second]
        rw [unrouted]
        apply Fin.ext
        rw [stop2ToIndex_val]
        simp
        split_ifs <;> omega
      · by_cases third :
          coordinate.val < firstUsed + secondUsed + thirdUsed
        · have unrouted : stop2FromIndex firstUsed secondUsed thirdUsed
              firstPositive firstBound secondPositive secondBound thirdPositive
              thirdBound coordinate =
                (2, ⟨coordinate.val - firstUsed - secondUsed, by omega⟩) := by
            simp [stop2FromIndex, first, second, third]
          rw [unrouted]
          apply Fin.ext
          rw [stop2ToIndex_val]
          simp
          split_ifs <;> omega
        · by_cases firstPadding :
            coordinate.val < secondUsed + thirdUsed + 4
          · have unrouted : stop2FromIndex firstUsed secondUsed thirdUsed
                firstPositive firstBound secondPositive secondBound
                thirdPositive thirdBound coordinate =
                  (0, ⟨coordinate.val - secondUsed - thirdUsed, by omega⟩) := by
              simp [stop2FromIndex, first, second, third, firstPadding]
            rw [unrouted]
            apply Fin.ext
            rw [stop2ToIndex_val]
            simp
            split_ifs <;> omega
          · by_cases secondPadding : coordinate.val < thirdUsed + 8
            · have unrouted : stop2FromIndex firstUsed secondUsed thirdUsed
                  firstPositive firstBound secondPositive secondBound
                  thirdPositive thirdBound coordinate =
                    (1, ⟨coordinate.val - thirdUsed - 4, by omega⟩) := by
                simp [stop2FromIndex, first, second, third, firstPadding,
                  secondPadding]
              rw [unrouted]
              apply Fin.ext
              rw [stop2ToIndex_val]
              simp
              split_ifs <;> omega
            · have unrouted : stop2FromIndex firstUsed secondUsed thirdUsed
                  firstPositive firstBound secondPositive secondBound
                  thirdPositive thirdBound coordinate =
                    (2, ⟨coordinate.val - 8, by omega⟩) := by
                simp [stop2FromIndex, first, second, third, firstPadding,
                  secondPadding]
              rw [unrouted]
              apply Fin.ext
              rw [stop2ToIndex_val]
              simp
              split_ifs <;> omega

/-- Reindex a flat twelve-coordinate family into three routed four-coordinate
families. -/
def routeCoordinates {alpha : Type} (index : Fin 3 × Fin 4 ≃ Fin 12)
    (flat : Fin 12 → alpha) : Fin 3 → Fin 4 → alpha :=
  fun attempt block => flat (index (attempt, block))

/-- Undo `routeCoordinates`. -/
def unrouteCoordinates {alpha : Type} (index : Fin 3 × Fin 4 ≃ Fin 12)
    (routed : Fin 3 → Fin 4 → alpha) : Fin 12 → alpha :=
  fun coordinate =>
    let routedCoordinate := index.symm coordinate
    routed routedCoordinate.1 routedCoordinate.2

@[simp] theorem unroute_route_coordinates {alpha : Type}
    (index : Fin 3 × Fin 4 ≃ Fin 12) (flat : Fin 12 → alpha) :
    unrouteCoordinates index (routeCoordinates index flat) = flat := by
  funext coordinate
  simp [unrouteCoordinates, routeCoordinates]

@[simp] theorem route_unroute_coordinates {alpha : Type}
    (index : Fin 3 × Fin 4 ≃ Fin 12)
    (routed : Fin 3 → Fin 4 → alpha) :
    routeCoordinates index (unrouteCoordinates index routed) = routed := by
  funext attempt block
  simp [unrouteCoordinates, routeCoordinates]

/-! ## Four-block operational/raw commute -/

/-- The literal flattened words of four digest blocks, written in direct
block/word coordinates. -/
theorem flattenedWords_fourGammaBlocks_coordinates
    (blocks : FourGammaBlocks) :
    flattenedWords (List.ofFn blocks) =
      List.ofFn fun draw : Fin 32 =>
        littleEndianWord
          (blocks ⟨draw.val / 8, by omega⟩)
          ⟨draw.val % 8, Nat.mod_lt _ (by norm_num)⟩ := by
  apply List.ext_getElem
  · simp [flattenedWords_length]
  · intro index leftBound rightBound
    simp only [List.length_ofFn] at rightBound
    simp [flattenedWords, blockWords]

/-- The raw-stream equivalence uses exactly the same chronological word list
as the production block decoder. -/
theorem flattenedWords_fourGammaBlocksRawEquiv
    (blocks : FourGammaBlocks) :
    flattenedWords (List.ofFn blocks) =
      rawWordsToNat (fourGammaBlocksRawEquiv blocks).1 := by
  rw [flattenedWords_fourGammaBlocks_coordinates]
  apply List.ext_getElem
  · simp [rawWordsToNat, tag73MaximumRawWordCount, tag73LimbCount,
      tag73LimbRetryLimit]
  · intro index leftBound rightBound
    have indexBound : index < 32 := by simpa using leftBound
    let block : Fin 4 := ⟨index / 8, by omega⟩
    let word : Fin 8 := ⟨index % 8, Nat.mod_lt _ (by norm_num)⟩
    have coordinate :
        fourBlockWordIndexEquiv (block, word) =
          (⟨index, by
            norm_num [tag73MaximumRawWordCount, tag73LimbCount,
              tag73LimbRetryLimit]
            exact indexBound⟩ : Fin tag73MaximumRawWordCount) := by
      apply Fin.ext
      change word.val + 8 * block.val = index
      dsimp [block, word]
      exact Nat.mod_add_div index 8
    simp only [List.getElem_ofFn, rawWordsToNat, List.getElem_map]
    rw [show (fourGammaBlocksRawEquiv blocks).1[index] =
        (Equiv.vectorEquivFin RawWord tag73MaximumRawWordCount
          (fourGammaBlocksRawEquiv blocks))
          (⟨index, by
            norm_num [tag73MaximumRawWordCount, tag73LimbCount,
              tag73LimbRetryLimit]
            exact indexBound⟩ : Fin tag73MaximumRawWordCount) by rfl]
    rw [← coordinate, fourGammaBlocksRawEquiv_word_value]

def ordinaryPrefixDecodeOfRawSuccess
    (blocks : FourGammaBlocks)
    (result : (Fin tag73LimbCount → M31Value) × List RawWord) :
    OrdinaryPrefixDecode :=
  let decoded := limbsDecodeOfRawSuccess
    (fourGammaBlocksRawEquiv blocks).1 result
  { value := encodeQm31Limbs decoded.limbs
    limbs := decoded.limbs
    wordsUsed := decoded.wordsUsed
    blocksUsed := blocksNeededForWords decoded.wordsUsed
    remainingBlocks := (List.ofFn blocks).drop
      (blocksNeededForWords decoded.wordsUsed) }

/-- Total operational commute for one four-block routed window.  It includes
failure as well as success, and exposes the exact consumed-block suffix. -/
theorem decodeOrdinaryPrefix_fourGammaBlocksRawEquiv
    (blocks : FourGammaBlocks) :
    decodeOrdinaryPrefix (List.ofFn blocks) =
      (tag73RawRun (fourGammaBlocksRawEquiv blocks)).map
        (ordinaryPrefixDecodeOfRawSuccess blocks) := by
  let raw := fourGammaBlocksRawEquiv blocks
  have words : flattenedWords (List.ofFn blocks) = rawWordsToNat raw.1 := by
    exact flattenedWords_fourGammaBlocksRawEquiv blocks
  cases rawRun : tag73RawRun raw with
  | none =>
      have limbsNone : decodeLimbs 4 (flattenedWords (List.ofFn blocks)) =
          none := by
        rw [words, decodeFourLimbs_rawWordsToNat]
        simpa [tag73RawRun] using rawRun
      simp only [Option.map_none]
      have blocksEq : List.ofFn blocks =
          [blocks 0, blocks 1, blocks 2, blocks 3] := by rfl
      rw [blocksEq]
      unfold decodeOrdinaryPrefix
      have limbsNone' :
          decodeLimbs 4
            (flattenedWords [blocks 0, blocks 1, blocks 2, blocks 3]) =
              none := by simpa using limbsNone
      rw [limbsNone']
      rfl
  | some result =>
      have limbsSome : decodeLimbs 4 (flattenedWords (List.ofFn blocks)) =
          some (limbsDecodeOfRawSuccess raw.1 result) := by
        rw [words, decodeFourLimbs_rawWordsToNat]
        change (tag73RawRun raw).map (limbsDecodeOfRawSuccess raw.1) =
          some (limbsDecodeOfRawSuccess raw.1 result)
        rw [rawRun]
        rfl
      have cap := decodeFourLimbs_word_cap
        (flattenedWords (List.ofFn blocks))
        (limbsDecodeOfRawSuccess raw.1 result) limbsSome
      have valid :
          0 < blocksNeededForWords
                (limbsDecodeOfRawSuccess raw.1 result).wordsUsed ∧
            blocksNeededForWords
                (limbsDecodeOfRawSuccess raw.1 result).wordsUsed ≤ 4 ∧
            blocksNeededForWords
                (limbsDecodeOfRawSuccess raw.1 result).wordsUsed ≤
              (List.ofFn blocks).length := by
        simp only [List.length_ofFn]
        unfold blocksNeededForWords
        omega
      simp only [Option.map_some]
      have blocksEq : List.ofFn blocks =
          [blocks 0, blocks 1, blocks 2, blocks 3] := by rfl
      rw [blocksEq]
      unfold decodeOrdinaryPrefix
      have limbsSome' :
          decodeLimbs 4
            (flattenedWords [blocks 0, blocks 1, blocks 2, blocks 3]) =
              some (limbsDecodeOfRawSuccess raw.1 result) := by
        simpa using limbsSome
      rw [limbsSome']
      have validShort :
          0 < blocksNeededForWords
                (limbsDecodeOfRawSuccess raw.1 result).wordsUsed ∧
            blocksNeededForWords
                (limbsDecodeOfRawSuccess raw.1 result).wordsUsed ≤ 4 :=
        ⟨valid.1, valid.2.1⟩
      simp [validShort, ordinaryPrefixDecodeOfRawSuccess, raw]

theorem fourGammaBlocksRawEquiv_success_iff
    (blocks : FourGammaBlocks) :
    (decodeOrdinaryPrefix (List.ofFn blocks)).isSome ↔
      Tag73RawSucceeds (fourGammaBlocksRawEquiv blocks) := by
  rw [decodeOrdinaryPrefix_fourGammaBlocksRawEquiv]
  unfold Tag73RawSucceeds
  cases tag73RawRun (fourGammaBlocksRawEquiv blocks) <;> simp

/-- The consumed block count of every successful ordinary prefix is a
positive member of the four-block call budget. -/
theorem decodeOrdinaryPrefix_blocksUsed_bounds
    (blocks : List Digest256) (decoded : OrdinaryPrefixDecode)
    (run : decodeOrdinaryPrefix blocks = some decoded) :
    0 < decoded.blocksUsed ∧ decoded.blocksUsed ≤ 4 := by
  cases blocks with
  | nil => simp [decodeOrdinaryPrefix] at run
  | cons block rest =>
      cases limbsRun : decodeLimbs 4 (flattenedWords (block :: rest)) with
      | none => simp [decodeOrdinaryPrefix, limbsRun] at run
      | some limbs =>
          by_cases valid :
              0 < blocksNeededForWords limbs.wordsUsed ∧
                blocksNeededForWords limbs.wordsUsed ≤ 4 ∧
                blocksNeededForWords limbs.wordsUsed ≤ (block :: rest).length
          · simp [decodeOrdinaryPrefix, limbsRun, valid] at run
            rcases run with ⟨_, decodedEq⟩
            subst decoded
            exact ⟨valid.1, valid.2.1⟩
          · simp [decodeOrdinaryPrefix, limbsRun] at run
            exact False.elim (valid run.1)

theorem decodeOrdinaryPrefix_remaining_eq_drop
    (blocks : List Digest256) (decoded : OrdinaryPrefixDecode)
    (run : decodeOrdinaryPrefix blocks = some decoded) :
    decoded.remainingBlocks = blocks.drop decoded.blocksUsed := by
  obtain ⟨before, accepted, after, decomposition, wordsUsed, limbCount,
      finalLimb, value, blocksUsed, remaining, blocksUsedLe⟩ :=
    decodeOrdinaryPrefix_fourth_limb_trace blocks decoded run
  exact remaining

/-- Replacing only the unread suffix of a successful ordinary call preserves
all of its stopping data. -/
theorem decodeOrdinaryPrefix_of_matching_consumed_prefix
    (source target : List Digest256) (decoded : OrdinaryPrefixDecode)
    (run : decodeOrdinaryPrefix source = some decoded)
    (targetLong : decoded.blocksUsed ≤ target.length)
    (prefixEq : target.take decoded.blocksUsed =
      source.take decoded.blocksUsed) :
    decodeOrdinaryPrefix target =
      some { decoded with remainingBlocks := target.drop decoded.blocksUsed } := by
  have trimmed := decodeOrdinaryPrefix_take_blocksUsed source decoded run
  have extended := decodeOrdinaryPrefix_append_of_some
    (source.take decoded.blocksUsed) (target.drop decoded.blocksUsed)
    { decoded with remainingBlocks := [] } trimmed
  have targetSplit : target.take decoded.blocksUsed ++
      target.drop decoded.blocksUsed = target :=
    List.take_append_drop decoded.blocksUsed target
  rw [← prefixEq] at extended
  rw [← targetSplit]
  simpa [appendOrdinaryRemaining] using extended

/-- Runtime bytes from the local commute are the literal canonical encoding
of the raw sampler's four-limb value. -/
theorem ordinaryPrefixDecodeOfRawSuccess_value_eq_exact_encoding
    (blocks : FourGammaBlocks)
    (result : (Fin tag73LimbCount → M31Value) × List RawWord) :
    (ordinaryPrefixDecodeOfRawSuccess blocks result).value =
      encodeTagQM31ExactLE (tag73FourLimbsToExact result.1) := by
  let limbs := (List.ofFn result.1).map Fin.val
  have lengthExact : limbs.length = 4 := by
    simp [limbs, tag73LimbCount]
  have canonical : ∀ limb ∈ limbs, limb < m31Prime := by
    intro limb member
    simp [limbs] at member
    obtain ⟨index, value⟩ := member
    subst limb
    exact (result.1 index).isLt
  rw [show (ordinaryPrefixDecodeOfRawSuccess blocks result).value =
      encodeQm31Limbs limbs by rfl]
  have limbEq :
      exactLimbsOfList limbs lengthExact canonical = result.1 := by
    funext index
    fin_cases index <;> apply Fin.ext <;>
      simp [exactLimbsOfList, limbs, listValue, tag73LimbCount]
  rw [encodeQm31Limbs_eq_exact_encoding limbs lengthExact canonical]
  exact congrArg encodeTagQM31ExactLE
    (congrArg qm31ExactLimbEquiv limbEq)

/-- The operational bytes in the commute theorem decode to the exact value
coordinate returned by the raw sampler. -/
theorem ordinaryPrefixDecodeOfRawSuccess_exact_value
    (blocks : FourGammaBlocks)
    (result : (Fin tag73LimbCount → M31Value) × List RawWord) :
    decodeTagQM31ExactLE
        (ordinaryPrefixDecodeOfRawSuccess blocks result).value =
      some (tag73FourLimbsToExact result.1) := by
  rw [ordinaryPrefixDecodeOfRawSuccess_value_eq_exact_encoding]
  exact decodeTagQM31ExactLE_encodeTagQM31ExactLE _

theorem encodeTagQM31ExactLE_injective :
    Function.Injective encodeTagQM31ExactLE := by
  intro left right equality
  apply_fun decodeTagQM31ExactLE at equality
  simpa only [decodeTagQM31ExactLE_encodeTagQM31ExactLE,
    Option.some.injEq] using equality

/-- The unique raw result selected by a successful raw stream. -/
def successfulRawResult (raw : SuccessfulTag73RawStream) :
    (Fin tag73LimbCount → M31Value) × List RawWord :=
  (tag73RawRun raw.1).get raw.2

@[simp] theorem tag73RawRun_successfulRawResult
    (raw : SuccessfulTag73RawStream) :
    tag73RawRun raw.1 = some (successfulRawResult raw) := by
  exact (Option.some_get raw.2).symm

/-- Canonical production-level ordinary result carried by a successful raw
four-block window. -/
def successfulRawOrdinaryDecode (raw : SuccessfulTag73RawStream) :
    OrdinaryPrefixDecode :=
  ordinaryPrefixDecodeOfRawSuccess
    (fourGammaBlocksRawEquiv.symm raw.1) (successfulRawResult raw)

@[simp] theorem successfulRawOrdinaryDecode_run
    (raw : SuccessfulTag73RawStream) :
    decodeOrdinaryPrefix
        (List.ofFn (fourGammaBlocksRawEquiv.symm raw.1)) =
      some (successfulRawOrdinaryDecode raw) := by
  rw [decodeOrdinaryPrefix_fourGammaBlocksRawEquiv]
  simp [successfulRawOrdinaryDecode]

theorem successfulRawOrdinaryDecode_blocksUsed_bounds
    (raw : SuccessfulTag73RawStream) :
    0 < (successfulRawOrdinaryDecode raw).blocksUsed ∧
      (successfulRawOrdinaryDecode raw).blocksUsed ≤ 4 :=
  decodeOrdinaryPrefix_blocksUsed_bounds _ _
    (successfulRawOrdinaryDecode_run raw)

theorem successfulRawOrdinaryDecode_value_eq_exact_encoding
    (raw : SuccessfulTag73RawStream) :
    (successfulRawOrdinaryDecode raw).value =
      encodeTagQM31ExactLE (successfulOrdinaryExactValue raw) := by
  rw [successfulRawOrdinaryDecode,
    ordinaryPrefixDecodeOfRawSuccess_value_eq_exact_encoding]
  congr 1
  simp [successfulOrdinaryExactValue, successfulTag73Values,
    tag73ValuesOrFirst]

@[simp] theorem encodeTagQM31ExactLE_zero_local :
    encodeTagQM31ExactLE (0 : QM31Exact) = zeroBytes 16 := by
  funext index
  fin_cases index <;> rfl

@[simp] theorem successfulZeroRawOrdinaryDecode_value
    (raw : SuccessfulZeroGammaOrdinaryRaw) :
    (successfulRawOrdinaryDecode raw.1).value = zeroBytes 16 := by
  rw [successfulRawOrdinaryDecode_value_eq_exact_encoding, raw.2,
    encodeTagQM31ExactLE_zero_local]

theorem successfulNonzeroRawOrdinaryDecode_value
    (raw : SuccessfulNonzeroGammaOrdinaryRaw) :
    (successfulRawOrdinaryDecode raw.1).value ≠ zeroBytes 16 := by
  rw [successfulRawOrdinaryDecode_value_eq_exact_encoding,
    ← encodeTagQM31ExactLE_zero_local]
  exact fun equality => raw.2 (encodeTagQM31ExactLE_injective equality)

def successfulRawOfOrdinaryRun
    (blocks : FourGammaBlocks) (decoded : OrdinaryPrefixDecode)
    (run : decodeOrdinaryPrefix (List.ofFn blocks) = some decoded) :
    SuccessfulTag73RawStream :=
  ⟨fourGammaBlocksRawEquiv blocks,
    (fourGammaBlocksRawEquiv_success_iff blocks).mp (by
      change (decodeOrdinaryPrefix (List.ofFn blocks)).isSome
      rw [run]
      rfl)⟩

@[simp] theorem successfulRawOrdinaryDecode_of_run
    (blocks : FourGammaBlocks) (decoded : OrdinaryPrefixDecode)
    (run : decodeOrdinaryPrefix (List.ofFn blocks) = some decoded) :
    successfulRawOrdinaryDecode
      (successfulRawOfOrdinaryRun blocks decoded run) = decoded := by
  have canonicalRun := successfulRawOrdinaryDecode_run
    (successfulRawOfOrdinaryRun blocks decoded run)
  have blocksEq :
      fourGammaBlocksRawEquiv.symm
          (successfulRawOfOrdinaryRun blocks decoded run).1 = blocks := by
    exact fourGammaBlocksRawEquiv.symm_apply_apply blocks
  rw [blocksEq] at canonicalRun
  rw [run] at canonicalRun
  exact (Option.some.inj canonicalRun).symm

def successfulZeroRawOfOrdinaryRun
    (blocks : FourGammaBlocks) (decoded : OrdinaryPrefixDecode)
    (run : decodeOrdinaryPrefix (List.ofFn blocks) = some decoded)
    (zero : decoded.value = zeroBytes 16) :
    SuccessfulZeroGammaOrdinaryRaw := by
  let raw := successfulRawOfOrdinaryRun blocks decoded run
  refine ⟨raw, ?_⟩
  apply encodeTagQM31ExactLE_injective
  rw [encodeTagQM31ExactLE_zero_local]
  rw [← successfulRawOrdinaryDecode_value_eq_exact_encoding raw]
  simpa [raw] using zero

def successfulNonzeroRawOfOrdinaryRun
    (blocks : FourGammaBlocks) (decoded : OrdinaryPrefixDecode)
    (run : decodeOrdinaryPrefix (List.ofFn blocks) = some decoded)
    (nonzero : decoded.value ≠ zeroBytes 16) :
    SuccessfulNonzeroGammaOrdinaryRaw := by
  let raw := successfulRawOfOrdinaryRun blocks decoded run
  refine ⟨raw, ?_⟩
  intro exactZero
  apply nonzero
  rw [← successfulRawOrdinaryDecode_of_run blocks decoded run]
  rw [successfulRawOrdinaryDecode_value_eq_exact_encoding, exactZero,
    encodeTagQM31ExactLE_zero_local]

/-! ## Consumed-prefix transport through a coordinate route -/

/-- If a routed window's consumed coordinates occupy a consecutive interval
of the chronological tape, unrouting preserves that interval literally. -/
theorem take_drop_ofFn_unrouteCoordinates
    {alpha : Type} (index : Fin 3 × Fin 4 ≃ Fin 12)
    (routed : Fin 3 → Fin 4 → alpha) (attempt : Fin 3)
    (offset used : Nat) (usedBound : used ≤ 4)
    (intervalBound : offset + used ≤ 12)
    (coordinates : ∀ block : Fin 4, block.val < used →
      (index (attempt, block)).val = offset + block.val) :
    ((List.ofFn (unrouteCoordinates index routed)).drop offset).take used =
      (List.ofFn (routed attempt)).take used := by
  have usedLeDrop : used ≤ 12 - offset := by omega
  apply List.ext_getElem
  · simp [List.length_take, List.length_drop, usedBound, usedLeDrop]
  · intro position leftBound rightBound
    have positionBounds : position < used ∧ position < 12 - offset := by
      simpa [List.length_take, List.length_drop] using leftBound
    have positionUsed : position < used := positionBounds.1
    have positionFour : position < 4 := lt_of_lt_of_le positionUsed usedBound
    have positionTwelve : offset + position < 12 := by omega
    let block : Fin 4 := ⟨position, positionFour⟩
    let flat : Fin 12 := ⟨offset + position, positionTwelve⟩
    have indexEq : index (attempt, block) = flat := by
      apply Fin.ext
      exact coordinates block positionUsed
    have inverseEq : index.symm flat = (attempt, block) := by
      rw [← indexEq]
      exact index.symm_apply_apply (attempt, block)
    simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]
    change routed (index.symm flat).1 (index.symm flat).2 =
      routed attempt block
    rw [inverseEq]

theorem stop0IndexEquiv_first_interval (block : Fin 4) :
    (stop0IndexEquiv (0, block)).val = block.val := by
  rfl

theorem stop1IndexEquiv_first_interval
    (firstUsed secondUsed : Nat)
    (firstPositive : 0 < firstUsed) (firstBound : firstUsed ≤ 4)
    (secondPositive : 0 < secondUsed) (secondBound : secondUsed ≤ 4)
    (block : Fin 4) (before : block.val < firstUsed) :
    (stop1IndexEquiv firstUsed secondUsed firstPositive firstBound
      secondPositive secondBound (0, block)).val = block.val := by
  simp [stop1IndexEquiv, stop1ToIndex, before]

theorem stop1IndexEquiv_second_interval
    (firstUsed secondUsed : Nat)
    (firstPositive : 0 < firstUsed) (firstBound : firstUsed ≤ 4)
    (secondPositive : 0 < secondUsed) (secondBound : secondUsed ≤ 4)
    (block : Fin 4) (before : block.val < secondUsed) :
    (stop1IndexEquiv firstUsed secondUsed firstPositive firstBound
      secondPositive secondBound (1, block)).val = firstUsed + block.val := by
  simp [stop1IndexEquiv, stop1ToIndex, before]

theorem stop2IndexEquiv_first_interval
    (firstUsed secondUsed thirdUsed : Nat)
    (firstPositive : 0 < firstUsed) (firstBound : firstUsed ≤ 4)
    (secondPositive : 0 < secondUsed) (secondBound : secondUsed ≤ 4)
    (thirdPositive : 0 < thirdUsed) (thirdBound : thirdUsed ≤ 4)
    (block : Fin 4) (before : block.val < firstUsed) :
    (stop2IndexEquiv firstUsed secondUsed thirdUsed firstPositive firstBound
      secondPositive secondBound thirdPositive thirdBound (0, block)).val =
        block.val := by
  simp [stop2IndexEquiv, stop2ToIndex, before]

theorem stop2IndexEquiv_second_interval
    (firstUsed secondUsed thirdUsed : Nat)
    (firstPositive : 0 < firstUsed) (firstBound : firstUsed ≤ 4)
    (secondPositive : 0 < secondUsed) (secondBound : secondUsed ≤ 4)
    (thirdPositive : 0 < thirdUsed) (thirdBound : thirdUsed ≤ 4)
    (block : Fin 4) (before : block.val < secondUsed) :
    (stop2IndexEquiv firstUsed secondUsed thirdUsed firstPositive firstBound
      secondPositive secondBound thirdPositive thirdBound (1, block)).val =
        firstUsed + block.val := by
  simp [stop2IndexEquiv, stop2ToIndex, before]

theorem stop2IndexEquiv_third_interval
    (firstUsed secondUsed thirdUsed : Nat)
    (firstPositive : 0 < firstUsed) (firstBound : firstUsed ≤ 4)
    (secondPositive : 0 < secondUsed) (secondBound : secondUsed ≤ 4)
    (thirdPositive : 0 < thirdUsed) (thirdBound : thirdUsed ≤ 4)
    (block : Fin 4) (before : block.val < thirdUsed) :
    (stop2IndexEquiv firstUsed secondUsed thirdUsed firstPositive firstBound
      secondPositive secondBound thirdPositive thirdBound (2, block)).val =
        firstUsed + secondUsed + block.val := by
  simp [stop2IndexEquiv, stop2ToIndex, before]

theorem decodeOrdinaryPrefix_routeCoordinates
    (index : Fin 3 × Fin 4 ≃ Fin 12) (flat : Fin 12 → Digest256)
    (attempt : Fin 3) (offset : Nat) (decoded : OrdinaryPrefixDecode)
    (run : decodeOrdinaryPrefix ((List.ofFn flat).drop offset) = some decoded)
    (usedBound : decoded.blocksUsed ≤ 4)
    (intervalBound : offset + decoded.blocksUsed ≤ 12)
    (coordinates : ∀ block : Fin 4, block.val < decoded.blocksUsed →
      (index (attempt, block)).val = offset + block.val) :
    decodeOrdinaryPrefix
        (List.ofFn (routeCoordinates index flat attempt)) =
      some { decoded with remainingBlocks :=
        ((List.ofFn (routeCoordinates index flat attempt)).drop
          decoded.blocksUsed) } := by
  have interval := take_drop_ofFn_unrouteCoordinates index
    (routeCoordinates index flat) attempt offset decoded.blocksUsed usedBound
    intervalBound coordinates
  have prefixEq :
      (List.ofFn (routeCoordinates index flat attempt)).take
          decoded.blocksUsed =
        ((List.ofFn flat).drop offset).take decoded.blocksUsed := by
    simpa using interval.symm
  exact decodeOrdinaryPrefix_of_matching_consumed_prefix
    ((List.ofFn flat).drop offset)
    (List.ofFn (routeCoordinates index flat attempt)) decoded run
    (by simp; omega) prefixEq

/-- The converse consumed-prefix transport.  A successful routed call is an
ordinary call of the unrouted chronological tape at the corresponding dynamic
offset.  Only the actually consumed coordinates are used. -/
theorem decodeOrdinaryPrefix_unrouteCoordinates
    (index : Fin 3 × Fin 4 ≃ Fin 12)
    (routed : Fin 3 → Fin 4 → Digest256)
    (attempt : Fin 3) (offset : Nat) (decoded : OrdinaryPrefixDecode)
    (run : decodeOrdinaryPrefix (List.ofFn (routed attempt)) = some decoded)
    (usedBound : decoded.blocksUsed ≤ 4)
    (intervalBound : offset + decoded.blocksUsed ≤ 12)
    (coordinates : ∀ block : Fin 4, block.val < decoded.blocksUsed →
      (index (attempt, block)).val = offset + block.val) :
    decodeOrdinaryPrefix
        ((List.ofFn (unrouteCoordinates index routed)).drop offset) =
      some { decoded with remainingBlocks :=
        (List.drop decoded.blocksUsed
          ((List.ofFn (unrouteCoordinates index routed)).drop offset)) } := by
  have prefixEq := take_drop_ofFn_unrouteCoordinates index routed attempt
    offset decoded.blocksUsed usedBound intervalBound coordinates
  exact decodeOrdinaryPrefix_of_matching_consumed_prefix
    (List.ofFn (routed attempt))
    ((List.ofFn (unrouteCoordinates index routed)).drop offset) decoded run
    (by simp; omega) prefixEq

/-! ## Executable routed-to-flat sampler tape -/

def routedGammaRawStreams
    (sample : RoutedSuccessfulGammaTape) : Fin 3 → Tag73RawStream :=
  match sample with
  | .stop0 current later _ =>
      fun attempt => Fin.cases current.1 (fun laterAttempt => later laterAttempt) attempt
  | .stop1 before current later _ =>
      fun attempt => Fin.cases before.1
        (fun remaining => Fin.cases current.1 (fun _ => later) remaining) attempt
  | .stop2 first second current _ =>
      fun attempt => Fin.cases first.1
        (fun remaining => Fin.cases second.1 (fun _ => current.1) remaining) attempt

@[simp] theorem routedGammaRawStreams_stop0_zero
    (current later advance) :
    routedGammaRawStreams (.stop0 current later advance) 0 = current.1 := rfl

@[simp] theorem routedGammaRawStreams_stop0_one
    (current later advance) :
    routedGammaRawStreams (.stop0 current later advance) 1 = later 0 := by
  rfl

@[simp] theorem routedGammaRawStreams_stop0_two
    (current later advance) :
    routedGammaRawStreams (.stop0 current later advance) 2 = later 1 := by
  rfl

@[simp] theorem routedGammaRawStreams_stop1_zero
    (before current later advance) :
    routedGammaRawStreams (.stop1 before current later advance) 0 = before.1 := rfl

@[simp] theorem routedGammaRawStreams_stop1_one
    (before current later advance) :
    routedGammaRawStreams (.stop1 before current later advance) 1 = current.1 := by
  rfl

@[simp] theorem routedGammaRawStreams_stop1_two
    (before current later advance) :
    routedGammaRawStreams (.stop1 before current later advance) 2 = later := by
  rfl

@[simp] theorem routedGammaRawStreams_stop2_zero
    (first second current advance) :
    routedGammaRawStreams (.stop2 first second current advance) 0 = first.1 := rfl

@[simp] theorem routedGammaRawStreams_stop2_one
    (first second current advance) :
    routedGammaRawStreams (.stop2 first second current advance) 1 = second.1 := by
  rfl

@[simp] theorem routedGammaRawStreams_stop2_two
    (first second current advance) :
    routedGammaRawStreams (.stop2 first second current advance) 2 = current.1 := by
  rfl

def routedGammaBlocks
    (sample : RoutedSuccessfulGammaTape) : Fin 3 → FourGammaBlocks :=
  fun attempt => fourGammaBlocksRawEquiv.symm
    (routedGammaRawStreams sample attempt)

def routedGammaAdvances
    (sample : RoutedSuccessfulGammaTape) : Tag73AdvanceDigestGhosts :=
  match sample with
  | .stop0 _ _ advance => advance
  | .stop1 _ _ _ advance => advance
  | .stop2 _ _ _ advance => advance

def routedGammaIndex
    (sample : RoutedSuccessfulGammaTape) : Fin 3 × Fin 4 ≃ Fin 12 :=
  match sample with
  | .stop0 _ _ _ => stop0IndexEquiv
  | .stop1 before current _ _ =>
      stop1IndexEquiv
        (successfulRawOrdinaryDecode before.1).blocksUsed
        (successfulRawOrdinaryDecode current.1).blocksUsed
        (successfulRawOrdinaryDecode_blocksUsed_bounds before.1).1
        (successfulRawOrdinaryDecode_blocksUsed_bounds before.1).2
        (successfulRawOrdinaryDecode_blocksUsed_bounds current.1).1
        (successfulRawOrdinaryDecode_blocksUsed_bounds current.1).2
  | .stop2 first second current _ =>
      stop2IndexEquiv
        (successfulRawOrdinaryDecode first.1).blocksUsed
        (successfulRawOrdinaryDecode second.1).blocksUsed
        (successfulRawOrdinaryDecode current.1).blocksUsed
        (successfulRawOrdinaryDecode_blocksUsed_bounds first.1).1
        (successfulRawOrdinaryDecode_blocksUsed_bounds first.1).2
        (successfulRawOrdinaryDecode_blocksUsed_bounds second.1).1
        (successfulRawOrdinaryDecode_blocksUsed_bounds second.1).2
        (successfulRawOrdinaryDecode_blocksUsed_bounds current.1).1
        (successfulRawOrdinaryDecode_blocksUsed_bounds current.1).2

def routedGammaFlatTape
    (sample : RoutedSuccessfulGammaTape) : TotalGammaDuplexTape :=
  (unrouteCoordinates (routedGammaIndex sample) (routedGammaBlocks sample),
    unrouteCoordinates (routedGammaIndex sample) (routedGammaAdvances sample))

def routedGammaStopIndex (sample : RoutedSuccessfulGammaTape) : Fin 3 :=
  match sample with
  | .stop0 .. => 0
  | .stop1 .. => 1
  | .stop2 .. => 2

theorem routedGammaFlatTape_decode_at
    (sample : RoutedSuccessfulGammaTape) (attempt : Fin 3)
    (offset : Nat) (decoded : OrdinaryPrefixDecode)
    (run : decodeOrdinaryPrefix
      (List.ofFn (routedGammaBlocks sample attempt)) = some decoded)
    (usedBound : decoded.blocksUsed ≤ 4)
    (intervalBound : offset + decoded.blocksUsed ≤ 12)
    (coordinates : ∀ block : Fin 4, block.val < decoded.blocksUsed →
      ((routedGammaIndex sample) (attempt, block)).val =
        offset + block.val) :
    decodeOrdinaryPrefix
        ((gammaOutputBlocks (routedGammaFlatTape sample)).drop offset) =
      some { decoded with remainingBlocks :=
        ((gammaOutputBlocks (routedGammaFlatTape sample)).drop
          (offset + decoded.blocksUsed)) } := by
  have transported := decodeOrdinaryPrefix_unrouteCoordinates
    (routedGammaIndex sample) (routedGammaBlocks sample) attempt offset decoded
    run usedBound intervalBound coordinates
  simpa [gammaOutputBlocks, routedGammaFlatTape, List.drop_drop,
    Nat.add_comm] using transported

theorem routedGammaFlatTape_trace
    (sample : RoutedSuccessfulGammaTape) :
    ∃ decoded : OrdinaryPrefixDecode,
      GammaPrefixTrace 3
        (gammaOutputBlocks (routedGammaFlatTape sample))
        (routedGammaStopIndex sample) decoded ∧
      decodeTagQM31ExactLE decoded.value =
        some (routedSuccessfulGammaValue sample).1 := by
  cases sample with
  | stop0 current later advance =>
      let decoded := successfulRawOrdinaryDecode current.1
      have bounds := successfulRawOrdinaryDecode_blocksUsed_bounds current.1
      have decodedBound : decoded.blocksUsed ≤ 4 := by
        simpa [decoded] using bounds.2
      have sourceRun :
          decodeOrdinaryPrefix
              (List.ofFn (routedGammaBlocks
                (.stop0 current later advance) 0)) = some decoded := by
        simpa [routedGammaBlocks, routedGammaRawStreams, decoded] using
          successfulRawOrdinaryDecode_run current.1
      have prefixEq :
          (gammaOutputBlocks (routedGammaFlatTape
              (.stop0 current later advance))).take decoded.blocksUsed =
            (List.ofFn (routedGammaBlocks
              (.stop0 current later advance) 0)).take decoded.blocksUsed := by
        have interval := take_drop_ofFn_unrouteCoordinates
          (routedGammaIndex (.stop0 current later advance))
          (routedGammaBlocks (.stop0 current later advance)) 0 0
          decoded.blocksUsed decodedBound (by omega)
          (by
            intro block before
            simpa [routedGammaIndex] using
              stop0IndexEquiv_first_interval block)
        simpa [gammaOutputBlocks, routedGammaFlatTape] using interval
      have targetRun := decodeOrdinaryPrefix_of_matching_consumed_prefix
        (List.ofFn (routedGammaBlocks (.stop0 current later advance) 0))
        (gammaOutputBlocks (routedGammaFlatTape
          (.stop0 current later advance))) decoded sourceRun (by
            simp [gammaOutputBlocks, routedGammaFlatTape]
            omega)
        prefixEq
      have nonzero : decoded.value ≠ zeroBytes 16 := by
        exact successfulNonzeroRawOrdinaryDecode_value current
      exact ⟨{ decoded with remainingBlocks :=
          (gammaOutputBlocks (routedGammaFlatTape
            (.stop0 current later advance))).drop decoded.blocksUsed },
        GammaPrefixTrace.stop targetRun nonzero, by
          change decodeTagQM31ExactLE decoded.value =
            some (routedSuccessfulGammaValue
              (.stop0 current later advance)).1
          rw [show decoded = successfulRawOrdinaryDecode current.1 by rfl]
          rw [successfulRawOrdinaryDecode_value_eq_exact_encoding,
            decodeTagQM31ExactLE_encodeTagQM31ExactLE]
          rfl⟩
  | stop1 before current later advance =>
      let firstDecoded := successfulRawOrdinaryDecode before.1
      let currentDecoded := successfulRawOrdinaryDecode current.1
      have firstBounds :=
        successfulRawOrdinaryDecode_blocksUsed_bounds before.1
      have currentBounds :=
        successfulRawOrdinaryDecode_blocksUsed_bounds current.1
      have firstBound : firstDecoded.blocksUsed ≤ 4 := by
        simpa [firstDecoded] using firstBounds.2
      have currentBound : currentDecoded.blocksUsed ≤ 4 := by
        simpa [currentDecoded] using currentBounds.2
      have firstSourceRun :
          decodeOrdinaryPrefix
              (List.ofFn (routedGammaBlocks
                (.stop1 before current later advance) 0)) =
            some firstDecoded := by
        simpa [routedGammaBlocks, routedGammaRawStreams, firstDecoded] using
          successfulRawOrdinaryDecode_run before.1
      have currentSourceRun :
          decodeOrdinaryPrefix
              (List.ofFn (routedGammaBlocks
                (.stop1 before current later advance) 1)) =
            some currentDecoded := by
        rw [show routedGammaBlocks (.stop1 before current later advance) 1 =
            fourGammaBlocksRawEquiv.symm current.1 by
          simp [routedGammaBlocks]]
        simpa [currentDecoded] using
          successfulRawOrdinaryDecode_run current.1
      have firstPrefix :
          (gammaOutputBlocks (routedGammaFlatTape
              (.stop1 before current later advance))).take
                firstDecoded.blocksUsed =
            (List.ofFn (routedGammaBlocks
              (.stop1 before current later advance) 0)).take
                firstDecoded.blocksUsed := by
        have interval := take_drop_ofFn_unrouteCoordinates
          (routedGammaIndex (.stop1 before current later advance))
          (routedGammaBlocks (.stop1 before current later advance)) 0 0
          firstDecoded.blocksUsed firstBound (by omega)
          (by
            intro block blockBefore
            simpa [routedGammaIndex, firstDecoded, currentDecoded] using
              stop1IndexEquiv_first_interval
                firstDecoded.blocksUsed currentDecoded.blocksUsed
                (by simpa [firstDecoded] using firstBounds.1) firstBound
                (by simpa [currentDecoded] using currentBounds.1) currentBound
                block blockBefore)
        simpa [gammaOutputBlocks, routedGammaFlatTape] using interval
      have firstRun := decodeOrdinaryPrefix_of_matching_consumed_prefix
        (List.ofFn (routedGammaBlocks
          (.stop1 before current later advance) 0))
        (gammaOutputBlocks (routedGammaFlatTape
          (.stop1 before current later advance))) firstDecoded firstSourceRun
        (by simp [gammaOutputBlocks, routedGammaFlatTape]; omega) firstPrefix
      have currentPrefix :
          ((gammaOutputBlocks (routedGammaFlatTape
              (.stop1 before current later advance))).drop
                firstDecoded.blocksUsed).take currentDecoded.blocksUsed =
            (List.ofFn (routedGammaBlocks
              (.stop1 before current later advance) 1)).take
                currentDecoded.blocksUsed := by
        have interval := take_drop_ofFn_unrouteCoordinates
          (routedGammaIndex (.stop1 before current later advance))
          (routedGammaBlocks (.stop1 before current later advance)) 1
          firstDecoded.blocksUsed currentDecoded.blocksUsed currentBound
          (by omega)
          (by
            intro block blockBefore
            simpa [routedGammaIndex, firstDecoded, currentDecoded] using
              stop1IndexEquiv_second_interval
                firstDecoded.blocksUsed currentDecoded.blocksUsed
                (by simpa [firstDecoded] using firstBounds.1) firstBound
                (by simpa [currentDecoded] using currentBounds.1) currentBound
                block blockBefore)
        simpa [gammaOutputBlocks, routedGammaFlatTape] using interval
      have currentRun := decodeOrdinaryPrefix_of_matching_consumed_prefix
        (List.ofFn (routedGammaBlocks
          (.stop1 before current later advance) 1))
        ((gammaOutputBlocks (routedGammaFlatTape
          (.stop1 before current later advance))).drop
            firstDecoded.blocksUsed)
        currentDecoded currentSourceRun
        (by
          simp [gammaOutputBlocks, routedGammaFlatTape]
          omega)
        currentPrefix
      have firstZero : firstDecoded.value = zeroBytes 16 := by
        exact successfulZeroRawOrdinaryDecode_value before
      have currentNonzero : currentDecoded.value ≠ zeroBytes 16 := by
        exact successfulNonzeroRawOrdinaryDecode_value current
      exact ⟨{ currentDecoded with remainingBlocks :=
          ((gammaOutputBlocks (routedGammaFlatTape
            (.stop1 before current later advance))).drop
              firstDecoded.blocksUsed).drop currentDecoded.blocksUsed },
        GammaPrefixTrace.next firstRun firstZero
          (GammaPrefixTrace.stop currentRun currentNonzero), by
          change decodeTagQM31ExactLE currentDecoded.value =
            some (routedSuccessfulGammaValue
              (.stop1 before current later advance)).1
          rw [show currentDecoded = successfulRawOrdinaryDecode current.1 by rfl]
          rw [successfulRawOrdinaryDecode_value_eq_exact_encoding,
            decodeTagQM31ExactLE_encodeTagQM31ExactLE]
          rfl⟩
  | stop2 first second current advance =>
      let firstDecoded := successfulRawOrdinaryDecode first.1
      let secondDecoded := successfulRawOrdinaryDecode second.1
      let currentDecoded := successfulRawOrdinaryDecode current.1
      have firstBounds := successfulRawOrdinaryDecode_blocksUsed_bounds first.1
      have secondBounds := successfulRawOrdinaryDecode_blocksUsed_bounds second.1
      have currentBounds := successfulRawOrdinaryDecode_blocksUsed_bounds current.1
      have firstBound : firstDecoded.blocksUsed ≤ 4 := by
        simpa [firstDecoded] using firstBounds.2
      have secondBound : secondDecoded.blocksUsed ≤ 4 := by
        simpa [secondDecoded] using secondBounds.2
      have currentBound : currentDecoded.blocksUsed ≤ 4 := by
        simpa [currentDecoded] using currentBounds.2
      have firstSourceRun :
          decodeOrdinaryPrefix (List.ofFn (routedGammaBlocks
              (.stop2 first second current advance) 0)) = some firstDecoded := by
        simpa [routedGammaBlocks, routedGammaRawStreams, firstDecoded] using
          successfulRawOrdinaryDecode_run first.1
      have secondSourceRun :
          decodeOrdinaryPrefix (List.ofFn (routedGammaBlocks
              (.stop2 first second current advance) 1)) = some secondDecoded := by
        rw [show routedGammaBlocks (.stop2 first second current advance) 1 =
            fourGammaBlocksRawEquiv.symm second.1 by
          simp [routedGammaBlocks]]
        simpa [secondDecoded] using successfulRawOrdinaryDecode_run second.1
      have currentSourceRun :
          decodeOrdinaryPrefix (List.ofFn (routedGammaBlocks
              (.stop2 first second current advance) 2)) = some currentDecoded := by
        rw [show routedGammaBlocks (.stop2 first second current advance) 2 =
            fourGammaBlocksRawEquiv.symm current.1 by
          simp [routedGammaBlocks]]
        simpa [currentDecoded] using successfulRawOrdinaryDecode_run current.1
      have firstPrefix :
          (gammaOutputBlocks (routedGammaFlatTape
              (.stop2 first second current advance))).take
                firstDecoded.blocksUsed =
            (List.ofFn (routedGammaBlocks
              (.stop2 first second current advance) 0)).take
                firstDecoded.blocksUsed := by
        have interval := take_drop_ofFn_unrouteCoordinates
          (routedGammaIndex (.stop2 first second current advance))
          (routedGammaBlocks (.stop2 first second current advance)) 0 0
          firstDecoded.blocksUsed firstBound (by omega)
          (by
            intro block blockBefore
            simpa [routedGammaIndex, firstDecoded, secondDecoded,
              currentDecoded] using
              stop2IndexEquiv_first_interval
                firstDecoded.blocksUsed secondDecoded.blocksUsed
                currentDecoded.blocksUsed
                (by simpa [firstDecoded] using firstBounds.1) firstBound
                (by simpa [secondDecoded] using secondBounds.1) secondBound
                (by simpa [currentDecoded] using currentBounds.1) currentBound
                block blockBefore)
        simpa [gammaOutputBlocks, routedGammaFlatTape] using interval
      have firstRun := decodeOrdinaryPrefix_of_matching_consumed_prefix
        (List.ofFn (routedGammaBlocks
          (.stop2 first second current advance) 0))
        (gammaOutputBlocks (routedGammaFlatTape
          (.stop2 first second current advance))) firstDecoded firstSourceRun
        (by simp [gammaOutputBlocks, routedGammaFlatTape]; omega) firstPrefix
      have secondPrefix :
          ((gammaOutputBlocks (routedGammaFlatTape
              (.stop2 first second current advance))).drop
                firstDecoded.blocksUsed).take secondDecoded.blocksUsed =
            (List.ofFn (routedGammaBlocks
              (.stop2 first second current advance) 1)).take
                secondDecoded.blocksUsed := by
        have interval := take_drop_ofFn_unrouteCoordinates
          (routedGammaIndex (.stop2 first second current advance))
          (routedGammaBlocks (.stop2 first second current advance)) 1
          firstDecoded.blocksUsed secondDecoded.blocksUsed secondBound
          (by omega)
          (by
            intro block blockBefore
            simpa [routedGammaIndex, firstDecoded, secondDecoded,
              currentDecoded] using
              stop2IndexEquiv_second_interval
                firstDecoded.blocksUsed secondDecoded.blocksUsed
                currentDecoded.blocksUsed
                (by simpa [firstDecoded] using firstBounds.1) firstBound
                (by simpa [secondDecoded] using secondBounds.1) secondBound
                (by simpa [currentDecoded] using currentBounds.1) currentBound
                block blockBefore)
        simpa [gammaOutputBlocks, routedGammaFlatTape] using interval
      have secondRun := decodeOrdinaryPrefix_of_matching_consumed_prefix
        (List.ofFn (routedGammaBlocks
          (.stop2 first second current advance) 1))
        ((gammaOutputBlocks (routedGammaFlatTape
          (.stop2 first second current advance))).drop firstDecoded.blocksUsed)
        secondDecoded secondSourceRun
        (by simp [gammaOutputBlocks, routedGammaFlatTape]; omega) secondPrefix
      have currentPrefix :
          ((gammaOutputBlocks (routedGammaFlatTape
              (.stop2 first second current advance))).drop
                (firstDecoded.blocksUsed + secondDecoded.blocksUsed)).take
                  currentDecoded.blocksUsed =
            (List.ofFn (routedGammaBlocks
              (.stop2 first second current advance) 2)).take
                currentDecoded.blocksUsed := by
        have interval := take_drop_ofFn_unrouteCoordinates
          (routedGammaIndex (.stop2 first second current advance))
          (routedGammaBlocks (.stop2 first second current advance)) 2
          (firstDecoded.blocksUsed + secondDecoded.blocksUsed)
          currentDecoded.blocksUsed currentBound (by omega)
          (by
            intro block blockBefore
            simpa [routedGammaIndex, firstDecoded, secondDecoded,
              currentDecoded] using
              stop2IndexEquiv_third_interval
                firstDecoded.blocksUsed secondDecoded.blocksUsed
                currentDecoded.blocksUsed
                (by simpa [firstDecoded] using firstBounds.1) firstBound
                (by simpa [secondDecoded] using secondBounds.1) secondBound
                (by simpa [currentDecoded] using currentBounds.1) currentBound
                block blockBefore)
        simpa [gammaOutputBlocks, routedGammaFlatTape] using interval
      have dropDrop :
          ((gammaOutputBlocks (routedGammaFlatTape
            (.stop2 first second current advance))).drop
              firstDecoded.blocksUsed).drop secondDecoded.blocksUsed =
            (gammaOutputBlocks (routedGammaFlatTape
              (.stop2 first second current advance))).drop
                (firstDecoded.blocksUsed + secondDecoded.blocksUsed) := by
        rw [List.drop_drop]
      have currentRun := decodeOrdinaryPrefix_of_matching_consumed_prefix
        (List.ofFn (routedGammaBlocks
          (.stop2 first second current advance) 2))
        ((gammaOutputBlocks (routedGammaFlatTape
          (.stop2 first second current advance))).drop
            (firstDecoded.blocksUsed + secondDecoded.blocksUsed))
        currentDecoded currentSourceRun
        (by simp [gammaOutputBlocks, routedGammaFlatTape]; omega) currentPrefix
      have firstZero : firstDecoded.value = zeroBytes 16 := by
        exact successfulZeroRawOrdinaryDecode_value first
      have secondZero : secondDecoded.value = zeroBytes 16 := by
        exact successfulZeroRawOrdinaryDecode_value second
      have currentNonzero : currentDecoded.value ≠ zeroBytes 16 := by
        exact successfulNonzeroRawOrdinaryDecode_value current
      rw [← dropDrop] at currentRun
      exact ⟨{ currentDecoded with remainingBlocks :=
          (List.drop currentDecoded.blocksUsed
            (List.drop secondDecoded.blocksUsed
              (List.drop firstDecoded.blocksUsed
                (gammaOutputBlocks (routedGammaFlatTape
                  (.stop2 first second current advance)))))) },
        GammaPrefixTrace.next firstRun firstZero
          (GammaPrefixTrace.next secondRun secondZero
            (GammaPrefixTrace.stop currentRun currentNonzero)), by
          change decodeTagQM31ExactLE currentDecoded.value =
            some (routedSuccessfulGammaValue
              (.stop2 first second current advance)).1
          rw [show currentDecoded = successfulRawOrdinaryDecode current.1 by rfl]
          rw [successfulRawOrdinaryDecode_value_eq_exact_encoding,
            decodeTagQM31ExactLE_encodeTagQM31ExactLE]
          rfl⟩

theorem routedGammaFlatTape_succeeds
    (sample : RoutedSuccessfulGammaTape) :
    GammaPrefixSucceeds (routedGammaFlatTape sample) := by
  obtain ⟨decoded, trace, exactValue⟩ := routedGammaFlatTape_trace sample
  have indexed := (decodeNonzeroPrefixIndexed_iff_trace 3
    (gammaOutputBlocks (routedGammaFlatTape sample))
    (routedGammaStopIndex sample) decoded).mpr trace
  unfold GammaPrefixSucceeds runGammaPrefix
  rw [← decodeNonzeroPrefixIndexed_forget 3]
  rw [indexed]
  rfl

theorem routedGammaFlatTape_stopsAt
    (sample : RoutedSuccessfulGammaTape) :
    GammaPrefixStopsAt (routedGammaStopIndex sample)
      (routedGammaFlatTape sample) := by
  obtain ⟨decoded, trace, exactValue⟩ := routedGammaFlatTape_trace sample
  have indexed := (decodeNonzeroPrefixIndexed_iff_trace 3
    (gammaOutputBlocks (routedGammaFlatTape sample))
    (routedGammaStopIndex sample) decoded).mpr trace
  unfold GammaPrefixStopsAt
  rw [indexed]
  rfl

theorem routedGammaFlatTape_returned_exact_value
    (sample : RoutedSuccessfulGammaTape) (decoded : OrdinaryPrefixDecode)
    (run : runGammaPrefix (routedGammaFlatTape sample) = some decoded) :
    decodeTagQM31ExactLE decoded.value =
      some (routedSuccessfulGammaValue sample).1 := by
  obtain ⟨canonical, trace, exactValue⟩ :=
    routedGammaFlatTape_trace sample
  have indexed := (decodeNonzeroPrefixIndexed_iff_trace 3
    (gammaOutputBlocks (routedGammaFlatTape sample))
    (routedGammaStopIndex sample) canonical).mpr trace
  have canonicalRun :
      runGammaPrefix (routedGammaFlatTape sample) = some canonical := by
    unfold runGammaPrefix
    rw [← decodeNonzeroPrefixIndexed_forget 3]
    rw [indexed]
    rfl
  rw [canonicalRun] at run
  cases Option.some.inj run
  exact exactValue

/-- Every routed successful branch has an executable chronological production
tape.  Unused suffix coordinates remain arbitrary and are only permuted. -/
def routedSuccessfulGammaToFlat :
    RoutedSuccessfulGammaTape → SuccessfulGammaPrefixTape :=
  fun sample => ⟨routedGammaFlatTape sample,
    routedGammaFlatTape_succeeds sample⟩

@[simp] theorem route_routedGammaFlatTape_outputs
    (sample : RoutedSuccessfulGammaTape) :
    routeCoordinates (routedGammaIndex sample)
        (routedGammaFlatTape sample).1 = routedGammaBlocks sample := by
  simpa only [routedGammaFlatTape] using
    route_unroute_coordinates (routedGammaIndex sample)
      (routedGammaBlocks sample)

@[simp] theorem route_routedGammaFlatTape_advances
    (sample : RoutedSuccessfulGammaTape) :
    routeCoordinates (routedGammaIndex sample)
        (routedGammaFlatTape sample).2 = routedGammaAdvances sample := by
  simpa only [routedGammaFlatTape] using
    route_unroute_coordinates (routedGammaIndex sample)
      (routedGammaAdvances sample)

theorem route_routedGammaFlatTape_raw
    (sample : RoutedSuccessfulGammaTape) (attempt : Fin 3) :
    fourGammaBlocksRawEquiv
        (routeCoordinates (routedGammaIndex sample)
          (routedGammaFlatTape sample).1 attempt) =
      routedGammaRawStreams sample attempt := by
  rw [route_routedGammaFlatTape_outputs]
  exact fourGammaBlocksRawEquiv.apply_symm_apply _

/-- The adaptive routing permutation is recoverable from the chronological
tape.  Its dynamic lengths are outputs of deterministic ordinary decodes at
the reached offsets. -/
theorem routedGammaIndex_eq_of_flatTape_eq
    (left right : RoutedSuccessfulGammaTape)
    (flatEq : routedGammaFlatTape left = routedGammaFlatTape right) :
    routedGammaIndex left = routedGammaIndex right := by
  have stopEq : routedGammaStopIndex left = routedGammaStopIndex right := by
    apply gamma_prefix_stopping_branches_disjoint (routedGammaFlatTape left)
    · exact routedGammaFlatTape_stopsAt left
    · rw [flatEq]
      exact routedGammaFlatTape_stopsAt right
  cases left with
  | stop0 leftCurrent leftLater leftAdvance =>
      cases right with
      | stop0 rightCurrent rightLater rightAdvance => rfl
      | stop1 _ _ _ _ =>
          have impossible := congrArg Fin.val stopEq
          norm_num [routedGammaStopIndex] at impossible
      | stop2 _ _ _ _ =>
          have impossible := congrArg Fin.val stopEq
          norm_num [routedGammaStopIndex] at impossible
  | stop1 leftBefore leftCurrent leftLater leftAdvance =>
      cases right with
      | stop0 _ _ _ =>
          have impossible := congrArg Fin.val stopEq
          norm_num [routedGammaStopIndex] at impossible
      | stop1 rightBefore rightCurrent rightLater rightAdvance =>
          let leftFirst := successfulRawOrdinaryDecode leftBefore.1
          let leftSecond := successfulRawOrdinaryDecode leftCurrent.1
          let rightFirst := successfulRawOrdinaryDecode rightBefore.1
          let rightSecond := successfulRawOrdinaryDecode rightCurrent.1
          have leftFirstBounds :=
            successfulRawOrdinaryDecode_blocksUsed_bounds leftBefore.1
          have leftSecondBounds :=
            successfulRawOrdinaryDecode_blocksUsed_bounds leftCurrent.1
          have rightFirstBounds :=
            successfulRawOrdinaryDecode_blocksUsed_bounds rightBefore.1
          have rightSecondBounds :=
            successfulRawOrdinaryDecode_blocksUsed_bounds rightCurrent.1
          have leftFirstPositive : 0 < leftFirst.blocksUsed := by
            simpa [leftFirst] using leftFirstBounds.1
          have leftFirstBound : leftFirst.blocksUsed ≤ 4 := by
            simpa [leftFirst] using leftFirstBounds.2
          have leftSecondPositive : 0 < leftSecond.blocksUsed := by
            simpa [leftSecond] using leftSecondBounds.1
          have leftSecondBound : leftSecond.blocksUsed ≤ 4 := by
            simpa [leftSecond] using leftSecondBounds.2
          have rightFirstPositive : 0 < rightFirst.blocksUsed := by
            simpa [rightFirst] using rightFirstBounds.1
          have rightFirstBound : rightFirst.blocksUsed ≤ 4 := by
            simpa [rightFirst] using rightFirstBounds.2
          have rightSecondPositive : 0 < rightSecond.blocksUsed := by
            simpa [rightSecond] using rightSecondBounds.1
          have rightSecondBound : rightSecond.blocksUsed ≤ 4 := by
            simpa [rightSecond] using rightSecondBounds.2
          have leftFirstSource :
              decodeOrdinaryPrefix
                  (List.ofFn (routedGammaBlocks
                    (.stop1 leftBefore leftCurrent leftLater leftAdvance) 0)) =
                some leftFirst := by
            simpa [routedGammaBlocks, routedGammaRawStreams, leftFirst] using
              successfulRawOrdinaryDecode_run leftBefore.1
          have rightFirstSource :
              decodeOrdinaryPrefix
                  (List.ofFn (routedGammaBlocks
                    (.stop1 rightBefore rightCurrent rightLater rightAdvance) 0)) =
                some rightFirst := by
            simpa [routedGammaBlocks, routedGammaRawStreams, rightFirst] using
              successfulRawOrdinaryDecode_run rightBefore.1
          have leftFirstRun := routedGammaFlatTape_decode_at
            (.stop1 leftBefore leftCurrent leftLater leftAdvance) 0 0 leftFirst
            leftFirstSource leftFirstBound
            (by omega)
            (by
              intro block before
              simpa [routedGammaIndex, leftFirst, leftSecond] using
                stop1IndexEquiv_first_interval
                  leftFirst.blocksUsed leftSecond.blocksUsed
                  leftFirstPositive leftFirstBound
                  leftSecondPositive leftSecondBound
                  block before)
          have rightFirstRun := routedGammaFlatTape_decode_at
            (.stop1 rightBefore rightCurrent rightLater rightAdvance) 0 0
            rightFirst rightFirstSource
            rightFirstBound (by omega)
            (by
              intro block before
              simpa [routedGammaIndex, rightFirst, rightSecond] using
                stop1IndexEquiv_first_interval
                  rightFirst.blocksUsed rightSecond.blocksUsed
                  rightFirstPositive rightFirstBound
                  rightSecondPositive rightSecondBound
                  block before)
          rw [flatEq] at leftFirstRun
          have firstDecodedEq :=
            Option.some.inj (leftFirstRun.symm.trans rightFirstRun)
          have firstUsedEq : leftFirst.blocksUsed = rightFirst.blocksUsed := by
            simpa using congrArg OrdinaryPrefixDecode.blocksUsed firstDecodedEq
          have leftSecondSource :
              decodeOrdinaryPrefix
                  (List.ofFn (routedGammaBlocks
                    (.stop1 leftBefore leftCurrent leftLater leftAdvance) 1)) =
                some leftSecond := by
            rw [show routedGammaBlocks
                (.stop1 leftBefore leftCurrent leftLater leftAdvance) 1 =
                  fourGammaBlocksRawEquiv.symm leftCurrent.1 by
              simp [routedGammaBlocks]]
            simpa [leftSecond] using
              successfulRawOrdinaryDecode_run leftCurrent.1
          have rightSecondSource :
              decodeOrdinaryPrefix
                  (List.ofFn (routedGammaBlocks
                    (.stop1 rightBefore rightCurrent rightLater rightAdvance) 1)) =
                some rightSecond := by
            rw [show routedGammaBlocks
                (.stop1 rightBefore rightCurrent rightLater rightAdvance) 1 =
                  fourGammaBlocksRawEquiv.symm rightCurrent.1 by
              simp [routedGammaBlocks]]
            simpa [rightSecond] using
              successfulRawOrdinaryDecode_run rightCurrent.1
          have leftSecondRun := routedGammaFlatTape_decode_at
            (.stop1 leftBefore leftCurrent leftLater leftAdvance) 1
            leftFirst.blocksUsed leftSecond leftSecondSource
            leftSecondBound (by omega)
            (by
              intro block before
              simpa [routedGammaIndex, leftFirst, leftSecond] using
                stop1IndexEquiv_second_interval
                  leftFirst.blocksUsed leftSecond.blocksUsed
                  leftFirstPositive leftFirstBound
                  leftSecondPositive leftSecondBound
                  block before)
          have rightSecondRun := routedGammaFlatTape_decode_at
            (.stop1 rightBefore rightCurrent rightLater rightAdvance) 1
            rightFirst.blocksUsed rightSecond rightSecondSource
            rightSecondBound (by omega)
            (by
              intro block before
              simpa [routedGammaIndex, rightFirst, rightSecond] using
                stop1IndexEquiv_second_interval
                  rightFirst.blocksUsed rightSecond.blocksUsed
                  rightFirstPositive rightFirstBound
                  rightSecondPositive rightSecondBound
                  block before)
          rw [flatEq, firstUsedEq] at leftSecondRun
          have secondDecodedEq :=
            Option.some.inj (leftSecondRun.symm.trans rightSecondRun)
          have secondUsedEq : leftSecond.blocksUsed = rightSecond.blocksUsed := by
            simpa using congrArg OrdinaryPrefixDecode.blocksUsed secondDecodedEq
          simp only [routedGammaIndex]
          have firstUsedEq' :
              (successfulRawOrdinaryDecode leftBefore.1).blocksUsed =
                (successfulRawOrdinaryDecode rightBefore.1).blocksUsed := by
            simpa [leftFirst, rightFirst] using firstUsedEq
          have secondUsedEq' :
              (successfulRawOrdinaryDecode leftCurrent.1).blocksUsed =
                (successfulRawOrdinaryDecode rightCurrent.1).blocksUsed := by
            simpa [leftSecond, rightSecond] using secondUsedEq
          apply Equiv.ext
          intro coordinate
          apply Fin.ext
          change
            (stop1ToIndex
              (successfulRawOrdinaryDecode leftBefore.1).blocksUsed
              (successfulRawOrdinaryDecode leftCurrent.1).blocksUsed
              (successfulRawOrdinaryDecode_blocksUsed_bounds leftBefore.1).1
              (successfulRawOrdinaryDecode_blocksUsed_bounds leftBefore.1).2
              (successfulRawOrdinaryDecode_blocksUsed_bounds leftCurrent.1).1
              (successfulRawOrdinaryDecode_blocksUsed_bounds leftCurrent.1).2
              coordinate).val =
            (stop1ToIndex
              (successfulRawOrdinaryDecode rightBefore.1).blocksUsed
              (successfulRawOrdinaryDecode rightCurrent.1).blocksUsed
              (successfulRawOrdinaryDecode_blocksUsed_bounds rightBefore.1).1
              (successfulRawOrdinaryDecode_blocksUsed_bounds rightBefore.1).2
              (successfulRawOrdinaryDecode_blocksUsed_bounds rightCurrent.1).1
              (successfulRawOrdinaryDecode_blocksUsed_bounds rightCurrent.1).2
              coordinate).val
          rw [stop1ToIndex_val, stop1ToIndex_val, firstUsedEq', secondUsedEq']
      | stop2 _ _ _ _ =>
          have impossible := congrArg Fin.val stopEq
          norm_num [routedGammaStopIndex] at impossible
  | stop2 leftFirstRaw leftSecondRaw leftCurrent leftAdvance =>
      cases right with
      | stop0 _ _ _ =>
          have impossible := congrArg Fin.val stopEq
          norm_num [routedGammaStopIndex] at impossible
      | stop1 _ _ _ _ =>
          have impossible := congrArg Fin.val stopEq
          norm_num [routedGammaStopIndex] at impossible
      | stop2 rightFirstRaw rightSecondRaw rightCurrent rightAdvance =>
          let leftFirst := successfulRawOrdinaryDecode leftFirstRaw.1
          let leftSecond := successfulRawOrdinaryDecode leftSecondRaw.1
          let leftThird := successfulRawOrdinaryDecode leftCurrent.1
          let rightFirst := successfulRawOrdinaryDecode rightFirstRaw.1
          let rightSecond := successfulRawOrdinaryDecode rightSecondRaw.1
          let rightThird := successfulRawOrdinaryDecode rightCurrent.1
          have leftFirstBounds :=
            successfulRawOrdinaryDecode_blocksUsed_bounds leftFirstRaw.1
          have leftSecondBounds :=
            successfulRawOrdinaryDecode_blocksUsed_bounds leftSecondRaw.1
          have leftThirdBounds :=
            successfulRawOrdinaryDecode_blocksUsed_bounds leftCurrent.1
          have rightFirstBounds :=
            successfulRawOrdinaryDecode_blocksUsed_bounds rightFirstRaw.1
          have rightSecondBounds :=
            successfulRawOrdinaryDecode_blocksUsed_bounds rightSecondRaw.1
          have rightThirdBounds :=
            successfulRawOrdinaryDecode_blocksUsed_bounds rightCurrent.1
          have leftFirstPositive : 0 < leftFirst.blocksUsed := by
            simpa [leftFirst] using leftFirstBounds.1
          have leftFirstBound : leftFirst.blocksUsed ≤ 4 := by
            simpa [leftFirst] using leftFirstBounds.2
          have leftSecondPositive : 0 < leftSecond.blocksUsed := by
            simpa [leftSecond] using leftSecondBounds.1
          have leftSecondBound : leftSecond.blocksUsed ≤ 4 := by
            simpa [leftSecond] using leftSecondBounds.2
          have leftThirdPositive : 0 < leftThird.blocksUsed := by
            simpa [leftThird] using leftThirdBounds.1
          have leftThirdBound : leftThird.blocksUsed ≤ 4 := by
            simpa [leftThird] using leftThirdBounds.2
          have rightFirstPositive : 0 < rightFirst.blocksUsed := by
            simpa [rightFirst] using rightFirstBounds.1
          have rightFirstBound : rightFirst.blocksUsed ≤ 4 := by
            simpa [rightFirst] using rightFirstBounds.2
          have rightSecondPositive : 0 < rightSecond.blocksUsed := by
            simpa [rightSecond] using rightSecondBounds.1
          have rightSecondBound : rightSecond.blocksUsed ≤ 4 := by
            simpa [rightSecond] using rightSecondBounds.2
          have rightThirdPositive : 0 < rightThird.blocksUsed := by
            simpa [rightThird] using rightThirdBounds.1
          have rightThirdBound : rightThird.blocksUsed ≤ 4 := by
            simpa [rightThird] using rightThirdBounds.2
          have leftFirstSource :
              decodeOrdinaryPrefix
                  (List.ofFn (routedGammaBlocks
                    (.stop2 leftFirstRaw leftSecondRaw leftCurrent leftAdvance) 0)) =
                some leftFirst := by
            simpa [routedGammaBlocks, routedGammaRawStreams, leftFirst] using
              successfulRawOrdinaryDecode_run leftFirstRaw.1
          have rightFirstSource :
              decodeOrdinaryPrefix
                  (List.ofFn (routedGammaBlocks
                    (.stop2 rightFirstRaw rightSecondRaw rightCurrent rightAdvance) 0)) =
                some rightFirst := by
            simpa [routedGammaBlocks, routedGammaRawStreams, rightFirst] using
              successfulRawOrdinaryDecode_run rightFirstRaw.1
          have leftFirstRun := routedGammaFlatTape_decode_at
            (.stop2 leftFirstRaw leftSecondRaw leftCurrent leftAdvance) 0 0
            leftFirst leftFirstSource
            leftFirstBound (by omega)
            (by
              intro block before
              simpa [routedGammaIndex, leftFirst, leftSecond, leftThird] using
                stop2IndexEquiv_first_interval
                  leftFirst.blocksUsed leftSecond.blocksUsed leftThird.blocksUsed
                  leftFirstPositive leftFirstBound
                  leftSecondPositive leftSecondBound
                  leftThirdPositive leftThirdBound
                  block before)
          have rightFirstRun := routedGammaFlatTape_decode_at
            (.stop2 rightFirstRaw rightSecondRaw rightCurrent rightAdvance) 0 0
            rightFirst rightFirstSource
            rightFirstBound (by omega)
            (by
              intro block before
              simpa [routedGammaIndex, rightFirst, rightSecond, rightThird] using
                stop2IndexEquiv_first_interval
                  rightFirst.blocksUsed rightSecond.blocksUsed
                  rightThird.blocksUsed
                  rightFirstPositive rightFirstBound
                  rightSecondPositive rightSecondBound
                  rightThirdPositive rightThirdBound
                  block before)
          rw [flatEq] at leftFirstRun
          have firstDecodedEq :=
            Option.some.inj (leftFirstRun.symm.trans rightFirstRun)
          have firstUsedEq : leftFirst.blocksUsed = rightFirst.blocksUsed := by
            simpa using congrArg OrdinaryPrefixDecode.blocksUsed firstDecodedEq
          have leftSecondSource :
              decodeOrdinaryPrefix
                  (List.ofFn (routedGammaBlocks
                    (.stop2 leftFirstRaw leftSecondRaw leftCurrent leftAdvance) 1)) =
                some leftSecond := by
            rw [show routedGammaBlocks
                (.stop2 leftFirstRaw leftSecondRaw leftCurrent leftAdvance) 1 =
                  fourGammaBlocksRawEquiv.symm leftSecondRaw.1 by
              simp [routedGammaBlocks]]
            simpa [leftSecond] using
              successfulRawOrdinaryDecode_run leftSecondRaw.1
          have rightSecondSource :
              decodeOrdinaryPrefix
                  (List.ofFn (routedGammaBlocks
                    (.stop2 rightFirstRaw rightSecondRaw rightCurrent rightAdvance) 1)) =
                some rightSecond := by
            rw [show routedGammaBlocks
                (.stop2 rightFirstRaw rightSecondRaw rightCurrent rightAdvance) 1 =
                  fourGammaBlocksRawEquiv.symm rightSecondRaw.1 by
              simp [routedGammaBlocks]]
            simpa [rightSecond] using
              successfulRawOrdinaryDecode_run rightSecondRaw.1
          have leftSecondRun := routedGammaFlatTape_decode_at
            (.stop2 leftFirstRaw leftSecondRaw leftCurrent leftAdvance) 1
            leftFirst.blocksUsed leftSecond leftSecondSource
            leftSecondBound (by omega)
            (by
              intro block before
              simpa [routedGammaIndex, leftFirst, leftSecond, leftThird] using
                stop2IndexEquiv_second_interval
                  leftFirst.blocksUsed leftSecond.blocksUsed leftThird.blocksUsed
                  leftFirstPositive leftFirstBound
                  leftSecondPositive leftSecondBound
                  leftThirdPositive leftThirdBound
                  block before)
          have rightSecondRun := routedGammaFlatTape_decode_at
            (.stop2 rightFirstRaw rightSecondRaw rightCurrent rightAdvance) 1
            rightFirst.blocksUsed rightSecond rightSecondSource
            rightSecondBound (by omega)
            (by
              intro block before
              simpa [routedGammaIndex, rightFirst, rightSecond, rightThird] using
                stop2IndexEquiv_second_interval
                  rightFirst.blocksUsed rightSecond.blocksUsed
                  rightThird.blocksUsed
                  rightFirstPositive rightFirstBound
                  rightSecondPositive rightSecondBound
                  rightThirdPositive rightThirdBound
                  block before)
          rw [flatEq, firstUsedEq] at leftSecondRun
          have secondDecodedEq :=
            Option.some.inj (leftSecondRun.symm.trans rightSecondRun)
          have secondUsedEq : leftSecond.blocksUsed = rightSecond.blocksUsed := by
            simpa using congrArg OrdinaryPrefixDecode.blocksUsed secondDecodedEq
          have leftThirdSource :
              decodeOrdinaryPrefix
                  (List.ofFn (routedGammaBlocks
                    (.stop2 leftFirstRaw leftSecondRaw leftCurrent leftAdvance) 2)) =
                some leftThird := by
            rw [show routedGammaBlocks
                (.stop2 leftFirstRaw leftSecondRaw leftCurrent leftAdvance) 2 =
                  fourGammaBlocksRawEquiv.symm leftCurrent.1 by
              simp [routedGammaBlocks]]
            simpa [leftThird] using
              successfulRawOrdinaryDecode_run leftCurrent.1
          have rightThirdSource :
              decodeOrdinaryPrefix
                  (List.ofFn (routedGammaBlocks
                    (.stop2 rightFirstRaw rightSecondRaw rightCurrent rightAdvance) 2)) =
                some rightThird := by
            rw [show routedGammaBlocks
                (.stop2 rightFirstRaw rightSecondRaw rightCurrent rightAdvance) 2 =
                  fourGammaBlocksRawEquiv.symm rightCurrent.1 by
              simp [routedGammaBlocks]]
            simpa [rightThird] using
              successfulRawOrdinaryDecode_run rightCurrent.1
          have leftThirdRun := routedGammaFlatTape_decode_at
            (.stop2 leftFirstRaw leftSecondRaw leftCurrent leftAdvance) 2
            (leftFirst.blocksUsed + leftSecond.blocksUsed) leftThird
            leftThirdSource leftThirdBound
            (by omega)
            (by
              intro block before
              simpa [routedGammaIndex, leftFirst, leftSecond, leftThird] using
                stop2IndexEquiv_third_interval
                  leftFirst.blocksUsed leftSecond.blocksUsed leftThird.blocksUsed
                  leftFirstPositive leftFirstBound
                  leftSecondPositive leftSecondBound
                  leftThirdPositive leftThirdBound
                  block before)
          have rightThirdRun := routedGammaFlatTape_decode_at
            (.stop2 rightFirstRaw rightSecondRaw rightCurrent rightAdvance) 2
            (rightFirst.blocksUsed + rightSecond.blocksUsed) rightThird
            rightThirdSource rightThirdBound
            (by omega)
            (by
              intro block before
              simpa [routedGammaIndex, rightFirst, rightSecond, rightThird] using
                stop2IndexEquiv_third_interval
                  rightFirst.blocksUsed rightSecond.blocksUsed
                  rightThird.blocksUsed
                  rightFirstPositive rightFirstBound
                  rightSecondPositive rightSecondBound
                  rightThirdPositive rightThirdBound
                  block before)
          rw [flatEq, firstUsedEq, secondUsedEq] at leftThirdRun
          have thirdDecodedEq :=
            Option.some.inj (leftThirdRun.symm.trans rightThirdRun)
          have thirdUsedEq : leftThird.blocksUsed = rightThird.blocksUsed := by
            simpa using congrArg OrdinaryPrefixDecode.blocksUsed thirdDecodedEq
          simp only [routedGammaIndex]
          have firstUsedEq' :
              (successfulRawOrdinaryDecode leftFirstRaw.1).blocksUsed =
                (successfulRawOrdinaryDecode rightFirstRaw.1).blocksUsed := by
            simpa [leftFirst, rightFirst] using firstUsedEq
          have secondUsedEq' :
              (successfulRawOrdinaryDecode leftSecondRaw.1).blocksUsed =
                (successfulRawOrdinaryDecode rightSecondRaw.1).blocksUsed := by
            simpa [leftSecond, rightSecond] using secondUsedEq
          have thirdUsedEq' :
              (successfulRawOrdinaryDecode leftCurrent.1).blocksUsed =
                (successfulRawOrdinaryDecode rightCurrent.1).blocksUsed := by
            simpa [leftThird, rightThird] using thirdUsedEq
          apply Equiv.ext
          intro coordinate
          apply Fin.ext
          change
            (stop2ToIndex
              (successfulRawOrdinaryDecode leftFirstRaw.1).blocksUsed
              (successfulRawOrdinaryDecode leftSecondRaw.1).blocksUsed
              (successfulRawOrdinaryDecode leftCurrent.1).blocksUsed
              (successfulRawOrdinaryDecode_blocksUsed_bounds leftFirstRaw.1).1
              (successfulRawOrdinaryDecode_blocksUsed_bounds leftFirstRaw.1).2
              (successfulRawOrdinaryDecode_blocksUsed_bounds leftSecondRaw.1).1
              (successfulRawOrdinaryDecode_blocksUsed_bounds leftSecondRaw.1).2
              (successfulRawOrdinaryDecode_blocksUsed_bounds leftCurrent.1).1
              (successfulRawOrdinaryDecode_blocksUsed_bounds leftCurrent.1).2
              coordinate).val =
            (stop2ToIndex
              (successfulRawOrdinaryDecode rightFirstRaw.1).blocksUsed
              (successfulRawOrdinaryDecode rightSecondRaw.1).blocksUsed
              (successfulRawOrdinaryDecode rightCurrent.1).blocksUsed
              (successfulRawOrdinaryDecode_blocksUsed_bounds rightFirstRaw.1).1
              (successfulRawOrdinaryDecode_blocksUsed_bounds rightFirstRaw.1).2
              (successfulRawOrdinaryDecode_blocksUsed_bounds rightSecondRaw.1).1
              (successfulRawOrdinaryDecode_blocksUsed_bounds rightSecondRaw.1).2
              (successfulRawOrdinaryDecode_blocksUsed_bounds rightCurrent.1).1
              (successfulRawOrdinaryDecode_blocksUsed_bounds rightCurrent.1).2
              coordinate).val
          rw [stop2ToIndex_val, stop2ToIndex_val, firstUsedEq', secondUsedEq',
            thirdUsedEq']

/-- The routed branch is completely determined by its stopping tag, three raw
windows, and the routed advance digests. -/
theorem routedSuccessfulGammaTape_eq_of_observations
    (left right : RoutedSuccessfulGammaTape)
    (stopEq : routedGammaStopIndex left = routedGammaStopIndex right)
    (rawEq : routedGammaRawStreams left = routedGammaRawStreams right)
    (advanceEq : routedGammaAdvances left = routedGammaAdvances right) :
    left = right := by
  cases left with
  | stop0 leftCurrent leftLater leftAdvance =>
      cases right with
      | stop0 rightCurrent rightLater rightAdvance =>
          have currentEq : leftCurrent = rightCurrent := by
            apply Subtype.ext
            apply Subtype.ext
            exact congrFun rawEq 0
          have laterEq : leftLater = rightLater := by
            funext attempt
            fin_cases attempt
            · exact congrFun rawEq 1
            · exact congrFun rawEq 2
          cases currentEq
          cases laterEq
          cases advanceEq
          rfl
      | stop1 _ _ _ _ =>
          have impossible := congrArg Fin.val stopEq
          norm_num [routedGammaStopIndex] at impossible
      | stop2 _ _ _ _ =>
          have impossible := congrArg Fin.val stopEq
          norm_num [routedGammaStopIndex] at impossible
  | stop1 leftBefore leftCurrent leftLater leftAdvance =>
      cases right with
      | stop0 _ _ _ =>
          have impossible := congrArg Fin.val stopEq
          norm_num [routedGammaStopIndex] at impossible
      | stop1 rightBefore rightCurrent rightLater rightAdvance =>
          have beforeEq : leftBefore = rightBefore := by
            apply Subtype.ext
            apply Subtype.ext
            exact congrFun rawEq 0
          have currentEq : leftCurrent = rightCurrent := by
            apply Subtype.ext
            apply Subtype.ext
            exact congrFun rawEq 1
          have laterEq : leftLater = rightLater := congrFun rawEq 2
          cases beforeEq
          cases currentEq
          cases laterEq
          cases advanceEq
          rfl
      | stop2 _ _ _ _ =>
          have impossible := congrArg Fin.val stopEq
          norm_num [routedGammaStopIndex] at impossible
  | stop2 leftFirst leftSecond leftCurrent leftAdvance =>
      cases right with
      | stop0 _ _ _ =>
          have impossible := congrArg Fin.val stopEq
          norm_num [routedGammaStopIndex] at impossible
      | stop1 _ _ _ _ =>
          have impossible := congrArg Fin.val stopEq
          norm_num [routedGammaStopIndex] at impossible
      | stop2 rightFirst rightSecond rightCurrent rightAdvance =>
          have firstEq : leftFirst = rightFirst := by
            apply Subtype.ext
            apply Subtype.ext
            exact congrFun rawEq 0
          have secondEq : leftSecond = rightSecond := by
            apply Subtype.ext
            apply Subtype.ext
            exact congrFun rawEq 1
          have currentEq : leftCurrent = rightCurrent := by
            apply Subtype.ext
            apply Subtype.ext
            exact congrFun rawEq 2
          cases firstEq
          cases secondEq
          cases currentEq
          cases advanceEq
          rfl

theorem routedSuccessfulGammaToFlat_surjective :
    Function.Surjective routedSuccessfulGammaToFlat := by
  intro flat
  obtain ⟨stopIndex, stops⟩ :=
    (gamma_prefix_success_iff_stopping_branch flat.1).mp flat.2
  unfold GammaPrefixStopsAt at stops
  cases indexedRun : decodeNonzeroPrefixIndexed 3
      (gammaOutputBlocks flat.1) with
  | none => simp [indexedRun] at stops
  | some result =>
      rcases result with ⟨actualIndex, decoded⟩
      have indexEq : actualIndex = stopIndex := by
        rw [indexedRun] at stops
        exact Option.some.inj stops
      subst stopIndex
      have trace := (decodeNonzeroPrefixIndexed_iff_trace 3
        (gammaOutputBlocks flat.1) actualIndex decoded).mp indexedRun
      cases trace with
      | stop ordinary nonzero =>
          have bounds := decodeOrdinaryPrefix_blocksUsed_bounds _ _ ordinary
          let index := stop0IndexEquiv
          let routedBlocks := routeCoordinates index flat.1.1
          have routedRun := decodeOrdinaryPrefix_routeCoordinates index
            flat.1.1 0 0 decoded (by
              simpa [gammaOutputBlocks] using ordinary) bounds.2 (by omega)
            (by
              intro block before
              simpa [index] using stop0IndexEquiv_first_interval block)
          let routedDecoded : OrdinaryPrefixDecode :=
            { decoded with remainingBlocks :=
                (List.ofFn (routedBlocks 0)).drop decoded.blocksUsed }
          let current : SuccessfulNonzeroGammaOrdinaryRaw :=
            successfulNonzeroRawOfOrdinaryRun (routedBlocks 0) routedDecoded
              (by simpa [routedBlocks, routedDecoded] using routedRun)
              (by simpa [routedDecoded] using nonzero)
          let later : Fin 2 → Tag73RawStream := fun attempt =>
            fourGammaBlocksRawEquiv (routedBlocks attempt.succ)
          let advances : Tag73AdvanceDigestGhosts :=
            routeCoordinates index flat.1.2
          let candidate : RoutedSuccessfulGammaTape :=
            .stop0 current later advances
          refine ⟨candidate, ?_⟩
          apply Subtype.ext
          apply Prod.ext
          · change (routedGammaFlatTape candidate).1 = flat.1.1
            have indexCandidate : routedGammaIndex candidate = index := by rfl
            have blocksCandidate : routedGammaBlocks candidate = routedBlocks := by
              funext attempt
              apply fourGammaBlocksRawEquiv.injective
              simp only [routedGammaBlocks,
                fourGammaBlocksRawEquiv.apply_symm_apply]
              change routedGammaRawStreams candidate attempt =
                fourGammaBlocksRawEquiv (routedBlocks attempt)
              fin_cases attempt <;>
                simp [candidate, current, later,
                  successfulNonzeroRawOfOrdinaryRun,
                  successfulRawOfOrdinaryRun]
            rw [routedGammaFlatTape, indexCandidate, blocksCandidate]
            exact unroute_route_coordinates index flat.1.1
          · change (routedGammaFlatTape candidate).2 = flat.1.2
            have indexCandidate : routedGammaIndex candidate = index := by rfl
            have advancesCandidate : routedGammaAdvances candidate = advances := by
              rfl
            rw [routedGammaFlatTape, indexCandidate, advancesCandidate]
            exact unroute_route_coordinates index flat.1.2
      | @next attempts blocks first final index' ordinary zero tail =>
          cases tail with
          | stop currentRun currentNonzero =>
              have firstBounds :=
                decodeOrdinaryPrefix_blocksUsed_bounds _ _ ordinary
              have currentBounds :=
                decodeOrdinaryPrefix_blocksUsed_bounds _ _ currentRun
              have firstRemaining :=
                decodeOrdinaryPrefix_remaining_eq_drop _ _ ordinary
              let index := stop1IndexEquiv first.blocksUsed decoded.blocksUsed
                firstBounds.1 firstBounds.2 currentBounds.1 currentBounds.2
              let routedBlocks := routeCoordinates index flat.1.1
              have firstRoutedRun := decodeOrdinaryPrefix_routeCoordinates
                index flat.1.1 0 0 first (by
                  simpa [gammaOutputBlocks] using ordinary) firstBounds.2
                (by omega)
                (by
                  intro block before
                  simpa [index] using
                    stop1IndexEquiv_first_interval _ _ _ _ _ _ block before)
              have currentSourceRun :
                  decodeOrdinaryPrefix
                      ((List.ofFn flat.1.1).drop first.blocksUsed) =
                    some decoded := by
                simpa [gammaOutputBlocks, firstRemaining] using currentRun
              have currentRoutedRun := decodeOrdinaryPrefix_routeCoordinates
                index flat.1.1 1 first.blocksUsed decoded currentSourceRun
                currentBounds.2 (by omega)
                (by
                  intro block before
                  simpa [index] using
                    stop1IndexEquiv_second_interval _ _ _ _ _ _ block before)
              let firstRouted : OrdinaryPrefixDecode :=
                { first with remainingBlocks :=
                    (List.ofFn (routedBlocks 0)).drop first.blocksUsed }
              let currentRouted : OrdinaryPrefixDecode :=
                { decoded with remainingBlocks :=
                    (List.ofFn (routedBlocks 1)).drop decoded.blocksUsed }
              let beforeRaw : SuccessfulZeroGammaOrdinaryRaw :=
                successfulZeroRawOfOrdinaryRun (routedBlocks 0) firstRouted
                  (by simpa [routedBlocks, firstRouted] using firstRoutedRun)
                  (by simpa [firstRouted] using zero)
              let currentRaw : SuccessfulNonzeroGammaOrdinaryRaw :=
                successfulNonzeroRawOfOrdinaryRun (routedBlocks 1)
                  currentRouted
                  (by simpa [routedBlocks, currentRouted] using currentRoutedRun)
                  (by simpa [currentRouted] using currentNonzero)
              let laterRaw : Tag73RawStream :=
                fourGammaBlocksRawEquiv (routedBlocks 2)
              let advances : Tag73AdvanceDigestGhosts :=
                routeCoordinates index flat.1.2
              let candidate : RoutedSuccessfulGammaTape :=
                .stop1 beforeRaw currentRaw laterRaw advances
              refine ⟨candidate, ?_⟩
              apply Subtype.ext
              apply Prod.ext
              · change (routedGammaFlatTape candidate).1 = flat.1.1
                have beforeDecode :
                    successfulRawOrdinaryDecode beforeRaw.1 = firstRouted := by
                  exact successfulRawOrdinaryDecode_of_run _ _ (by
                    simpa [routedBlocks, firstRouted] using firstRoutedRun)
                have currentDecode :
                    successfulRawOrdinaryDecode currentRaw.1 = currentRouted := by
                  exact successfulRawOrdinaryDecode_of_run _ _ (by
                    simpa [routedBlocks, currentRouted] using currentRoutedRun)
                have indexCandidate : routedGammaIndex candidate = index := by
                  simp only [candidate, routedGammaIndex]
                  simp [beforeDecode, currentDecode, firstRouted,
                    currentRouted, index]
                have blocksCandidate :
                    routedGammaBlocks candidate = routedBlocks := by
                  funext attempt
                  apply fourGammaBlocksRawEquiv.injective
                  simp only [routedGammaBlocks,
                    fourGammaBlocksRawEquiv.apply_symm_apply]
                  change routedGammaRawStreams candidate attempt =
                    fourGammaBlocksRawEquiv (routedBlocks attempt)
                  fin_cases attempt <;>
                    simp [candidate, beforeRaw, currentRaw, laterRaw,
                      successfulZeroRawOfOrdinaryRun,
                      successfulNonzeroRawOfOrdinaryRun,
                      successfulRawOfOrdinaryRun]
                rw [routedGammaFlatTape, indexCandidate, blocksCandidate]
                exact unroute_route_coordinates index flat.1.1
              · change (routedGammaFlatTape candidate).2 = flat.1.2
                have beforeDecode :
                    successfulRawOrdinaryDecode beforeRaw.1 = firstRouted := by
                  exact successfulRawOrdinaryDecode_of_run _ _ (by
                    simpa [routedBlocks, firstRouted] using firstRoutedRun)
                have currentDecode :
                    successfulRawOrdinaryDecode currentRaw.1 = currentRouted := by
                  exact successfulRawOrdinaryDecode_of_run _ _ (by
                    simpa [routedBlocks, currentRouted] using currentRoutedRun)
                have indexCandidate : routedGammaIndex candidate = index := by
                  simp only [candidate, routedGammaIndex]
                  simp [beforeDecode, currentDecode, firstRouted,
                    currentRouted, index]
                have advancesCandidate :
                    routedGammaAdvances candidate = advances := by rfl
                rw [routedGammaFlatTape, indexCandidate, advancesCandidate]
                exact unroute_route_coordinates index flat.1.2
          | @next attempts2 blocks2 second final2 index2 secondRun secondZero last =>
              cases last with
              | stop currentRun currentNonzero =>
                  have firstBounds :=
                    decodeOrdinaryPrefix_blocksUsed_bounds _ _ ordinary
                  have secondBounds :=
                    decodeOrdinaryPrefix_blocksUsed_bounds _ _ secondRun
                  have currentBounds :=
                    decodeOrdinaryPrefix_blocksUsed_bounds _ _ currentRun
                  have firstRemaining :=
                    decodeOrdinaryPrefix_remaining_eq_drop _ _ ordinary
                  have secondRemaining :=
                    decodeOrdinaryPrefix_remaining_eq_drop _ _ secondRun
                  let index := stop2IndexEquiv first.blocksUsed
                    second.blocksUsed decoded.blocksUsed
                    firstBounds.1 firstBounds.2 secondBounds.1 secondBounds.2
                    currentBounds.1 currentBounds.2
                  let routedBlocks := routeCoordinates index flat.1.1
                  have firstRoutedRun := decodeOrdinaryPrefix_routeCoordinates
                    index flat.1.1 0 0 first (by
                      simpa [gammaOutputBlocks] using ordinary) firstBounds.2
                    (by omega)
                    (by
                      intro block before
                      simpa [index] using stop2IndexEquiv_first_interval
                        _ _ _ _ _ _ _ _ _ block before)
                  have secondSourceRun :
                      decodeOrdinaryPrefix
                          ((List.ofFn flat.1.1).drop first.blocksUsed) =
                        some second := by
                    simpa [gammaOutputBlocks, firstRemaining] using secondRun
                  have secondRoutedRun :=
                    decodeOrdinaryPrefix_routeCoordinates index flat.1.1 1
                      first.blocksUsed second secondSourceRun secondBounds.2
                      (by omega)
                      (by
                        intro block before
                        simpa [index] using stop2IndexEquiv_second_interval
                          _ _ _ _ _ _ _ _ _ block before)
                  have currentSourceRun :
                      decodeOrdinaryPrefix
                          ((List.ofFn flat.1.1).drop
                            (first.blocksUsed + second.blocksUsed)) =
                        some decoded := by
                    simpa [gammaOutputBlocks, firstRemaining, secondRemaining,
                      List.drop_drop] using currentRun
                  have currentRoutedRun :=
                    decodeOrdinaryPrefix_routeCoordinates index flat.1.1 2
                      (first.blocksUsed + second.blocksUsed) decoded
                      currentSourceRun currentBounds.2 (by omega)
                      (by
                        intro block before
                        simpa [index] using stop2IndexEquiv_third_interval
                          _ _ _ _ _ _ _ _ _ block before)
                  let firstRouted : OrdinaryPrefixDecode :=
                    { first with remainingBlocks :=
                        (List.ofFn (routedBlocks 0)).drop first.blocksUsed }
                  let secondRouted : OrdinaryPrefixDecode :=
                    { second with remainingBlocks :=
                        (List.ofFn (routedBlocks 1)).drop second.blocksUsed }
                  let currentRouted : OrdinaryPrefixDecode :=
                    { decoded with remainingBlocks :=
                        (List.ofFn (routedBlocks 2)).drop decoded.blocksUsed }
                  let firstRaw : SuccessfulZeroGammaOrdinaryRaw :=
                    successfulZeroRawOfOrdinaryRun (routedBlocks 0) firstRouted
                      (by simpa [routedBlocks, firstRouted] using firstRoutedRun)
                      (by simpa [firstRouted] using zero)
                  let secondRaw : SuccessfulZeroGammaOrdinaryRaw :=
                    successfulZeroRawOfOrdinaryRun (routedBlocks 1) secondRouted
                      (by simpa [routedBlocks, secondRouted] using secondRoutedRun)
                      (by simpa [secondRouted] using secondZero)
                  let currentRaw : SuccessfulNonzeroGammaOrdinaryRaw :=
                    successfulNonzeroRawOfOrdinaryRun (routedBlocks 2)
                      currentRouted
                      (by simpa [routedBlocks, currentRouted] using currentRoutedRun)
                      (by simpa [currentRouted] using currentNonzero)
                  let advances : Tag73AdvanceDigestGhosts :=
                    routeCoordinates index flat.1.2
                  let candidate : RoutedSuccessfulGammaTape :=
                    .stop2 firstRaw secondRaw currentRaw advances
                  refine ⟨candidate, ?_⟩
                  apply Subtype.ext
                  apply Prod.ext
                  · change (routedGammaFlatTape candidate).1 = flat.1.1
                    have firstDecode :
                        successfulRawOrdinaryDecode firstRaw.1 = firstRouted := by
                      exact successfulRawOrdinaryDecode_of_run _ _ (by
                        simpa [routedBlocks, firstRouted] using firstRoutedRun)
                    have secondDecode :
                        successfulRawOrdinaryDecode secondRaw.1 = secondRouted := by
                      exact successfulRawOrdinaryDecode_of_run _ _ (by
                        simpa [routedBlocks, secondRouted] using secondRoutedRun)
                    have currentDecode :
                        successfulRawOrdinaryDecode currentRaw.1 =
                          currentRouted := by
                      exact successfulRawOrdinaryDecode_of_run _ _ (by
                        simpa [routedBlocks, currentRouted] using currentRoutedRun)
                    have indexCandidate : routedGammaIndex candidate = index := by
                      simp only [candidate, routedGammaIndex]
                      simp [firstDecode, secondDecode, currentDecode,
                        firstRouted, secondRouted, currentRouted, index]
                    have blocksCandidate :
                        routedGammaBlocks candidate = routedBlocks := by
                      funext attempt
                      apply fourGammaBlocksRawEquiv.injective
                      simp only [routedGammaBlocks,
                        fourGammaBlocksRawEquiv.apply_symm_apply]
                      change routedGammaRawStreams candidate attempt =
                        fourGammaBlocksRawEquiv (routedBlocks attempt)
                      fin_cases attempt <;>
                        simp [candidate, firstRaw, secondRaw, currentRaw,
                          successfulZeroRawOfOrdinaryRun,
                          successfulNonzeroRawOfOrdinaryRun,
                          successfulRawOfOrdinaryRun]
                    rw [routedGammaFlatTape, indexCandidate, blocksCandidate]
                    exact unroute_route_coordinates index flat.1.1
                  · change (routedGammaFlatTape candidate).2 = flat.1.2
                    have firstDecode :
                        successfulRawOrdinaryDecode firstRaw.1 = firstRouted := by
                      exact successfulRawOrdinaryDecode_of_run _ _ (by
                        simpa [routedBlocks, firstRouted] using firstRoutedRun)
                    have secondDecode :
                        successfulRawOrdinaryDecode secondRaw.1 = secondRouted := by
                      exact successfulRawOrdinaryDecode_of_run _ _ (by
                        simpa [routedBlocks, secondRouted] using secondRoutedRun)
                    have currentDecode :
                        successfulRawOrdinaryDecode currentRaw.1 =
                          currentRouted := by
                      exact successfulRawOrdinaryDecode_of_run _ _ (by
                        simpa [routedBlocks, currentRouted] using currentRoutedRun)
                    have indexCandidate : routedGammaIndex candidate = index := by
                      simp only [candidate, routedGammaIndex]
                      simp [firstDecode, secondDecode, currentDecode,
                        firstRouted, secondRouted, currentRouted, index]
                    have advancesCandidate :
                        routedGammaAdvances candidate = advances := by rfl
                    rw [routedGammaFlatTape, indexCandidate, advancesCandidate]
                    exact unroute_route_coordinates index flat.1.2
              | next impossible zero impossibleTail =>
                  cases impossibleTail

theorem routedSuccessfulGammaToFlat_injective :
    Function.Injective routedSuccessfulGammaToFlat := by
  intro left right equality
  have flatEq : routedGammaFlatTape left = routedGammaFlatTape right := by
    exact congrArg Subtype.val equality
  have stopEq : routedGammaStopIndex left = routedGammaStopIndex right := by
    apply gamma_prefix_stopping_branches_disjoint (routedGammaFlatTape left)
    · exact routedGammaFlatTape_stopsAt left
    · rw [flatEq]
      exact routedGammaFlatTape_stopsAt right
  have indexEq : routedGammaIndex left = routedGammaIndex right :=
    routedGammaIndex_eq_of_flatTape_eq left right flatEq
  have rawEq : routedGammaRawStreams left = routedGammaRawStreams right := by
    funext attempt
    rw [← route_routedGammaFlatTape_raw left attempt,
      ← route_routedGammaFlatTape_raw right attempt, indexEq, flatEq]
  have advanceEq : routedGammaAdvances left = routedGammaAdvances right := by
    rw [← route_routedGammaFlatTape_advances left,
      ← route_routedGammaFlatTape_advances right, indexEq, flatEq]
  exact routedSuccessfulGammaTape_eq_of_observations left right stopEq rawEq
    advanceEq

theorem routedSuccessfulGammaToFlat_bijective :
    Function.Bijective routedSuccessfulGammaToFlat :=
  ⟨routedSuccessfulGammaToFlat_injective,
    routedSuccessfulGammaToFlat_surjective⟩

/-- Exact chronological/routed equivalence for the successful variable-prefix
sampler.  The forward direction dynamically identifies only reached calls;
unused suffix blocks and all advance digests are preserved by a permutation. -/
def successfulGammaPrefixFlatRoutingEquiv :
    SuccessfulGammaPrefixTape ≃ RoutedSuccessfulGammaTape :=
  (Equiv.ofBijective routedSuccessfulGammaToFlat
    routedSuccessfulGammaToFlat_bijective).symm

/-- Exact product factorization of the literal successful chronological tape.
The nuisance coordinate includes the stopping branch, reached ordinary-call
skeletons, unread raw suffix data, and every advance digest. -/
def successfulGammaPrefixFactorization :
    SuccessfulGammaPrefixTape ≃
      VariableGammaCompleteSkeleton × NonzeroQM31Exact :=
  successfulGammaPrefixFlatRoutingEquiv.trans
    routedSuccessfulGammaFactorization

@[simp] theorem successfulGammaPrefixFactorization_value
    (flat : SuccessfulGammaPrefixTape) :
    (successfulGammaPrefixFactorization flat).2 =
      routedSuccessfulGammaValue
        (successfulGammaPrefixFlatRoutingEquiv flat) := by
  exact routedSuccessfulGammaFactorization_value _

@[simp] theorem routedSuccessfulGammaToFlat_flatRoutingEquiv
    (flat : SuccessfulGammaPrefixTape) :
    routedSuccessfulGammaToFlat (successfulGammaPrefixFlatRoutingEquiv flat) =
      flat := by
  exact (Equiv.ofBijective routedSuccessfulGammaToFlat
    routedSuccessfulGammaToFlat_bijective).apply_symm_apply flat

@[simp] theorem flatRoutingEquiv_routedSuccessfulGammaToFlat
    (routed : RoutedSuccessfulGammaTape) :
    successfulGammaPrefixFlatRoutingEquiv
      (routedSuccessfulGammaToFlat routed) = routed := by
  exact (Equiv.ofBijective routedSuccessfulGammaToFlat
    routedSuccessfulGammaToFlat_bijective).symm_apply_apply routed

theorem flatRoutingEquiv_stopsAt
    (flat : SuccessfulGammaPrefixTape) :
    GammaPrefixStopsAt
      (routedGammaStopIndex (successfulGammaPrefixFlatRoutingEquiv flat))
      flat.1 := by
  have tapeEq :
      routedGammaFlatTape (successfulGammaPrefixFlatRoutingEquiv flat) =
        flat.1 := by
    exact congrArg Subtype.val
      (routedSuccessfulGammaToFlat_flatRoutingEquiv flat)
  rw [← tapeEq]
  exact routedGammaFlatTape_stopsAt _

theorem flatRoutingEquiv_stopIndex_eq
    (flat : SuccessfulGammaPrefixTape) (index : Fin 3)
    (stops : GammaPrefixStopsAt index flat.1) :
    routedGammaStopIndex (successfulGammaPrefixFlatRoutingEquiv flat) =
      index := by
  exact gamma_prefix_stopping_branches_disjoint flat.1 _ _
    (flatRoutingEquiv_stopsAt flat) stops

theorem flatRoutingEquiv_returned_exact_value
    (flat : SuccessfulGammaPrefixTape) (decoded : OrdinaryPrefixDecode)
    (run : runGammaPrefix flat.1 = some decoded) :
    decodeTagQM31ExactLE decoded.value =
      some (routedSuccessfulGammaValue
        (successfulGammaPrefixFlatRoutingEquiv flat)).1 := by
  apply routedGammaFlatTape_returned_exact_value
    (successfulGammaPrefixFlatRoutingEquiv flat) decoded
  have tapeEq :
      routedGammaFlatTape (successfulGammaPrefixFlatRoutingEquiv flat) =
        flat.1 := by
    exact congrArg Subtype.val
      (routedSuccessfulGammaToFlat_flatRoutingEquiv flat)
  rw [tapeEq]
  exact run

#print axioms stop1IndexEquiv
#print axioms stop2IndexEquiv
#print axioms unroute_route_coordinates
#print axioms route_unroute_coordinates
#print axioms flattenedWords_fourGammaBlocksRawEquiv
#print axioms decodeOrdinaryPrefix_fourGammaBlocksRawEquiv
#print axioms fourGammaBlocksRawEquiv_success_iff
#print axioms ordinaryPrefixDecodeOfRawSuccess_exact_value
#print axioms decodeOrdinaryPrefix_blocksUsed_bounds
#print axioms decodeOrdinaryPrefix_of_matching_consumed_prefix
#print axioms successfulRawOrdinaryDecode_run
#print axioms successfulRawOrdinaryDecode_value_eq_exact_encoding
#print axioms take_drop_ofFn_unrouteCoordinates
#print axioms routedGammaFlatTape_trace
#print axioms routedGammaFlatTape_succeeds
#print axioms routedGammaFlatTape_stopsAt
#print axioms routedGammaFlatTape_returned_exact_value
#print axioms routedSuccessfulGammaToFlat
#print axioms route_routedGammaFlatTape_raw
#print axioms routedGammaIndex_eq_of_flatTape_eq
#print axioms routedSuccessfulGammaTape_eq_of_observations
#print axioms routedSuccessfulGammaToFlat_surjective
#print axioms routedSuccessfulGammaToFlat_injective
#print axioms routedSuccessfulGammaToFlat_bijective
#print axioms successfulGammaPrefixFlatRoutingEquiv
#print axioms successfulGammaPrefixFactorization
#print axioms successfulGammaPrefixFactorization_value
#print axioms flatRoutingEquiv_stopsAt
#print axioms flatRoutingEquiv_stopIndex_eq
#print axioms flatRoutingEquiv_returned_exact_value

end

end AspisK1.V7Tag73VariablePrefixGammaFlatRouting

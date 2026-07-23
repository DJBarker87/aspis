import GoodMatricesCurrent.ProbeGeneratedConcrete
import GoodMatricesCurrent.SourceExtractedGoodAModelBridge

namespace GoodMatricesCurrent.RuntimeKernelConcreteBridge

open GoodMatricesCurrent.ProbeGeneratedConcrete
open GoodMatricesCurrent.SourceExtractedGoodAModelBridge
open AspisV5ComponentADeployedTerminalApplicability

/-- Binary exponentiation spelling of the deployed circle representative.
This is propositionally the ordinary group power, but kernel reduction takes
logarithmic rather than linear time. -/
def fastRepresentativeX (index : Nat) :
    AspisV5ComponentCQM31TowerExact.M31Exact :=
  AspisCircleGroupOrder.X
    (npowBinRec (2 ^ 11 + 2 ^ 13 * index) AspisCircleGroupOrder.g)

theorem representativeX_eq_fastRepresentativeX (index : Nat) :
    AspisCircleDiscreteAvailability.representativeX index =
      fastRepresentativeX index := by
  rw [AspisCircleDiscreteAvailability.representativeX,
    AspisCircleDiscreteAvailability.representativeExp]
  rw [show (2 : Int) ^ 11 + (2 : Int) ^ 13 * index =
      ((2 ^ 11 + 2 ^ 13 * index : Nat) : Int) by norm_num,
    zpow_natCast]
  congr 1
  change npowRecAuto (2 ^ 11 + 2 ^ 13 * index) AspisCircleGroupOrder.g =
    npowBinRecAuto (2 ^ 11 + 2 ^ 13 * index) AspisCircleGroupOrder.g
  rw [npowRec_eq_npowBinRec]

def concreteRepresentativeX :
    Fin AspisCircleDiscreteAvailability.queryCount →
      AspisV5ComponentCQM31TowerExact.M31Exact :=
  ![1692338035, 650720525, 1810929516, 1090586317, 1505636368,
    1014802797, 168071934, 856624473, 242687340, 381357878,
    1013981414, 1880616092, 1740853386, 2083712450, 1019463676,
    9503459, 297859898, 881364631]

theorem concreteRepresentativeX_exact
    (query : Fin AspisCircleDiscreteAvailability.queryCount) :
    AspisCircleDiscreteAvailability.representativeX
        (ConcreteProbeWitness.naturalQ18 query) =
      concreteRepresentativeX query := by
  rw [representativeX_eq_fastRepresentativeX]
  fin_cases query <;>
    decide

def concreteRepresentativeXSquared :
    Fin 18 → AspisV5ComponentADeployedTerminalApplicability.Base :=
  ![571440617, 1093211761, 1729533681, 1221282579, 1068602989,
    1179545768, 1159686949, 461252953, 795615960, 97828349,
    973328309, 1088545178, 732957194, 622561264, 49968897,
    1160706449, 67186387, 1030447771]

theorem concreteRepresentativeXSquared_exact (query : Fin 18) :
    (concreteRepresentativeX query) ^ 2 =
      concreteRepresentativeXSquared query := by
  fin_cases query <;> decide

/-- After bit-reversal normalization, the maintained kernel polynomial is the
explicit product of the 18 concrete quadratic fibre factors. -/
theorem kernelPoly_eq_concrete :
    AspisV5AtomicComponentA.kernelPoly ConcreteProbeWitness.naturalQ18 =
      ∏ query : Fin 18,
        (Polynomial.X - Polynomial.C (concreteRepresentativeX query)) *
          (Polynomial.X + Polynomial.C (concreteRepresentativeX query)) := by
  rw [AspisV5AtomicComponentA.kernelPoly, Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro query _
  rw [Fin.prod_univ_two]
  rw [concreteRepresentativeX_exact]
  norm_num [AspisCircleDiscreteAvailability.signedCoordinate]

noncomputable def halfConcreteKernel :
    Polynomial AspisV5ComponentADeployedTerminalApplicability.Base :=
  ∏ query : Fin 18,
    (Polynomial.X - Polynomial.C (concreteRepresentativeXSquared query))

def concreteSquaredList :
    List AspisV5ComponentADeployedTerminalApplicability.Base :=
  [571440617, 1093211761, 1729533681, 1221282579, 1068602989,
    1179545768, 1159686949, 461252953, 795615960, 97828349,
    973328309, 1088545178, 732957194, 622561264, 49968897,
    1160706449, 67186387, 1030447771]

def coefficientStep
    (root : AspisV5ComponentADeployedTerminalApplicability.Base)
    (tail : Fin 24 → AspisV5ComponentADeployedTerminalApplicability.Base) :
    Fin 24 → AspisV5ComponentADeployedTerminalApplicability.Base :=
  Fin.cases (-root * tail 0)
    (fun index => tail index.castSucc - root * tail index.succ)

def coefficientFold :
    List AspisV5ComponentADeployedTerminalApplicability.Base →
      Fin 24 → AspisV5ComponentADeployedTerminalApplicability.Base
  | [] => Fin.cases 1 (fun _ => 0)
  | root :: roots => coefficientStep root (coefficientFold roots)

noncomputable def listKernelPolynomial :
    List AspisV5ComponentADeployedTerminalApplicability.Base →
      Polynomial AspisV5ComponentADeployedTerminalApplicability.Base
  | [] => 1
  | root :: roots =>
      (Polynomial.X - Polynomial.C root) * listKernelPolynomial roots

theorem coefficientFold_eq_coeff
    (roots : List AspisV5ComponentADeployedTerminalApplicability.Base)
    (index : Fin 24) :
    coefficientFold roots index = (listKernelPolynomial roots).coeff index := by
  induction roots generalizing index with
  | nil =>
      refine Fin.cases ?_ (fun index => ?_) index
      · simp [coefficientFold, listKernelPolynomial]
      · have hindex : index.val + 1 ≠ 0 := by omega
        change 0 = (1 : Polynomial
          AspisV5ComponentADeployedTerminalApplicability.Base).coeff
            (index.val + 1)
        rw [Polynomial.coeff_one, if_neg hindex]
  | cons root roots ih =>
      refine Fin.cases ?_ (fun index => ?_) index
      · simp [coefficientFold, coefficientStep, listKernelPolynomial,
          Polynomial.mul_coeff_zero, ih]
      · simpa [coefficientFold, coefficientStep, listKernelPolynomial, ih]
          using (Polynomial.coeff_X_sub_C_mul
            (p := listKernelPolynomial roots) (r := root) (a := index.val)
          ).symm

theorem halfConcreteKernel_eq_listKernel :
    halfConcreteKernel = listKernelPolynomial concreteSquaredList := by
  simp [halfConcreteKernel, concreteSquaredList, listKernelPolynomial,
    concreteRepresentativeXSquared, Fin.prod_univ_succ]

def expectedHalfCoefficients :
    Fin 24 → AspisV5ComponentADeployedTerminalApplicability.Base :=
  ![519620177, 528764235, 671819249, 2140992514, 1843223343,
    1094648776, 1064183334, 1834578843, 113403409, 785436993,
    852377093, 1757436383, 1641054439, 479908979, 1253767301,
    1177649036, 1272219910, 2076166121, 1, 0, 0, 0, 0, 0]

def tripleCoefficientStep
    (root₀ root₁ root₂ :
      AspisV5ComponentADeployedTerminalApplicability.Base)
    (tail : Fin 24 → AspisV5ComponentADeployedTerminalApplicability.Base) :
    Fin 24 → AspisV5ComponentADeployedTerminalApplicability.Base :=
  coefficientStep root₀ (coefficientStep root₁ (coefficientStep root₂ tail))

theorem coefficientFold_three
    (root₀ root₁ root₂ :
      AspisV5ComponentADeployedTerminalApplicability.Base)
    (roots : List AspisV5ComponentADeployedTerminalApplicability.Base) :
    coefficientFold (root₀ :: root₁ :: root₂ :: roots) =
      tripleCoefficientStep root₀ root₁ root₂ (coefficientFold roots) :=
  rfl

def coefficientStage0 :
    Fin 24 → AspisV5ComponentADeployedTerminalApplicability.Base :=
  ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem coefficientFold_nil_eq_stage0 :
    coefficientFold [] = coefficientStage0 := by
  funext index
  fin_cases index <;> rfl

def coefficientStage3 :
    Fin 24 → AspisV5ComponentADeployedTerminalApplicability.Base :=
  ![1611996462, 1322513003, 2036626687, 1, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def coefficientStage6 :
    Fin 24 → AspisV5ComponentADeployedTerminalApplicability.Base :=
  ![1455590622, 230066763, 128502033, 1471499532, 2042189670, 631139332,
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def coefficientStage9 :
    Fin 24 → AspisV5ComponentADeployedTerminalApplicability.Base :=
  ![1959756317, 292833958, 1068528099, 1628186383, 2054896456, 535381436,
    1401952925, 392261072, 618921143, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0]

def coefficientStage12 :
    Fin 24 → AspisV5ComponentADeployedTerminalApplicability.Base :=
  ![885133220, 1926056584, 879275705, 623682588, 2062532411, 695870446,
    1851369893, 222904374, 1483948225, 976992164, 1559682810, 349848928, 1,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def coefficientStage15 :
    Fin 24 → AspisV5ComponentADeployedTerminalApplicability.Base :=
  ![1188647537, 859227604, 1728087575, 635687963, 2114161809, 1004787545,
    1237518416, 232829971, 277200651, 457444529, 372493460, 28236937,
    1795142497, 1448014600, 1175384886, 1, 0, 0, 0, 0, 0, 0, 0, 0]

theorem coefficientStage0_to_3 :
    tripleCoefficientStep 1160706449 67186387 1030447771 coefficientStage0 =
      coefficientStage3 := by
  funext index
  fin_cases index <;> decide

theorem coefficientStage3_to_6 :
    tripleCoefficientStep 732957194 622561264 49968897 coefficientStage3 =
      coefficientStage6 := by
  funext index
  fin_cases index <;> decide

theorem coefficientStage6_to_9 :
    tripleCoefficientStep 97828349 973328309 1088545178 coefficientStage6 =
      coefficientStage9 := by
  funext index
  fin_cases index <;> decide

theorem coefficientStage9_to_12 :
    tripleCoefficientStep 1159686949 461252953 795615960 coefficientStage9 =
      coefficientStage12 := by
  funext index
  fin_cases index <;> decide

theorem coefficientStage12_to_15 :
    tripleCoefficientStep 1221282579 1068602989 1179545768 coefficientStage12 =
      coefficientStage15 := by
  funext index
  fin_cases index <;> decide

theorem coefficientStage15_to_18 :
    tripleCoefficientStep 571440617 1093211761 1729533681 coefficientStage15 =
      expectedHalfCoefficients := by
  funext index
  fin_cases index <;> decide

theorem concreteCoefficientFold_function :
    coefficientFold concreteSquaredList = expectedHalfCoefficients := by
  unfold concreteSquaredList
  rw [coefficientFold_three, coefficientFold_three, coefficientFold_three,
    coefficientFold_three, coefficientFold_three, coefficientFold_three]
  rw [coefficientFold_nil_eq_stage0]
  rw [coefficientStage0_to_3, coefficientStage3_to_6,
    coefficientStage6_to_9, coefficientStage9_to_12,
    coefficientStage12_to_15, coefficientStage15_to_18]

theorem concreteCoefficientFold_exact (index : Fin 24) :
    coefficientFold concreteSquaredList index = expectedHalfCoefficients index :=
  congrFun concreteCoefficientFold_function index

theorem halfConcreteKernel_coeff_exact (index : Fin 24) :
    halfConcreteKernel.coeff index = expectedHalfCoefficients index := by
  rw [halfConcreteKernel_eq_listKernel,
    ← coefficientFold_eq_coeff concreteSquaredList index]
  exact concreteCoefficientFold_exact index

theorem concreteKernel_eq_expand :
    (∏ query : Fin 18,
        (Polynomial.X - Polynomial.C (concreteRepresentativeX query)) *
          (Polynomial.X + Polynomial.C (concreteRepresentativeX query))) =
      Polynomial.expand
        AspisV5ComponentADeployedTerminalApplicability.Base 2
        halfConcreteKernel := by
  unfold halfConcreteKernel
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro query _
  simp only [map_sub, Polynomial.expand_X, Polynomial.expand_C]
  rw [← concreteRepresentativeXSquared_exact]
  rw [map_pow]
  ring

theorem concreteKernel_coeff_odd_zero (degreeHalf : Nat) :
    (∏ query : Fin 18,
        (Polynomial.X - Polynomial.C (concreteRepresentativeX query)) *
          (Polynomial.X + Polynomial.C (concreteRepresentativeX query))).coeff
        (2 * degreeHalf + 1) = 0 := by
  rw [concreteKernel_eq_expand]
  rw [Polynomial.coeff_expand (p := 2) (by omega)
    halfConcreteKernel (2 * degreeHalf + 1)]
  rw [if_neg (by omega)]

/-- The maintained ordinary coefficient vector of the concrete public
selector-zero query-kernel polynomial. -/
noncomputable def maintainedConcreteOrdinary :
    Fin 48 → AspisV5ComponentADeployedTerminalApplicability.Base :=
  polynomialBlock
    (AspisV5AtomicComponentA.kernelPoly ConcreteProbeWitness.naturalQ18)

theorem runtimeKernelOddCoordinate (degreeHalf : Fin 24) :
    EvenKernel.evenKernelOrdinary kernel
        ⟨2 * degreeHalf.val + 1, by omega⟩ =
      maintainedConcreteOrdinary ⟨2 * degreeHalf.val + 1, by omega⟩ := by
  rw [maintainedConcreteOrdinary, polynomialBlock, kernelPoly_eq_concrete,
    concreteKernel_coeff_odd_zero]
  fin_cases degreeHalf <;>
    norm_num [GoodMatricesCurrent.SourceExtractedEvenKernel.evenKernelOrdinary,
      kernel, Aeneas.Std.Array.make]

theorem runtimeKernelEvenCoordinate (degreeHalf : Fin 24) :
    EvenKernel.evenKernelOrdinary kernel
        ⟨2 * degreeHalf.val, by omega⟩ =
      maintainedConcreteOrdinary ⟨2 * degreeHalf.val, by omega⟩ := by
  unfold maintainedConcreteOrdinary polynomialBlock
  change EvenKernel.evenKernelOrdinary kernel
      ⟨2 * degreeHalf.val, by omega⟩ =
    (AspisV5AtomicComponentA.kernelPoly
      ConcreteProbeWitness.naturalQ18).coeff (2 * degreeHalf.val)
  rw [kernelPoly_eq_concrete, concreteKernel_eq_expand]
  rw [Polynomial.coeff_expand_mul' (p := 2) (by omega),
    halfConcreteKernel_coeff_exact]
  fin_cases degreeHalf <;>
    norm_num [GoodMatricesCurrent.SourceExtractedEvenKernel.evenKernelOrdinary,
      kernel, Aeneas.Std.Array.make, expectedHalfCoefficients]

theorem runtimeKernelBlock0 (limb : Fin 4) :
    EvenKernel.evenKernelOrdinary kernel ⟨limb.val, by omega⟩ =
      maintainedConcreteOrdinary ⟨limb.val, by omega⟩ := by
  fin_cases limb
  · exact runtimeKernelEvenCoordinate 0
  · exact runtimeKernelOddCoordinate 0
  · exact runtimeKernelEvenCoordinate 1
  · exact runtimeKernelOddCoordinate 1

theorem runtimeKernelBlock1 (limb : Fin 4) :
    EvenKernel.evenKernelOrdinary kernel ⟨4 + limb.val, by omega⟩ =
      maintainedConcreteOrdinary ⟨4 + limb.val, by omega⟩ := by
  fin_cases limb
  · exact runtimeKernelEvenCoordinate 2
  · exact runtimeKernelOddCoordinate 2
  · exact runtimeKernelEvenCoordinate 3
  · exact runtimeKernelOddCoordinate 3

theorem runtimeKernelBlock2 (limb : Fin 4) :
    EvenKernel.evenKernelOrdinary kernel ⟨8 + limb.val, by omega⟩ =
      maintainedConcreteOrdinary ⟨8 + limb.val, by omega⟩ := by
  fin_cases limb
  · exact runtimeKernelEvenCoordinate 4
  · exact runtimeKernelOddCoordinate 4
  · exact runtimeKernelEvenCoordinate 5
  · exact runtimeKernelOddCoordinate 5

theorem runtimeKernelBlock3 (limb : Fin 4) :
    EvenKernel.evenKernelOrdinary kernel ⟨12 + limb.val, by omega⟩ =
      maintainedConcreteOrdinary ⟨12 + limb.val, by omega⟩ := by
  fin_cases limb
  · exact runtimeKernelEvenCoordinate 6
  · exact runtimeKernelOddCoordinate 6
  · exact runtimeKernelEvenCoordinate 7
  · exact runtimeKernelOddCoordinate 7

theorem runtimeKernelBlock4 (limb : Fin 4) :
    EvenKernel.evenKernelOrdinary kernel ⟨16 + limb.val, by omega⟩ =
      maintainedConcreteOrdinary ⟨16 + limb.val, by omega⟩ := by
  fin_cases limb
  · exact runtimeKernelEvenCoordinate 8
  · exact runtimeKernelOddCoordinate 8
  · exact runtimeKernelEvenCoordinate 9
  · exact runtimeKernelOddCoordinate 9

theorem runtimeKernelBlock5 (limb : Fin 4) :
    EvenKernel.evenKernelOrdinary kernel ⟨20 + limb.val, by omega⟩ =
      maintainedConcreteOrdinary ⟨20 + limb.val, by omega⟩ := by
  fin_cases limb
  · exact runtimeKernelEvenCoordinate 10
  · exact runtimeKernelOddCoordinate 10
  · exact runtimeKernelEvenCoordinate 11
  · exact runtimeKernelOddCoordinate 11

theorem runtimeKernelBlock6 (limb : Fin 4) :
    EvenKernel.evenKernelOrdinary kernel ⟨24 + limb.val, by omega⟩ =
      maintainedConcreteOrdinary ⟨24 + limb.val, by omega⟩ := by
  fin_cases limb
  · exact runtimeKernelEvenCoordinate 12
  · exact runtimeKernelOddCoordinate 12
  · exact runtimeKernelEvenCoordinate 13
  · exact runtimeKernelOddCoordinate 13

theorem runtimeKernelBlock7 (limb : Fin 4) :
    EvenKernel.evenKernelOrdinary kernel ⟨28 + limb.val, by omega⟩ =
      maintainedConcreteOrdinary ⟨28 + limb.val, by omega⟩ := by
  fin_cases limb
  · exact runtimeKernelEvenCoordinate 14
  · exact runtimeKernelOddCoordinate 14
  · exact runtimeKernelEvenCoordinate 15
  · exact runtimeKernelOddCoordinate 15

theorem runtimeKernelBlock8 (limb : Fin 4) :
    EvenKernel.evenKernelOrdinary kernel ⟨32 + limb.val, by omega⟩ =
      maintainedConcreteOrdinary ⟨32 + limb.val, by omega⟩ := by
  fin_cases limb
  · exact runtimeKernelEvenCoordinate 16
  · exact runtimeKernelOddCoordinate 16
  · exact runtimeKernelEvenCoordinate 17
  · exact runtimeKernelOddCoordinate 17

theorem runtimeKernelBlock9 (limb : Fin 4) :
    EvenKernel.evenKernelOrdinary kernel ⟨36 + limb.val, by omega⟩ =
      maintainedConcreteOrdinary ⟨36 + limb.val, by omega⟩ := by
  fin_cases limb
  · exact runtimeKernelEvenCoordinate 18
  · exact runtimeKernelOddCoordinate 18
  · exact runtimeKernelEvenCoordinate 19
  · exact runtimeKernelOddCoordinate 19

theorem runtimeKernelBlock10 (limb : Fin 4) :
    EvenKernel.evenKernelOrdinary kernel ⟨40 + limb.val, by omega⟩ =
      maintainedConcreteOrdinary ⟨40 + limb.val, by omega⟩ := by
  fin_cases limb
  · exact runtimeKernelEvenCoordinate 20
  · exact runtimeKernelOddCoordinate 20
  · exact runtimeKernelEvenCoordinate 21
  · exact runtimeKernelOddCoordinate 21

theorem runtimeKernelBlock11 (limb : Fin 4) :
    EvenKernel.evenKernelOrdinary kernel ⟨44 + limb.val, by omega⟩ =
      maintainedConcreteOrdinary ⟨44 + limb.val, by omega⟩ := by
  fin_cases limb
  · exact runtimeKernelEvenCoordinate 22
  · exact runtimeKernelOddCoordinate 22
  · exact runtimeKernelEvenCoordinate 23
  · exact runtimeKernelOddCoordinate 23

theorem runtimeKernelMatchesMaintainedConcreteOrdinary :
    RuntimeKernelMatchesOrdinary kernel maintainedConcreteOrdinary := by
  unfold RuntimeKernelMatchesOrdinary
  funext index
  fin_cases index
  · exact runtimeKernelBlock0 0
  · exact runtimeKernelBlock0 1
  · exact runtimeKernelBlock0 2
  · exact runtimeKernelBlock0 3
  · exact runtimeKernelBlock1 0
  · exact runtimeKernelBlock1 1
  · exact runtimeKernelBlock1 2
  · exact runtimeKernelBlock1 3
  · exact runtimeKernelBlock2 0
  · exact runtimeKernelBlock2 1
  · exact runtimeKernelBlock2 2
  · exact runtimeKernelBlock2 3
  · exact runtimeKernelBlock3 0
  · exact runtimeKernelBlock3 1
  · exact runtimeKernelBlock3 2
  · exact runtimeKernelBlock3 3
  · exact runtimeKernelBlock4 0
  · exact runtimeKernelBlock4 1
  · exact runtimeKernelBlock4 2
  · exact runtimeKernelBlock4 3
  · exact runtimeKernelBlock5 0
  · exact runtimeKernelBlock5 1
  · exact runtimeKernelBlock5 2
  · exact runtimeKernelBlock5 3
  · exact runtimeKernelBlock6 0
  · exact runtimeKernelBlock6 1
  · exact runtimeKernelBlock6 2
  · exact runtimeKernelBlock6 3
  · exact runtimeKernelBlock7 0
  · exact runtimeKernelBlock7 1
  · exact runtimeKernelBlock7 2
  · exact runtimeKernelBlock7 3
  · exact runtimeKernelBlock8 0
  · exact runtimeKernelBlock8 1
  · exact runtimeKernelBlock8 2
  · exact runtimeKernelBlock8 3
  · exact runtimeKernelBlock9 0
  · exact runtimeKernelBlock9 1
  · exact runtimeKernelBlock9 2
  · exact runtimeKernelBlock9 3
  · exact runtimeKernelBlock10 0
  · exact runtimeKernelBlock10 1
  · exact runtimeKernelBlock10 2
  · exact runtimeKernelBlock10 3
  · exact runtimeKernelBlock11 0
  · exact runtimeKernelBlock11 1
  · exact runtimeKernelBlock11 2
  · exact runtimeKernelBlock11 3

#print axioms representativeX_eq_fastRepresentativeX
#print axioms concreteRepresentativeX_exact
#print axioms runtimeKernelMatchesMaintainedConcreteOrdinary

end GoodMatricesCurrent.RuntimeKernelConcreteBridge

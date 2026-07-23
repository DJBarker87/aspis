import GoodMatricesCurrent.ProbeAbstractDot

open Aeneas Aeneas.Std Result ControlFlow Error
open aspis_verifier

namespace GoodMatricesCurrent.ProbeTerminalMatrix

open GoodMatricesCurrent.ProbeGeneratedConcrete
open GoodMatricesCurrent.ProbeAbstractDot
open GoodMatricesCurrent.SourceExtractedTerminalField
open GoodMatricesCurrent.SourceExtractedTerminalWeights
open GoodMatricesCurrent.SourceExtractedTerminalEvaluator
open AspisV5GoodGateSparseShift

abbrev ExactM31 := AspisV5ComponentCQM31TowerExact.M31Exact
abbrev ExactQM31 := AspisV5ComponentCQM31TowerExact.QM31Exact
abbrev LocalWeights := GoodMatricesCurrent.SourceExtractedTerminalWeights.LocalWeights

def evenCoefficients0 : Fin 24 → ExactM31 :=
  ![1447460119, 615059998, 79177021, 264360387, 175677395,
    690316057, 1940922128, 1980834973, 244042458, 1373926702,
    926559219, 1646207007, 542340637, 1581685827, 496267907,
    29599140, 1471327346, 1038083065, 268435456, 0, 0, 0, 0, 0]

theorem baseDirection_exact_evenVector :
    GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact baseDirection =
      evenVector evenCoefficients0 := by
  funext output
  fin_cases output <;>
    norm_num [baseDirection, evenVector, evenCoefficients0,
      v, Aeneas.Std.Array.make,
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact,
      GoodMatricesCurrent.SourceExtractedFixedSupport.arrayEntry,
      GoodMatricesCurrent.SourceExtractedField.m31ToExact,
      AspisV5ComponentCQM31TowerExact.P]

theorem shiftedExact_zero :
    shiftedExact 0 = evenVector evenCoefficients0 := by
  simp only [shiftedExact, sparseShiftIter]
  exact baseDirection_exact_evenVector

def exactWeightWordFor (localWeights : LocalWeights) (index limb : Nat) : ExactM31 :=
  if hindex : index < 64 then
    if hlimb : limb < 4 then
      exactQM31Limb (weightsToExact localWeights ⟨index, hindex⟩) ⟨limb, hlimb⟩
    else 0
  else 0

def exactDotLimbFor (localWeights : LocalWeights) (shift : Fin 12)
    (mask limb : Nat) : ExactM31 :=
  ∑ logical ∈ Finset.range (19 + shift.val / 2),
    if hindex : shift.val % 2 + 2 * logical < 48 then
      shiftedExact shift.val ⟨shift.val % 2 + 2 * logical, hindex⟩ *
        exactWeightWordFor localWeights
          (Nat.xor (shift.val % 2 + 2 * logical) mask) limb
    else 0

def exactQ (a b c d : ExactM31) : ExactQM31 := ⟨⟨a, b⟩, ⟨c, d⟩⟩

def exactDotFor (localWeights : LocalWeights) (shift : Fin 12)
    (mask : Nat) : ExactQM31 :=
  exactQ
    (exactDotLimbFor localWeights shift mask 0)
    (exactDotLimbFor localWeights shift mask 1)
    (exactDotLimbFor localWeights shift mask 2)
    (exactDotLimbFor localWeights shift mask 3)

theorem exactDotLimbFor_zero (localWeights : LocalWeights) (mask limb : Nat) :
    exactDotLimbFor localWeights 0 mask limb =
      ∑ logical ∈ Finset.range 19,
        if hindex : 2 * logical < 48 then
          shiftedExact 0 ⟨2 * logical, hindex⟩ *
            exactWeightWordFor localWeights (Nat.xor (2 * logical) mask) limb
        else 0 := by
  rfl

theorem shiftedExact_one_oddVector :
    shiftedExact 1 = oddVector evenCoefficients0 := by
  change sparseShift (shiftedExact 0) = _
  rw [shiftedExact_zero, sparseShift_evenVector]

def successorWeights : LocalWeights := Array.make 64#usize [
    q 354562408#u32 1979137509#u32 1576723225#u32 1893970271#u32,
    q 908972504#u32 426597837#u32 1280874442#u32 860951374#u32,
    q 2045018604#u32 1104482557#u32 905540835#u32 1457622686#u32,
    q 381872533#u32 290600175#u32 1695695561#u32 2087646420#u32,
    q 339039238#u32 1417666162#u32 65949812#u32 1732877992#u32,
    q 13551646#u32 1890365063#u32 2076706865#u32 1223609504#u32,
    q 1822444950#u32 774596174#u32 1616257162#u32 2096095707#u32,
    q 1140953538#u32 1759606954#u32 544721995#u32 2055470932#u32,
    q 13766320#u32 635087042#u32 482005931#u32 1902685871#u32,
    q 359403818#u32 115107278#u32 548440567#u32 1250011538#u32,
    q 410605377#u32 1877777767#u32 1320652137#u32 1452161629#u32,
    q 752062608#u32 1834533166#u32 1420745953#u32 914689679#u32,
    q 2083758814#u32 938557679#u32 1465040919#u32 277993749#u32,
    q 1415168730#u32 1867043810#u32 1583272224#u32 2079739131#u32,
    q 1816936575#u32 1023926795#u32 1605485054#u32 1208778658#u32,
    q 1521600523#u32 989116672#u32 681506259#u32 804555828#u32,
    q 442057872#u32 249874489#u32 1157344218#u32 468464629#u32,
    q 29977657#u32 1356789752#u32 713860866#u32 541683430#u32,
    q 1169688587#u32 1788397019#u32 1838149838#u32 1465521853#u32,
    q 474037290#u32 1629721983#u32 1036634008#u32 1919074502#u32,
    q 1349724135#u32 223499658#u32 1331606952#u32 336079749#u32,
    q 712822376#u32 81325874#u32 1979326553#u32 816497853#u32,
    q 891151084#u32 388420070#u32 1390710355#u32 378947771#u32,
    q 1962835952#u32 1097262183#u32 379553799#u32 1395070829#u32,
    q 87584589#u32 725270556#u32 171358266#u32 2045496873#u32,
    q 1045662976#u32 686285769#u32 199987777#u32 1864085411#u32,
    q 2080424579#u32 667912868#u32 1373317323#u32 1568020064#u32,
    q 1527199701#u32 869369195#u32 1653606205#u32 531102197#u32,
    q 250457721#u32 1595660125#u32 1438236873#u32 1039293878#u32,
    q 889849491#u32 1484448158#u32 1982837148#u32 1940788068#u32,
    q 746018142#u32 183880968#u32 1454010460#u32 344033662#u32,
    q 821434239#u32 186001731#u32 656231514#u32 1474535109#u32,
    q 1598682415#u32 98023458#u32 606165539#u32 193964999#u32,
    q 1512350847#u32 67350821#u32 1086025080#u32 977220655#u32,
    q 1207433981#u32 137505828#u32 1979439650#u32 519231772#u32,
    q 1803062500#u32 1339885529#u32 615551071#u32 902558709#u32,
    q 264661577#u32 567957233#u32 1090270970#u32 1785206092#u32,
    q 509521235#u32 1998320469#u32 1778105212#u32 982851033#u32,
    q 787230267#u32 623802516#u32 1870390758#u32 607928973#u32,
    q 1287442715#u32 1349015889#u32 1091625947#u32 487914502#u32,
    q 1625475529#u32 942060415#u32 2079115737#u32 1449366168#u32,
    q 1777844936#u32 406673273#u32 1820851957#u32 1424601467#u32,
    q 1811011500#u32 1744885182#u32 1756900206#u32 1972766433#u32,
    q 1752569100#u32 1099867740#u32 184183974#u32 1361310304#u32,
    q 1640513202#u32 1789606681#u32 1539811699#u32 1060073723#u32,
    q 247101665#u32 1236463298#u32 1542049626#u32 77635482#u32,
    q 208317784#u32 935075126#u32 1397340921#u32 1771956594#u32,
    q 107566599#u32 1127574863#u32 810907120#u32 536978250#u32,
    q 644566004#u32 1222122650#u32 648985871#u32 818321370#u32,
    q 417912558#u32 926779699#u32 491314841#u32 64154306#u32,
    q 1349233025#u32 1017913082#u32 1170102020#u32 1433694722#u32,
    q 442009885#u32 1234982338#u32 1691114516#u32 714943319#u32,
    q 599013758#u32 59865326#u32 923182462#u32 1389008942#u32,
    q 537551007#u32 1310379604#u32 377942624#u32 2047341972#u32,
    q 324840331#u32 954638469#u32 686900062#u32 2036415316#u32,
    q 165253646#u32 1347588698#u32 1100754535#u32 1115759062#u32,
    q 245528885#u32 1898627321#u32 1432587722#u32 1076205808#u32,
    q 124848037#u32 1205445973#u32 769178682#u32 547584348#u32,
    q 1292146133#u32 146883093#u32 806931159#u32 1672923318#u32,
    q 66630929#u32 599668246#u32 446114995#u32 1533335573#u32,
    q 1188074526#u32 1421544938#u32 874544806#u32 1091769522#u32,
    q 917536916#u32 48724952#u32 656227577#u32 1750953723#u32,
    q 783193113#u32 1929442649#u32 48961295#u32 219136528#u32,
    q 882289288#u32 1497511013#u32 2014474268#u32 111257813#u32]

theorem successorWeights_canonical : CanonicalLocalWeights successorWeights := by
  intro index
  fin_cases index <;>
    norm_num [successorWeights, weightEntry, q, Aeneas.Std.Array.make,
      CanonicalLocalQM31, CanonicalLocalCM31, CanonicalLocalM31,
      AspisV5ComponentCQM31TowerExact.P]

theorem successorWeights_exact :
    weightsToExact successorWeights =
      exactSuffixWeight (pointToExact successor) := by
  funext index
  fin_cases index <;> decide

theorem successorWeights_call :
    v5_cu_probe.good_gate_probe.mle_six_coordinate_suffix_weights successor =
      .ok successorWeights := by
  obtain ⟨result, hcall, hcanonical, hexact⟩ :=
    mle_six_coordinate_suffix_weights_exact_spec successor successor_canonical
  have hresult : result = successorWeights :=
    canonical_weights_exact_injective result successorWeights
      hcanonical successorWeights_canonical
      (hexact.trans successorWeights_exact.symm)
  simpa [hresult] using hcall

theorem exactDotLimbFor_1 (localWeights : LocalWeights)
    (mask limb : Nat) :
    exactDotLimbFor localWeights (1 : Fin 12) mask limb =
      ∑ logical ∈ Finset.range 19,
        if hindex : 1 + 2 * logical < 48 then
          shiftedExact 1 ⟨1 + 2 * logical, hindex⟩ *
            exactWeightWordFor localWeights
              (Nat.xor (1 + 2 * logical) mask) limb
        else 0 := by
  rfl

theorem exactDotLimbFor_2 (localWeights : LocalWeights)
    (mask limb : Nat) :
    exactDotLimbFor localWeights (2 : Fin 12) mask limb =
      ∑ logical ∈ Finset.range 20,
        if hindex : 0 + 2 * logical < 48 then
          shiftedExact 2 ⟨0 + 2 * logical, hindex⟩ *
            exactWeightWordFor localWeights
              (Nat.xor (0 + 2 * logical) mask) limb
        else 0 := by
  rfl

theorem exactDotLimbFor_3 (localWeights : LocalWeights)
    (mask limb : Nat) :
    exactDotLimbFor localWeights (3 : Fin 12) mask limb =
      ∑ logical ∈ Finset.range 20,
        if hindex : 1 + 2 * logical < 48 then
          shiftedExact 3 ⟨1 + 2 * logical, hindex⟩ *
            exactWeightWordFor localWeights
              (Nat.xor (1 + 2 * logical) mask) limb
        else 0 := by
  rfl

theorem exactDotLimbFor_4 (localWeights : LocalWeights)
    (mask limb : Nat) :
    exactDotLimbFor localWeights (4 : Fin 12) mask limb =
      ∑ logical ∈ Finset.range 21,
        if hindex : 0 + 2 * logical < 48 then
          shiftedExact 4 ⟨0 + 2 * logical, hindex⟩ *
            exactWeightWordFor localWeights
              (Nat.xor (0 + 2 * logical) mask) limb
        else 0 := by
  rfl

theorem exactDotLimbFor_5 (localWeights : LocalWeights)
    (mask limb : Nat) :
    exactDotLimbFor localWeights (5 : Fin 12) mask limb =
      ∑ logical ∈ Finset.range 21,
        if hindex : 1 + 2 * logical < 48 then
          shiftedExact 5 ⟨1 + 2 * logical, hindex⟩ *
            exactWeightWordFor localWeights
              (Nat.xor (1 + 2 * logical) mask) limb
        else 0 := by
  rfl

theorem exactDotLimbFor_6 (localWeights : LocalWeights)
    (mask limb : Nat) :
    exactDotLimbFor localWeights (6 : Fin 12) mask limb =
      ∑ logical ∈ Finset.range 22,
        if hindex : 0 + 2 * logical < 48 then
          shiftedExact 6 ⟨0 + 2 * logical, hindex⟩ *
            exactWeightWordFor localWeights
              (Nat.xor (0 + 2 * logical) mask) limb
        else 0 := by
  rfl

theorem exactDotLimbFor_7 (localWeights : LocalWeights)
    (mask limb : Nat) :
    exactDotLimbFor localWeights (7 : Fin 12) mask limb =
      ∑ logical ∈ Finset.range 22,
        if hindex : 1 + 2 * logical < 48 then
          shiftedExact 7 ⟨1 + 2 * logical, hindex⟩ *
            exactWeightWordFor localWeights
              (Nat.xor (1 + 2 * logical) mask) limb
        else 0 := by
  rfl

theorem exactDotLimbFor_8 (localWeights : LocalWeights)
    (mask limb : Nat) :
    exactDotLimbFor localWeights (8 : Fin 12) mask limb =
      ∑ logical ∈ Finset.range 23,
        if hindex : 0 + 2 * logical < 48 then
          shiftedExact 8 ⟨0 + 2 * logical, hindex⟩ *
            exactWeightWordFor localWeights
              (Nat.xor (0 + 2 * logical) mask) limb
        else 0 := by
  rfl

theorem exactDotLimbFor_9 (localWeights : LocalWeights)
    (mask limb : Nat) :
    exactDotLimbFor localWeights (9 : Fin 12) mask limb =
      ∑ logical ∈ Finset.range 23,
        if hindex : 1 + 2 * logical < 48 then
          shiftedExact 9 ⟨1 + 2 * logical, hindex⟩ *
            exactWeightWordFor localWeights
              (Nat.xor (1 + 2 * logical) mask) limb
        else 0 := by
  rfl

theorem exactDotLimbFor_10 (localWeights : LocalWeights)
    (mask limb : Nat) :
    exactDotLimbFor localWeights (10 : Fin 12) mask limb =
      ∑ logical ∈ Finset.range 24,
        if hindex : 0 + 2 * logical < 48 then
          shiftedExact 10 ⟨0 + 2 * logical, hindex⟩ *
            exactWeightWordFor localWeights
              (Nat.xor (0 + 2 * logical) mask) limb
        else 0 := by
  rfl

theorem exactDotLimbFor_11 (localWeights : LocalWeights)
    (mask limb : Nat) :
    exactDotLimbFor localWeights (11 : Fin 12) mask limb =
      ∑ logical ∈ Finset.range 24,
        if hindex : 1 + 2 * logical < 48 then
          shiftedExact 11 ⟨1 + 2 * logical, hindex⟩ *
            exactWeightWordFor localWeights
              (Nat.xor (1 + 2 * logical) mask) limb
        else 0 := by
  rfl



def baseDotsExact : Fin 12 → ExactQM31 :=
  ![exactQ 1177441048 1114808065 401050107 1884844344,
    exactQ 748609204 552298247 1773340568 1274769379,
    exactQ 617542433 684730370 4297974 1866716448,
    exactQ 1563147802 1109336937 861984956 1633434049,
    exactQ 1055869420 318680542 825662962 79711146,
    exactQ 324800969 507859990 667302552 855606506,
    exactQ 452671168 428377729 319029284 856392185,
    exactQ 1228912323 1023362706 2168621 1781567123,
    exactQ 1782217801 1441022287 1801093522 987507599,
    exactQ 1131137628 758225504 1098326829 775483528,
    exactQ 1957787122 464226565 1667537936 1370636367,
    exactQ 636530255 1929595933 227249300 2078627877]

def xorDotsExact : Fin 12 → ExactQM31 :=
  ![exactQ 1364250210 62393271 95770609 1697408413,
    exactQ 1690169382 776014768 515584851 916836831,
    exactQ 1324502204 1358947460 1453218240 1676945478,
    exactQ 1650630470 1331992451 1155398006 874728678,
    exactQ 1750044486 749098943 1725347682 1344479241,
    exactQ 1456397822 1498127156 1149063658 450453548,
    exactQ 1660361295 1248428151 958438626 1711975264,
    exactQ 592782956 604639299 2014878637 373814266,
    exactQ 502180272 980806616 400057269 1728001269,
    exactQ 38515511 1762523594 1753176908 1160560284,
    exactQ 339455363 833595187 18623743 1516983476,
    exactQ 1345015830 1674377074 378167951 1919462786]

def successorDotsExact : Fin 12 → ExactQM31 :=
  ![exactQ 2022821717 1966365463 409161548 700309045,
    exactQ 2138336129 1982579366 614734809 860306563,
    exactQ 253188236 903776845 1281713196 1642730313,
    exactQ 1622314899 560228873 882037016 268544953,
    exactQ 657518833 969731750 1300867248 639171883,
    exactQ 1735515961 897624410 1030310249 22431618,
    exactQ 861137379 1788668155 1031393321 64480858,
    exactQ 591194902 1882512392 898253712 814934492,
    exactQ 966484702 563079389 1224741049 1727099900,
    exactQ 1202219491 1866044797 1694347751 1403187801,
    exactQ 1813950566 1995961022 1877249787 203693226,
    exactQ 1173358696 1256038636 1641408172 84012701]


theorem baseDot_one :
    exactDotFor weights 1 0 = baseDotsExact 1 := by
  ext <;> simp only [exactDotFor, exactQ, baseDotsExact]
  all_goals
    rw [exactDotLimbFor_1]
    rw [shiftedExact_one_oddVector]
    norm_num [Finset.sum_range_succ, oddVector, evenCoefficients0,
      exactWeightWordFor, weightsToExact, weightEntry,
      exactQM31Limb, qm31ToExact, cm31ToExact,
      weights, q, Aeneas.Std.Array.make,
      AspisV5ComponentCQM31TowerExact.P] <;> decide


theorem baseDot_zero : exactDotFor weights 0 0 = baseDotsExact 0 := by
  ext <;> simp only [exactDotFor, exactQ, baseDotsExact]
  all_goals
    rw [exactDotLimbFor_zero]
    rw [shiftedExact_zero]
    norm_num [Finset.sum_range_succ, evenVector, evenCoefficients0,
      exactWeightWordFor, weightsToExact, weightEntry,
      exactQM31Limb, qm31ToExact, cm31ToExact,
      weights, q, Aeneas.Std.Array.make,
      AspisV5ComponentCQM31TowerExact.P] <;> decide

theorem baseDot_2 :
    exactDotFor weights 2 0 = baseDotsExact 2 := by
  ext <;> simp only [exactDotFor, exactQ, baseDotsExact]
  all_goals
    rw [exactDotLimbFor_2]
    rw [shiftedExact_two_evenVector]
    norm_num [Finset.sum_range_succ, evenVector, evenCoefficients2,
      exactWeightWordFor, weightsToExact, weightEntry,
      exactQM31Limb, qm31ToExact, cm31ToExact,
      weights, q, Aeneas.Std.Array.make,
      AspisV5ComponentCQM31TowerExact.P] <;> decide

theorem baseDot_3 :
    exactDotFor weights 3 0 = baseDotsExact 3 := by
  ext <;> simp only [exactDotFor, exactQ, baseDotsExact]
  all_goals
    rw [exactDotLimbFor_3]
    rw [shiftedExact_three]
    norm_num [Finset.sum_range_succ, oddVector, evenCoefficients2,
      exactWeightWordFor, weightsToExact, weightEntry,
      exactQM31Limb, qm31ToExact, cm31ToExact,
      weights, q, Aeneas.Std.Array.make,
      AspisV5ComponentCQM31TowerExact.P] <;> decide

theorem baseDot_4 :
    exactDotFor weights 4 0 = baseDotsExact 4 := by
  ext <;> simp only [exactDotFor, exactQ, baseDotsExact]
  all_goals
    rw [exactDotLimbFor_4]
    rw [shiftedExact_four]
    norm_num [Finset.sum_range_succ, evenVector, evenCoefficients4,
      exactWeightWordFor, weightsToExact, weightEntry,
      exactQM31Limb, qm31ToExact, cm31ToExact,
      weights, q, Aeneas.Std.Array.make,
      AspisV5ComponentCQM31TowerExact.P] <;> decide

theorem baseDot_5 :
    exactDotFor weights 5 0 = baseDotsExact 5 := by
  ext <;> simp only [exactDotFor, exactQ, baseDotsExact]
  all_goals
    rw [exactDotLimbFor_5]
    rw [shiftedExact_five]
    norm_num [Finset.sum_range_succ, oddVector, evenCoefficients4,
      exactWeightWordFor, weightsToExact, weightEntry,
      exactQM31Limb, qm31ToExact, cm31ToExact,
      weights, q, Aeneas.Std.Array.make,
      AspisV5ComponentCQM31TowerExact.P] <;> decide

theorem baseDot_6 :
    exactDotFor weights 6 0 = baseDotsExact 6 := by
  ext <;> simp only [exactDotFor, exactQ, baseDotsExact]
  all_goals
    rw [exactDotLimbFor_6]
    rw [shiftedExact_six]
    norm_num [Finset.sum_range_succ, evenVector, evenCoefficients6,
      exactWeightWordFor, weightsToExact, weightEntry,
      exactQM31Limb, qm31ToExact, cm31ToExact,
      weights, q, Aeneas.Std.Array.make,
      AspisV5ComponentCQM31TowerExact.P] <;> decide

theorem baseDot_7 :
    exactDotFor weights 7 0 = baseDotsExact 7 := by
  ext <;> simp only [exactDotFor, exactQ, baseDotsExact]
  all_goals
    rw [exactDotLimbFor_7]
    rw [shiftedExact_seven]
    norm_num [Finset.sum_range_succ, oddVector, evenCoefficients6,
      exactWeightWordFor, weightsToExact, weightEntry,
      exactQM31Limb, qm31ToExact, cm31ToExact,
      weights, q, Aeneas.Std.Array.make,
      AspisV5ComponentCQM31TowerExact.P] <;> decide

theorem baseDot_8 :
    exactDotFor weights 8 0 = baseDotsExact 8 := by
  ext <;> simp only [exactDotFor, exactQ, baseDotsExact]
  all_goals
    rw [exactDotLimbFor_8]
    rw [shiftedExact_eight]
    norm_num [Finset.sum_range_succ, evenVector, evenCoefficients8,
      exactWeightWordFor, weightsToExact, weightEntry,
      exactQM31Limb, qm31ToExact, cm31ToExact,
      weights, q, Aeneas.Std.Array.make,
      AspisV5ComponentCQM31TowerExact.P] <;> decide

theorem baseDot_9 :
    exactDotFor weights 9 0 = baseDotsExact 9 := by
  ext <;> simp only [exactDotFor, exactQ, baseDotsExact]
  all_goals
    rw [exactDotLimbFor_9]
    rw [shiftedExact_nine]
    norm_num [Finset.sum_range_succ, oddVector, evenCoefficients8,
      exactWeightWordFor, weightsToExact, weightEntry,
      exactQM31Limb, qm31ToExact, cm31ToExact,
      weights, q, Aeneas.Std.Array.make,
      AspisV5ComponentCQM31TowerExact.P] <;> decide

theorem baseDot_10 :
    exactDotFor weights 10 0 = baseDotsExact 10 := by
  ext <;> simp only [exactDotFor, exactQ, baseDotsExact]
  all_goals
    rw [exactDotLimbFor_10]
    rw [shiftedExact_ten]
    norm_num [Finset.sum_range_succ, evenVector, evenCoefficients10,
      exactWeightWordFor, weightsToExact, weightEntry,
      exactQM31Limb, qm31ToExact, cm31ToExact,
      weights, q, Aeneas.Std.Array.make,
      AspisV5ComponentCQM31TowerExact.P] <;> decide

theorem baseDot_11 :
    exactDotFor weights 11 0 = baseDotsExact 11 := by
  ext <;> simp only [exactDotFor, exactQ, baseDotsExact]
  all_goals
    rw [exactDotLimbFor_11]
    rw [shiftedExact_eleven]
    norm_num [Finset.sum_range_succ, oddVector, evenCoefficients10,
      exactWeightWordFor, weightsToExact, weightEntry,
      exactQM31Limb, qm31ToExact, cm31ToExact,
      weights, q, Aeneas.Std.Array.make,
      AspisV5ComponentCQM31TowerExact.P] <;> decide

theorem xorDot_0 :
    exactDotFor weights 0 6 = xorDotsExact 0 := by
  ext <;> simp only [exactDotFor, exactQ, xorDotsExact]
  all_goals
    rw [exactDotLimbFor_zero]
    rw [shiftedExact_zero]
    norm_num [Finset.sum_range_succ, evenVector, evenCoefficients0,
      exactWeightWordFor, weightsToExact, weightEntry,
      exactQM31Limb, qm31ToExact, cm31ToExact,
      weights, q, Aeneas.Std.Array.make,
      AspisV5ComponentCQM31TowerExact.P] <;> decide

theorem xorDot_1 :
    exactDotFor weights 1 6 = xorDotsExact 1 := by
  ext <;> simp only [exactDotFor, exactQ, xorDotsExact]
  all_goals
    rw [exactDotLimbFor_1]
    rw [shiftedExact_one_oddVector]
    norm_num [Finset.sum_range_succ, oddVector, evenCoefficients0,
      exactWeightWordFor, weightsToExact, weightEntry,
      exactQM31Limb, qm31ToExact, cm31ToExact,
      weights, q, Aeneas.Std.Array.make,
      AspisV5ComponentCQM31TowerExact.P] <;> decide

theorem xorDot_2 :
    exactDotFor weights 2 6 = xorDotsExact 2 := by
  ext <;> simp only [exactDotFor, exactQ, xorDotsExact]
  all_goals
    rw [exactDotLimbFor_2]
    rw [shiftedExact_two_evenVector]
    norm_num [Finset.sum_range_succ, evenVector, evenCoefficients2,
      exactWeightWordFor, weightsToExact, weightEntry,
      exactQM31Limb, qm31ToExact, cm31ToExact,
      weights, q, Aeneas.Std.Array.make,
      AspisV5ComponentCQM31TowerExact.P] <;> decide

theorem xorDot_3 :
    exactDotFor weights 3 6 = xorDotsExact 3 := by
  ext <;> simp only [exactDotFor, exactQ, xorDotsExact]
  all_goals
    rw [exactDotLimbFor_3]
    rw [shiftedExact_three]
    norm_num [Finset.sum_range_succ, oddVector, evenCoefficients2,
      exactWeightWordFor, weightsToExact, weightEntry,
      exactQM31Limb, qm31ToExact, cm31ToExact,
      weights, q, Aeneas.Std.Array.make,
      AspisV5ComponentCQM31TowerExact.P] <;> decide

theorem xorDot_4 :
    exactDotFor weights 4 6 = xorDotsExact 4 := by
  ext <;> simp only [exactDotFor, exactQ, xorDotsExact]
  all_goals
    rw [exactDotLimbFor_4]
    rw [shiftedExact_four]
    norm_num [Finset.sum_range_succ, evenVector, evenCoefficients4,
      exactWeightWordFor, weightsToExact, weightEntry,
      exactQM31Limb, qm31ToExact, cm31ToExact,
      weights, q, Aeneas.Std.Array.make,
      AspisV5ComponentCQM31TowerExact.P] <;> decide

theorem xorDot_5 :
    exactDotFor weights 5 6 = xorDotsExact 5 := by
  ext <;> simp only [exactDotFor, exactQ, xorDotsExact]
  all_goals
    rw [exactDotLimbFor_5]
    rw [shiftedExact_five]
    norm_num [Finset.sum_range_succ, oddVector, evenCoefficients4,
      exactWeightWordFor, weightsToExact, weightEntry,
      exactQM31Limb, qm31ToExact, cm31ToExact,
      weights, q, Aeneas.Std.Array.make,
      AspisV5ComponentCQM31TowerExact.P] <;> decide

theorem xorDot_6 :
    exactDotFor weights 6 6 = xorDotsExact 6 := by
  ext <;> simp only [exactDotFor, exactQ, xorDotsExact]
  all_goals
    rw [exactDotLimbFor_6]
    rw [shiftedExact_six]
    norm_num [Finset.sum_range_succ, evenVector, evenCoefficients6,
      exactWeightWordFor, weightsToExact, weightEntry,
      exactQM31Limb, qm31ToExact, cm31ToExact,
      weights, q, Aeneas.Std.Array.make,
      AspisV5ComponentCQM31TowerExact.P] <;> decide

theorem xorDot_7 :
    exactDotFor weights 7 6 = xorDotsExact 7 := by
  ext <;> simp only [exactDotFor, exactQ, xorDotsExact]
  all_goals
    rw [exactDotLimbFor_7]
    rw [shiftedExact_seven]
    norm_num [Finset.sum_range_succ, oddVector, evenCoefficients6,
      exactWeightWordFor, weightsToExact, weightEntry,
      exactQM31Limb, qm31ToExact, cm31ToExact,
      weights, q, Aeneas.Std.Array.make,
      AspisV5ComponentCQM31TowerExact.P] <;> decide

theorem xorDot_8 :
    exactDotFor weights 8 6 = xorDotsExact 8 := by
  ext <;> simp only [exactDotFor, exactQ, xorDotsExact]
  all_goals
    rw [exactDotLimbFor_8]
    rw [shiftedExact_eight]
    norm_num [Finset.sum_range_succ, evenVector, evenCoefficients8,
      exactWeightWordFor, weightsToExact, weightEntry,
      exactQM31Limb, qm31ToExact, cm31ToExact,
      weights, q, Aeneas.Std.Array.make,
      AspisV5ComponentCQM31TowerExact.P] <;> decide

theorem xorDot_9 :
    exactDotFor weights 9 6 = xorDotsExact 9 := by
  ext <;> simp only [exactDotFor, exactQ, xorDotsExact]
  all_goals
    rw [exactDotLimbFor_9]
    rw [shiftedExact_nine]
    norm_num [Finset.sum_range_succ, oddVector, evenCoefficients8,
      exactWeightWordFor, weightsToExact, weightEntry,
      exactQM31Limb, qm31ToExact, cm31ToExact,
      weights, q, Aeneas.Std.Array.make,
      AspisV5ComponentCQM31TowerExact.P] <;> decide

theorem xorDot_10 :
    exactDotFor weights 10 6 = xorDotsExact 10 := by
  ext <;> simp only [exactDotFor, exactQ, xorDotsExact]
  all_goals
    rw [exactDotLimbFor_10]
    rw [shiftedExact_ten]
    norm_num [Finset.sum_range_succ, evenVector, evenCoefficients10,
      exactWeightWordFor, weightsToExact, weightEntry,
      exactQM31Limb, qm31ToExact, cm31ToExact,
      weights, q, Aeneas.Std.Array.make,
      AspisV5ComponentCQM31TowerExact.P] <;> decide

theorem xorDot_11 :
    exactDotFor weights 11 6 = xorDotsExact 11 := by
  ext <;> simp only [exactDotFor, exactQ, xorDotsExact]
  all_goals
    rw [exactDotLimbFor_11]
    rw [shiftedExact_eleven]
    norm_num [Finset.sum_range_succ, oddVector, evenCoefficients10,
      exactWeightWordFor, weightsToExact, weightEntry,
      exactQM31Limb, qm31ToExact, cm31ToExact,
      weights, q, Aeneas.Std.Array.make,
      AspisV5ComponentCQM31TowerExact.P] <;> decide

theorem successorDot_0 :
    exactDotFor successorWeights 0 0 = successorDotsExact 0 := by
  ext <;> simp only [exactDotFor, exactQ, successorDotsExact]
  all_goals
    rw [exactDotLimbFor_zero]
    rw [shiftedExact_zero]
    norm_num [Finset.sum_range_succ, evenVector, evenCoefficients0,
      exactWeightWordFor, weightsToExact, weightEntry,
      exactQM31Limb, qm31ToExact, cm31ToExact,
      successorWeights, q, Aeneas.Std.Array.make,
      AspisV5ComponentCQM31TowerExact.P] <;> decide

theorem successorDot_1 :
    exactDotFor successorWeights 1 0 = successorDotsExact 1 := by
  ext <;> simp only [exactDotFor, exactQ, successorDotsExact]
  all_goals
    rw [exactDotLimbFor_1]
    rw [shiftedExact_one_oddVector]
    norm_num [Finset.sum_range_succ, oddVector, evenCoefficients0,
      exactWeightWordFor, weightsToExact, weightEntry,
      exactQM31Limb, qm31ToExact, cm31ToExact,
      successorWeights, q, Aeneas.Std.Array.make,
      AspisV5ComponentCQM31TowerExact.P] <;> decide

theorem successorDot_2 :
    exactDotFor successorWeights 2 0 = successorDotsExact 2 := by
  ext <;> simp only [exactDotFor, exactQ, successorDotsExact]
  all_goals
    rw [exactDotLimbFor_2]
    rw [shiftedExact_two_evenVector]
    norm_num [Finset.sum_range_succ, evenVector, evenCoefficients2,
      exactWeightWordFor, weightsToExact, weightEntry,
      exactQM31Limb, qm31ToExact, cm31ToExact,
      successorWeights, q, Aeneas.Std.Array.make,
      AspisV5ComponentCQM31TowerExact.P] <;> decide

theorem successorDot_3 :
    exactDotFor successorWeights 3 0 = successorDotsExact 3 := by
  ext <;> simp only [exactDotFor, exactQ, successorDotsExact]
  all_goals
    rw [exactDotLimbFor_3]
    rw [shiftedExact_three]
    norm_num [Finset.sum_range_succ, oddVector, evenCoefficients2,
      exactWeightWordFor, weightsToExact, weightEntry,
      exactQM31Limb, qm31ToExact, cm31ToExact,
      successorWeights, q, Aeneas.Std.Array.make,
      AspisV5ComponentCQM31TowerExact.P] <;> decide

theorem successorDot_4 :
    exactDotFor successorWeights 4 0 = successorDotsExact 4 := by
  ext <;> simp only [exactDotFor, exactQ, successorDotsExact]
  all_goals
    rw [exactDotLimbFor_4]
    rw [shiftedExact_four]
    norm_num [Finset.sum_range_succ, evenVector, evenCoefficients4,
      exactWeightWordFor, weightsToExact, weightEntry,
      exactQM31Limb, qm31ToExact, cm31ToExact,
      successorWeights, q, Aeneas.Std.Array.make,
      AspisV5ComponentCQM31TowerExact.P] <;> decide

theorem successorDot_5 :
    exactDotFor successorWeights 5 0 = successorDotsExact 5 := by
  ext <;> simp only [exactDotFor, exactQ, successorDotsExact]
  all_goals
    rw [exactDotLimbFor_5]
    rw [shiftedExact_five]
    norm_num [Finset.sum_range_succ, oddVector, evenCoefficients4,
      exactWeightWordFor, weightsToExact, weightEntry,
      exactQM31Limb, qm31ToExact, cm31ToExact,
      successorWeights, q, Aeneas.Std.Array.make,
      AspisV5ComponentCQM31TowerExact.P] <;> decide

theorem successorDot_6 :
    exactDotFor successorWeights 6 0 = successorDotsExact 6 := by
  ext <;> simp only [exactDotFor, exactQ, successorDotsExact]
  all_goals
    rw [exactDotLimbFor_6]
    rw [shiftedExact_six]
    norm_num [Finset.sum_range_succ, evenVector, evenCoefficients6,
      exactWeightWordFor, weightsToExact, weightEntry,
      exactQM31Limb, qm31ToExact, cm31ToExact,
      successorWeights, q, Aeneas.Std.Array.make,
      AspisV5ComponentCQM31TowerExact.P] <;> decide

theorem successorDot_7 :
    exactDotFor successorWeights 7 0 = successorDotsExact 7 := by
  ext <;> simp only [exactDotFor, exactQ, successorDotsExact]
  all_goals
    rw [exactDotLimbFor_7]
    rw [shiftedExact_seven]
    norm_num [Finset.sum_range_succ, oddVector, evenCoefficients6,
      exactWeightWordFor, weightsToExact, weightEntry,
      exactQM31Limb, qm31ToExact, cm31ToExact,
      successorWeights, q, Aeneas.Std.Array.make,
      AspisV5ComponentCQM31TowerExact.P] <;> decide

theorem successorDot_8 :
    exactDotFor successorWeights 8 0 = successorDotsExact 8 := by
  ext <;> simp only [exactDotFor, exactQ, successorDotsExact]
  all_goals
    rw [exactDotLimbFor_8]
    rw [shiftedExact_eight]
    norm_num [Finset.sum_range_succ, evenVector, evenCoefficients8,
      exactWeightWordFor, weightsToExact, weightEntry,
      exactQM31Limb, qm31ToExact, cm31ToExact,
      successorWeights, q, Aeneas.Std.Array.make,
      AspisV5ComponentCQM31TowerExact.P] <;> decide

theorem successorDot_9 :
    exactDotFor successorWeights 9 0 = successorDotsExact 9 := by
  ext <;> simp only [exactDotFor, exactQ, successorDotsExact]
  all_goals
    rw [exactDotLimbFor_9]
    rw [shiftedExact_nine]
    norm_num [Finset.sum_range_succ, oddVector, evenCoefficients8,
      exactWeightWordFor, weightsToExact, weightEntry,
      exactQM31Limb, qm31ToExact, cm31ToExact,
      successorWeights, q, Aeneas.Std.Array.make,
      AspisV5ComponentCQM31TowerExact.P] <;> decide

theorem successorDot_10 :
    exactDotFor successorWeights 10 0 = successorDotsExact 10 := by
  ext <;> simp only [exactDotFor, exactQ, successorDotsExact]
  all_goals
    rw [exactDotLimbFor_10]
    rw [shiftedExact_ten]
    norm_num [Finset.sum_range_succ, evenVector, evenCoefficients10,
      exactWeightWordFor, weightsToExact, weightEntry,
      exactQM31Limb, qm31ToExact, cm31ToExact,
      successorWeights, q, Aeneas.Std.Array.make,
      AspisV5ComponentCQM31TowerExact.P] <;> decide

theorem successorDot_11 :
    exactDotFor successorWeights 11 0 = successorDotsExact 11 := by
  ext <;> simp only [exactDotFor, exactQ, successorDotsExact]
  all_goals
    rw [exactDotLimbFor_11]
    rw [shiftedExact_eleven]
    norm_num [Finset.sum_range_succ, oddVector, evenCoefficients10,
      exactWeightWordFor, weightsToExact, weightEntry,
      exactQM31Limb, qm31ToExact, cm31ToExact,
      successorWeights, q, Aeneas.Std.Array.make,
      AspisV5ComponentCQM31TowerExact.P] <;> decide


theorem baseDots_exact :
    (fun shift : Fin 12 => exactDotFor weights shift 0) = baseDotsExact := by
  funext shift
  fin_cases shift
  · exact baseDot_zero
  · exact baseDot_one
  · exact baseDot_2
  · exact baseDot_3
  · exact baseDot_4
  · exact baseDot_5
  · exact baseDot_6
  · exact baseDot_7
  · exact baseDot_8
  · exact baseDot_9
  · exact baseDot_10
  · exact baseDot_11

theorem xorDots_exact :
    (fun shift : Fin 12 => exactDotFor weights shift 6) = xorDotsExact := by
  funext shift
  fin_cases shift
  · exact xorDot_0
  · exact xorDot_1
  · exact xorDot_2
  · exact xorDot_3
  · exact xorDot_4
  · exact xorDot_5
  · exact xorDot_6
  · exact xorDot_7
  · exact xorDot_8
  · exact xorDot_9
  · exact xorDot_10
  · exact xorDot_11

theorem successorDots_exact :
    (fun shift : Fin 12 => exactDotFor successorWeights shift 0) =
      successorDotsExact := by
  funext shift
  fin_cases shift
  · exact successorDot_0
  · exact successorDot_1
  · exact successorDot_2
  · exact successorDot_3
  · exact successorDot_4
  · exact successorDot_5
  · exact successorDot_6
  · exact successorDot_7
  · exact successorDot_8
  · exact successorDot_9
  · exact successorDot_10
  · exact successorDot_11

end GoodMatricesCurrent.ProbeTerminalMatrix

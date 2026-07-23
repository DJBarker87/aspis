import GoodMatricesCurrent.SourceExtractedTerminalWeights
import GoodMatricesCurrent.SourceExtractedSuccessorAll
import GoodMatricesCurrent.SourceExtractedEvenKernel
import GoodMatricesCurrent.SourceExtractedGoodAModelBridge

open Aeneas Aeneas.Std Result ControlFlow Error
open aspis_verifier

namespace GoodMatricesCurrent.ProbeGeneratedConcrete

abbrev LocalQM31 := aspis_verifier.aspis_core.field.QM31
abbrev LocalPoint := Array LocalQM31 10#usize
abbrev LocalWeights := Array LocalQM31 64#usize

deriving instance DecidableEq for aspis_verifier.aspis_core.field.CM31
deriving instance DecidableEq for aspis_verifier.aspis_core.field.QM31
deriving instance DecidableEq for Aeneas.Std.Error
deriving instance DecidableEq for Aeneas.Std.Result

instance {α : Type} [DecidableEq α] {n : Std.Usize} :
    DecidableEq (Aeneas.Std.Array α n) := fun left right =>
  decidable_of_iff (left.val = right.val) (by
    constructor
    · exact Subtype.ext
    · intro h
      exact congrArg Subtype.val h)

def q (a b c d : Std.U32) : LocalQM31 :=
  { c0 := { a := a, b := b }, c1 := { a := c, b := d } }

def point : LocalPoint := Array.make 10#usize [
  q 404107582#u32 1727074950#u32 929436228#u32 337050246#u32,
  q 1551059663#u32 276722441#u32 1042656822#u32 513863785#u32,
  q 164049145#u32 1996763382#u32 1728701267#u32 1725471872#u32,
  q 1579020738#u32 1603896284#u32 1206833734#u32 1303440574#u32,
  q 444095533#u32 1733870221#u32 271870451#u32 46368227#u32,
  q 1281619349#u32 328022466#u32 1429624261#u32 972991110#u32,
  q 1204014726#u32 1716417842#u32 1524198052#u32 774277607#u32,
  q 1082422057#u32 694365077#u32 591158920#u32 1683812251#u32,
  q 1577214774#u32 1016671131#u32 411456236#u32 1648869862#u32,
  q 758441825#u32 1940717419#u32 1517866177#u32 737596238#u32]

def weights : LocalWeights := Array.make 64#usize [
  q 1275428044#u32 1242013445#u32 1630939657#u32 1336779759#u32,
  q 1921241914#u32 1589273607#u32 1586452267#u32 1203051557#u32,
  q 18207996#u32 715708674#u32 1395022550#u32 1822590451#u32,
  q 1145194869#u32 308820941#u32 532323551#u32 42645069#u32,
  q 428322155#u32 1422152534#u32 1481124870#u32 1863323769#u32,
  q 362961004#u32 1354487275#u32 562829437#u32 602369730#u32,
  q 1199756582#u32 1739060785#u32 2020045581#u32 1332963219#u32,
  q 754940970#u32 1826891148#u32 637676377#u32 1370081965#u32,
  q 1519488712#u32 174410415#u32 831952546#u32 755710835#u32,
  q 298596831#u32 536925340#u32 2053160327#u32 1746048508#u32,
  q 28759261#u32 1419411017#u32 1761165347#u32 4924273#u32,
  q 1622627256#u32 1018285852#u32 146248669#u32 433872017#u32,
  q 183460883#u32 1402426231#u32 1631797246#u32 734592152#u32,
  q 1499862925#u32 928931244#u32 2045123412#u32 911269628#u32,
  q 947102639#u32 1307427160#u32 302566497#u32 88267893#u32,
  q 1227132645#u32 2045699638#u32 1259826516#u32 824690000#u32,
  q 2027295822#u32 788777474#u32 1021134328#u32 144718033#u32,
  q 2029941714#u32 1824491134#u32 157786320#u32 1864302607#u32,
  q 653956101#u32 1337710605#u32 695791233#u32 1649690677#u32,
  q 925302732#u32 684136891#u32 1602283767#u32 35144596#u32,
  q 19846691#u32 533745589#u32 1580333304#u32 780318183#u32,
  q 1780209513#u32 1170915364#u32 1267267561#u32 2109160229#u32,
  q 1047033849#u32 796912573#u32 1178089627#u32 160825311#u32,
  q 1509704204#u32 1446489282#u32 1226103365#u32 515514075#u32,
  q 1859838828#u32 811454280#u32 2061575413#u32 1823291211#u32,
  q 869041834#u32 1484090268#u32 1693520718#u32 546145940#u32,
  q 1296516270#u32 1593168788#u32 1607038280#u32 666754780#u32,
  q 830258891#u32 663706548#u32 1618961052#u32 1586434363#u32,
  q 878521500#u32 1730765349#u32 1793836204#u32 346133247#u32,
  q 1137510876#u32 1703484548#u32 1762694963#u32 1194613118#u32,
  q 135215890#u32 223856040#u32 1510210903#u32 1902691355#u32,
  q 1347438214#u32 1225179323#u32 1087957318#u32 509895581#u32,
  q 103400299#u32 998528472#u32 292976155#u32 2059746705#u32,
  q 1123251681#u32 603046988#u32 682890399#u32 433416417#u32,
  q 562549419#u32 616279543#u32 1417669746#u32 2123067575#u32,
  q 1996367964#u32 977506884#u32 1653759822#u32 71617589#u32,
  q 2058331342#u32 1604343159#u32 2092878158#u32 2098556668#u32,
  q 960192013#u32 1946160454#u32 1026134392#u32 1733160476#u32,
  q 42246242#u32 839598902#u32 1619456717#u32 1467727374#u32,
  q 364582454#u32 2102088532#u32 1847138794#u32 1670994277#u32,
  q 1511404187#u32 142492897#u32 613274509#u32 268145917#u32,
  q 372886528#u32 798397280#u32 733474400#u32 266128555#u32,
  q 2123503527#u32 1894968479#u32 1364651329#u32 750122463#u32,
  q 1851852510#u32 1230080742#u32 196590286#u32 166378312#u32,
  q 187430015#u32 2041470388#u32 832635306#u32 312064593#u32,
  q 1819281704#u32 387524332#u32 1474458626#u32 725127639#u32,
  q 749070830#u32 462597940#u32 1406275831#u32 1677831264#u32,
  q 1508723772#u32 1243825127#u32 1250315875#u32 1268619829#u32,
  q 299607292#u32 1498688596#u32 753467209#u32 884501790#u32,
  q 1862596550#u32 1395021348#u32 466217392#u32 1430464076#u32,
  q 598780228#u32 560143927#u32 716032323#u32 1945412036#u32,
  q 2077424981#u32 936155837#u32 250272699#u32 1859021955#u32,
  q 1925494441#u32 1424127734#u32 1747311534#u32 57295115#u32,
  q 756371076#u32 215903961#u32 1830436821#u32 1807452599#u32,
  q 779585442#u32 326651887#u32 219222700#u32 393912241#u32,
  q 467993420#u32 1353365988#u32 2034012729#u32 811888413#u32,
  q 1650487503#u32 1567323180#u32 858869581#u32 928283744#u32,
  q 1050461612#u32 2027244453#u32 1072112272#u32 224393401#u32,
  q 1142491382#u32 1137734034#u32 688749020#u32 1774910366#u32,
  q 801928183#u32 67322571#u32 679177133#u32 590261521#u32,
  q 59448168#u32 715693540#u32 548844338#u32 1493993908#u32,
  q 1592586286#u32 1896029690#u32 2023520708#u32 2138849639#u32,
  q 1174974745#u32 273423584#u32 568311368#u32 1209205230#u32,
  q 215969647#u32 532410540#u32 457950267#u32 1020627239#u32]

def successor : LocalPoint := Array.make 10#usize [
  q 1709413857#u32 1262388363#u32 1781824926#u32 593272244#u32,
  q 1269191070#u32 1005984724#u32 102117316#u32 540951424#u32,
  q 1292356916#u32 1614211921#u32 1940278827#u32 752107833#u32,
  q 204126482#u32 73931667#u32 1028314550#u32 1522116093#u32,
  q 839234315#u32 2118951038#u32 683834885#u32 1391763168#u32,
  q 427811287#u32 1497779637#u32 1857178002#u32 1848604400#u32,
  q 310567372#u32 1886635095#u32 1547721827#u32 1916817595#u32,
  q 1622260373#u32 1339591833#u32 737288956#u32 1644216715#u32,
  q 739093681#u32 1148153300#u32 550685409#u32 2036173971#u32,
  q 1389041823#u32 206766228#u32 629617470#u32 1409887409#u32]

abbrev LocalKernel := Array Std.U32 37#usize
abbrev LocalVector := Array Std.U32 48#usize
abbrev LocalChain := alloc.vec.Vec LocalVector

def kernel : LocalKernel := Array.make 37#usize [
  519620177#u32, 0#u32, 528764235#u32, 0#u32, 671819249#u32, 0#u32,
  2140992514#u32, 0#u32, 1843223343#u32, 0#u32, 1094648776#u32, 0#u32,
  1064183334#u32, 0#u32, 1834578843#u32, 0#u32, 113403409#u32, 0#u32,
  785436993#u32, 0#u32, 852377093#u32, 0#u32, 1757436383#u32, 0#u32,
  1641054439#u32, 0#u32, 479908979#u32, 0#u32, 1253767301#u32, 0#u32,
  1177649036#u32, 0#u32, 1272219910#u32, 0#u32, 2076166121#u32, 0#u32,
  1#u32]

def v (values : List Std.U32) (h : values.length = 48 := by simp) : LocalVector :=
  Array.make 48#usize values (by simpa using h)

def baseDirection : LocalVector :=
  v [1447460119#u32,0#u32,615059998#u32,0#u32,79177021#u32,0#u32,
    264360387#u32,0#u32,175677395#u32,0#u32,690316057#u32,0#u32,
    1940922128#u32,0#u32,1980834973#u32,0#u32,244042458#u32,0#u32,
    1373926702#u32,0#u32,926559219#u32,0#u32,1646207007#u32,0#u32,
    542340637#u32,0#u32,1581685827#u32,0#u32,496267907#u32,0#u32,
    29599140#u32,0#u32,1471327346#u32,0#u32,1038083065#u32,0#u32,
    268435456#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,
    0#u32,0#u32,0#u32,0#u32]

def direction1 : LocalVector :=
  v [0#u32,1447460119#u32,0#u32,615059998#u32,0#u32,79177021#u32,
    0#u32,264360387#u32,0#u32,175677395#u32,0#u32,690316057#u32,
    0#u32,1940922128#u32,0#u32,1980834973#u32,0#u32,244042458#u32,
    0#u32,1373926702#u32,0#u32,926559219#u32,0#u32,1646207007#u32,
    0#u32,542340637#u32,0#u32,1581685827#u32,0#u32,496267907#u32,
    0#u32,29599140#u32,0#u32,1471327346#u32,0#u32,1038083065#u32,
    0#u32,268435456#u32,0#u32,0#u32,0#u32,0#u32,0#u32,0#u32,
    0#u32,0#u32,0#u32,0#u32]

def directions : LocalChain := ⟨[
  baseDirection,
  direction1,
  v [1706355906#u32,0#u32,2105001882#u32,0#u32,1870056342#u32,0#u32,
    171768704#u32,0#u32,4196220#u32,0#u32,432996726#u32,0#u32,
    564506998#u32,0#u32,887136727#u32,0#u32,1736455008#u32,0#u32,
    808984580#u32,0#u32,681442125#u32,0#u32,1286383113#u32,0#u32,
    70761176#u32,0#u32,1062013232#u32,0#u32,1187826107#u32,0#u32,
    1336675347#u32,0#u32,1801415780#u32,0#u32,180963382#u32,0#u32,
    930609406#u32,0#u32,134217728#u32,0#u32,0#u32,0#u32,0#u32,
    0#u32,0#u32,0#u32,0#u32,0#u32],
  v [0#u32,1706355906#u32,0#u32,2105001882#u32,0#u32,1870056342#u32,
    0#u32,171768704#u32,0#u32,4196220#u32,0#u32,432996726#u32,
    0#u32,564506998#u32,0#u32,887136727#u32,0#u32,1736455008#u32,
    0#u32,808984580#u32,0#u32,681442125#u32,0#u32,1286383113#u32,
    0#u32,70761176#u32,0#u32,1062013232#u32,0#u32,1187826107#u32,
    0#u32,1336675347#u32,0#u32,1801415780#u32,0#u32,180963382#u32,
    0#u32,930609406#u32,0#u32,134217728#u32,0#u32,0#u32,0#u32,
    0#u32,0#u32,0#u32,0#u32,0#u32],
  v [491483702#u32,0#u32,1905678894#u32,0#u32,430478994#u32,0#u32,
    1020912523#u32,0#u32,1048016838#u32,0#u32,218596473#u32,0#u32,
    1149157774#u32,0#u32,1799563686#u32,0#u32,833388881#u32,0#u32,
    1272719794#u32,0#u32,327692074#u32,0#u32,983912619#u32,0#u32,
    1702508027#u32,0#u32,566387204#u32,0#u32,1730456110#u32,0#u32,
    1262250727#u32,0#u32,1205823648#u32,0#u32,991189581#u32,0#u32,
    1617841804#u32,0#u32,532413567#u32,0#u32,16777216#u32,0#u32,
    0#u32,0#u32,0#u32,0#u32,0#u32,0#u32],
  v [0#u32,491483702#u32,0#u32,1905678894#u32,0#u32,430478994#u32,
    0#u32,1020912523#u32,0#u32,1048016838#u32,0#u32,218596473#u32,
    0#u32,1149157774#u32,0#u32,1799563686#u32,0#u32,833388881#u32,
    0#u32,1272719794#u32,0#u32,327692074#u32,0#u32,983912619#u32,
    0#u32,1702508027#u32,0#u32,566387204#u32,0#u32,1730456110#u32,
    0#u32,1262250727#u32,0#u32,1205823648#u32,0#u32,991189581#u32,
    0#u32,1617841804#u32,0#u32,532413567#u32,0#u32,16777216#u32,
    0#u32,0#u32,0#u32,0#u32,0#u32,0#u32],
  v [2008326665#u32,0#u32,1198581298#u32,0#u32,1483758263#u32,0#u32,
    1799437582#u32,0#u32,1736523431#u32,0#u32,1707048479#u32,0#u32,
    542248015#u32,0#u32,1474360730#u32,0#u32,1451880051#u32,0#u32,
    2126796161#u32,0#u32,1264875052#u32,0#u32,1729544170#u32,0#u32,
    736750321#u32,0#u32,60705792#u32,0#u32,785516626#u32,0#u32,
    422611595#u32,0#u32,1694903754#u32,0#u32,24764791#u32,0#u32,
    1189821689#u32,0#u32,1385862#u32,0#u32,1953988495#u32,0#u32,
    8388608#u32,0#u32,0#u32,0#u32,0#u32,0#u32],
  v [0#u32,2008326665#u32,0#u32,1198581298#u32,0#u32,1483758263#u32,
    0#u32,1799437582#u32,0#u32,1736523431#u32,0#u32,1707048479#u32,
    0#u32,542248015#u32,0#u32,1474360730#u32,0#u32,1451880051#u32,
    0#u32,2126796161#u32,0#u32,1264875052#u32,0#u32,1729544170#u32,
    0#u32,736750321#u32,0#u32,60705792#u32,0#u32,785516626#u32,
    0#u32,422611595#u32,0#u32,1694903754#u32,0#u32,24764791#u32,
    0#u32,1189821689#u32,0#u32,1385862#u32,0#u32,1953988495#u32,
    0#u32,8388608#u32,0#u32,0#u32,0#u32,0#u32],
  v [1030112737#u32,0#u32,529712158#u32,0#u32,417642028#u32,0#u32,
    567856099#u32,0#u32,93635889#u32,0#u32,1721785955#u32,0#u32,
    529605398#u32,0#u32,2082046196#u32,0#u32,115997850#u32,0#u32,
    1789338106#u32,0#u32,1059651697#u32,0#u32,1497209611#u32,0#u32,
    921006535#u32,0#u32,1472469880#u32,0#u32,2124200395#u32,0#u32,
    1677805934#u32,0#u32,531478600#u32,0#u32,1933576096#u32,0#u32,
    64577596#u32,0#u32,1669345599#u32,0#u32,1516135544#u32,0#u32,
    2054930375#u32,0#u32,2097152#u32,0#u32,0#u32,0#u32],
  v [0#u32,1030112737#u32,0#u32,529712158#u32,0#u32,417642028#u32,
    0#u32,567856099#u32,0#u32,93635889#u32,0#u32,1721785955#u32,
    0#u32,529605398#u32,0#u32,2082046196#u32,0#u32,115997850#u32,
    0#u32,1789338106#u32,0#u32,1059651697#u32,0#u32,1497209611#u32,
    0#u32,921006535#u32,0#u32,1472469880#u32,0#u32,2124200395#u32,
    0#u32,1677805934#u32,0#u32,531478600#u32,0#u32,1933576096#u32,
    0#u32,64577596#u32,0#u32,1669345599#u32,0#u32,1516135544#u32,
    0#u32,2054930375#u32,0#u32,2097152#u32,0#u32,0#u32],
  v [1035243471#u32,0#u32,1853654271#u32,0#u32,1020083990#u32,0#u32,
    1566490887#u32,0#u32,1076937676#u32,0#u32,907710922#u32,0#u32,
    678889825#u32,0#u32,1305825797#u32,0#u32,927475411#u32,0#u32,
    952667978#u32,0#u32,814591866#u32,0#u32,1278430654#u32,0#u32,
    420191313#u32,0#u32,122996384#u32,0#u32,1849669151#u32,0#u32,
    827261341#u32,0#u32,1681321599#u32,0#u32,1232527348#u32,0#u32,
    396148310#u32,0#u32,1940703421#u32,0#u32,675162198#u32,0#u32,
    711791136#u32,0#u32,2125393905#u32,0#u32,1048576#u32,0#u32],
  v [0#u32,1035243471#u32,0#u32,1853654271#u32,0#u32,1020083990#u32,
    0#u32,1566490887#u32,0#u32,1076937676#u32,0#u32,907710922#u32,
    0#u32,678889825#u32,0#u32,1305825797#u32,0#u32,927475411#u32,
    0#u32,952667978#u32,0#u32,814591866#u32,0#u32,1278430654#u32,
    0#u32,420191313#u32,0#u32,122996384#u32,0#u32,1849669151#u32,
    0#u32,827261341#u32,0#u32,1681321599#u32,0#u32,1232527348#u32,
    0#u32,396148310#u32,0#u32,1940703421#u32,0#u32,675162198#u32,
    0#u32,711791136#u32,0#u32,2125393905#u32,0#u32,1048576#u32]
  ], by
    rcases System.Platform.numBits_eq with hplatform | hplatform <;>
      norm_num [Std.Usize.max, Std.Usize.numBits, hplatform]⟩

def directionEntry (shift : Fin 12) : LocalVector :=
  directions.val[shift.val]'(by
    norm_num [directions])

#synth DecidableEq LocalQM31
#synth DecidableEq LocalWeights
#synth DecidableEq (Aeneas.Std.Result LocalWeights)
#check List.ext_getElem

open GoodMatricesCurrent.SourceExtractedTerminalField
open GoodMatricesCurrent.SourceExtractedTerminalWeights

local macro "prove_base_coordinate" : tactic =>
  `(tactic|
    (rw [GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion_eq_formula]
     simp only [
       GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityFormula,
       Fintype.linearCombination_apply, Fintype.sum_apply]
     norm_num [
       Fin.sum_univ_succ,
       GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityRow,
       GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityKernelCoefficient,
       GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityTableWord,
       AspisV5ComponentCQM31TowerExact.P,
       v5_cu_probe.good_gate_probe.MONOMIAL_TO_NATURAL_PARITY,
       baseDirection, v, kernel, Aeneas.Std.Array.make,
       GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact,
       GoodMatricesCurrent.SourceExtractedFixedSupport.arrayToExact,
       GoodMatricesCurrent.SourceExtractedFixedSupport.arrayEntry,
       GoodMatricesCurrent.SourceExtractedField.m31ToExact] <;> decide))

theorem baseDirection_source_exact_0 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨0, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨0, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_1 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨1, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨1, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_2 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨2, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨2, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_3 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨3, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨3, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_4 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨4, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨4, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_5 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨5, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨5, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_6 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨6, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨6, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_7 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨7, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨7, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_8 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨8, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨8, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_9 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨9, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨9, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_10 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨10, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨10, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_11 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨11, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨11, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_12 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨12, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨12, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_13 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨13, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨13, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_14 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨14, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨14, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_15 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨15, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨15, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_16 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨16, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨16, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_17 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨17, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨17, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_18 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨18, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨18, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_19 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨19, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨19, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_20 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨20, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨20, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_21 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨21, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨21, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_22 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨22, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨22, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_23 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨23, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨23, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_24 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨24, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨24, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_25 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨25, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨25, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_26 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨26, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨26, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_27 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨27, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨27, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_28 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨28, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨28, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_29 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨29, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨29, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_30 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨30, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨30, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_31 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨31, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨31, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_32 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨32, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨32, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_33 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨33, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨33, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_34 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨34, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨34, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_35 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨35, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨35, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_36 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨36, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨36, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_37 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨37, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨37, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_38 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨38, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨38, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_39 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨39, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨39, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_40 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨40, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨40, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_41 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨41, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨41, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_42 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨42, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨42, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_43 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨43, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨43, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_44 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨44, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨44, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_45 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨45, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨45, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_46 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨46, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨46, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact_47 :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection ⟨47, by omega⟩ =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel ⟨47, by omega⟩ := by
  prove_base_coordinate

theorem baseDirection_source_exact :
    GoodMatricesCurrent.SourceExtractedGoodAModelBridge.FixedSupport.arrayToExact
        baseDirection =
      GoodMatricesCurrent.SourceExtractedEvenKernel.sourceParityConversion
        kernel := by
  funext coordinate
  fin_cases coordinate
  · exact baseDirection_source_exact_0
  · exact baseDirection_source_exact_1
  · exact baseDirection_source_exact_2
  · exact baseDirection_source_exact_3
  · exact baseDirection_source_exact_4
  · exact baseDirection_source_exact_5
  · exact baseDirection_source_exact_6
  · exact baseDirection_source_exact_7
  · exact baseDirection_source_exact_8
  · exact baseDirection_source_exact_9
  · exact baseDirection_source_exact_10
  · exact baseDirection_source_exact_11
  · exact baseDirection_source_exact_12
  · exact baseDirection_source_exact_13
  · exact baseDirection_source_exact_14
  · exact baseDirection_source_exact_15
  · exact baseDirection_source_exact_16
  · exact baseDirection_source_exact_17
  · exact baseDirection_source_exact_18
  · exact baseDirection_source_exact_19
  · exact baseDirection_source_exact_20
  · exact baseDirection_source_exact_21
  · exact baseDirection_source_exact_22
  · exact baseDirection_source_exact_23
  · exact baseDirection_source_exact_24
  · exact baseDirection_source_exact_25
  · exact baseDirection_source_exact_26
  · exact baseDirection_source_exact_27
  · exact baseDirection_source_exact_28
  · exact baseDirection_source_exact_29
  · exact baseDirection_source_exact_30
  · exact baseDirection_source_exact_31
  · exact baseDirection_source_exact_32
  · exact baseDirection_source_exact_33
  · exact baseDirection_source_exact_34
  · exact baseDirection_source_exact_35
  · exact baseDirection_source_exact_36
  · exact baseDirection_source_exact_37
  · exact baseDirection_source_exact_38
  · exact baseDirection_source_exact_39
  · exact baseDirection_source_exact_40
  · exact baseDirection_source_exact_41
  · exact baseDirection_source_exact_42
  · exact baseDirection_source_exact_43
  · exact baseDirection_source_exact_44
  · exact baseDirection_source_exact_45
  · exact baseDirection_source_exact_46
  · exact baseDirection_source_exact_47

theorem sum_range_47_chunks {M : Type*} [AddCommMonoid M]
    (term : Nat → M) :
    (∑ index ∈ Finset.range 47, term index) =
      (∑ index ∈ Finset.range 4, term (index)) +
      (∑ index ∈ Finset.range 4, term (4 + index)) +
      (∑ index ∈ Finset.range 4, term (8 + index)) +
      (∑ index ∈ Finset.range 4, term (12 + index)) +
      (∑ index ∈ Finset.range 4, term (16 + index)) +
      (∑ index ∈ Finset.range 4, term (20 + index)) +
      (∑ index ∈ Finset.range 4, term (24 + index)) +
      (∑ index ∈ Finset.range 4, term (28 + index)) +
      (∑ index ∈ Finset.range 4, term (32 + index)) +
      (∑ index ∈ Finset.range 4, term (36 + index)) +
      (∑ index ∈ Finset.range 4, term (40 + index)) +
      (∑ index ∈ Finset.range 3, term (44 + index)) := by
  rw [show 47 = 4 + 43 by omega, Finset.sum_range_add]
  rw [show 43 = 4 + 39 by omega, Finset.sum_range_add]
  rw [show 39 = 4 + 35 by omega, Finset.sum_range_add]
  rw [show 35 = 4 + 31 by omega, Finset.sum_range_add]
  rw [show 31 = 4 + 27 by omega, Finset.sum_range_add]
  rw [show 27 = 4 + 23 by omega, Finset.sum_range_add]
  rw [show 23 = 4 + 19 by omega, Finset.sum_range_add]
  rw [show 19 = 4 + 15 by omega, Finset.sum_range_add]
  rw [show 15 = 4 + 11 by omega, Finset.sum_range_add]
  rw [show 11 = 4 + 7 by omega, Finset.sum_range_add]
  rw [show 7 = 4 + 3 by omega, Finset.sum_range_add]
  ac_rfl

example :
    AspisV5GoodGateSparseShift.sparseBasis
      (K := AspisV5ComponentCQM31TowerExact.M31Exact)
      (0 : Fin 47) (0 : Fin 48) = 0 := by
  classical
  simp [AspisV5GoodGateSparseShift.sparseBasis,
    AspisV5GoodGateSparseShift.successorIndex]

theorem point_canonical : CanonicalLocalPoint point := by
  intro index
  fin_cases index <;>
    norm_num [point, pointEntry, q, Aeneas.Std.Array.make,
      CanonicalLocalQM31, CanonicalLocalCM31, CanonicalLocalM31,
      AspisV5ComponentCQM31TowerExact.P]

theorem weights_canonical : CanonicalLocalWeights weights := by
  intro index
  fin_cases index <;>
    norm_num [weights, weightEntry, q, Aeneas.Std.Array.make,
      CanonicalLocalQM31, CanonicalLocalCM31, CanonicalLocalM31,
      AspisV5ComponentCQM31TowerExact.P]

example : weightsToExact weights = exactSuffixWeight (pointToExact point) := by
  funext index
  fin_cases index <;> decide

theorem canonical_m31_exact_injective (left right : Std.U32)
    (hleft : CanonicalLocalM31 left) (hright : CanonicalLocalM31 right)
    (hexact : (left.val : AspisV5ComponentCQM31TowerExact.M31Exact) =
      (right.val : AspisV5ComponentCQM31TowerExact.M31Exact)) :
    left = right := by
  apply UScalar.val_eq_imp
  rw [ZMod.natCast_eq_natCast_iff] at hexact
  exact hexact.eq_of_lt_of_lt hleft hright

theorem canonical_qm31_exact_injective (left right : LocalQM31)
    (hleft : CanonicalLocalQM31 left) (hright : CanonicalLocalQM31 right)
    (hexact : qm31ToExact left = qm31ToExact right) : left = right := by
  have h00 := congrArg (fun value => value.re.re) hexact
  have h01 := congrArg (fun value => value.re.im) hexact
  have h10 := congrArg (fun value => value.im.re) hexact
  have h11 := congrArg (fun value => value.im.im) hexact
  have e00 := canonical_m31_exact_injective left.c0.a right.c0.a
    hleft.1.1 hright.1.1 h00
  have e01 := canonical_m31_exact_injective left.c0.b right.c0.b
    hleft.1.2 hright.1.2 h01
  have e10 := canonical_m31_exact_injective left.c1.a right.c1.a
    hleft.2.1 hright.2.1 h10
  have e11 := canonical_m31_exact_injective left.c1.b right.c1.b
    hleft.2.2 hright.2.2 h11
  cases left with
  | mk left0 left1 =>
    cases left0 with
    | mk left00 left01 =>
      cases left1 with
      | mk left10 left11 =>
        cases right with
        | mk right0 right1 =>
          cases right0 with
          | mk right00 right01 =>
            cases right1 with
            | mk right10 right11 =>
              simp only at e00 e01 e10 e11
              subst right00
              subst right01
              subst right10
              subst right11
              rfl

theorem canonical_weights_exact_injective (left right : LocalWeights)
    (hleft : CanonicalLocalWeights left)
    (hright : CanonicalLocalWeights right)
    (hexact : weightsToExact left = weightsToExact right) : left = right := by
  apply Subtype.ext
  apply List.ext_getElem
  · rw [left.property, right.property]
  · intro index hindexLeft hindexRight
    have hindex : index < 64 := by
      simpa [left.property] using hindexLeft
    exact canonical_qm31_exact_injective
      (weightEntry left ⟨index, hindex⟩)
      (weightEntry right ⟨index, hindex⟩)
      (hleft ⟨index, hindex⟩) (hright ⟨index, hindex⟩)
      (congrFun hexact ⟨index, hindex⟩)

theorem weights_call :
    v5_cu_probe.good_gate_probe.mle_six_coordinate_suffix_weights point =
      .ok weights := by
  obtain ⟨result, hcall, hcanonical, hexact⟩ :=
    mle_six_coordinate_suffix_weights_exact_spec point point_canonical
  have hliteralExact :
      weightsToExact weights = exactSuffixWeight (pointToExact point) := by
    funext index
    fin_cases index <;> decide
  have hresult : result = weights := canonical_weights_exact_injective
    result weights hcanonical weights_canonical (hexact.trans hliteralExact.symm)
  simpa [hresult] using hcall

theorem successor_canonical :
    GoodMatricesCurrent.SourceExtractedSuccessor.CanonicalLocalPoint successor := by
  intro index
  fin_cases index <;>
    norm_num [successor,
      GoodMatricesCurrent.SourceExtractedSuccessor.pointEntry,
      q, Aeneas.Std.Array.make, CanonicalLocalQM31,
      CanonicalLocalCM31, CanonicalLocalM31,
      AspisV5ComponentCQM31TowerExact.P]

theorem canonical_point_exact_injective
    (left right : LocalPoint)
    (hleft : GoodMatricesCurrent.SourceExtractedSuccessor.CanonicalLocalPoint left)
    (hright : GoodMatricesCurrent.SourceExtractedSuccessor.CanonicalLocalPoint right)
    (hexact : GoodMatricesCurrent.SourceExtractedSuccessor.pointToExact left =
      GoodMatricesCurrent.SourceExtractedSuccessor.pointToExact right) :
    left = right := by
  apply Subtype.ext
  apply List.ext_getElem
  · rw [left.property, right.property]
  · intro index hindexLeft hindexRight
    have hindex : index < 10 := by
      simpa [left.property] using hindexLeft
    exact canonical_qm31_exact_injective
      (GoodMatricesCurrent.SourceExtractedSuccessor.pointEntry
        left ⟨index, hindex⟩)
      (GoodMatricesCurrent.SourceExtractedSuccessor.pointEntry
        right ⟨index, hindex⟩)
      (hleft ⟨index, hindex⟩) (hright ⟨index, hindex⟩)
      (congrFun hexact ⟨index, hindex⟩)

theorem successor_exact :
    GoodMatricesCurrent.SourceExtractedSuccessor.pointToExact successor =
      AspisV5ComponentADeployedTerminalApplicability.deployedSuccessorPoint
        (GoodMatricesCurrent.SourceExtractedSuccessor.pointToExact point) := by
  funext index
  fin_cases index <;> decide

theorem successor_call :
    v5_cu_probe.good_gate_probe.binary_successor_point point =
      .ok successor := by
  have hpointSuccessor :
      GoodMatricesCurrent.SourceExtractedSuccessor.CanonicalLocalPoint point := by
    intro index
    fin_cases index <;>
      norm_num [point,
        GoodMatricesCurrent.SourceExtractedSuccessor.pointEntry,
        q, Aeneas.Std.Array.make, CanonicalLocalQM31,
        CanonicalLocalCM31, CanonicalLocalM31,
        AspisV5ComponentCQM31TowerExact.P]
  obtain ⟨result, hcall, hcanonical, hexact⟩ :=
    GoodMatricesCurrent.SourceExtractedSuccessor.binary_successor_point_exact_spec
      point hpointSuccessor
  have hresult : result = successor := canonical_point_exact_injective
    result successor hcanonical successor_canonical
      (hexact.trans successor_exact.symm)
  simpa [hresult] using hcall

end GoodMatricesCurrent.ProbeGeneratedConcrete

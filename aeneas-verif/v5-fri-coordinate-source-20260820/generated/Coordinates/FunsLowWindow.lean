-- Deterministic low-memory normalization of the recorded Aeneas output.
import Coordinates.FunsHighWindow
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace V5FriCoordinateAdapter

private def rate512LowChunk0 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 1633461177#u32, 574296567#u32 ],
    Array.make 2#usize [ 1242192167#u32, 1322293366#u32 ],
    Array.make 2#usize [ 1139757936#u32, 161139962#u32 ],
    Array.make 2#usize [ 2056541252#u32, 1900478857#u32 ],
    Array.make 2#usize [ 1765678898#u32, 2028236613#u32 ],
    Array.make 2#usize [ 1503715524#u32, 748528002#u32 ],
    Array.make 2#usize [ 687167191#u32, 1193781868#u32 ],
    Array.make 2#usize [ 1076514332#u32, 1068664781#u32 ],
    Array.make 2#usize [ 2016807951#u32, 234018695#u32 ],
    Array.make 2#usize [ 1210077794#u32, 246102266#u32 ],
    Array.make 2#usize [ 1235766230#u32, 338243230#u32 ],
    Array.make 2#usize [ 713314261#u32, 425545952#u32 ],
    Array.make 2#usize [ 1300335129#u32, 1837567123#u32 ],
    Array.make 2#usize [ 1032881673#u32, 494228663#u32 ],
    Array.make 2#usize [ 342937346#u32, 440901543#u32 ],
    Array.make 2#usize [ 346773666#u32, 152947344#u32 ]
  ] (by rfl)

private def rate512LowChunk1 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 1343125376#u32, 1611076075#u32 ],
    Array.make 2#usize [ 1719915550#u32, 648525961#u32 ],
    Array.make 2#usize [ 1071628068#u32, 1255434837#u32 ],
    Array.make 2#usize [ 611826819#u32, 1330717448#u32 ],
    Array.make 2#usize [ 821570021#u32, 1145420705#u32 ],
    Array.make 2#usize [ 229177162#u32, 396528583#u32 ],
    Array.make 2#usize [ 1309999598#u32, 467334114#u32 ],
    Array.make 2#usize [ 1124013519#u32, 1413144457#u32 ],
    Array.make 2#usize [ 1408282706#u32, 600722738#u32 ],
    Array.make 2#usize [ 1817546580#u32, 1225707862#u32 ],
    Array.make 2#usize [ 511564144#u32, 1485902172#u32 ],
    Array.make 2#usize [ 1078945591#u32, 1940049095#u32 ],
    Array.make 2#usize [ 1423034495#u32, 1044300741#u32 ],
    Array.make 2#usize [ 1300505822#u32, 1483719533#u32 ],
    Array.make 2#usize [ 1752942601#u32, 1104368066#u32 ],
    Array.make 2#usize [ 1425723522#u32, 1087018637#u32 ]
  ] (by rfl)

private def rate512LowChunk2 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 302125271#u32, 1416107052#u32 ],
    Array.make 2#usize [ 459121708#u32, 1982887005#u32 ],
    Array.make 2#usize [ 301592792#u32, 2080568233#u32 ],
    Array.make 2#usize [ 443122237#u32, 696551100#u32 ],
    Array.make 2#usize [ 295990997#u32, 941692002#u32 ],
    Array.make 2#usize [ 1394038486#u32, 1247069276#u32 ],
    Array.make 2#usize [ 1519289632#u32, 554415477#u32 ],
    Array.make 2#usize [ 1102231607#u32, 609468827#u32 ],
    Array.make 2#usize [ 985045909#u32, 786285443#u32 ],
    Array.make 2#usize [ 1482323122#u32, 40945560#u32 ],
    Array.make 2#usize [ 1396387241#u32, 1636248379#u32 ],
    Array.make 2#usize [ 533049899#u32, 1473067927#u32 ],
    Array.make 2#usize [ 966434100#u32, 857433908#u32 ],
    Array.make 2#usize [ 559088903#u32, 1739101071#u32 ],
    Array.make 2#usize [ 796901153#u32, 679264882#u32 ],
    Array.make 2#usize [ 1968056945#u32, 1093869942#u32 ]
  ] (by rfl)

private def rate512LowChunk3 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 1338663259#u32, 1317602281#u32 ],
    Array.make 2#usize [ 799108626#u32, 281610748#u32 ],
    Array.make 2#usize [ 1993145094#u32, 1556913362#u32 ],
    Array.make 2#usize [ 114019110#u32, 1704020237#u32 ],
    Array.make 2#usize [ 492808319#u32, 1202170691#u32 ],
    Array.make 2#usize [ 1924931282#u32, 420158453#u32 ],
    Array.make 2#usize [ 833065953#u32, 160077459#u32 ],
    Array.make 2#usize [ 1512942634#u32, 1920073229#u32 ],
    Array.make 2#usize [ 1180239345#u32, 1380236185#u32 ],
    Array.make 2#usize [ 616220563#u32, 21676868#u32 ],
    Array.make 2#usize [ 1762390813#u32, 1601969049#u32 ],
    Array.make 2#usize [ 1797665716#u32, 1562938324#u32 ],
    Array.make 2#usize [ 712896677#u32, 412924820#u32 ],
    Array.make 2#usize [ 1194561107#u32, 2080170062#u32 ],
    Array.make 2#usize [ 1277755557#u32, 2036963937#u32 ],
    Array.make 2#usize [ 1187658047#u32, 1597100399#u32 ]
  ] (by rfl)

private def rate512LowChunk4 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 1881642285#u32, 2063950130#u32 ],
    Array.make 2#usize [ 1032118432#u32, 794826108#u32 ],
    Array.make 2#usize [ 956657888#u32, 291038160#u32 ],
    Array.make 2#usize [ 1957875930#u32, 296561667#u32 ],
    Array.make 2#usize [ 333497#u32, 1196617052#u32 ],
    Array.make 2#usize [ 1960759475#u32, 1372600266#u32 ],
    Array.make 2#usize [ 471311722#u32, 784900931#u32 ],
    Array.make 2#usize [ 1812847060#u32, 604811917#u32 ],
    Array.make 2#usize [ 1307842360#u32, 1890785536#u32 ],
    Array.make 2#usize [ 551783859#u32, 1315528016#u32 ],
    Array.make 2#usize [ 1572839832#u32, 1327270854#u32 ],
    Array.make 2#usize [ 2116389638#u32, 752539481#u32 ],
    Array.make 2#usize [ 868013894#u32, 1609896752#u32 ],
    Array.make 2#usize [ 1321537508#u32, 1042492503#u32 ],
    Array.make 2#usize [ 359306860#u32, 804380630#u32 ],
    Array.make 2#usize [ 2008431186#u32, 940311739#u32 ]
  ] (by rfl)

private def rate512LowChunk5 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 1456798835#u32, 1310838394#u32 ],
    Array.make 2#usize [ 1250242608#u32, 1515212572#u32 ],
    Array.make 2#usize [ 1743622189#u32, 1434497021#u32 ],
    Array.make 2#usize [ 1347334562#u32, 1707466059#u32 ],
    Array.make 2#usize [ 664296618#u32, 511286472#u32 ],
    Array.make 2#usize [ 1543289736#u32, 2072169015#u32 ],
    Array.make 2#usize [ 1447523228#u32, 863369865#u32 ],
    Array.make 2#usize [ 610182946#u32, 362571378#u32 ],
    Array.make 2#usize [ 962811294#u32, 1542119379#u32 ],
    Array.make 2#usize [ 2100755100#u32, 781855347#u32 ],
    Array.make 2#usize [ 1009483326#u32, 159986540#u32 ],
    Array.make 2#usize [ 2130500018#u32, 697494463#u32 ],
    Array.make 2#usize [ 6960782#u32, 674583491#u32 ],
    Array.make 2#usize [ 516159545#u32, 404337395#u32 ],
    Array.make 2#usize [ 1277257384#u32, 687295715#u32 ],
    Array.make 2#usize [ 501634918#u32, 1964085203#u32 ]
  ] (by rfl)

private def rate512LowChunk6 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 490854036#u32, 1299738414#u32 ],
    Array.make 2#usize [ 1775078444#u32, 117895462#u32 ],
    Array.make 2#usize [ 847375021#u32, 1683564466#u32 ],
    Array.make 2#usize [ 276270000#u32, 635791752#u32 ],
    Array.make 2#usize [ 1618314829#u32, 1579390512#u32 ],
    Array.make 2#usize [ 1576897924#u32, 2028163542#u32 ],
    Array.make 2#usize [ 681138556#u32, 1124705724#u32 ],
    Array.make 2#usize [ 247373802#u32, 1199896598#u32 ],
    Array.make 2#usize [ 138411218#u32, 355127523#u32 ],
    Array.make 2#usize [ 1676823327#u32, 1452493739#u32 ],
    Array.make 2#usize [ 1006454549#u32, 136324594#u32 ],
    Array.make 2#usize [ 489683669#u32, 1738843794#u32 ],
    Array.make 2#usize [ 827672611#u32, 312920181#u32 ],
    Array.make 2#usize [ 1474400930#u32, 1313634630#u32 ],
    Array.make 2#usize [ 1388297937#u32, 319639269#u32 ],
    Array.make 2#usize [ 1494170122#u32, 1749961689#u32 ]
  ] (by rfl)

private def rate512LowChunk7 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 1701675353#u32, 1983132973#u32 ],
    Array.make 2#usize [ 1278764565#u32, 841096995#u32 ],
    Array.make 2#usize [ 1182829080#u32, 1403391250#u32 ],
    Array.make 2#usize [ 784554145#u32, 618566048#u32 ],
    Array.make 2#usize [ 10399282#u32, 1552502053#u32 ],
    Array.make 2#usize [ 53864678#u32, 1944243352#u32 ],
    Array.make 2#usize [ 838794177#u32, 327403577#u32 ],
    Array.make 2#usize [ 1588926912#u32, 436478465#u32 ],
    Array.make 2#usize [ 313826601#u32, 1570162033#u32 ],
    Array.make 2#usize [ 825064211#u32, 854395739#u32 ],
    Array.make 2#usize [ 941931943#u32, 1990652193#u32 ],
    Array.make 2#usize [ 1048721901#u32, 873552759#u32 ],
    Array.make 2#usize [ 1816676196#u32, 292450356#u32 ],
    Array.make 2#usize [ 530505031#u32, 1579778597#u32 ],
    Array.make 2#usize [ 1535598549#u32, 1063355251#u32 ],
    Array.make 2#usize [ 1732548992#u32, 915469288#u32 ]
  ] (by rfl)

private def rate512LowChunk8 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 1914600967#u32, 506085132#u32 ],
    Array.make 2#usize [ 1909192314#u32, 1844835468#u32 ],
    Array.make 2#usize [ 1270585819#u32, 495661776#u32 ],
    Array.make 2#usize [ 648309269#u32, 1206339559#u32 ],
    Array.make 2#usize [ 1957109964#u32, 1326400046#u32 ],
    Array.make 2#usize [ 1705932716#u32, 1727581645#u32 ],
    Array.make 2#usize [ 168264802#u32, 516171306#u32 ],
    Array.make 2#usize [ 541611057#u32, 162264327#u32 ],
    Array.make 2#usize [ 221399553#u32, 587879569#u32 ],
    Array.make 2#usize [ 883092198#u32, 272785874#u32 ],
    Array.make 2#usize [ 619580768#u32, 1148852869#u32 ],
    Array.make 2#usize [ 17110996#u32, 1021904928#u32 ],
    Array.make 2#usize [ 1105018290#u32, 1957296251#u32 ],
    Array.make 2#usize [ 1433871289#u32, 2139981508#u32 ],
    Array.make 2#usize [ 787040929#u32, 1634518590#u32 ],
    Array.make 2#usize [ 208613625#u32, 824621910#u32 ]
  ] (by rfl)

private def rate512LowChunk9 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 219435866#u32, 377252687#u32 ],
    Array.make 2#usize [ 1490537147#u32, 1891083626#u32 ],
    Array.make 2#usize [ 650335755#u32, 1992007170#u32 ],
    Array.make 2#usize [ 611900083#u32, 1265134679#u32 ],
    Array.make 2#usize [ 2011166020#u32, 982819427#u32 ],
    Array.make 2#usize [ 1863704483#u32, 1043572570#u32 ],
    Array.make 2#usize [ 1645857755#u32, 1384113798#u32 ],
    Array.make 2#usize [ 1995809018#u32, 1145122471#u32 ],
    Array.make 2#usize [ 1890954877#u32, 1438477731#u32 ],
    Array.make 2#usize [ 582253716#u32, 1019166718#u32 ],
    Array.make 2#usize [ 198106855#u32, 1659832589#u32 ],
    Array.make 2#usize [ 49867993#u32, 2068465849#u32 ],
    Array.make 2#usize [ 1496164995#u32, 1024141368#u32 ],
    Array.make 2#usize [ 767352283#u32, 1837817220#u32 ],
    Array.make 2#usize [ 987305072#u32, 1984816879#u32 ],
    Array.make 2#usize [ 19263154#u32, 1877804976#u32 ]
  ] (by rfl)

private def rate512LowChunk10 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 39796372#u32, 1795587531#u32 ],
    Array.make 2#usize [ 1365401309#u32, 2005940350#u32 ],
    Array.make 2#usize [ 1602771614#u32, 910634326#u32 ],
    Array.make 2#usize [ 723229594#u32, 630298203#u32 ],
    Array.make 2#usize [ 816774718#u32, 838521420#u32 ],
    Array.make 2#usize [ 1408711532#u32, 577331418#u32 ],
    Array.make 2#usize [ 950234314#u32, 463963186#u32 ],
    Array.make 2#usize [ 1488380703#u32, 1022280304#u32 ],
    Array.make 2#usize [ 1781484387#u32, 1946973940#u32 ],
    Array.make 2#usize [ 308622607#u32, 582345987#u32 ],
    Array.make 2#usize [ 1887476042#u32, 1775028025#u32 ],
    Array.make 2#usize [ 246287241#u32, 435789778#u32 ],
    Array.make 2#usize [ 916111591#u32, 957769475#u32 ],
    Array.make 2#usize [ 2082859020#u32, 1877859929#u32 ],
    Array.make 2#usize [ 2038832625#u32, 988975593#u32 ],
    Array.make 2#usize [ 1979423951#u32, 1333969356#u32 ]
  ] (by rfl)

private def rate512LowChunk11 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 1668817195#u32, 843962082#u32 ],
    Array.make 2#usize [ 1887780950#u32, 452204806#u32 ],
    Array.make 2#usize [ 1439914440#u32, 657772724#u32 ],
    Array.make 2#usize [ 1736704193#u32, 1578626329#u32 ],
    Array.make 2#usize [ 1916994672#u32, 239421051#u32 ],
    Array.make 2#usize [ 1035073006#u32, 165878859#u32 ],
    Array.make 2#usize [ 1460750656#u32, 108875396#u32 ],
    Array.make 2#usize [ 512219769#u32, 1134864512#u32 ],
    Array.make 2#usize [ 1838848635#u32, 622257382#u32 ],
    Array.make 2#usize [ 1522966898#u32, 2128973937#u32 ],
    Array.make 2#usize [ 1388359144#u32, 422592399#u32 ],
    Array.make 2#usize [ 1680682578#u32, 1114934559#u32 ],
    Array.make 2#usize [ 722248920#u32, 1611527851#u32 ],
    Array.make 2#usize [ 1025324822#u32, 965918188#u32 ],
    Array.make 2#usize [ 1644340484#u32, 713999276#u32 ],
    Array.make 2#usize [ 69199171#u32, 1459013896#u32 ]
  ] (by rfl)

private def rate512LowChunk12 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 1966255236#u32, 1551328122#u32 ],
    Array.make 2#usize [ 504581547#u32, 1300814674#u32 ],
    Array.make 2#usize [ 1762312790#u32, 776071643#u32 ],
    Array.make 2#usize [ 1144265652#u32, 1837334851#u32 ],
    Array.make 2#usize [ 709902178#u32, 2110281785#u32 ],
    Array.make 2#usize [ 1729842475#u32, 593664546#u32 ],
    Array.make 2#usize [ 1828981294#u32, 1162512737#u32 ],
    Array.make 2#usize [ 1625844944#u32, 2099106256#u32 ],
    Array.make 2#usize [ 1835813766#u32, 859677911#u32 ],
    Array.make 2#usize [ 1517879088#u32, 353463264#u32 ],
    Array.make 2#usize [ 1506232713#u32, 157397350#u32 ],
    Array.make 2#usize [ 215394231#u32, 1580783182#u32 ],
    Array.make 2#usize [ 2108052949#u32, 1679811569#u32 ],
    Array.make 2#usize [ 1354751622#u32, 1851124520#u32 ],
    Array.make 2#usize [ 745057264#u32, 1732215737#u32 ],
    Array.make 2#usize [ 2042449047#u32, 871491139#u32 ]
  ] (by rfl)

private def rate512LowChunk13 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 9727703#u32, 1273818536#u32 ],
    Array.make 2#usize [ 728179275#u32, 1749465481#u32 ],
    Array.make 2#usize [ 851434018#u32, 692926311#u32 ],
    Array.make 2#usize [ 1777804945#u32, 1519358968#u32 ],
    Array.make 2#usize [ 166487160#u32, 1268884951#u32 ],
    Array.make 2#usize [ 508262895#u32, 173851794#u32 ],
    Array.make 2#usize [ 1379225081#u32, 1459079308#u32 ],
    Array.make 2#usize [ 979569419#u32, 1762318406#u32 ],
    Array.make 2#usize [ 568333187#u32, 92958549#u32 ],
    Array.make 2#usize [ 554457363#u32, 855073356#u32 ],
    Array.make 2#usize [ 387211603#u32, 1625814783#u32 ],
    Array.make 2#usize [ 2063530488#u32, 1481183708#u32 ],
    Array.make 2#usize [ 1803431760#u32, 1738044928#u32 ],
    Array.make 2#usize [ 219280493#u32, 403222989#u32 ],
    Array.make 2#usize [ 1915589214#u32, 1570116309#u32 ],
    Array.make 2#usize [ 1051459399#u32, 57587034#u32 ]
  ] (by rfl)

private def rate512LowChunk14 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 850894900#u32, 182596059#u32 ],
    Array.make 2#usize [ 354641152#u32, 889740466#u32 ],
    Array.make 2#usize [ 394228737#u32, 57909558#u32 ],
    Array.make 2#usize [ 1167064397#u32, 616906471#u32 ],
    Array.make 2#usize [ 1228438909#u32, 1220198410#u32 ],
    Array.make 2#usize [ 822208803#u32, 1117959092#u32 ],
    Array.make 2#usize [ 1117438582#u32, 550440180#u32 ],
    Array.make 2#usize [ 1681380816#u32, 1401572967#u32 ],
    Array.make 2#usize [ 781777559#u32, 2008530061#u32 ],
    Array.make 2#usize [ 881367132#u32, 780354091#u32 ],
    Array.make 2#usize [ 818852619#u32, 1485120666#u32 ],
    Array.make 2#usize [ 143743858#u32, 1141336085#u32 ],
    Array.make 2#usize [ 537367934#u32, 2108230403#u32 ],
    Array.make 2#usize [ 892736918#u32, 727189655#u32 ],
    Array.make 2#usize [ 620428519#u32, 2098213995#u32 ],
    Array.make 2#usize [ 370380811#u32, 385474991#u32 ]
  ] (by rfl)

private def rate512LowChunk15 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 511685053#u32, 1201607207#u32 ],
    Array.make 2#usize [ 1449072755#u32, 1201092171#u32 ],
    Array.make 2#usize [ 2088706129#u32, 1171915492#u32 ],
    Array.make 2#usize [ 57468962#u32, 1154563812#u32 ],
    Array.make 2#usize [ 1962428849#u32, 1800159415#u32 ],
    Array.make 2#usize [ 972466316#u32, 716990261#u32 ],
    Array.make 2#usize [ 286626231#u32, 905945789#u32 ],
    Array.make 2#usize [ 1021874147#u32, 1123482147#u32 ],
    Array.make 2#usize [ 1816759166#u32, 500919401#u32 ],
    Array.make 2#usize [ 1331181958#u32, 787552408#u32 ],
    Array.make 2#usize [ 1012262651#u32, 412102140#u32 ],
    Array.make 2#usize [ 164104256#u32, 364961688#u32 ],
    Array.make 2#usize [ 1591253798#u32, 2127971120#u32 ],
    Array.make 2#usize [ 1488347483#u32, 1042908511#u32 ],
    Array.make 2#usize [ 792328457#u32, 505875917#u32 ],
    Array.make 2#usize [ 1856645042#u32, 307723169#u32 ]
  ] (by rfl)

/-- Exact normalized declaration of the Aeneas literal table. -/
@[global_simps, rust_const "aspis_core::circle_fri::RATE512_CIRCLE_LOW8_WINDOW"]
def aspis_core.circle_fri.RATE512_CIRCLE_LOW8_WINDOW
  : Array (Array Std.U32 2#usize) 256#usize :=
  Array.make 256#usize (
    rate512LowChunk0.val ++
    rate512LowChunk1.val ++
    rate512LowChunk2.val ++
    rate512LowChunk3.val ++
    rate512LowChunk4.val ++
    rate512LowChunk5.val ++
    rate512LowChunk6.val ++
    rate512LowChunk7.val ++
    rate512LowChunk8.val ++
    rate512LowChunk9.val ++
    rate512LowChunk10.val ++
    rate512LowChunk11.val ++
    rate512LowChunk12.val ++
    rate512LowChunk13.val ++
    rate512LowChunk14.val ++
    rate512LowChunk15.val
  ) (by
    simp only [List.length_append, Array.length_eq]
    norm_num)

end V5FriCoordinateAdapter

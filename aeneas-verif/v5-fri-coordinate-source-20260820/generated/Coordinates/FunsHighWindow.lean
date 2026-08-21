-- Deterministic low-memory normalization of the recorded Aeneas output.
import Coordinates.FunsField
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace V5FriCoordinateAdapter

private def rate512HighChunk0 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 1#u32, 0#u32 ],
    Array.make 2#usize [ 1434706457#u32, 1835793811#u32 ],
    Array.make 2#usize [ 13610297#u32, 1064696601#u32 ],
    Array.make 2#usize [ 609228044#u32, 827893883#u32 ],
    Array.make 2#usize [ 785043271#u32, 1260750973#u32 ],
    Array.make 2#usize [ 477465227#u32, 1464821634#u32 ],
    Array.make 2#usize [ 655387905#u32, 752064346#u32 ],
    Array.make 2#usize [ 1919800332#u32, 1732277387#u32 ],
    Array.make 2#usize [ 838195206#u32, 1774253895#u32 ],
    Array.make 2#usize [ 904293309#u32, 989947986#u32 ],
    Array.make 2#usize [ 951582730#u32, 528066207#u32 ],
    Array.make 2#usize [ 941653828#u32, 2075806777#u32 ],
    Array.make 2#usize [ 1357626641#u32, 2066105389#u32 ],
    Array.make 2#usize [ 88230288#u32, 1857622143#u32 ],
    Array.make 2#usize [ 810533124#u32, 839591040#u32 ],
    Array.make 2#usize [ 767685501#u32, 566492308#u32 ]
  ] (by rfl)

private def rate512HighChunk1 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 579625837#u32, 1690787918#u32 ],
    Array.make 2#usize [ 1122865474#u32, 1974665904#u32 ],
    Array.make 2#usize [ 994833177#u32, 1716662235#u32 ],
    Array.make 2#usize [ 535895406#u32, 330498905#u32 ],
    Array.make 2#usize [ 251924953#u32, 636875771#u32 ],
    Array.make 2#usize [ 1887689736#u32, 750301505#u32 ],
    Array.make 2#usize [ 1371669334#u32, 2103108137#u32 ],
    Array.make 2#usize [ 143051046#u32, 499966977#u32 ],
    Array.make 2#usize [ 2013328190#u32, 1108537731#u32 ],
    Array.make 2#usize [ 1391377897#u32, 1051518090#u32 ],
    Array.make 2#usize [ 1194689061#u32, 472916039#u32 ],
    Array.make 2#usize [ 844222273#u32, 269141577#u32 ],
    Array.make 2#usize [ 141956360#u32, 170449934#u32 ],
    Array.make 2#usize [ 1398714324#u32, 543170620#u32 ],
    Array.make 2#usize [ 416817213#u32, 36815260#u32 ],
    Array.make 2#usize [ 1097043213#u32, 1741011703#u32 ]
  ] (by rfl)

private def rate512HighChunk2 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 1179735656#u32, 1241207368#u32 ],
    Array.make 2#usize [ 1936974060#u32, 824292393#u32 ],
    Array.make 2#usize [ 1664948088#u32, 776881039#u32 ],
    Array.make 2#usize [ 89405266#u32, 1638487879#u32 ],
    Array.make 2#usize [ 1911378744#u32, 1577470940#u32 ],
    Array.make 2#usize [ 897507430#u32, 1380714367#u32 ],
    Array.make 2#usize [ 820860779#u32, 1644164930#u32 ],
    Array.make 2#usize [ 773269826#u32, 650162669#u32 ],
    Array.make 2#usize [ 2140339328#u32, 404685994#u32 ],
    Array.make 2#usize [ 1474708134#u32, 499205677#u32 ],
    Array.make 2#usize [ 543822408#u32, 1398285837#u32 ],
    Array.make 2#usize [ 1981291345#u32, 1330638276#u32 ],
    Array.make 2#usize [ 1563928157#u32, 849605071#u32 ],
    Array.make 2#usize [ 37656326#u32, 1059774538#u32 ],
    Array.make 2#usize [ 617361773#u32, 1541513586#u32 ],
    Array.make 2#usize [ 1570802141#u32, 2103767252#u32 ]
  ] (by rfl)

private def rate512HighChunk3 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 1866536500#u32, 1133522282#u32 ],
    Array.make 2#usize [ 506023947#u32, 2109066236#u32 ],
    Array.make 2#usize [ 1202912605#u32, 167450866#u32 ],
    Array.make 2#usize [ 1495259209#u32, 375548322#u32 ],
    Array.make 2#usize [ 640817200#u32, 1702126977#u32 ],
    Array.make 2#usize [ 1669783215#u32, 1361499402#u32 ],
    Array.make 2#usize [ 224958826#u32, 485600145#u32 ],
    Array.make 2#usize [ 1647103293#u32, 269176336#u32 ],
    Array.make 2#usize [ 1263730590#u32, 350742286#u32 ],
    Array.make 2#usize [ 1270188826#u32, 1501011474#u32 ],
    Array.make 2#usize [ 226571076#u32, 1233386319#u32 ],
    Array.make 2#usize [ 665711726#u32, 354138878#u32 ],
    Array.make 2#usize [ 1067683608#u32, 1949783546#u32 ],
    Array.make 2#usize [ 1182972905#u32, 1856336347#u32 ],
    Array.make 2#usize [ 1113159341#u32, 1293504395#u32 ],
    Array.make 2#usize [ 1412788483#u32, 1845756189#u32 ]
  ] (by rfl)

private def rate512HighChunk4 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 590768354#u32, 978592373#u32 ],
    Array.make 2#usize [ 938665521#u32, 1190084038#u32 ],
    Array.make 2#usize [ 328267072#u32, 484667533#u32 ],
    Array.make 2#usize [ 621205469#u32, 1763527383#u32 ],
    Array.make 2#usize [ 479120236#u32, 225856549#u32 ],
    Array.make 2#usize [ 481825426#u32, 675922742#u32 ],
    Array.make 2#usize [ 469386237#u32, 1756768506#u32 ],
    Array.make 2#usize [ 1988358717#u32, 1802066642#u32 ],
    Array.make 2#usize [ 206059115#u32, 212443077#u32 ],
    Array.make 2#usize [ 1066848801#u32, 1918438855#u32 ],
    Array.make 2#usize [ 1995206774#u32, 1568822693#u32 ],
    Array.make 2#usize [ 80908896#u32, 639814482#u32 ],
    Array.make 2#usize [ 1498890429#u32, 1093071961#u32 ],
    Array.make 2#usize [ 928236221#u32, 1594495101#u32 ],
    Array.make 2#usize [ 1916124599#u32, 1960324689#u32 ],
    Array.make 2#usize [ 1107763315#u32, 1912333344#u32 ]
  ] (by rfl)

private def rate512HighChunk5 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 1952787376#u32, 1580223790#u32 ],
    Array.make 2#usize [ 1283743803#u32, 1118217466#u32 ],
    Array.make 2#usize [ 1207781610#u32, 378535762#u32 ],
    Array.make 2#usize [ 1532871443#u32, 1146601110#u32 ],
    Array.make 2#usize [ 1514613395#u32, 870936612#u32 ],
    Array.make 2#usize [ 382117576#u32, 2071247511#u32 ],
    Array.make 2#usize [ 1981631761#u32, 1674906685#u32 ],
    Array.make 2#usize [ 2117909028#u32, 999688792#u32 ],
    Array.make 2#usize [ 2079025011#u32, 2137679949#u32 ],
    Array.make 2#usize [ 1001031510#u32, 308816680#u32 ],
    Array.make 2#usize [ 806637293#u32, 1487465746#u32 ],
    Array.make 2#usize [ 1819501362#u32, 202176565#u32 ],
    Array.make 2#usize [ 61740007#u32, 812986380#u32 ],
    Array.make 2#usize [ 1879385002#u32, 951261442#u32 ],
    Array.make 2#usize [ 1777644782#u32, 1383853684#u32 ],
    Array.make 2#usize [ 375505490#u32, 896850794#u32 ]
  ] (by rfl)

private def rate512HighChunk6 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 34602070#u32, 732393395#u32 ],
    Array.make 2#usize [ 1762318749#u32, 1543329494#u32 ],
    Array.make 2#usize [ 793810598#u32, 252929270#u32 ],
    Array.make 2#usize [ 1204564734#u32, 402099265#u32 ],
    Array.make 2#usize [ 477953613#u32, 125103457#u32 ],
    Array.make 2#usize [ 75244103#u32, 893042083#u32 ],
    Array.make 2#usize [ 820980485#u32, 784964762#u32 ],
    Array.make 2#usize [ 1823446081#u32, 784723556#u32 ],
    Array.make 2#usize [ 14530030#u32, 228509164#u32 ],
    Array.make 2#usize [ 1922198201#u32, 694966700#u32 ],
    Array.make 2#usize [ 278287463#u32, 222277859#u32 ],
    Array.make 2#usize [ 358859723#u32, 962257603#u32 ],
    Array.make 2#usize [ 250538254#u32, 2098580229#u32 ],
    Array.make 2#usize [ 218795070#u32, 1872514139#u32 ],
    Array.make 2#usize [ 1637799161#u32, 1854234209#u32 ],
    Array.make 2#usize [ 1195953466#u32, 906381151#u32 ]
  ] (by rfl)

private def rate512HighChunk7 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 26164677#u32, 505542828#u32 ],
    Array.make 2#usize [ 2071235581#u32, 133640314#u32 ],
    Array.make 2#usize [ 1312947780#u32, 222141861#u32 ],
    Array.make 2#usize [ 478680713#u32, 1391987716#u32 ],
    Array.make 2#usize [ 1014093253#u32, 2137011181#u32 ],
    Array.make 2#usize [ 428162150#u32, 440454181#u32 ],
    Array.make 2#usize [ 750098750#u32, 749414350#u32 ],
    Array.make 2#usize [ 28670693#u32, 368578328#u32 ],
    Array.make 2#usize [ 1885292596#u32, 408478793#u32 ],
    Array.make 2#usize [ 801147693#u32, 1538500177#u32 ],
    Array.make 2#usize [ 1792244284#u32, 2110925851#u32 ],
    Array.make 2#usize [ 293881126#u32, 116984891#u32 ],
    Array.make 2#usize [ 593814437#u32, 1411221007#u32 ],
    Array.make 2#usize [ 910717687#u32, 557591127#u32 ],
    Array.make 2#usize [ 1494204761#u32, 735494074#u32 ],
    Array.make 2#usize [ 1916987415#u32, 271138064#u32 ]
  ] (by rfl)

private def rate512HighChunk8 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 32768#u32, 2147450879#u32 ],
    Array.make 2#usize [ 1876345583#u32, 230496232#u32 ],
    Array.make 2#usize [ 1411989573#u32, 653278886#u32 ],
    Array.make 2#usize [ 1589892520#u32, 1236765960#u32 ],
    Array.make 2#usize [ 736262640#u32, 1553669210#u32 ],
    Array.make 2#usize [ 2030498756#u32, 1853602521#u32 ],
    Array.make 2#usize [ 36557796#u32, 355239363#u32 ],
    Array.make 2#usize [ 608983470#u32, 1346335954#u32 ],
    Array.make 2#usize [ 1739004854#u32, 262191051#u32 ],
    Array.make 2#usize [ 1778905319#u32, 2118812954#u32 ],
    Array.make 2#usize [ 1398069297#u32, 1397384897#u32 ],
    Array.make 2#usize [ 1707029466#u32, 1719321497#u32 ],
    Array.make 2#usize [ 10472466#u32, 1133390394#u32 ],
    Array.make 2#usize [ 755495931#u32, 1668802934#u32 ],
    Array.make 2#usize [ 1925341786#u32, 834535867#u32 ],
    Array.make 2#usize [ 2013843333#u32, 76248066#u32 ]
  ] (by rfl)

private def rate512HighChunk9 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 1641940819#u32, 2121318970#u32 ],
    Array.make 2#usize [ 1241102496#u32, 951530181#u32 ],
    Array.make 2#usize [ 293249438#u32, 509684486#u32 ],
    Array.make 2#usize [ 274969508#u32, 1928688577#u32 ],
    Array.make 2#usize [ 48903418#u32, 1896945393#u32 ],
    Array.make 2#usize [ 1185226044#u32, 1788623924#u32 ],
    Array.make 2#usize [ 1925205788#u32, 1869196184#u32 ],
    Array.make 2#usize [ 1452516947#u32, 225285446#u32 ],
    Array.make 2#usize [ 1918974483#u32, 2132953617#u32 ],
    Array.make 2#usize [ 1362760091#u32, 324037566#u32 ],
    Array.make 2#usize [ 1362518885#u32, 1326503162#u32 ],
    Array.make 2#usize [ 1254441564#u32, 2072239544#u32 ],
    Array.make 2#usize [ 2022380190#u32, 1669530034#u32 ],
    Array.make 2#usize [ 1745384382#u32, 942918913#u32 ],
    Array.make 2#usize [ 1894554377#u32, 1353673049#u32 ],
    Array.make 2#usize [ 604154153#u32, 385164898#u32 ]
  ] (by rfl)

private def rate512HighChunk10 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 1415090252#u32, 2112881577#u32 ],
    Array.make 2#usize [ 1250632853#u32, 1771978157#u32 ],
    Array.make 2#usize [ 763629963#u32, 369838865#u32 ],
    Array.make 2#usize [ 1196222205#u32, 268098645#u32 ],
    Array.make 2#usize [ 1334497267#u32, 2085743640#u32 ],
    Array.make 2#usize [ 1945307082#u32, 327982285#u32 ],
    Array.make 2#usize [ 660017901#u32, 1340846354#u32 ],
    Array.make 2#usize [ 1838666967#u32, 1146452137#u32 ],
    Array.make 2#usize [ 9803698#u32, 68458636#u32 ],
    Array.make 2#usize [ 1147794855#u32, 29574619#u32 ],
    Array.make 2#usize [ 472576962#u32, 165851886#u32 ],
    Array.make 2#usize [ 76236136#u32, 1765366071#u32 ],
    Array.make 2#usize [ 1276547035#u32, 632870252#u32 ],
    Array.make 2#usize [ 1000882537#u32, 614612204#u32 ],
    Array.make 2#usize [ 1768947885#u32, 939702037#u32 ],
    Array.make 2#usize [ 1029266181#u32, 863739844#u32 ]
  ] (by rfl)

private def rate512HighChunk11 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 567259857#u32, 194696271#u32 ],
    Array.make 2#usize [ 235150303#u32, 1039720332#u32 ],
    Array.make 2#usize [ 187158958#u32, 231359048#u32 ],
    Array.make 2#usize [ 552988546#u32, 1219247426#u32 ],
    Array.make 2#usize [ 1054411686#u32, 648593218#u32 ],
    Array.make 2#usize [ 1507669165#u32, 2066574751#u32 ],
    Array.make 2#usize [ 578660954#u32, 152276873#u32 ],
    Array.make 2#usize [ 229044792#u32, 1080634846#u32 ],
    Array.make 2#usize [ 1935040570#u32, 1941424532#u32 ],
    Array.make 2#usize [ 345417005#u32, 159124930#u32 ],
    Array.make 2#usize [ 390715141#u32, 1678097410#u32 ],
    Array.make 2#usize [ 1471560905#u32, 1665658221#u32 ],
    Array.make 2#usize [ 1921627098#u32, 1668363411#u32 ],
    Array.make 2#usize [ 383956264#u32, 1526278178#u32 ],
    Array.make 2#usize [ 1662816114#u32, 1819216575#u32 ],
    Array.make 2#usize [ 957399609#u32, 1208818126#u32 ]
  ] (by rfl)

private def rate512HighChunk12 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 1168891274#u32, 1556715293#u32 ],
    Array.make 2#usize [ 301727458#u32, 734695164#u32 ],
    Array.make 2#usize [ 853979252#u32, 1034324306#u32 ],
    Array.make 2#usize [ 291147300#u32, 964510742#u32 ],
    Array.make 2#usize [ 197700101#u32, 1079800039#u32 ],
    Array.make 2#usize [ 1793344769#u32, 1481771921#u32 ],
    Array.make 2#usize [ 914097328#u32, 1920912571#u32 ],
    Array.make 2#usize [ 646472173#u32, 877294821#u32 ],
    Array.make 2#usize [ 1796741361#u32, 883753057#u32 ],
    Array.make 2#usize [ 1878307311#u32, 500380354#u32 ],
    Array.make 2#usize [ 1661883502#u32, 1922524821#u32 ],
    Array.make 2#usize [ 785984245#u32, 477700432#u32 ],
    Array.make 2#usize [ 445356670#u32, 1506666447#u32 ],
    Array.make 2#usize [ 1771935325#u32, 652224438#u32 ],
    Array.make 2#usize [ 1980032781#u32, 944571042#u32 ],
    Array.make 2#usize [ 38417411#u32, 1641459700#u32 ]
  ] (by rfl)

private def rate512HighChunk13 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 1013961365#u32, 280947147#u32 ],
    Array.make 2#usize [ 43716395#u32, 576681506#u32 ],
    Array.make 2#usize [ 605970061#u32, 1530121874#u32 ],
    Array.make 2#usize [ 1087709109#u32, 2109827321#u32 ],
    Array.make 2#usize [ 1297878576#u32, 583555490#u32 ],
    Array.make 2#usize [ 816845371#u32, 166192302#u32 ],
    Array.make 2#usize [ 749197810#u32, 1603661239#u32 ],
    Array.make 2#usize [ 1648277970#u32, 672775513#u32 ],
    Array.make 2#usize [ 1742797653#u32, 7144319#u32 ],
    Array.make 2#usize [ 1497320978#u32, 1374213821#u32 ],
    Array.make 2#usize [ 503318717#u32, 1326622868#u32 ],
    Array.make 2#usize [ 766769280#u32, 1249976217#u32 ],
    Array.make 2#usize [ 570012707#u32, 236104903#u32 ],
    Array.make 2#usize [ 508995768#u32, 2058078381#u32 ],
    Array.make 2#usize [ 1370602608#u32, 482535559#u32 ],
    Array.make 2#usize [ 1323191254#u32, 210509587#u32 ]
  ] (by rfl)

private def rate512HighChunk14 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 906276279#u32, 967747991#u32 ],
    Array.make 2#usize [ 406471944#u32, 1050440434#u32 ],
    Array.make 2#usize [ 2110668387#u32, 1730666434#u32 ],
    Array.make 2#usize [ 1604313027#u32, 748769323#u32 ],
    Array.make 2#usize [ 1977033713#u32, 2005527287#u32 ],
    Array.make 2#usize [ 1878342070#u32, 1303261374#u32 ],
    Array.make 2#usize [ 1674567608#u32, 952794586#u32 ],
    Array.make 2#usize [ 1095965557#u32, 756105750#u32 ],
    Array.make 2#usize [ 1038945916#u32, 134155457#u32 ],
    Array.make 2#usize [ 1647516670#u32, 2004432601#u32 ],
    Array.make 2#usize [ 44375510#u32, 775814313#u32 ],
    Array.make 2#usize [ 1397182142#u32, 259793911#u32 ],
    Array.make 2#usize [ 1510607876#u32, 1895558694#u32 ],
    Array.make 2#usize [ 1816984742#u32, 1611588241#u32 ],
    Array.make 2#usize [ 430821412#u32, 1152650470#u32 ],
    Array.make 2#usize [ 172817743#u32, 1024618173#u32 ]
  ] (by rfl)

private def rate512HighChunk15 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 456695729#u32, 1567857810#u32 ],
    Array.make 2#usize [ 1580991339#u32, 1379798146#u32 ],
    Array.make 2#usize [ 1307892607#u32, 1336950523#u32 ],
    Array.make 2#usize [ 289861504#u32, 2059253359#u32 ],
    Array.make 2#usize [ 81378258#u32, 789857006#u32 ],
    Array.make 2#usize [ 71676870#u32, 1205829819#u32 ],
    Array.make 2#usize [ 1619417440#u32, 1195900917#u32 ],
    Array.make 2#usize [ 1157535661#u32, 1243190338#u32 ],
    Array.make 2#usize [ 373229752#u32, 1309288441#u32 ],
    Array.make 2#usize [ 415206260#u32, 227683315#u32 ],
    Array.make 2#usize [ 1395419301#u32, 1492095742#u32 ],
    Array.make 2#usize [ 682662013#u32, 1670018420#u32 ],
    Array.make 2#usize [ 886732674#u32, 1362440376#u32 ],
    Array.make 2#usize [ 1319589764#u32, 1538255603#u32 ],
    Array.make 2#usize [ 1082787046#u32, 2133873350#u32 ],
    Array.make 2#usize [ 311689836#u32, 712777190#u32 ]
  ] (by rfl)

private def rate512HighChunk16 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 0#u32, 2147483646#u32 ],
    Array.make 2#usize [ 1835793811#u32, 712777190#u32 ],
    Array.make 2#usize [ 1064696601#u32, 2133873350#u32 ],
    Array.make 2#usize [ 827893883#u32, 1538255603#u32 ],
    Array.make 2#usize [ 1260750973#u32, 1362440376#u32 ],
    Array.make 2#usize [ 1464821634#u32, 1670018420#u32 ],
    Array.make 2#usize [ 752064346#u32, 1492095742#u32 ],
    Array.make 2#usize [ 1732277387#u32, 227683315#u32 ],
    Array.make 2#usize [ 1774253895#u32, 1309288441#u32 ],
    Array.make 2#usize [ 989947986#u32, 1243190338#u32 ],
    Array.make 2#usize [ 528066207#u32, 1195900917#u32 ],
    Array.make 2#usize [ 2075806777#u32, 1205829819#u32 ],
    Array.make 2#usize [ 2066105389#u32, 789857006#u32 ],
    Array.make 2#usize [ 1857622143#u32, 2059253359#u32 ],
    Array.make 2#usize [ 839591040#u32, 1336950523#u32 ],
    Array.make 2#usize [ 566492308#u32, 1379798146#u32 ]
  ] (by rfl)

private def rate512HighChunk17 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 1690787918#u32, 1567857810#u32 ],
    Array.make 2#usize [ 1974665904#u32, 1024618173#u32 ],
    Array.make 2#usize [ 1716662235#u32, 1152650470#u32 ],
    Array.make 2#usize [ 330498905#u32, 1611588241#u32 ],
    Array.make 2#usize [ 636875771#u32, 1895558694#u32 ],
    Array.make 2#usize [ 750301505#u32, 259793911#u32 ],
    Array.make 2#usize [ 2103108137#u32, 775814313#u32 ],
    Array.make 2#usize [ 499966977#u32, 2004432601#u32 ],
    Array.make 2#usize [ 1108537731#u32, 134155457#u32 ],
    Array.make 2#usize [ 1051518090#u32, 756105750#u32 ],
    Array.make 2#usize [ 472916039#u32, 952794586#u32 ],
    Array.make 2#usize [ 269141577#u32, 1303261374#u32 ],
    Array.make 2#usize [ 170449934#u32, 2005527287#u32 ],
    Array.make 2#usize [ 543170620#u32, 748769323#u32 ],
    Array.make 2#usize [ 36815260#u32, 1730666434#u32 ],
    Array.make 2#usize [ 1741011703#u32, 1050440434#u32 ]
  ] (by rfl)

private def rate512HighChunk18 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 1241207368#u32, 967747991#u32 ],
    Array.make 2#usize [ 824292393#u32, 210509587#u32 ],
    Array.make 2#usize [ 776881039#u32, 482535559#u32 ],
    Array.make 2#usize [ 1638487879#u32, 2058078381#u32 ],
    Array.make 2#usize [ 1577470940#u32, 236104903#u32 ],
    Array.make 2#usize [ 1380714367#u32, 1249976217#u32 ],
    Array.make 2#usize [ 1644164930#u32, 1326622868#u32 ],
    Array.make 2#usize [ 650162669#u32, 1374213821#u32 ],
    Array.make 2#usize [ 404685994#u32, 7144319#u32 ],
    Array.make 2#usize [ 499205677#u32, 672775513#u32 ],
    Array.make 2#usize [ 1398285837#u32, 1603661239#u32 ],
    Array.make 2#usize [ 1330638276#u32, 166192302#u32 ],
    Array.make 2#usize [ 849605071#u32, 583555490#u32 ],
    Array.make 2#usize [ 1059774538#u32, 2109827321#u32 ],
    Array.make 2#usize [ 1541513586#u32, 1530121874#u32 ],
    Array.make 2#usize [ 2103767252#u32, 576681506#u32 ]
  ] (by rfl)

private def rate512HighChunk19 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 1133522282#u32, 280947147#u32 ],
    Array.make 2#usize [ 2109066236#u32, 1641459700#u32 ],
    Array.make 2#usize [ 167450866#u32, 944571042#u32 ],
    Array.make 2#usize [ 375548322#u32, 652224438#u32 ],
    Array.make 2#usize [ 1702126977#u32, 1506666447#u32 ],
    Array.make 2#usize [ 1361499402#u32, 477700432#u32 ],
    Array.make 2#usize [ 485600145#u32, 1922524821#u32 ],
    Array.make 2#usize [ 269176336#u32, 500380354#u32 ],
    Array.make 2#usize [ 350742286#u32, 883753057#u32 ],
    Array.make 2#usize [ 1501011474#u32, 877294821#u32 ],
    Array.make 2#usize [ 1233386319#u32, 1920912571#u32 ],
    Array.make 2#usize [ 354138878#u32, 1481771921#u32 ],
    Array.make 2#usize [ 1949783546#u32, 1079800039#u32 ],
    Array.make 2#usize [ 1856336347#u32, 964510742#u32 ],
    Array.make 2#usize [ 1293504395#u32, 1034324306#u32 ],
    Array.make 2#usize [ 1845756189#u32, 734695164#u32 ]
  ] (by rfl)

private def rate512HighChunk20 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 978592373#u32, 1556715293#u32 ],
    Array.make 2#usize [ 1190084038#u32, 1208818126#u32 ],
    Array.make 2#usize [ 484667533#u32, 1819216575#u32 ],
    Array.make 2#usize [ 1763527383#u32, 1526278178#u32 ],
    Array.make 2#usize [ 225856549#u32, 1668363411#u32 ],
    Array.make 2#usize [ 675922742#u32, 1665658221#u32 ],
    Array.make 2#usize [ 1756768506#u32, 1678097410#u32 ],
    Array.make 2#usize [ 1802066642#u32, 159124930#u32 ],
    Array.make 2#usize [ 212443077#u32, 1941424532#u32 ],
    Array.make 2#usize [ 1918438855#u32, 1080634846#u32 ],
    Array.make 2#usize [ 1568822693#u32, 152276873#u32 ],
    Array.make 2#usize [ 639814482#u32, 2066574751#u32 ],
    Array.make 2#usize [ 1093071961#u32, 648593218#u32 ],
    Array.make 2#usize [ 1594495101#u32, 1219247426#u32 ],
    Array.make 2#usize [ 1960324689#u32, 231359048#u32 ],
    Array.make 2#usize [ 1912333344#u32, 1039720332#u32 ]
  ] (by rfl)

private def rate512HighChunk21 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 1580223790#u32, 194696271#u32 ],
    Array.make 2#usize [ 1118217466#u32, 863739844#u32 ],
    Array.make 2#usize [ 378535762#u32, 939702037#u32 ],
    Array.make 2#usize [ 1146601110#u32, 614612204#u32 ],
    Array.make 2#usize [ 870936612#u32, 632870252#u32 ],
    Array.make 2#usize [ 2071247511#u32, 1765366071#u32 ],
    Array.make 2#usize [ 1674906685#u32, 165851886#u32 ],
    Array.make 2#usize [ 999688792#u32, 29574619#u32 ],
    Array.make 2#usize [ 2137679949#u32, 68458636#u32 ],
    Array.make 2#usize [ 308816680#u32, 1146452137#u32 ],
    Array.make 2#usize [ 1487465746#u32, 1340846354#u32 ],
    Array.make 2#usize [ 202176565#u32, 327982285#u32 ],
    Array.make 2#usize [ 812986380#u32, 2085743640#u32 ],
    Array.make 2#usize [ 951261442#u32, 268098645#u32 ],
    Array.make 2#usize [ 1383853684#u32, 369838865#u32 ],
    Array.make 2#usize [ 896850794#u32, 1771978157#u32 ]
  ] (by rfl)

private def rate512HighChunk22 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 732393395#u32, 2112881577#u32 ],
    Array.make 2#usize [ 1543329494#u32, 385164898#u32 ],
    Array.make 2#usize [ 252929270#u32, 1353673049#u32 ],
    Array.make 2#usize [ 402099265#u32, 942918913#u32 ],
    Array.make 2#usize [ 125103457#u32, 1669530034#u32 ],
    Array.make 2#usize [ 893042083#u32, 2072239544#u32 ],
    Array.make 2#usize [ 784964762#u32, 1326503162#u32 ],
    Array.make 2#usize [ 784723556#u32, 324037566#u32 ],
    Array.make 2#usize [ 228509164#u32, 2132953617#u32 ],
    Array.make 2#usize [ 694966700#u32, 225285446#u32 ],
    Array.make 2#usize [ 222277859#u32, 1869196184#u32 ],
    Array.make 2#usize [ 962257603#u32, 1788623924#u32 ],
    Array.make 2#usize [ 2098580229#u32, 1896945393#u32 ],
    Array.make 2#usize [ 1872514139#u32, 1928688577#u32 ],
    Array.make 2#usize [ 1854234209#u32, 509684486#u32 ],
    Array.make 2#usize [ 906381151#u32, 951530181#u32 ]
  ] (by rfl)

private def rate512HighChunk23 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 505542828#u32, 2121318970#u32 ],
    Array.make 2#usize [ 133640314#u32, 76248066#u32 ],
    Array.make 2#usize [ 222141861#u32, 834535867#u32 ],
    Array.make 2#usize [ 1391987716#u32, 1668802934#u32 ],
    Array.make 2#usize [ 2137011181#u32, 1133390394#u32 ],
    Array.make 2#usize [ 440454181#u32, 1719321497#u32 ],
    Array.make 2#usize [ 749414350#u32, 1397384897#u32 ],
    Array.make 2#usize [ 368578328#u32, 2118812954#u32 ],
    Array.make 2#usize [ 408478793#u32, 262191051#u32 ],
    Array.make 2#usize [ 1538500177#u32, 1346335954#u32 ],
    Array.make 2#usize [ 2110925851#u32, 355239363#u32 ],
    Array.make 2#usize [ 116984891#u32, 1853602521#u32 ],
    Array.make 2#usize [ 1411221007#u32, 1553669210#u32 ],
    Array.make 2#usize [ 557591127#u32, 1236765960#u32 ],
    Array.make 2#usize [ 735494074#u32, 653278886#u32 ],
    Array.make 2#usize [ 271138064#u32, 230496232#u32 ]
  ] (by rfl)

private def rate512HighChunk24 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 2147450879#u32, 2147450879#u32 ],
    Array.make 2#usize [ 230496232#u32, 271138064#u32 ],
    Array.make 2#usize [ 653278886#u32, 735494074#u32 ],
    Array.make 2#usize [ 1236765960#u32, 557591127#u32 ],
    Array.make 2#usize [ 1553669210#u32, 1411221007#u32 ],
    Array.make 2#usize [ 1853602521#u32, 116984891#u32 ],
    Array.make 2#usize [ 355239363#u32, 2110925851#u32 ],
    Array.make 2#usize [ 1346335954#u32, 1538500177#u32 ],
    Array.make 2#usize [ 262191051#u32, 408478793#u32 ],
    Array.make 2#usize [ 2118812954#u32, 368578328#u32 ],
    Array.make 2#usize [ 1397384897#u32, 749414350#u32 ],
    Array.make 2#usize [ 1719321497#u32, 440454181#u32 ],
    Array.make 2#usize [ 1133390394#u32, 2137011181#u32 ],
    Array.make 2#usize [ 1668802934#u32, 1391987716#u32 ],
    Array.make 2#usize [ 834535867#u32, 222141861#u32 ],
    Array.make 2#usize [ 76248066#u32, 133640314#u32 ]
  ] (by rfl)

private def rate512HighChunk25 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 2121318970#u32, 505542828#u32 ],
    Array.make 2#usize [ 951530181#u32, 906381151#u32 ],
    Array.make 2#usize [ 509684486#u32, 1854234209#u32 ],
    Array.make 2#usize [ 1928688577#u32, 1872514139#u32 ],
    Array.make 2#usize [ 1896945393#u32, 2098580229#u32 ],
    Array.make 2#usize [ 1788623924#u32, 962257603#u32 ],
    Array.make 2#usize [ 1869196184#u32, 222277859#u32 ],
    Array.make 2#usize [ 225285446#u32, 694966700#u32 ],
    Array.make 2#usize [ 2132953617#u32, 228509164#u32 ],
    Array.make 2#usize [ 324037566#u32, 784723556#u32 ],
    Array.make 2#usize [ 1326503162#u32, 784964762#u32 ],
    Array.make 2#usize [ 2072239544#u32, 893042083#u32 ],
    Array.make 2#usize [ 1669530034#u32, 125103457#u32 ],
    Array.make 2#usize [ 942918913#u32, 402099265#u32 ],
    Array.make 2#usize [ 1353673049#u32, 252929270#u32 ],
    Array.make 2#usize [ 385164898#u32, 1543329494#u32 ]
  ] (by rfl)

private def rate512HighChunk26 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 2112881577#u32, 732393395#u32 ],
    Array.make 2#usize [ 1771978157#u32, 896850794#u32 ],
    Array.make 2#usize [ 369838865#u32, 1383853684#u32 ],
    Array.make 2#usize [ 268098645#u32, 951261442#u32 ],
    Array.make 2#usize [ 2085743640#u32, 812986380#u32 ],
    Array.make 2#usize [ 327982285#u32, 202176565#u32 ],
    Array.make 2#usize [ 1340846354#u32, 1487465746#u32 ],
    Array.make 2#usize [ 1146452137#u32, 308816680#u32 ],
    Array.make 2#usize [ 68458636#u32, 2137679949#u32 ],
    Array.make 2#usize [ 29574619#u32, 999688792#u32 ],
    Array.make 2#usize [ 165851886#u32, 1674906685#u32 ],
    Array.make 2#usize [ 1765366071#u32, 2071247511#u32 ],
    Array.make 2#usize [ 632870252#u32, 870936612#u32 ],
    Array.make 2#usize [ 614612204#u32, 1146601110#u32 ],
    Array.make 2#usize [ 939702037#u32, 378535762#u32 ],
    Array.make 2#usize [ 863739844#u32, 1118217466#u32 ]
  ] (by rfl)

private def rate512HighChunk27 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 194696271#u32, 1580223790#u32 ],
    Array.make 2#usize [ 1039720332#u32, 1912333344#u32 ],
    Array.make 2#usize [ 231359048#u32, 1960324689#u32 ],
    Array.make 2#usize [ 1219247426#u32, 1594495101#u32 ],
    Array.make 2#usize [ 648593218#u32, 1093071961#u32 ],
    Array.make 2#usize [ 2066574751#u32, 639814482#u32 ],
    Array.make 2#usize [ 152276873#u32, 1568822693#u32 ],
    Array.make 2#usize [ 1080634846#u32, 1918438855#u32 ],
    Array.make 2#usize [ 1941424532#u32, 212443077#u32 ],
    Array.make 2#usize [ 159124930#u32, 1802066642#u32 ],
    Array.make 2#usize [ 1678097410#u32, 1756768506#u32 ],
    Array.make 2#usize [ 1665658221#u32, 675922742#u32 ],
    Array.make 2#usize [ 1668363411#u32, 225856549#u32 ],
    Array.make 2#usize [ 1526278178#u32, 1763527383#u32 ],
    Array.make 2#usize [ 1819216575#u32, 484667533#u32 ],
    Array.make 2#usize [ 1208818126#u32, 1190084038#u32 ]
  ] (by rfl)

private def rate512HighChunk28 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 1556715293#u32, 978592373#u32 ],
    Array.make 2#usize [ 734695164#u32, 1845756189#u32 ],
    Array.make 2#usize [ 1034324306#u32, 1293504395#u32 ],
    Array.make 2#usize [ 964510742#u32, 1856336347#u32 ],
    Array.make 2#usize [ 1079800039#u32, 1949783546#u32 ],
    Array.make 2#usize [ 1481771921#u32, 354138878#u32 ],
    Array.make 2#usize [ 1920912571#u32, 1233386319#u32 ],
    Array.make 2#usize [ 877294821#u32, 1501011474#u32 ],
    Array.make 2#usize [ 883753057#u32, 350742286#u32 ],
    Array.make 2#usize [ 500380354#u32, 269176336#u32 ],
    Array.make 2#usize [ 1922524821#u32, 485600145#u32 ],
    Array.make 2#usize [ 477700432#u32, 1361499402#u32 ],
    Array.make 2#usize [ 1506666447#u32, 1702126977#u32 ],
    Array.make 2#usize [ 652224438#u32, 375548322#u32 ],
    Array.make 2#usize [ 944571042#u32, 167450866#u32 ],
    Array.make 2#usize [ 1641459700#u32, 2109066236#u32 ]
  ] (by rfl)

private def rate512HighChunk29 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 280947147#u32, 1133522282#u32 ],
    Array.make 2#usize [ 576681506#u32, 2103767252#u32 ],
    Array.make 2#usize [ 1530121874#u32, 1541513586#u32 ],
    Array.make 2#usize [ 2109827321#u32, 1059774538#u32 ],
    Array.make 2#usize [ 583555490#u32, 849605071#u32 ],
    Array.make 2#usize [ 166192302#u32, 1330638276#u32 ],
    Array.make 2#usize [ 1603661239#u32, 1398285837#u32 ],
    Array.make 2#usize [ 672775513#u32, 499205677#u32 ],
    Array.make 2#usize [ 7144319#u32, 404685994#u32 ],
    Array.make 2#usize [ 1374213821#u32, 650162669#u32 ],
    Array.make 2#usize [ 1326622868#u32, 1644164930#u32 ],
    Array.make 2#usize [ 1249976217#u32, 1380714367#u32 ],
    Array.make 2#usize [ 236104903#u32, 1577470940#u32 ],
    Array.make 2#usize [ 2058078381#u32, 1638487879#u32 ],
    Array.make 2#usize [ 482535559#u32, 776881039#u32 ],
    Array.make 2#usize [ 210509587#u32, 824292393#u32 ]
  ] (by rfl)

private def rate512HighChunk30 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 967747991#u32, 1241207368#u32 ],
    Array.make 2#usize [ 1050440434#u32, 1741011703#u32 ],
    Array.make 2#usize [ 1730666434#u32, 36815260#u32 ],
    Array.make 2#usize [ 748769323#u32, 543170620#u32 ],
    Array.make 2#usize [ 2005527287#u32, 170449934#u32 ],
    Array.make 2#usize [ 1303261374#u32, 269141577#u32 ],
    Array.make 2#usize [ 952794586#u32, 472916039#u32 ],
    Array.make 2#usize [ 756105750#u32, 1051518090#u32 ],
    Array.make 2#usize [ 134155457#u32, 1108537731#u32 ],
    Array.make 2#usize [ 2004432601#u32, 499966977#u32 ],
    Array.make 2#usize [ 775814313#u32, 2103108137#u32 ],
    Array.make 2#usize [ 259793911#u32, 750301505#u32 ],
    Array.make 2#usize [ 1895558694#u32, 636875771#u32 ],
    Array.make 2#usize [ 1611588241#u32, 330498905#u32 ],
    Array.make 2#usize [ 1152650470#u32, 1716662235#u32 ],
    Array.make 2#usize [ 1024618173#u32, 1974665904#u32 ]
  ] (by rfl)

private def rate512HighChunk31 :
    Array (Array Std.U32 2#usize) 16#usize :=
  Array.make 16#usize [
    Array.make 2#usize [ 1567857810#u32, 1690787918#u32 ],
    Array.make 2#usize [ 1379798146#u32, 566492308#u32 ],
    Array.make 2#usize [ 1336950523#u32, 839591040#u32 ],
    Array.make 2#usize [ 2059253359#u32, 1857622143#u32 ],
    Array.make 2#usize [ 789857006#u32, 2066105389#u32 ],
    Array.make 2#usize [ 1205829819#u32, 2075806777#u32 ],
    Array.make 2#usize [ 1195900917#u32, 528066207#u32 ],
    Array.make 2#usize [ 1243190338#u32, 989947986#u32 ],
    Array.make 2#usize [ 1309288441#u32, 1774253895#u32 ],
    Array.make 2#usize [ 227683315#u32, 1732277387#u32 ],
    Array.make 2#usize [ 1492095742#u32, 752064346#u32 ],
    Array.make 2#usize [ 1670018420#u32, 1464821634#u32 ],
    Array.make 2#usize [ 1362440376#u32, 1260750973#u32 ],
    Array.make 2#usize [ 1538255603#u32, 827893883#u32 ],
    Array.make 2#usize [ 2133873350#u32, 1064696601#u32 ],
    Array.make 2#usize [ 712777190#u32, 1835793811#u32 ]
  ] (by rfl)

/-- Exact normalized declaration of the Aeneas literal table. -/
@[global_simps, rust_const "aspis_core::circle_fri::RATE512_CIRCLE_HIGH9_WINDOW"]
def aspis_core.circle_fri.RATE512_CIRCLE_HIGH9_WINDOW
  : Array (Array Std.U32 2#usize) 512#usize :=
  Array.make 512#usize (
    rate512HighChunk0.val ++
    rate512HighChunk1.val ++
    rate512HighChunk2.val ++
    rate512HighChunk3.val ++
    rate512HighChunk4.val ++
    rate512HighChunk5.val ++
    rate512HighChunk6.val ++
    rate512HighChunk7.val ++
    rate512HighChunk8.val ++
    rate512HighChunk9.val ++
    rate512HighChunk10.val ++
    rate512HighChunk11.val ++
    rate512HighChunk12.val ++
    rate512HighChunk13.val ++
    rate512HighChunk14.val ++
    rate512HighChunk15.val ++
    rate512HighChunk16.val ++
    rate512HighChunk17.val ++
    rate512HighChunk18.val ++
    rate512HighChunk19.val ++
    rate512HighChunk20.val ++
    rate512HighChunk21.val ++
    rate512HighChunk22.val ++
    rate512HighChunk23.val ++
    rate512HighChunk24.val ++
    rate512HighChunk25.val ++
    rate512HighChunk26.val ++
    rate512HighChunk27.val ++
    rate512HighChunk28.val ++
    rate512HighChunk29.val ++
    rate512HighChunk30.val ++
    rate512HighChunk31.val
  ) (by
    simp only [List.length_append, Array.length_eq]
    norm_num)

end V5FriCoordinateAdapter

import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsChunk39

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
/-- [aspis_statement::state_only_poseidon::full_round]: loop 0:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 336:4-338:5
    Name pattern: [aspis_statement::state_only_poseidon::full_round] -/
@[rust_loop, rust_fun "aspis_statement::state_only_poseidon::full_round"]
def aspis_statement.state_only_poseidon.full_round_loop
  (iter : core.ops.range.Range Std.Usize)
  (state : Array aspis_core.field.QM31 16#usize)
  (constants1 : Array aspis_core.field.QM31 16#usize) :
  Result (Array aspis_core.field.QM31 16#usize)
  := do
  loop
    (fun (iter1, state1) =>
      aspis_statement.state_only_poseidon.full_round_loop.body constants1 iter1
      state1)
    (iter, state)

/-- [aspis_statement::state_only_poseidon::full_round]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 332:0-335:28
    Name pattern: [aspis_statement::state_only_poseidon::full_round] -/
@[rust_fun "aspis_statement::state_only_poseidon::full_round"]
def aspis_statement.state_only_poseidon.full_round
  (state : Array aspis_core.field.QM31 16#usize)
  (constants1 : Array aspis_core.field.QM31 16#usize) :
  Result (Array aspis_core.field.QM31 16#usize)
  := do
  let state1 ←
    aspis_statement.state_only_poseidon.full_round_loop
      { start := 0#usize, «end» := aspis_statement.poseidon2.POSEIDON2_WIDTH
      } state constants1
  aspis_statement.state_only_poseidon.external_linear_lazy state1

/-- [aspis_statement::poseidon2::EXTERNAL_FINAL]
    Source: 'crates/aspis-statement/src/poseidon2.rs', lines 106:0-106:47
    Name pattern: [aspis_statement::poseidon2::EXTERNAL_FINAL] -/
@[global_simps, irreducible, rust_const
  "aspis_statement::poseidon2::EXTERNAL_FINAL"]
def aspis_statement.poseidon2.EXTERNAL_FINAL
  : Array (Array Std.U32 16#usize) 4#usize :=
  Array.make 4#usize [
    Array.make 16#usize [
      1460209171#u32, 530850056#u32, 398192464#u32, 536338716#u32,
      75179210#u32, 1309934197#u32, 1335920373#u32, 127611036#u32,
      291093831#u32, 1832379621#u32, 123571662#u32, 303176864#u32,
      2137685056#u32, 1759609530#u32, 1418928155#u32, 71608334#u32
      ],
    Array.make 16#usize [
      6616262#u32, 1684515814#u32, 1721194338#u32, 720801691#u32,
      878392254#u32, 460379263#u32, 87930647#u32, 940673483#u32,
      1136203256#u32, 551499412#u32, 256220454#u32, 2007034235#u32,
      796124985#u32, 410436345#u32, 1705042586#u32, 1286336446#u32
      ],
    Array.make 16#usize [
      1522340456#u32, 1295296352#u32, 309794713#u32, 1772145068#u32,
      956898901#u32, 2137070800#u32, 988829146#u32, 2059451359#u32,
      1846491684#u32, 1105442551#u32, 1236497773#u32, 1452000568#u32,
      549485016#u32, 385992492#u32, 1987107948#u32, 1514377269#u32
      ],
    Array.make 16#usize [
      2090065934#u32, 1444920141#u32, 293113979#u32, 41120774#u32,
      855319793#u32, 1663284746#u32, 1789994008#u32, 1120509162#u32,
      358222743#u32, 1406256810#u32, 735183687#u32, 664485235#u32,
      1331641456#u32, 38121324#u32, 595810771#u32, 1234594393#u32
      ]
    ]

/-- [aspis_statement::poseidon2::EXTERNAL_INITIAL]
    Source: 'crates/aspis-statement/src/poseidon2.rs', lines 83:0-83:49
    Name pattern: [aspis_statement::poseidon2::EXTERNAL_INITIAL] -/
@[global_simps, irreducible, rust_const
  "aspis_statement::poseidon2::EXTERNAL_INITIAL"]
def aspis_statement.poseidon2.EXTERNAL_INITIAL
  : Array (Array Std.U32 16#usize) 4#usize :=
  Array.make 4#usize [
    Array.make 16#usize [
      1988864850#u32, 1893772157#u32, 1025928330#u32, 1839472709#u32,
      1611656994#u32, 1104858731#u32, 1694088660#u32, 1564660990#u32,
      1991332205#u32, 1875486487#u32, 1890340790#u32, 1658614#u32,
      582370530#u32, 528029397#u32, 1196956642#u32, 655401251#u32
      ],
    Array.make 16#usize [
      1652877415#u32, 26032894#u32, 1576640243#u32, 1277052539#u32,
      1450142396#u32, 697623591#u32, 1401580866#u32, 1568404175#u32,
      2145004971#u32, 265835716#u32, 1183985610#u32, 1031234465#u32,
      436012490#u32, 172735299#u32, 352802897#u32, 1032863094#u32
      ],
    Array.make 16#usize [
      757665783#u32, 1082171296#u32, 1507509996#u32, 309929890#u32,
      1807683232#u32, 43258895#u32, 611592566#u32, 1854193793#u32,
      575164234#u32, 894217817#u32, 72613857#u32, 1061659596#u32, 8921166#u32,
      1617355017#u32, 998001536#u32, 1800758877#u32
      ],
    Array.make 16#usize [
      1002748055#u32, 1935405944#u32, 1351462722#u32, 411368491#u32,
      1913975372#u32, 1956167178#u32, 442558016#u32, 855898408#u32,
      699687798#u32, 1553382248#u32, 1708169125#u32, 490049183#u32,
      1251643415#u32, 1193594742#u32, 880473871#u32, 511174042#u32
      ]
    ]

/-- [aspis_statement::state_only_poseidon::interpolated_full_pair_packed]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 504:0-507:45
    Name pattern: [aspis_statement::state_only_poseidon::interpolated_full_pair_packed] -/
@[rust_fun
  "aspis_statement::state_only_poseidon::interpolated_full_pair_packed"]
def aspis_statement.state_only_poseidon.interpolated_full_pair_packed
  (state : Array aspis_core.field.QM31 16#usize)
  (local1 : Array aspis_core.field.QM31 16#usize) :
  Result (Array aspis_core.field.QM31 4#usize)
  := do
  let q ← Array.index_usize local1 1#usize
  let q1 ← Array.index_usize local1 9#usize
  let q2 ← Array.index_usize local1 10#usize
  let a ←
    Array.index_usize aspis_statement.poseidon2.EXTERNAL_INITIAL 2#usize
  let a1 ← Array.index_usize aspis_statement.poseidon2.EXTERNAL_FINAL 0#usize
  let a2 ← Array.index_usize aspis_statement.poseidon2.EXTERNAL_FINAL 2#usize
  let even ←
    aspis_statement.state_only_poseidon.interpolate_three_constant_columns
      (Array.make 3#usize [ q, q1, q2 ]) a a1 a2
  let a3 ←
    Array.index_usize aspis_statement.poseidon2.EXTERNAL_INITIAL 3#usize
  let a4 ← Array.index_usize aspis_statement.poseidon2.EXTERNAL_FINAL 1#usize
  let a5 ← Array.index_usize aspis_statement.poseidon2.EXTERNAL_FINAL 3#usize
  let odd ←
    aspis_statement.state_only_poseidon.interpolate_three_constant_columns
      (Array.make 3#usize [ q, q1, q2 ]) a3 a4 a5
  let a6 ← aspis_statement.state_only_poseidon.full_round state even
  aspis_statement.state_only_poseidon.full_round_packed a6 odd

/-- [aspis_statement::state_only_poseidon::full_round_m31_constants_packed]: loop body 0:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 375:4-378:5
    Name pattern: [aspis_statement::state_only_poseidon::full_round_m31_constants_packed] -/
@[rust_loop_body, rust_fun
  "aspis_statement::state_only_poseidon::full_round_m31_constants_packed"]
def
  aspis_statement.state_only_poseidon.full_round_m31_constants_packed_loop.body
  (constants1 : Array Std.U32 16#usize) (iter : core.ops.range.Range Std.Usize)
  (state : Array aspis_core.field.QM31 16#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array
    aspis_core.field.QM31 16#usize)) (Array aspis_core.field.QM31 16#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done state)
  | some lane =>
    let q ← Array.index_usize state lane
    let i ← Array.index_usize constants1 lane
    let m ← aspis_core.field.M31.add q.c0.a i
    let (q1, index_mut_back) ← Array.index_mut_usize state lane
    let state1 := index_mut_back { q1 with c0 := { q1.c0 with a := m } }
    let q2 ← Array.index_usize state1 lane
    let q3 ← aspis_statement.state_only_poseidon.pow5 q2
    let a ← Array.update state1 lane q3
    ok (cont (iter1, a))

/-- [aspis_statement::state_only_poseidon::full_round_m31_constants_packed]: loop 0:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 375:4-378:5
    Name pattern: [aspis_statement::state_only_poseidon::full_round_m31_constants_packed] -/
@[rust_loop, rust_fun
  "aspis_statement::state_only_poseidon::full_round_m31_constants_packed"]
def aspis_statement.state_only_poseidon.full_round_m31_constants_packed_loop
  (iter : core.ops.range.Range Std.Usize)
  (state : Array aspis_core.field.QM31 16#usize)
  (constants1 : Array Std.U32 16#usize) :
  Result (Array aspis_core.field.QM31 16#usize)
  := do
  loop
    (fun (iter1, state1) =>
      aspis_statement.state_only_poseidon.full_round_m31_constants_packed_loop.body
      constants1 iter1 state1)
    (iter, state)

/-- [aspis_statement::state_only_poseidon::full_round_m31_constants_packed]:
    Source: 'crates/aspis-statement/src/state_only_poseidon.rs', lines 371:0-374:45
    Name pattern: [aspis_statement::state_only_poseidon::full_round_m31_constants_packed] -/
@[rust_fun
  "aspis_statement::state_only_poseidon::full_round_m31_constants_packed"]
def aspis_statement.state_only_poseidon.full_round_m31_constants_packed
  (state : Array aspis_core.field.QM31 16#usize)
  (constants1 : Array Std.U32 16#usize) :
  Result (Array aspis_core.field.QM31 4#usize)
  := do
  let state1 ←
    aspis_statement.state_only_poseidon.full_round_m31_constants_packed_loop
      { start := 0#usize, «end» := aspis_statement.poseidon2.POSEIDON2_WIDTH
      } state constants1
  aspis_statement.state_only_poseidon.external_linear_packed state1


end V7Tag73CurrentHelpersOpaque

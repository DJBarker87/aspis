import Aeneas.Std
import Aeneas.Data.Discriminant
import Aeneas.Tactic.RustAttributes
import V7Tag73CurrentHelpersOpaque.Types
import V7Tag73CurrentHelpersOpaque.FunsChunk20

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section

namespace V7Tag73CurrentHelpersOpaque
/-- [aspis_statement::atomic_state_only_terminal::constants::ATOMIC_COPY_ROUTING_ENTRIES]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal_constants.rs', lines 47:0-47:62
    Name pattern: [aspis_statement::atomic_state_only_terminal::constants::ATOMIC_COPY_ROUTING_ENTRIES] -/
@[global_simps, irreducible, rust_const
  "aspis_statement::atomic_state_only_terminal::constants::ATOMIC_COPY_ROUTING_ENTRIES"]
def
  aspis_statement.atomic_state_only_terminal.constants.ATOMIC_COPY_ROUTING_ENTRIES
  : Array (Std.U8 × Std.U32) 434#usize :=
  Array.make 434#usize [
    (59#u8, 2147483646#u32), (60#u8, 1#u32), (24#u8, 1#u32), (29#u8, 1#u32),
    (25#u8, 1#u32), (12#u8, 1#u32), (28#u8, 1#u32), (44#u8, 1#u32), (60#u8,
    1#u32), (32#u8, 1#u32), (16#u8, 1#u32), (27#u8, 2147483646#u32), (60#u8,
    1#u32), (27#u8, 1#u32), (43#u8, 1#u32), (11#u8, 1#u32), (59#u8, 1#u32),
    (26#u8, 1#u32), (28#u8, 1#u32), (27#u8, 1#u32), (31#u8, 1#u32), (32#u8,
    1#u32), (34#u8, 1#u32), (12#u8, 12#u32), (28#u8, 13#u32), (32#u8, 1#u32),
    (44#u8, 14#u32), (48#u8, 2#u32), (60#u8, 15#u32), (29#u8, 1#u32), (41#u8,
    1#u32), (12#u8, 2147483646#u32), (44#u8, 2147483646#u32), (60#u8,
    2147483646#u32), (0#u8, 1#u32), (16#u8, 1#u32), (32#u8, 1#u32), (48#u8,
    1#u32), (12#u8, 1#u32), (28#u8, 1#u32), (32#u8, 1#u32), (44#u8, 1#u32),
    (48#u8, 1#u32), (60#u8, 1#u32), (1#u8, 1#u32), (4#u8, 1#u32), (7#u8,
    1#u32), (10#u8, 1#u32), (13#u8, 1#u32), (16#u8, 1#u32), (19#u8, 1#u32),
    (0#u8, 1#u32), (3#u8, 1#u32), (6#u8, 1#u32), (9#u8, 1#u32), (12#u8, 1#u32),
    (15#u8, 1#u32), (18#u8, 1#u32), (0#u8, 1#u32), (2#u8, 1#u32), (3#u8,
    1#u32), (5#u8, 1#u32), (6#u8, 1#u32), (8#u8, 1#u32), (9#u8, 1#u32), (11#u8,
    1#u32), (12#u8, 1#u32), (14#u8, 1#u32), (15#u8, 1#u32), (17#u8, 1#u32),
    (18#u8, 1#u32), (18#u8, 1#u32), (21#u8, 1#u32), (30#u8, 1#u32), (34#u8,
    1#u32), (37#u8, 1#u32), (40#u8, 1#u32), (44#u8, 1#u32), (47#u8, 1#u32),
    (50#u8, 1#u32), (53#u8, 1#u32), (56#u8, 1#u32), (59#u8, 1#u32), (62#u8,
    1#u32), (17#u8, 1#u32), (20#u8, 1#u32), (23#u8, 1#u32), (33#u8, 1#u32),
    (36#u8, 1#u32), (39#u8, 1#u32), (43#u8, 1#u32), (46#u8, 1#u32), (49#u8,
    1#u32), (52#u8, 1#u32), (55#u8, 1#u32), (58#u8, 1#u32), (61#u8, 1#u32),
    (0#u8, 106#u32), (3#u8, 112#u32), (6#u8, 118#u32), (9#u8, 124#u32), (12#u8,
    130#u32), (15#u8, 136#u32), (18#u8, 142#u32), (16#u8, 1#u32), (17#u8,
    1#u32), (19#u8, 1#u32), (20#u8, 1#u32), (22#u8, 1#u32), (23#u8, 1#u32),
    (31#u8, 1#u32), (32#u8, 1#u32), (33#u8, 1#u32), (35#u8, 1#u32), (36#u8,
    1#u32), (38#u8, 1#u32), (39#u8, 1#u32), (42#u8, 1#u32), (43#u8, 1#u32),
    (45#u8, 1#u32), (46#u8, 1#u32), (48#u8, 1#u32), (49#u8, 1#u32), (51#u8,
    1#u32), (52#u8, 1#u32), (54#u8, 1#u32), (55#u8, 1#u32), (57#u8, 1#u32),
    (58#u8, 1#u32), (60#u8, 1#u32), (61#u8, 1#u32), (63#u8, 1#u32), (16#u8,
    24#u32), (17#u8, 28#u32), (20#u8, 34#u32), (23#u8, 40#u32), (25#u8, 8#u32),
    (33#u8, 46#u32), (36#u8, 52#u32), (39#u8, 58#u32), (43#u8, 64#u32), (46#u8,
    70#u32), (49#u8, 76#u32), (52#u8, 82#u32), (55#u8, 88#u32), (58#u8,
    94#u32), (61#u8, 100#u32), (0#u8, 107#u32), (1#u8, 105#u32), (2#u8,
    112#u32), (3#u8, 113#u32), (4#u8, 111#u32), (5#u8, 118#u32), (6#u8,
    119#u32), (7#u8, 117#u32), (8#u8, 124#u32), (9#u8, 125#u32), (10#u8,
    123#u32), (11#u8, 130#u32), (12#u8, 131#u32), (13#u8, 129#u32), (14#u8,
    136#u32), (15#u8, 137#u32), (16#u8, 135#u32), (17#u8, 142#u32), (18#u8,
    143#u32), (19#u8, 141#u32), (16#u8, 28#u32), (17#u8, 29#u32), (18#u8,
    27#u32), (19#u8, 34#u32), (20#u8, 35#u32), (21#u8, 33#u32), (22#u8,
    40#u32), (23#u8, 41#u32), (25#u8, 16#u32), (30#u8, 39#u32), (31#u8,
    23#u32), (32#u8, 46#u32), (33#u8, 47#u32), (34#u8, 45#u32), (35#u8,
    52#u32), (36#u8, 53#u32), (37#u8, 51#u32), (38#u8, 58#u32), (39#u8,
    59#u32), (40#u8, 57#u32), (42#u8, 64#u32), (43#u8, 65#u32), (44#u8,
    63#u32), (45#u8, 70#u32), (46#u8, 71#u32), (47#u8, 69#u32), (48#u8,
    76#u32), (49#u8, 77#u32), (50#u8, 75#u32), (51#u8, 82#u32), (52#u8,
    83#u32), (53#u8, 81#u32), (54#u8, 88#u32), (55#u8, 89#u32), (56#u8,
    87#u32), (57#u8, 94#u32), (58#u8, 95#u32), (59#u8, 93#u32), (60#u8,
    100#u32), (61#u8, 101#u32), (62#u8, 99#u32), (63#u8, 106#u32), (13#u8,
    1#u32), (19#u8, 1#u32), (21#u8, 1#u32), (9#u8, 1#u32), (10#u8, 1#u32),
    (16#u8, 2147483646#u32), (0#u8, 1#u32), (1#u8, 1#u32), (2#u8, 1#u32),
    (4#u8, 1#u32), (8#u8, 2147483646#u32), (9#u8, 2147483646#u32), (11#u8,
    1#u32), (15#u8, 1#u32), (22#u8, 1#u32), (25#u8, 1#u32), (6#u8,
    2147483646#u32), (13#u8, 22#u32), (19#u8, 2147483645#u32), (20#u8, 1#u32),
    (21#u8, 2147483644#u32), (27#u8, 1#u32), (0#u8, 2147483646#u32), (1#u8,
    1073741823#u32), (5#u8, 1073741818#u32), (6#u8, 1073741824#u32), (8#u8,
    1#u32), (9#u8, 2#u32), (10#u8, 6#u32), (14#u8, 1073741824#u32), (16#u8,
    1073741815#u32), (18#u8, 2147483646#u32), (0#u8, 2147483634#u32), (1#u8,
    1073741820#u32), (5#u8, 1073741851#u32), (6#u8, 1073741821#u32), (8#u8,
    1#u32), (9#u8, 32#u32), (14#u8, 1073741821#u32), (16#u8, 1073741866#u32),
    (18#u8, 5#u32), (0#u8, 429496771#u32), (1#u8, 858993479#u32), (2#u8,
    12#u32), (3#u8, 2147483642#u32), (4#u8, 2147483644#u32), (5#u8, 1#u32),
    (8#u8, 1288490168#u32), (9#u8, 429496693#u32), (11#u8, 17#u32), (12#u8,
    2147483646#u32), (15#u8, 20#u32), (16#u8, 1#u32), (22#u8, 2147483645#u32),
    (23#u8, 1#u32), (25#u8, 2147483644#u32), (28#u8, 1#u32), (0#u8,
    1717986932#u32), (1#u8, 1288490193#u32), (8#u8, 858993454#u32), (9#u8,
    1717986908#u32), (0#u8, 2147483636#u32), (1#u8, 4#u32), (8#u8, 7#u32),
    (9#u8, 7#u32), (0#u8, 144#u32), (1#u8, 2147483646#u32), (8#u8, 1#u32),
    (9#u8, 1#u32), (10#u8, 1#u32), (0#u8, 1#u32), (3#u8, 2147483646#u32),
    (4#u8, 1#u32), (15#u8, 1#u32), (16#u8, 2147483646#u32), (1#u8, 1#u32),
    (8#u8, 2147483646#u32), (12#u8, 2147483646#u32), (25#u8, 1#u32), (19#u8,
    1#u32), (21#u8, 1#u32), (4#u8, 1#u32), (22#u8, 1#u32), (25#u8, 1#u32),
    (0#u8, 2147483646#u32), (0#u8, 2147483623#u32), (5#u8, 1#u32), (17#u8,
    1#u32), (5#u8, 2147483646#u32), (6#u8, 1#u32), (17#u8, 2147483646#u32),
    (19#u8, 1#u32), (21#u8, 1#u32), (6#u8, 2147483646#u32), (7#u8, 1#u32),
    (1#u8, 1073741825#u32), (4#u8, 1#u32), (5#u8, 1073741828#u32), (6#u8,
    1073741823#u32), (7#u8, 2147483646#u32), (8#u8, 2147483646#u32), (11#u8,
    1#u32), (14#u8, 1073741823#u32), (15#u8, 1#u32), (16#u8, 1073741822#u32),
    (22#u8, 1#u32), (25#u8, 1#u32), (5#u8, 2147483594#u32), (7#u8, 6#u32),
    (14#u8, 6#u32), (17#u8, 25#u32), (18#u8, 6#u32), (5#u8, 343597604#u32),
    (6#u8, 23#u32), (7#u8, 1460288855#u32), (14#u8, 1460288855#u32), (17#u8,
    2147483543#u32), (18#u8, 1460288855#u32), (19#u8, 2#u32), (20#u8, 1#u32),
    (21#u8, 2147483643#u32), (27#u8, 1#u32), (5#u8, 2061584376#u32), (7#u8,
    171798686#u32), (14#u8, 171798686#u32), (18#u8, 171798686#u32), (1#u8,
    28#u32), (3#u8, 2147483645#u32), (4#u8, 2147483637#u32), (5#u8, 126#u32),
    (6#u8, 2147483637#u32), (7#u8, 2147483623#u32), (8#u8, 2147483629#u32),
    (11#u8, 10#u32), (12#u8, 3#u32), (14#u8, 1610612722#u32), (15#u8, 11#u32),
    (16#u8, 2147483627#u32), (18#u8, 13#u32), (22#u8, 2#u32), (23#u8, 1#u32),
    (25#u8, 2147483643#u32), (28#u8, 1#u32), (5#u8, 41#u32), (6#u8,
    2147483644#u32), (14#u8, 715827879#u32), (18#u8, 2147483646#u32), (1#u8,
    1073741824#u32), (5#u8, 1073741830#u32), (6#u8, 1073741823#u32), (7#u8,
    2147483646#u32), (14#u8, 1073741823#u32), (16#u8, 1073741823#u32), (17#u8,
    1#u32), (5#u8, 2147483646#u32), (11#u8, 1#u32), (16#u8, 2147483646#u32),
    (12#u8, 1#u32), (22#u8, 1#u32), (4#u8, 1#u32), (7#u8, 1#u32), (23#u8,
    1#u32), (13#u8, 1#u32), (12#u8, 1#u32), (11#u8, 1#u32), (0#u8, 1#u32),
    (5#u8, 1#u32), (10#u8, 1#u32), (5#u8, 1#u32), (10#u8, 507044751#u32),
    (1#u8, 1#u32), (2#u8, 1#u32), (3#u8, 1#u32), (4#u8, 1#u32), (5#u8, 1#u32),
    (6#u8, 1#u32), (7#u8, 1#u32), (8#u8, 1#u32), (9#u8, 1#u32), (10#u8, 1#u32),
    (2#u8, 1#u32), (3#u8, 2#u32), (4#u8, 3#u32), (5#u8, 4#u32), (6#u8,
    894784853#u32), (7#u8, 894784854#u32), (8#u8, 894784855#u32), (9#u8,
    894784856#u32), (10#u8, 894784857#u32), (11#u8, 1610612736#u32), (1#u8,
    1#u32), (2#u8, 1#u32), (3#u8, 1#u32), (6#u8, 1#u32), (1#u8, 1#u32), (2#u8,
    1#u32), (6#u8, 1#u32), (1#u8, 1431655769#u32), (2#u8, 1073741821#u32),
    (3#u8, 1#u32), (6#u8, 5#u32), (7#u8, 4#u32), (1#u8, 1574821342#u32), (2#u8,
    1073741823#u32), (6#u8, 1#u32), (7#u8, 1288490189#u32), (1#u8, 1#u32),
    (3#u8, 1#u32), (6#u8, 1#u32), (0#u8, 1#u32), (1#u8, 1#u32), (6#u8, 1#u32),
    (2#u8, 1#u32), (3#u8, 1#u32), (0#u8, 1546188230#u32), (1#u8,
    858993459#u32), (2#u8, 1632087571#u32), (6#u8, 1#u32), (7#u8,
    687194768#u32), (1#u8, 536870913#u32), (2#u8, 1431655766#u32), (3#u8,
    1#u32), (1#u8, 1372003441#u32), (2#u8, 850045609#u32), (7#u8, 1#u32)
    ]

/-- [aspis_statement::atomic_state_only_terminal::constants::ATOMIC_COPY_ROUTING_RIGHT_DIRECT_BASIS]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal_constants.rs', lines 46:0-46:65
    Name pattern: [aspis_statement::atomic_state_only_terminal::constants::ATOMIC_COPY_ROUTING_RIGHT_DIRECT_BASIS] -/
@[global_simps, irreducible, rust_const
  "aspis_statement::atomic_state_only_terminal::constants::ATOMIC_COPY_ROUTING_RIGHT_DIRECT_BASIS"]
def
  aspis_statement.atomic_state_only_terminal.constants.ATOMIC_COPY_ROUTING_RIGHT_DIRECT_BASIS
  : Array Std.U8 18#usize :=
  Array.make 18#usize [
    0#u8, 255#u8, 255#u8, 1#u8, 2#u8, 4#u8, 255#u8, 255#u8, 7#u8, 5#u8, 3#u8,
    255#u8, 6#u8, 255#u8, 255#u8, 255#u8, 255#u8, 255#u8
    ]

/-- [aspis_statement::atomic_state_only_terminal::constants::ATOMIC_COPY_ROUTING_RIGHT_RECONSTRUCTION_FACTORS]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal_constants.rs', lines 45:0-45:82
    Name pattern: [aspis_statement::atomic_state_only_terminal::constants::ATOMIC_COPY_ROUTING_RIGHT_RECONSTRUCTION_FACTORS] -/
@[global_simps, irreducible, rust_const
  "aspis_statement::atomic_state_only_terminal::constants::ATOMIC_COPY_ROUTING_RIGHT_RECONSTRUCTION_FACTORS"]
def
  aspis_statement.atomic_state_only_terminal.constants.ATOMIC_COPY_ROUTING_RIGHT_RECONSTRUCTION_FACTORS
  : Array (Std.U16 × Std.U8) 18#usize :=
  Array.make 18#usize [
    (399#u16, 0#u8), (399#u16, 4#u8), (403#u16, 3#u8), (406#u16, 0#u8),
    (406#u16, 0#u8), (406#u16, 0#u8), (406#u16, 5#u8), (411#u16, 4#u8),
    (415#u16, 0#u8), (415#u16, 0#u8), (415#u16, 0#u8), (415#u16, 3#u8),
    (418#u16, 0#u8), (418#u16, 3#u8), (421#u16, 2#u8), (423#u16, 5#u8),
    (428#u16, 3#u8), (431#u16, 3#u8)
    ]

/-- [aspis_statement::atomic_state_only_terminal::constants::ATOMIC_COPY_ROUTING_RIGHT_BASIS_FACTORS]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal_constants.rs', lines 44:0-44:72
    Name pattern: [aspis_statement::atomic_state_only_terminal::constants::ATOMIC_COPY_ROUTING_RIGHT_BASIS_FACTORS] -/
@[global_simps, irreducible, rust_const
  "aspis_statement::atomic_state_only_terminal::constants::ATOMIC_COPY_ROUTING_RIGHT_BASIS_FACTORS"]
def
  aspis_statement.atomic_state_only_terminal.constants.ATOMIC_COPY_ROUTING_RIGHT_BASIS_FACTORS
  : Array (Std.U16 × Std.U8) 8#usize :=
  Array.make 8#usize [
    (371#u16, 1#u8), (372#u16, 1#u8), (373#u16, 1#u8), (374#u16, 1#u8),
    (375#u16, 2#u8), (377#u16, 2#u8), (379#u16, 10#u8), (389#u16, 10#u8)
    ]

/-- [aspis_statement::atomic_state_only_terminal::constants::ATOMIC_COPY_ROUTING_LEFT_DIRECT_BASIS]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal_constants.rs', lines 43:0-43:64
    Name pattern: [aspis_statement::atomic_state_only_terminal::constants::ATOMIC_COPY_ROUTING_LEFT_DIRECT_BASIS] -/
@[global_simps, irreducible, rust_const
  "aspis_statement::atomic_state_only_terminal::constants::ATOMIC_COPY_ROUTING_LEFT_DIRECT_BASIS"]
def
  aspis_statement.atomic_state_only_terminal.constants.ATOMIC_COPY_ROUTING_LEFT_DIRECT_BASIS
  : Array Std.U8 60#usize :=
  Array.make 60#usize [
    255#u8, 255#u8, 16#u8, 255#u8, 8#u8, 0#u8, 255#u8, 255#u8, 255#u8, 255#u8,
    255#u8, 255#u8, 255#u8, 255#u8, 9#u8, 10#u8, 255#u8, 255#u8, 11#u8, 1#u8,
    2#u8, 12#u8, 3#u8, 13#u8, 21#u8, 255#u8, 19#u8, 22#u8, 255#u8, 255#u8,
    255#u8, 27#u8, 28#u8, 255#u8, 4#u8, 25#u8, 255#u8, 255#u8, 18#u8, 255#u8,
    255#u8, 255#u8, 255#u8, 14#u8, 255#u8, 255#u8, 255#u8, 255#u8, 255#u8,
    15#u8, 255#u8, 6#u8, 5#u8, 17#u8, 20#u8, 255#u8, 24#u8, 26#u8, 7#u8, 23#u8
    ]

/-- [aspis_statement::atomic_state_only_terminal::constants::ATOMIC_COPY_ROUTING_LEFT_RECONSTRUCTION_FACTORS]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal_constants.rs', lines 42:0-42:81
    Name pattern: [aspis_statement::atomic_state_only_terminal::constants::ATOMIC_COPY_ROUTING_LEFT_RECONSTRUCTION_FACTORS] -/
@[global_simps, irreducible, rust_const
  "aspis_statement::atomic_state_only_terminal::constants::ATOMIC_COPY_ROUTING_LEFT_RECONSTRUCTION_FACTORS"]
def
  aspis_statement.atomic_state_only_terminal.constants.ATOMIC_COPY_ROUTING_LEFT_RECONSTRUCTION_FACTORS
  : Array (Std.U16 × Std.U8) 60#usize :=
  Array.make 60#usize [
    (209#u16, 3#u8), (212#u16, 3#u8), (215#u16, 0#u8), (215#u16, 10#u8),
    (225#u16, 0#u8), (225#u16, 0#u8), (225#u16, 6#u8), (231#u16, 10#u8),
    (241#u16, 9#u8), (250#u16, 16#u8), (266#u16, 4#u8), (270#u16, 4#u8),
    (274#u16, 1#u8), (275#u16, 4#u8), (279#u16, 0#u8), (279#u16, 0#u8),
    (279#u16, 4#u8), (283#u16, 1#u8), (284#u16, 0#u8), (284#u16, 0#u8),
    (284#u16, 0#u8), (284#u16, 0#u8), (284#u16, 0#u8), (284#u16, 0#u8),
    (284#u16, 0#u8), (284#u16, 4#u8), (288#u16, 0#u8), (288#u16, 0#u8),
    (288#u16, 2#u8), (290#u16, 3#u8), (293#u16, 1#u8), (294#u16, 0#u8),
    (294#u16, 0#u8), (294#u16, 1#u8), (295#u16, 0#u8), (295#u16, 0#u8),
    (295#u16, 2#u8), (297#u16, 5#u8), (302#u16, 0#u8), (302#u16, 2#u8),
    (304#u16, 12#u8), (316#u16, 5#u8), (321#u16, 10#u8), (331#u16, 0#u8),
    (331#u16, 4#u8), (335#u16, 17#u8), (352#u16, 4#u8), (356#u16, 7#u8),
    (363#u16, 3#u8), (366#u16, 0#u8), (366#u16, 2#u8), (368#u16, 0#u8),
    (368#u16, 0#u8), (368#u16, 0#u8), (368#u16, 0#u8), (368#u16, 3#u8),
    (371#u16, 0#u8), (371#u16, 0#u8), (371#u16, 0#u8), (371#u16, 0#u8)
    ]

/-- [aspis_statement::atomic_state_only_terminal::constants::ATOMIC_COPY_ROUTING_LEFT_BASIS_FACTORS]
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal_constants.rs', lines 41:0-41:72
    Name pattern: [aspis_statement::atomic_state_only_terminal::constants::ATOMIC_COPY_ROUTING_LEFT_BASIS_FACTORS] -/
@[global_simps, irreducible, rust_const
  "aspis_statement::atomic_state_only_terminal::constants::ATOMIC_COPY_ROUTING_LEFT_BASIS_FACTORS"]
def
  aspis_statement.atomic_state_only_terminal.constants.ATOMIC_COPY_ROUTING_LEFT_BASIS_FACTORS
  : Array (Std.U16 × Std.U8) 29#usize :=
  Array.make 29#usize [
    (0#u16, 1#u8), (1#u16, 1#u8), (2#u16, 1#u8), (3#u16, 1#u8), (4#u16, 1#u8),
    (5#u16, 4#u8), (9#u16, 1#u8), (10#u16, 1#u8), (11#u16, 2#u8), (13#u16,
    2#u8), (15#u16, 2#u8), (17#u16, 2#u8), (19#u16, 2#u8), (21#u16, 2#u8),
    (23#u16, 6#u8), (29#u16, 2#u8), (31#u16, 3#u8), (34#u16, 4#u8), (38#u16,
    6#u8), (44#u16, 7#u8), (51#u16, 7#u8), (58#u16, 13#u8), (71#u16, 13#u8),
    (84#u16, 13#u8), (97#u16, 7#u8), (104#u16, 28#u8), (132#u16, 15#u8),
    (147#u16, 20#u8), (167#u16, 42#u8)
    ]

/-- [aspis_statement::atomic_state_only_terminal::evaluate_atomic_copy_routing::{impl core::ops::function::FnMut<(&'_ aspis_core::field::QM31,), aspis_core::field::PreparedQm31Multiplier> for aspis_statement::atomic_state_only_terminal::evaluate_atomic_copy_routing::closure}::call_mut]:
    Source: 'crates/aspis-statement/src/atomic_state_only_terminal.rs', lines 819:13-819:20
    Name pattern: [aspis_statement::atomic_state_only_terminal::evaluate_atomic_copy_routing::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::evaluate_atomic_copy_routing::closure, (&'_ aspis_core::field::QM31), aspis_core::field::PreparedQm31Multiplier>}::call_mut] -/
@[rust_fun
  "aspis_statement::atomic_state_only_terminal::evaluate_atomic_copy_routing::{core::ops::function::FnMut<aspis_statement::atomic_state_only_terminal::evaluate_atomic_copy_routing::closure, (&'_ aspis_core::field::QM31), aspis_core::field::PreparedQm31Multiplier>}::call_mut"]
def
  aspis_statement.atomic_state_only_terminal.evaluate_atomic_copy_routing.closure.Insts.CoreOpsFunctionFnMutTupleSharedQM31PreparedQm31Multiplier.call_mut
  (c :
  aspis_statement.atomic_state_only_terminal.evaluate_atomic_copy_routing.closure)
  (tupled_args : aspis_core.field.QM31) :
  Result (aspis_core.field.PreparedQm31Multiplier ×
    aspis_statement.atomic_state_only_terminal.evaluate_atomic_copy_routing.closure)
  := do
  let pqm ← aspis_core.field.PreparedQm31Multiplier.new tupled_args
  ok (pqm, c)


end V7Tag73CurrentHelpersOpaque

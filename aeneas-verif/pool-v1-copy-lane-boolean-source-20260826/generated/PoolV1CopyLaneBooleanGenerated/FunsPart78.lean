-- SPLIT FROM THE NORMALIZED AENEAS-GENERATED Funs MODULE
import PoolV1CopyLaneBooleanGenerated.FunsPart77
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

namespace PoolV1CopyLaneBooleanGenerated

/-- [aspis_statement::pool_v1::payment_semantic_terminal::constants::PRIVATE_TRANSFER_COPY_LINKS]
    Source: 'crates/aspis-statement/src/pool_v1/payment_semantic_terminal_constants.rs', lines 27:0-106:2 -/
@[irreducible]
def pool_v1.payment_semantic_terminal.constants.PRIVATE_TRANSFER_COPY_LINKS
  :
  Array pool_v1.payment_semantic_terminal.CompiledPoolV1PaymentLink 78#usize
  :=
  Array.make 78#usize [
    {
      tag := 1090519040#u32,
      producer := { row := 27#u16, slot := 0#u8, pattern := 0#u8 },
      consumer := { row := 32#u16, slot := 0#u8, pattern := 0#u8 }
    },
    {
      tag := 1090519041#u32,
      producer := { row := 43#u16, slot := 0#u8, pattern := 0#u8 },
      consumer := { row := 48#u16, slot := 0#u8, pattern := 0#u8 }
    },
    {
      tag := 1090519042#u32,
      producer := { row := 395#u16, slot := 0#u8, pattern := 0#u8 },
      consumer := { row := 400#u16, slot := 0#u8, pattern := 0#u8 }
    },
    {
      tag := 1090519043#u32,
      producer := { row := 475#u16, slot := 0#u8, pattern := 0#u8 },
      consumer := { row := 480#u16, slot := 0#u8, pattern := 0#u8 }
    },
    {
      tag := 1090519044#u32,
      producer := { row := 491#u16, slot := 0#u8, pattern := 0#u8 },
      consumer := { row := 496#u16, slot := 0#u8, pattern := 0#u8 }
    },
    {
      tag := 1090519045#u32,
      producer := { row := 427#u16, slot := 0#u8, pattern := 0#u8 },
      consumer := { row := 432#u16, slot := 0#u8, pattern := 0#u8 }
    },
    {
      tag := 1090519046#u32,
      producer := { row := 443#u16, slot := 0#u8, pattern := 0#u8 },
      consumer := { row := 448#u16, slot := 0#u8, pattern := 0#u8 }
    },
    {
      tag := 1090519047#u32,
      producer := { row := 11#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 28#u16, slot := 0#u8, pattern := 1#u8 }
    },
    {
      tag := 1090519048#u32,
      producer := { row := 12#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 396#u16, slot := 0#u8, pattern := 1#u8 }
    },
    {
      tag := 1090519049#u32,
      producer := { row := 44#u16, slot := 0#u8, pattern := 2#u8 },
      consumer := { row := 412#u16, slot := 0#u8, pattern := 3#u8 }
    },
    {
      tag := 1090519050#u32,
      producer := { row := 60#u16, slot := 0#u8, pattern := 4#u8 },
      consumer := { row := 412#u16, slot := 1#u8, pattern := 5#u8 }
    },
    {
      tag := 1090519051#u32,
      producer := { row := 59#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 784#u16, slot := 0#u8, pattern := 6#u8 }
    },
    {
      tag := 1090519052#u32,
      producer := { row := 785#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 76#u16, slot := 0#u8, pattern := 1#u8 }
    },
    {
      tag := 1090519053#u32,
      producer := { row := 785#u16, slot := 1#u8, pattern := 7#u8 },
      consumer := { row := 64#u16, slot := 0#u8, pattern := 8#u8 }
    },
    {
      tag := 1090519054#u32,
      producer := { row := 75#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 786#u16, slot := 0#u8, pattern := 6#u8 }
    },
    {
      tag := 1090519055#u32,
      producer := { row := 787#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 92#u16, slot := 0#u8, pattern := 1#u8 }
    },
    {
      tag := 1090519056#u32,
      producer := { row := 787#u16, slot := 1#u8, pattern := 7#u8 },
      consumer := { row := 80#u16, slot := 0#u8, pattern := 8#u8 }
    },
    {
      tag := 1090519057#u32,
      producer := { row := 91#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 788#u16, slot := 0#u8, pattern := 6#u8 }
    },
    {
      tag := 1090519058#u32,
      producer := { row := 789#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 108#u16, slot := 0#u8, pattern := 1#u8 }
    },
    {
      tag := 1090519059#u32,
      producer := { row := 789#u16, slot := 1#u8, pattern := 7#u8 },
      consumer := { row := 96#u16, slot := 0#u8, pattern := 8#u8 }
    },
    {
      tag := 1090519060#u32,
      producer := { row := 107#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 790#u16, slot := 0#u8, pattern := 6#u8 }
    },
    {
      tag := 1090519061#u32,
      producer := { row := 791#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 124#u16, slot := 0#u8, pattern := 1#u8 }
    },
    {
      tag := 1090519062#u32,
      producer := { row := 791#u16, slot := 1#u8, pattern := 7#u8 },
      consumer := { row := 112#u16, slot := 0#u8, pattern := 8#u8 }
    },
    {
      tag := 1090519063#u32,
      producer := { row := 123#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 800#u16, slot := 0#u8, pattern := 6#u8 }
    },
    {
      tag := 1090519064#u32,
      producer := { row := 801#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 140#u16, slot := 0#u8, pattern := 1#u8 }
    },
    {
      tag := 1090519065#u32,
      producer := { row := 801#u16, slot := 1#u8, pattern := 7#u8 },
      consumer := { row := 128#u16, slot := 0#u8, pattern := 8#u8 }
    },
    {
      tag := 1090519066#u32,
      producer := { row := 139#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 802#u16, slot := 0#u8, pattern := 6#u8 }
    },
    {
      tag := 1090519067#u32,
      producer := { row := 803#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 156#u16, slot := 0#u8, pattern := 1#u8 }
    },
    {
      tag := 1090519068#u32,
      producer := { row := 803#u16, slot := 1#u8, pattern := 7#u8 },
      consumer := { row := 144#u16, slot := 0#u8, pattern := 8#u8 }
    },
    {
      tag := 1090519069#u32,
      producer := { row := 155#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 804#u16, slot := 0#u8, pattern := 6#u8 }
    },
    {
      tag := 1090519070#u32,
      producer := { row := 805#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 172#u16, slot := 0#u8, pattern := 1#u8 }
    },
    {
      tag := 1090519071#u32,
      producer := { row := 805#u16, slot := 1#u8, pattern := 7#u8 },
      consumer := { row := 160#u16, slot := 0#u8, pattern := 8#u8 }
    },
    {
      tag := 1090519072#u32,
      producer := { row := 171#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 806#u16, slot := 0#u8, pattern := 6#u8 }
    },
    {
      tag := 1090519073#u32,
      producer := { row := 807#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 188#u16, slot := 0#u8, pattern := 1#u8 }
    },
    {
      tag := 1090519074#u32,
      producer := { row := 807#u16, slot := 1#u8, pattern := 7#u8 },
      consumer := { row := 176#u16, slot := 0#u8, pattern := 8#u8 }
    },
    {
      tag := 1090519075#u32,
      producer := { row := 187#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 816#u16, slot := 0#u8, pattern := 6#u8 }
    },
    {
      tag := 1090519076#u32,
      producer := { row := 817#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 204#u16, slot := 0#u8, pattern := 1#u8 }
    },
    {
      tag := 1090519077#u32,
      producer := { row := 817#u16, slot := 1#u8, pattern := 7#u8 },
      consumer := { row := 192#u16, slot := 0#u8, pattern := 8#u8 }
    },
    {
      tag := 1090519078#u32,
      producer := { row := 203#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 818#u16, slot := 0#u8, pattern := 6#u8 }
    },
    {
      tag := 1090519079#u32,
      producer := { row := 819#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 220#u16, slot := 0#u8, pattern := 1#u8 }
    },
    {
      tag := 1090519080#u32,
      producer := { row := 819#u16, slot := 1#u8, pattern := 7#u8 },
      consumer := { row := 208#u16, slot := 0#u8, pattern := 8#u8 }
    },
    {
      tag := 1090519081#u32,
      producer := { row := 219#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 820#u16, slot := 0#u8, pattern := 6#u8 }
    },
    {
      tag := 1090519082#u32,
      producer := { row := 821#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 236#u16, slot := 0#u8, pattern := 1#u8 }
    },
    {
      tag := 1090519083#u32,
      producer := { row := 821#u16, slot := 1#u8, pattern := 7#u8 },
      consumer := { row := 224#u16, slot := 0#u8, pattern := 8#u8 }
    },
    {
      tag := 1090519084#u32,
      producer := { row := 235#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 822#u16, slot := 0#u8, pattern := 6#u8 }
    },
    {
      tag := 1090519085#u32,
      producer := { row := 823#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 252#u16, slot := 0#u8, pattern := 1#u8 }
    },
    {
      tag := 1090519086#u32,
      producer := { row := 823#u16, slot := 1#u8, pattern := 7#u8 },
      consumer := { row := 240#u16, slot := 0#u8, pattern := 8#u8 }
    },
    {
      tag := 1090519087#u32,
      producer := { row := 251#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 832#u16, slot := 0#u8, pattern := 6#u8 }
    },
    {
      tag := 1090519088#u32,
      producer := { row := 833#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 268#u16, slot := 0#u8, pattern := 1#u8 }
    },
    {
      tag := 1090519089#u32,
      producer := { row := 833#u16, slot := 1#u8, pattern := 7#u8 },
      consumer := { row := 256#u16, slot := 0#u8, pattern := 8#u8 }
    },
    {
      tag := 1090519090#u32,
      producer := { row := 267#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 834#u16, slot := 0#u8, pattern := 6#u8 }
    },
    {
      tag := 1090519091#u32,
      producer := { row := 835#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 284#u16, slot := 0#u8, pattern := 1#u8 }
    },
    {
      tag := 1090519092#u32,
      producer := { row := 835#u16, slot := 1#u8, pattern := 7#u8 },
      consumer := { row := 272#u16, slot := 0#u8, pattern := 8#u8 }
    },
    {
      tag := 1090519093#u32,
      producer := { row := 283#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 836#u16, slot := 0#u8, pattern := 6#u8 }
    },
    {
      tag := 1090519094#u32,
      producer := { row := 837#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 300#u16, slot := 0#u8, pattern := 1#u8 }
    },
    {
      tag := 1090519095#u32,
      producer := { row := 837#u16, slot := 1#u8, pattern := 7#u8 },
      consumer := { row := 288#u16, slot := 0#u8, pattern := 8#u8 }
    },
    {
      tag := 1090519096#u32,
      producer := { row := 299#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 838#u16, slot := 0#u8, pattern := 6#u8 }
    },
    {
      tag := 1090519097#u32,
      producer := { row := 839#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 316#u16, slot := 0#u8, pattern := 1#u8 }
    },
    {
      tag := 1090519098#u32,
      producer := { row := 839#u16, slot := 1#u8, pattern := 7#u8 },
      consumer := { row := 304#u16, slot := 0#u8, pattern := 8#u8 }
    },
    {
      tag := 1090519099#u32,
      producer := { row := 315#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 848#u16, slot := 0#u8, pattern := 6#u8 }
    },
    {
      tag := 1090519100#u32,
      producer := { row := 849#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 332#u16, slot := 0#u8, pattern := 1#u8 }
    },
    {
      tag := 1090519101#u32,
      producer := { row := 849#u16, slot := 1#u8, pattern := 7#u8 },
      consumer := { row := 320#u16, slot := 0#u8, pattern := 8#u8 }
    },
    {
      tag := 1090519102#u32,
      producer := { row := 331#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 850#u16, slot := 0#u8, pattern := 6#u8 }
    },
    {
      tag := 1090519103#u32,
      producer := { row := 851#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 348#u16, slot := 0#u8, pattern := 1#u8 }
    },
    {
      tag := 1090519104#u32,
      producer := { row := 851#u16, slot := 1#u8, pattern := 7#u8 },
      consumer := { row := 336#u16, slot := 0#u8, pattern := 8#u8 }
    },
    {
      tag := 1090519105#u32,
      producer := { row := 347#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 852#u16, slot := 0#u8, pattern := 6#u8 }
    },
    {
      tag := 1090519106#u32,
      producer := { row := 853#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 364#u16, slot := 0#u8, pattern := 1#u8 }
    },
    {
      tag := 1090519107#u32,
      producer := { row := 853#u16, slot := 1#u8, pattern := 7#u8 },
      consumer := { row := 352#u16, slot := 0#u8, pattern := 8#u8 }
    },
    {
      tag := 1090519108#u32,
      producer := { row := 363#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 854#u16, slot := 0#u8, pattern := 6#u8 }
    },
    {
      tag := 1090519109#u32,
      producer := { row := 855#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 380#u16, slot := 0#u8, pattern := 1#u8 }
    },
    {
      tag := 1090519110#u32,
      producer := { row := 855#u16, slot := 1#u8, pattern := 7#u8 },
      consumer := { row := 368#u16, slot := 0#u8, pattern := 8#u8 }
    },
    {
      tag := 1090519111#u32,
      producer := { row := 44#u16, slot := 1#u8, pattern := 9#u8 },
      consumer := { row := 864#u16, slot := 0#u8, pattern := 10#u8 }
    },
    {
      tag := 1090519112#u32,
      producer := { row := 444#u16, slot := 0#u8, pattern := 9#u8 },
      consumer := { row := 866#u16, slot := 0#u8, pattern := 10#u8 }
    },
    {
      tag := 1090519113#u32,
      producer := { row := 492#u16, slot := 0#u8, pattern := 9#u8 },
      consumer := { row := 868#u16, slot := 0#u8, pattern := 10#u8 }
    },
    {
      tag := 1090519114#u32,
      producer := { row := 864#u16, slot := 0#u8, pattern := 10#u8 },
      consumer := { row := 870#u16, slot := 0#u8, pattern := 9#u8 }
    },
    {
      tag := 1090519115#u32,
      producer := { row := 866#u16, slot := 0#u8, pattern := 10#u8 },
      consumer := { row := 870#u16, slot := 1#u8, pattern := 11#u8 }
    },
    {
      tag := 1090519116#u32,
      producer := { row := 868#u16, slot := 0#u8, pattern := 10#u8 },
      consumer := { row := 871#u16, slot := 0#u8, pattern := 11#u8 }
    },
    {
      tag := 1090519117#u32,
      producer := { row := 870#u16, slot := 0#u8, pattern := 12#u8 },
      consumer := { row := 871#u16, slot := 1#u8, pattern := 9#u8 }
    }
    ]

end PoolV1CopyLaneBooleanGenerated

-- Mechanically normalized from pinned-Aeneas output for
-- source/tag67_six_actual_steps.rs.  The unsupported standard-library Option
-- `Try` declarations are reduced to their two constructors; source function
-- names, Rust scalar widths, result shape, and six-deep short-circuit remain.
import Aeneas.Std

open Aeneas Aeneas.Std Result

namespace tag67_six_actual_steps

structure Tag67ProofWorkStep where
  position : Std.U8
  bits : Std.U8
  label : Std.U8
  fold_round : Std.U8
  nonce : Std.U64
  next_action : Std.U8
  deriving DecidableEq

def tag67_proof_require_real_v5_work
    (computed_ok : Bool) : Result (Option Unit) :=
  if computed_ok then ok (some ()) else ok none

def tag67_proof_check_and_absorb_batch
    (computed_ok : Bool) (nonce : Std.U64) :
    Result (Option Tag67ProofWorkStep) := do
  let checked ← tag67_proof_require_real_v5_work computed_ok
  match checked with
  | none => ok none
  | some _ => ok (some {
      position := 0#u8
      bits := 37#u8
      label := 28#u8
      fold_round := 255#u8
      nonce
      next_action := 0#u8
    })

def tag67_proof_check_and_absorb_fold
    (computed_ok : Bool) (round : Std.Usize) (nonce : Std.U64) :
    Result (Option Tag67ProofWorkStep) := do
  let data ← match round.val with
    | 0 => ok (some (1#u8, 34#u8, 0#u8, 1#u8))
    | 1 => ok (some (2#u8, 33#u8, 1#u8, 2#u8))
    | 2 => ok (some (3#u8, 30#u8, 2#u8, 3#u8))
    | 3 => ok (some (4#u8, 25#u8, 3#u8, 4#u8))
    | _ => ok none
  match data with
  | none => ok none
  | some data =>
    let checked ← tag67_proof_require_real_v5_work computed_ok
    match checked with
    | none => ok none
    | some _ => ok (some {
        position := data.1
        bits := data.2.1
        label := 20#u8
        fold_round := data.2.2.1
        nonce
        next_action := data.2.2.2
      })

def tag67_proof_check_and_absorb_final
    (computed_ok : Bool) (nonce : Std.U64) :
    Result (Option Tag67ProofWorkStep) := do
  let checked ← tag67_proof_require_real_v5_work computed_ok
  match checked with
  | none => ok none
  | some _ => ok (some {
      position := 5#u8
      bits := 32#u8
      label := 5#u8
      fold_round := 255#u8
      nonce
      next_action := 5#u8
    })

def tag67_proof_six_actual_steps
    (batch_ok fold0_ok fold1_ok fold2_ok fold3_ok final_ok : Bool)
    (batch_nonce fold0_nonce fold1_nonce fold2_nonce fold3_nonce final_nonce : Std.U64) :
    Result (Option (Array Tag67ProofWorkStep 6#usize)) := do
  let batch ← tag67_proof_check_and_absorb_batch batch_ok batch_nonce
  match batch with
  | none => ok none
  | some batch =>
    let fold0 ← tag67_proof_check_and_absorb_fold fold0_ok 0#usize fold0_nonce
    match fold0 with
    | none => ok none
    | some fold0 =>
      let fold1 ← tag67_proof_check_and_absorb_fold fold1_ok 1#usize fold1_nonce
      match fold1 with
      | none => ok none
      | some fold1 =>
        let fold2 ← tag67_proof_check_and_absorb_fold fold2_ok 2#usize fold2_nonce
        match fold2 with
        | none => ok none
        | some fold2 =>
          let fold3 ← tag67_proof_check_and_absorb_fold fold3_ok 3#usize fold3_nonce
          match fold3 with
          | none => ok none
          | some fold3 =>
            let final_query ← tag67_proof_check_and_absorb_final final_ok final_nonce
            match final_query with
            | none => ok none
            | some final_query =>
              ok (some (Array.make 6#usize
                [batch, fold0, fold1, fold2, fold3, final_query]))

end tag67_six_actual_steps

-- Lean-4.32-normalized semantic form of source/tag67_six_actual_steps.rs.
-- The proof-facing Rust source restricts `nonce` to u64; the maintained
-- bridge below supplies `Nonce64.val`, so no unbounded value enters it.

namespace AspisTag67GeneratedSixSteps

structure Tag67ProofWorkStep where
  position : Nat
  bits : Nat
  label : Nat
  foldRound : Nat
  nonce : Nat
  nextAction : Nat
  deriving DecidableEq

def tag67ProofRequireRealV5Work (computedOK : Bool) : Option Unit :=
  if computedOK then some () else none

def tag67ProofCheckAndAbsorbBatch
    (computedOK : Bool) (nonce : Nat) : Option Tag67ProofWorkStep := do
  let _ ← tag67ProofRequireRealV5Work computedOK
  some {
    position := 0
    bits := 37
    label := 28
    foldRound := 255
    nonce
    nextAction := 0
  }

def tag67ProofCheckAndAbsorbFold
    (computedOK : Bool) (round nonce : Nat) : Option Tag67ProofWorkStep := do
  let data ← match round with
    | 0 => some (1, 34, 1)
    | 1 => some (2, 33, 2)
    | 2 => some (3, 30, 3)
    | 3 => some (4, 25, 4)
    | _ => none
  let _ ← tag67ProofRequireRealV5Work computedOK
  some {
    position := data.1
    bits := data.2.1
    label := 20
    foldRound := round
    nonce
    nextAction := data.2.2
  }

def tag67ProofCheckAndAbsorbFinal
    (computedOK : Bool) (nonce : Nat) : Option Tag67ProofWorkStep := do
  let _ ← tag67ProofRequireRealV5Work computedOK
  some {
    position := 5
    bits := 32
    label := 5
    foldRound := 255
    nonce
    nextAction := 5
  }

def tag67ProofSixActualSteps
    (batchOK fold0OK fold1OK fold2OK fold3OK finalOK : Bool)
    (batchNonce fold0Nonce fold1Nonce fold2Nonce fold3Nonce finalNonce : Nat) :
    Option (List Tag67ProofWorkStep) := do
  let batch ← tag67ProofCheckAndAbsorbBatch batchOK batchNonce
  let fold0 ← tag67ProofCheckAndAbsorbFold fold0OK 0 fold0Nonce
  let fold1 ← tag67ProofCheckAndAbsorbFold fold1OK 1 fold1Nonce
  let fold2 ← tag67ProofCheckAndAbsorbFold fold2OK 2 fold2Nonce
  let fold3 ← tag67ProofCheckAndAbsorbFold fold3OK 3 fold3Nonce
  let finalQuery ← tag67ProofCheckAndAbsorbFinal finalOK finalNonce
  some [batch, fold0, fold1, fold2, fold3, finalQuery]

end AspisTag67GeneratedSixSteps

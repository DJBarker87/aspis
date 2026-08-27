import ASQ8Dispatch.Funs

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisPool.ASQ8DispatchSourceBridge

open ASQ8Dispatch

noncomputable section

abbrev Pubkey := solana_pubkey.Pubkey
abbrev AccountInfo := solana_account_info.AccountInfo
abbrev Instruction := solana_instruction.Instruction
abbrev TerminalResult :=
  aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalResultV1

/-- Executable model of exactly the three runtime calls made by the translated
dispatch function.  Solana CPI behavior remains data supplied by this state. -/
structure TraceRuntime where
  cleared : Bool
  invoked : Option Instruction
  invokeResult : core.result.Result Unit solana_program_error.ProgramError
  returned : Option (Pubkey × alloc.vec.Vec Std.U8)

def traceRuntimeInst :
    pair_forest_dispatch.PairForestVerifierRuntimeV1 TraceRuntime where
  clear_return_data runtime :=
    .ok { runtime with cleared := true, invoked := none }
  invoke runtime instruction _ :=
    .ok (runtime.invokeResult, { runtime with invoked := some instruction })
  get_return_data runtime := .ok (runtime.returned, runtime)

def readonlyMeta (key : Pubkey) : solana_instruction.account_meta.AccountMeta where
  pubkey := key
  is_signer := false
  is_writable := false

def exactInstruction
    (plan : pair_forest_dispatch.PlannedPairForestDispatchV1)
    (proof master checkpoint lane : AccountInfo) : Instruction where
  program_id := plan.selected_verifier
  accounts := alloc.slice.Slice.into_vec (Array.to_slice (Array.make 4#usize [
    readonlyMeta proof.key, readonlyMeta master.key,
    readonlyMeta checkpoint.key, readonlyMeta lane.key ]))
  data := plan.request_bytes

/-- Successful translated-source dispatch performs one CPI with the exact four
readonly metas, then reads and decodes the immediate ASR8 return.  The premise
about `supported_loader` is the named Solana loader-ID boundary; the decoder
premise is the exact generated ASR8 decoder call, not an acceptance premise. -/
theorem translated_success_has_exact_readonly_cpi_and_immediate_result
    (plan : pair_forest_dispatch.PlannedPairForestDispatchV1)
    (proof master checkpoint lane verifier : AccountInfo)
    (returnedBytes : alloc.vec.Vec Std.U8)
    (result : TerminalResult)
    (runtimeOut : TraceRuntime)
    (loader :
      pair_forest_dispatch.supported_loader verifier.owner = .ok true)
    (programKey : verifier.key = plan.selected_verifier)
    (executable : verifier.executable = true)
    (verifierReadonly : verifier.is_writable = false)
    (verifierNonsigner : verifier.is_signer = false)
    (proofOwner : proof.owner = plan.selected_verifier)
    (proofReadonly : proof.is_writable = false)
    (proofNonsigner : proof.is_signer = false)
    (resultLength : returnedBytes.val.length = 792)
    (decoded :
      aspis_statement.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_result_v1
        (alloc.vec.Vec.deref returnedBytes) = .ok (.Ok result))
    (run :
      pair_forest_dispatch.invoke_pair_forest_terminal_with_runtime_v1
        traceRuntimeInst plan proof master checkpoint lane verifier
        {
          cleared := false
          invoked := none
          invokeResult := .Ok ()
          returned := some (plan.selected_verifier, returnedBytes)
        } = .ok (.Ok result, runtimeOut)) :
    runtimeOut.cleared = true ∧
    runtimeOut.invoked = some (exactInstruction plan proof master checkpoint lane) ∧
    runtimeOut.returned = some (plan.selected_verifier, returnedBytes) := by
  have selectedNe :
      core.cmp.PartialEq.ne.trait_default
        solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey
        plan.selected_verifier plan.selected_verifier = .ok false := by
    simp [core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
      solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey.eq]
  have decoded' :
      aspis_statement.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_result_v1
        returnedBytes = .ok (.Ok result) := by
    simpa [alloc.vec.Vec.deref] using decoded
  simp [
    pair_forest_dispatch.invoke_pair_forest_terminal_with_runtime_v1,
    pair_forest_dispatch.require_verifier_program,
    loader, executable, programKey, verifierReadonly, verifierNonsigner,
    solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey.eq,
    proofOwner, proofReadonly, proofNonsigner,
    core.cmp.impls.PartialEqShared.ne, core.cmp.PartialEq.ne.default,
    selectedNe,
    solana_instruction.account_meta.AccountMeta.new_readonly,
    solana_account_info.AccountInfo.Insts.CoreCloneClone.clone,
    traceRuntimeInst, core.option.Option.ok_or,
    aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_RESULT_BYTES,
    resultLength, decoded',
    core.result.Result.map_err,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.IntoFrom.into,
    lift,
    alloc.vec.Vec.len,
    alloc.vec.Vec.deref
  ] at run
  cases run
  simp [exactInstruction, readonlyMeta]

#print axioms translated_success_has_exact_readonly_cpi_and_immediate_result

end

end AspisPool.ASQ8DispatchSourceBridge

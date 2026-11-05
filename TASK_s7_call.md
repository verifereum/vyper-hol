# TASK: CALL and STATICCALL against the frame run

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: project root

## Theorem Statement (FROZEN)

```sml
Theorem asm_frame_call_step:
  asm_frame_prog_ok prog /\ asm_frame_rel prog data es0 as es /\
  as.as_pc < LENGTH prog /\
  (EL as.as_pc prog = AsmOp "CALL" \/ EL as.as_pc prog = AsmOp "STATICCALL") ==>
  asm_frame_step_ok prog data es0 as es
```

Supporting definitions (`venom/codegen/proofs/asmFrameRelScript.sml`):

```sml
Definition asm_frame_prog_ok_def:
  asm_frame_prog_ok prog <=>
    asm_encoding_wf prog /\
    (!i. i < LENGTH prog /\ ~is_data_inst (EL i prog) ==>
         !j. j <= i ==> ~is_data_inst (EL j prog)) /\
    (!i name. i < LENGTH prog /\ EL i prog = AsmOp name ==>
       name <> "DELEGATECALL" /\ name <> "CREATE" /\ name <> "CREATE2" /\
       name <> "SELFDESTRUCT")
End

Definition asm_frame_rel_def:
  asm_frame_rel prog data es0 as es <=>
    ?c0 c rb rest.
      es0.contexts = (c0, rb) :: rest /\ es.contexts = (c, rb) :: rest /\
      c0.logs = [] /\ c.msgParams = c0.msgParams /\ ~c0.msgParams.static /\
      es.txParams = es0.txParams /\ wf_state es /\
      (?d. es.msdomain = Collect d) /\
      asm_evm_rel (prog ++ [AsmDataItem data]) as es /\
      as.as_outcomes = MAP SND (call_trace es) /\
      as.as_gas_readings = gas_readings es /\
      as.as_requests ++ call_requests es = call_requests es0
End

Definition asm_frame_step_ok_def:
  asm_frame_step_ok prog data es0 as es <=>
    (?r es'. run_call es = SOME (r, es') /\ frame_resource_starved es0 r es') \/
    case asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
                  (EL as.as_pc prog) as of
      AsmOK as1 =>
        ?es1. run_call es1 = run_call es /\ asm_frame_rel prog data es0 as1 es1
    | AsmHalt as1 =>
        ?r es'. run_call es = SOME (r, es') /\
          frame_outcome es0 r es' NONE as1.as_returndata as1.as_logs /\
          es'.rollback.accounts = as1.as_accounts /\
          es'.rollback.toDelete = as1.as_pending_deletions /\
          es'.rollback.tStorage = as1.as_transient /\
          as1.as_requests = call_requests es0
    | AsmRevert as1 =>
        ?r es'. run_call es = SOME (r, es') /\
          ?lgs. frame_outcome es0 r es' (SOME Reverted) as1.as_returndata lgs
    | AsmFault as1 =>
        ?r es'. run_call es = SOME (r, es') /\
          ?exc lgs. exc <> Reverted /\ frame_outcome es0 r es' (SOME exc) [] lgs
    | AsmError _ => T
End
```

Do not modify this statement. Prove it as-is, or produce a counterexample.
The theorem is in `venom/codegen/proofs/asmFrameCallStepScript.sml`, proved by `cheat`.
All existing definitions and other theorem statements are frozen. New
proof-only helper lemmas are weakly frozen.

## Completion Criteria

1. Prove the exact statement without admissions or added assumptions.
2. `asmFrameCallStepTheory` builds normally (proof steps on, default step limit) with
   no CHEAT from this theory's own theorems and no parser warnings.
3. Reuse existing helpers rather than duplicating them.

## Build

```sh
holbuild -j4 build asmFrameCallStepTheory
```

## Background

The assembly executes CALL/STATICCALL by taking the next outcome from
`as_outcomes` (`asm_consume_call_outcome`, `take_outcome`) and recording
the request (`record_request`). The EVM runs the call for real: it may
finish at the frame's depth (precompiles, calls that fail before a child
starts, value transfer to an account with insufficient balance, the depth
limit) or push a child frame and run it back to this frame. In
`asm_frame_rel` the assembly's outcomes are `MAP SND (call_trace es)` and
its requests plus `call_requests es` are the whole frame's, so one call
step consumes exactly the trace entry the EVM records for it
(`frameObsStep` lemmas). The lemma says the call step either starves the
frame (OutOfGas, StackOverflow) or re-establishes `asm_frame_rel` at the
EVM state where the call has come back (stack, memory including
expansion and the return-data write, return data, accounts, transient
storage, logs, pending deletions, requests, remaining outcomes and
readings), with `run_call` unchanged.

## Domain Constraints

- No changes to existing definitions or to any other theorem statement in
  the repository; no new axioms, admissions, `cheat`s, timeout overrides,
  or search tactics wrapped in `TRY`/`ORELSE`.
- Other theorems in `venom/codegen/proofs/` that are still `cheat` (the
  sibling leaves of this frame run) are frozen dependencies: you may use
  them, don't prove or change them here.
- Don't touch `semantics/`, `frontend/`, `lowering/`, `venom/defs/`,
  `venom/compiler/`, `venom/passes/`, or verifereum.
- Put helper lemmas in this task's own theory file, or in a new leaf
  theory next to it in `venom/codegen/proofs/` that the task's theory
  imports. Before adding a helper, search for an existing theorem
  (verifereum's `spec/prop/` has many step/frame lemmas).
- Proofs at most ~50 lines each; split long cases into helper lemmas.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Frame-run skeleton | `venom/codegen/proofs/asmFrameRelScript.sml`, `venom/codegen/proofs/asmFrameRunScript.sml`, `venom/codegen/proofs/codegenAsmRunCallScript.sml` | `asm_frame_rel`, `asm_frame_step_ok`, how the leaves are used |
| Call trace observer | `venom/codegen/frame/callTraceScript.sml` | `observe`, `frame_obs_tr`, `call_trace`, `gas_readings`, `request_of`, `outcome_of`, `observable_call`, `next_opcode` |
| Frame outcomes | `venom/codegen/frame/frameOutcomeScript.sml` | `frame_outcome`, `frame_resource_starved` |
| Entry relation | `venom/codegen/defs/codegenEntryRelScript.sml` | `initial_ctx_rel`, `entry_asm_state` |
| asm/EVM relation | `venom/codegen/defs/codegenRelScript.sml` | `asm_evm_rel`, `asm_pc_to_offset` |
| Assembly semantics | `venom/codegen/defs/asmSemScript.sml` | `asm_step`, `asm_steps`, `asm_exec_call`, `asm_gas`, ... |
| Call oracle | `extCallOracleScript.sml` (repo root) | `take_outcome`, `record_request`, `adopt_outcome`, `precompile_result`, `computed_precompile` |
| Encoding | `venom/codegen/defs/symbolResolveScript.sml`, `venom/codegen/defs/asmWfScript.sml` | `assemble`, `compute_label_offsets`, `build_offset_to_pc`, `asm_encoding_wf` |
| Single-frame asm/EVM step sim | `venom/codegen/proofs/evmStepSimScript.sml` | `asm_evm_step` and its per-opcode dispatch lemmas (one context, no calls, no GAS, stack bound) |
| Multi-step single-frame sim | `venom/codegen/proofs/asmBytecodeSimScript.sml` | `asm_bytecode_sim_aux` |
| asm-to-bytecode facts | `venom/codegen/proofs/asmToBytecodeProofsScript.sml`, `venom/codegen/asmToBytecodePropsScript.sml`, `venom/codegen/proofs/asmEncodeParseScript.sml`, `venom/codegen/proofs/asmParseProofsScript.sml` | parse/encode, `offset_to_pc_inverse_proof`, `offset_to_pc_reverse` |
| Data suffix | `venom/codegen/proofs/asmDataSuffixPropsScript.sml` | `assemble (prog ++ [AsmDataItem bytes]) = assemble prog ++ bytes` and friends |
| Call oracle props | `venom/codegen/proofs/asmCallOraclePropsScript.sml` | |
| EVM semantics (verifereum, pinned) | `alan-ref/verifereum/spec/vfmExecutionScript.sml` | `step`, `handle_step`, `handle_exception`, `pop_and_incorporate_context`, `step_call`, `run_call` |
| EVM properties | `alan-ref/verifereum/spec/prop/` | `vfmExecutionProp` (`wf_state`), `vfmRunCall` (`run_call_preserves_wf_state`, `run_call_eq_run_single_context`, push/pop structure), `vfmSameFrame`, `vfmStepLength`, `vfmHandleStep` (pop effects), `vfmContextLength` (`run_call_inr_length`, `step_length_not_drop_more_than_one`), `vfmAccountFrame` (`run_call_finite_trace`, `run_call_nested_trace`, `OWHILE_trace_continuation`), `vfmDecreasesGas` (`run_call_eq_tr`) |
| Repo guide | `AGENTS.md` | proof conventions |

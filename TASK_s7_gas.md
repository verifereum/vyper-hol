# TASK: GAS against one single-context EVM step

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: project root

## Theorem Statement (FROZEN)

```sml
Theorem asm_evm_gas_step:
  !prog data as es.
    asm_encoding_wf prog /\
    asm_evm_rel (prog ++ [AsmDataItem data]) as es /\
    LENGTH es.contexts = 1 /\
    as.as_pc < LENGTH prog /\
    (!j. j <= as.as_pc ==> ~is_data_inst (EL j prog)) /\
    EL as.as_pc prog = AsmOp "GAS" ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    ?es1 w. step es = (INL (), es1) /\ LENGTH es1.contexts = 1 /\
            (FST (HD es1.contexts)).stack = w :: (FST (HD es.contexts)).stack /\
            asm_evm_rel (prog ++ [AsmDataItem data])
              (as with <| as_stack := w :: as.as_stack;
                          as_pc := as.as_pc + 1 |>) es1
```

Do not modify this statement. Prove it as-is, or produce a counterexample.
The theorem is in `venom/codegen/proofs/asmEvmGasStepScript.sml`, proved by `cheat`.
All existing definitions and other theorem statements are frozen. New
proof-only helper lemmas are weakly frozen.

## Completion Criteria

1. Prove the exact statement without admissions or added assumptions.
2. `asmEvmGasStepTheory` builds normally (proof steps on, default step limit) with
   no CHEAT from this theory's own theorems and no parser warnings.
3. Reuse existing helpers rather than duplicating them.

## Build

```sh
holbuild -j4 build asmEvmGasStepTheory
```

## Background

GAS is the one instruction whose EVM result the assembly can't
compute: the assembly takes each reading from `as_gas_readings`. This
lemma says the EVM's GAS step either starves (OutOfGas or StackOverflow)
or pushes some word w on the frame's stack, and the assembly state with
w pushed and its pc advanced corresponds to the EVM state after the step
(`asm_evm_rel` over the program with its data suffix).

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

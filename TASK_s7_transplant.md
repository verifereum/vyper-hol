# TASK: a non-pushing EVM step in a nested frame vs the same step alone

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: project root

## Theorem Statement (FROZEN)

```sml
Theorem step_transplant_continue:
  es.contexts = (c, rb) :: rest /\ rest <> [] /\ wf_state es /\
  (!op. next_opcode c = SOME op ==>
        ~MEM op [Call; CallCode; DelegateCall; StaticCall; Create; Create2]) /\
  step (es with contexts := [(c, rb)]) = (INL (), t) ==>
  ?c'. t.contexts = [(c', rb)] /\
       step es = (INL (), t with contexts := (c', rb) :: rest)

Theorem step_transplant_end:
  es.contexts = (c, rb) :: rest /\ rest <> [] /\ wf_state es /\
  (!a. c.msgParams.outputTo <> Code a) /\
  (!op. next_opcode c = SOME op ==>
        ~MEM op [Call; CallCode; DelegateCall; StaticCall; Create; Create2]) /\
  step (es with contexts := [(c, rb)]) = (INR e, t) /\ ~vfm_abort e ==>
  ?c' rb' es' lgs.
    t.contexts = [(c', rb')] /\ c'.logs = c.logs ++ lgs /\
    step es = (INL (), es') /\
    frame_outcome es (INL ()) es' e c'.returnData lgs /\
    (e = NONE ==> es'.rollback = t.rollback)
```

Do not modify this statement. Prove it as-is, or produce a counterexample.
The theorems are in `venom/codegen/proofs/evmStepTransplantScript.sml`, proved by `cheat`.
All existing definitions and other theorem statements are frozen. New
proof-only helper lemmas are weakly frozen.

## Completion Criteria

1. Prove the exact statements without admissions or added assumptions.
2. `evmStepTransplantTheory` builds normally (proof steps on, default step limit) with
   no CHEAT from this theory's own theorems and no parser warnings.
3. Reuse existing helpers rather than duplicating them.

## Build

```sh
holbuild -j4 build evmStepTransplantTheory
```

## Background

The existing assembly/EVM step simulation (`evmStepSim$asm_evm_step`)
works on a single-context EVM state. The frame being simulated may be
nested (calls from other contracts). These lemmas move a single-context
step that pushes no context into the nested frame: a continuing step
leaves the outer contexts as they are below the new head, and a step that
ends the frame (INR in the single-context run) returns to the parent the
way `frame_outcome` describes (return data, success flag on the parent's
stack, parent pc, logs, memory write of the output, rollback restore on
failure). Only verifereum's EVM semantics is involved.

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

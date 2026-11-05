# TASK: call_trace, gas_readings and run_call over one frame step

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: project root

## Theorem Statement (FROZEN)

```sml
Theorem frame_obs_plain_step:
  step es = (INL (), es1) /\ LENGTH es1.contexts = LENGTH es.contexts /\
  next_opcode (FST (HD es.contexts)) <> SOME Gas /\
  ~observable_call (FST (HD es.contexts)) ==>
  call_trace es = call_trace es1 /\ gas_readings es = gas_readings es1

Theorem frame_obs_gas_step:
  step es = (INL (), es1) /\ LENGTH es1.contexts = LENGTH es.contexts /\
  next_opcode (FST (HD es.contexts)) = SOME Gas ==>
  call_trace es = call_trace es1 /\
  gas_readings es = HD (FST (HD es1.contexts)).stack :: gas_readings es1

Theorem frame_obs_call_same_depth:
  step es = (INL (), es1) /\ LENGTH es1.contexts = LENGTH es.contexts /\
  observable_call (FST (HD es.contexts)) ==>
  call_trace es =
    (request_of es,
     outcome_of (request_of es).cr_kind es1
       (LENGTH (FST (HD es.contexts)).logs) (LENGTH es.rollback.toDelete)) ::
    call_trace es1 /\
  gas_readings es = gas_readings es1

Theorem frame_obs_call_enter:
  step es = (INL (), es1) /\ LENGTH es1.contexts = SUC (LENGTH es.contexts) /\
  observable_call (FST (HD es.contexts)) /\
  run_call es1 = SOME (INL (), es2) /\
  LENGTH es2.contexts = LENGTH es.contexts ==>
  call_trace es =
    (request_of es,
     outcome_of (request_of es).cr_kind es2
       (LENGTH (FST (HD es.contexts)).logs) (LENGTH es.rollback.toDelete)) ::
    call_trace es2 /\
  gas_readings es = gas_readings es2

Theorem frame_obs_terminal:
  step es = (r, es1) /\ (ISR r \/ LENGTH es1.contexts < LENGTH es.contexts) ==>
  call_trace es = [] /\ gas_readings es = []

Theorem run_call_same_depth_step:
  step es = (INL (), es1) /\ LENGTH es1.contexts = LENGTH es.contexts ==>
  run_call es1 = run_call es

Theorem run_call_enter_return:
  step es = (INL (), es1) /\ LENGTH es1.contexts = SUC (LENGTH es.contexts) /\
  run_call es1 = SOME (INL (), es2) /\
  LENGTH es2.contexts = LENGTH es.contexts ==>
  run_call es2 = run_call es

Theorem run_call_terminal_step:
  step es = (r, es1) /\ (ISR r \/ LENGTH es1.contexts < LENGTH es.contexts) ==>
  run_call es = SOME (r, es1)
```

Do not modify this statement. Prove it as-is, or produce a counterexample.
The theorems are in `venom/codegen/proofs/frameObsStepScript.sml`, proved by `cheat`.
All existing definitions and other theorem statements are frozen. New
proof-only helper lemmas are weakly frozen.

## Completion Criteria

1. Prove the exact statements without admissions or added assumptions.
2. `frameObsStepTheory` builds normally (proof steps on, default step limit) with
   no CHEAT from this theory's own theorems and no parser warnings.
3. Reuse existing helpers rather than duplicating them.

## Build

```sh
holbuild -j4 build frameObsStepTheory
```

## Background

A frame at depth d = LENGTH es.contexts records, while it runs, the
calls it makes and the GAS readings it takes (`call_trace`, `gas_readings`,
via `frame_obs_tr`). These lemmas say how one step of the frame moves both
lists and `run_call`: a step that stays at depth d and is neither GAS nor
an observable call leaves them as they are; GAS adds one reading (the word
the step pushes); a call that comes back at the same depth adds one
entry; a call that enters a child adds one entry whose outcome is read at
the state where the child's `run_call` returns to depth d; a step that
ends the frame (INR, or a drop below d) leaves both empty. They are used
by the assembly/EVM frame simulation (`asmFrameLocalStep`,
`asmFrameCallStep`) to carry the assembly's remaining oracle lists across
each step.

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

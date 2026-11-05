# TASK: single-context assembly/EVM step with only resource exceptions extra

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: project root

## Theorem Statement (FROZEN)

```sml
Theorem asm_evm_step_starve:
  !prog data as es.
    asm_encoding_wf prog /\
    asm_evm_rel (prog ++ [AsmDataItem data]) as es /\
    LENGTH es.contexts = 1 /\ (?d. es.msdomain = Collect d) /\
    ~(FST (HD es.contexts)).msgParams.static /\
    (!i. i < LENGTH prog /\ ~is_data_inst (EL i prog) ==>
         !j. j <= i ==> ~is_data_inst (EL j prog)) /\
    as.as_pc < LENGTH prog /\ ~is_data_inst (EL as.as_pc prog) /\
    (!name. EL as.as_pc prog = AsmOp name ==> ~is_evm_call_name name) /\
    EL as.as_pc prog <> AsmOp "GAS" ==>
    (?es1 exc. step es = (INR (SOME exc), es1) /\
               (exc = OutOfGas \/ exc = StackOverflow)) \/
    case asm_step (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
                  (EL as.as_pc prog) as of
      AsmOK as1 =>
        ?es1. step es = (INL (), es1) /\ LENGTH es1.contexts = 1 /\
              asm_evm_rel (prog ++ [AsmDataItem data]) as1 es1
    | AsmHalt as1 =>
        ?es1. step es = (INR NONE, es1) /\ LENGTH es1.contexts = 1 /\
              asm_evm_rel (prog ++ [AsmDataItem data]) as1 es1
    | AsmRevert as1 =>
        ?es1. step es = (INR (SOME Reverted), es1) /\ LENGTH es1.contexts = 1 /\
              asm_evm_rel (prog ++ [AsmDataItem data]) as1 es1
    | AsmFault as1 =>
        ?es1 exc. step es = (INR (SOME exc), es1) /\ exc <> Reverted /\
                  ~vfm_abort (SOME exc) /\ LENGTH es1.contexts = 1 /\
                  (FST (HD es1.contexts)).returnData = []
    | AsmError _ => T
```

Do not modify this statement. Prove it as-is, or produce a counterexample.
The theorem is in `venom/codegen/proofs/asmEvmStepStarveScript.sml`, proved by `cheat`.
All existing definitions and other theorem statements are frozen. New
proof-only helper lemmas are weakly frozen.

## Completion Criteria

1. Prove the exact statement without admissions or added assumptions.
2. `asmEvmStepStarveTheory` builds normally (proof steps on, default step limit) with
   no CHEAT from this theory's own theorems and no parser warnings.
3. Reuse existing helpers rather than duplicating them.

## Build

```sh
holbuild -j4 build asmEvmStepStarveTheory
```

## Background

`evmStepSim$asm_evm_step` simulates one assembly step by one EVM step
for a single-context frame, but it assumes a stack bound and absorbs any
EVM exception other than StackOverflow. The frame-level theorem needs the
EVM to differ only by its resource limits: OutOfGas and StackOverflow are
starvation, every other EVM exception must line up with an assembly
fault or error. The frame's code is the program's bytecode followed by a
data section (`assemble (prog ++ [AsmDataItem data])`), and the assembly
runs `prog`. This lemma covers every instruction except GAS and the call
family.

`build_offset_to_pc` is being changed (a separate piece) to map only the
offsets of `AsmLabel` instructions; the `[local]` cheated lemma
`build_offset_to_pc_labels` in the same file states that map and stands
in for that change: use it, leave it cheated. With it, an assembly jump
that succeeds lands on a label, i.e. a JUMPDEST in the bytecode.

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

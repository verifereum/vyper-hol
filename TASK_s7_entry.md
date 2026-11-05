# TASK: codegen_entry_asm_sim (S7 Venom-to-assembly entry simulation)

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: venom/codegen/proofs/codegenEntrySimScript.sml (project root: this directory)

## Theorem Statement (FROZEN)

In `venom/codegen/proofs/codegenEntrySimScript.sml`:

```sml
Theorem codegen_entry_asm_sim:
  !fuel rpolicy unit cp prog Inv vs es.
    generate_context_plan unit.cu_context = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\
    unit_shape_ok unit /\
    codegen_context_obligations Inv unit.cu_context cp /\
    codegen_reachability_package Inv unit.cu_context vs /\
    initial_ctx_rel cp prog unit.cu_context vs es
    ==>
    (!ret vs'. run_context fuel unit.cu_context vs <> IntRet ret vs') /\
    (!vs'. run_context fuel unit.cu_context vs = Halt vs' ==>
       ?n as'. asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog) prog n
         (entry_asm_state vs es) = AsmHalt as' /\
         venom_asm_terminal_rel vs' as') /\
    (!a vs'. run_context fuel unit.cu_context vs = Abort a vs' ==>
       ?n as'.
         ((a = Revert_abort /\
           asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog) prog n
         (entry_asm_state vs es) = AsmRevert as') \/
          (a = ExHalt_abort /\
           asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog) prog n
         (entry_asm_state vs es) = AsmFault as')) /\
         venom_asm_terminal_rel vs' as')
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.
Do not change any definition it uses either.

## Completion Criteria

1. `holbuild -j4 build codegenEntrySimTheory` passes with no CHEAT in
   `codegen_entry_asm_sim` or any helper you add.
2. No duplicate or near-duplicate lemmas: search before adding one; each
   helper exists once, in its most general form.

**If the theorem is false as stated:** produce a counterexample, state the
tightest sufficient fix, and stop. Do NOT weaken the statement.

## Build

```
holbuild -j4 build codegenEntrySimTheory
```

## Background

This is the Venom-to-assembly half of `codegenCorrectness$codegen_correct`
(stage S7 of the Vyper compiler correctness proof): running a Venom
context from its entry function is simulated by the generated assembly,
started in the assembly state of the EVM frame (`entry_asm_state`). The
entry function never returns (no IntRet); its Halt and Abort results are
matched by an assembly run ending in AsmHalt / AsmRevert / AsmFault.
`codegen_correct` is already proved from this theorem.

The function-level simulation `venomToAsmProps$gen_fn_simulation` is
proved (possibly from other admitted pieces; those are fine to use).

## Domain Constraints

- Helper lemmas go in `codegenEntrySimScript.sml` itself, or in a new
  leaf theory next to it under `venom/codegen/proofs/` that only
  `codegenEntrySim` imports. Don't edit any other existing theory, and
  never anything under `semantics/`, `frontend/`, `lowering/`,
  `venom/defs/`, `venom/compiler/`, `venom/passes/`, `venom/codegen/defs/`.
- No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with
  `>~`, `>-`, `>|`.
- Don't raise the tactic timeout (2.5 s per step); split slow steps.
- No new axioms, definitions changed, or cheats.
- Use existing lemmas where they exist (e.g.
  `unitShapeDefs$entry_fn_first_lookup`, fcg reachability lemmas,
  `contextPlanLayoutProps`, `codegenAsmRunCall` helpers).

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Target | `venom/codegen/proofs/codegenEntrySimScript.sml` | The theorem, with a comment on why it holds |
| gen_fn_simulation | `venom/codegen/venomToAsmPropsScript.sml` | Function-level simulation; its premises are what must be discharged |
| Entry relations | `venom/codegen/defs/codegenEntryRelScript.sml` | `initial_ctx_rel`, `initial_state_rel`, `stack_params_rel`, `entry_asm_state` |
| Frame relations | `venom/codegen/defs/frameRelScript.sml` | `fn_entry_state_rel`, `fn_has_retpc`, `shared_state_rel` |
| Obligations | `venom/codegen/defs/contextCodegenRelScript.sml` | `codegen_context_obligations`, `codegen_reachability_package`, `entry_fn_no_ret`, `fn_entry_inv`, `reachability_closed` |
| Shape | `venom/compiler/unitShapeDefsScript.sml` | `unit_shape_ok`, `entry_fn_first`, `entry_fn_first_lookup` |
| Venom semantics | `venom/defs/venomExecSemanticsScript.sml` | `run_context`, `run_function`, `run_blocks`, `setup_callee` |
| Assembly semantics | `venom/codegen/defs/asmSemScript.sml` | `asm_steps`, `asm_block_at` |
| Codegen | `venom/codegen/defs/codegenScript.sml`, `stackPlanGenScript.sml` | `codegen_assembly`, `generate_context_plan`, `get_params` |
| Layout facts | `venom/codegen/proofs/contextPlanLayoutPropsScript.sml`, `fnPlanPlace*Script.sml` | Where regions sit in the program |
| Sibling piece | `venom/codegen/proofs/codegenAsmRunCallScript.sml` | The EVM half; may have reusable entry facts |
| S7 consumer | `venom/codegen/codegenCorrectnessScript.sml` | `codegen_correct`, proved from this theorem |
| Call graph | `venom/analysis/fcg/` | `fcg_analyze`, `fcgAnalysisProps$fcg_analyze_reachable_complete`, `reachable_fcg_acyclic` |
| Region placement | `venom/codegen/proofs/fnPlanPlaceFnRegionScript.sml` | `generate_context_plan_with_provenance`, `codegen_region_slice`, `context_region_leading_label` |
| Return facts | `venom/props/venomRetPropsScript.sml` | `run_context_not_int_ret`, `run_blocks_not_int_ret` |
| Call layout | `venom/defs/callLayoutDefsScript.sml` | `fn_retpc_param` (in `codegen_ready`), vs `frameRel$fn_has_retpc` |

## Notes

The Venom state at entry has no variables and no parameters, the entry
function is the first function in the context and has no entry-block
parameters, and the EVM frame's stack is empty.

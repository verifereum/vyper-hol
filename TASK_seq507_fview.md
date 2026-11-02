# TASK: A Venom step commutes with the frame view

## Meta
Status: planned
Priority: P1
Created: 2026-11-02
Location: . (vyper-hol project root; the theorem is in venom/codegen/proofs/frameViewStepScript.sml)

## Theorem Statement (FROZEN)

```sml
Theorem step_inst_frame_view:
  !fuel ctx fn ra inst vs vs' m.
    step_inst fuel ctx inst vs = OK vs' /\
    inst.inst_opcode <> INVOKE /\
    ~is_param_opcode inst.inst_opcode /\
    codegen_ready_fn fn /\ opaque_use_ok fn /\ retpc_shape_ok fn /\
    MEM inst (fn_insts fn) /\
    (!i. source_memory_read_byte inst vs i ==>
         read_byte i m = read_byte i vs.vs_memory) ==>
    ?m'. step_inst fuel ctx inst (frame_view fn ra vs with vs_memory := m) =
           OK (frame_view fn ra vs' with vs_memory := m') /\
         (!i. read_byte i m = read_byte i vs.vs_memory ==>
              read_byte i m' = read_byte i vs'.vs_memory) /\
         (!i. EVERY (\r. ~byte_in_memory_range r i)
                (source_memory_write_ranges inst vs) ==>
              read_byte i m' = read_byte i m)
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build frameViewStepTheory` passes; `step_inst_frame_view` and every helper you add have no cheat (the build log's CHEAT lines name only theorems that were already cheated before this task).
2. The frozen statements are unchanged byte for byte.
3. No duplicate or near-duplicate lemmas; reuse the existing ones listed below.
4. Do not edit any other theorem's statement, any `Definition`, or any `Resume` block you weren't asked to touch.

**If the theorem is false as stated:**
- Produce a HOL4 counterexample theorem.
- State the tightest sufficient fix.
- Do NOT silently weaken the statement.

## Build

```
holbuild -j4 build frameViewStepTheory
```
(run from this directory, the one with holproject.toml; for a new helper theory `fooTheory`, `holbuild -j4 build fooTheory` first)

## Background

`frame_view fn ra vs` (venom/codegen/defs/frameRelScript.sml) rewrites the value of every return-PC variable (`retpc_var`, the copy/PHI closure of RETPC_PARAM outputs, unitShapeDefsScript.sml) to the return address `ra`. `step_inst_frame_view` says a non-INVOKE, non-PARAM step of an instruction of a codegen-ready function gives the same result on the view, with memory replaced by any `m` that agrees with the real memory on the bytes the instruction reads (`source_memory_read_byte`, contextCodegenRelScript.sml), up to the view and a memory `m'` related to the real result's memory as the two conclusion clauses say. `opaque_use_ok` limits retpc operands to ASSIGN, PHI and RET's last operand; PHI and RET never give `OK` from `step_inst_base`. MEMTOP (which reads memory length) is excluded by `codegen_ready_fn`. This lemma is the Venom half of lifting the per-instruction codegen simulation to the frame invariant (`gen_inst_frame_sim` in genFrameSimScript.sml).

## Domain Constraints

- holbuild only; never Holmake. No `cheat` in finished work; no new axioms; no `Definition` changes.
- Keep the default 2.5 s per-tactic timeout: a step that runs over must be split or given a smaller rewrite set. Never raise the timeout.
- Never wrap `metis_tac` or other search in `TRY`/`ORELSE`; pick goals explicitly with `>-`, `>~`, `>|`.
- Proofs ≤ ~50 lines each; give complex cases their own lemma. No dependence on generated names (use `rename1`). `gen_tac` primes variables named like constants (`base`, `cp`): `rename1` them.
- Modern script syntax (`Theory`/`Ancestors`/`Libs`, `Theorem … Proof … QED`). Theories go in `Ancestors`, never `Libs`. Don't name theories with a `Lib` suffix.
- Read AGENTS.md (this directory) for project conventions.

## Available Resources

| Resource | Location | Description |
|---|---|---|
| Target theorem | venom/codegen/proofs/frameViewStepScript.sml (`step_inst_frame_view`) | |
| Venom state / operands | venom/defs/venomStateScript.sml (`eval_operand`, `update_var`, memory writes, `read_byte`) | |
| Opcode facts | venom/codegen/proofs/opcodeClassScript.sml, venom/defs/venomInstProofs*Script.sml | |
| Shape | venom/compiler/unitShapeDefsScript.sml (`copy_phi_var`, `opaque_use_ok`), frameRelScript.sml (`frame_view_*` lemmas, `retpc_shape_ok`) | |
| Plan generator | venom/codegen/defs/stackPlanGenScript.sml (`generate_inst_plan`, `generate_regular_inst_plan`, `generate_emit_ops`, `compute_operands`, `emit_input_plan`, `reorder_plan`, `popmany_plan`, `optimistic_swap_plan`, `fresh_label`, `revert_postamble`) | |
| Plan ops / execution | venom/codegen/defs/stackPlanOpsScript.sml (`release_dead_spills`), planExecScript.sml (`execute_plan`, `exec_stack_op`, `apply_prefix_ops`), stackModelScript.sml, stackPlanTypesScript.sml | |
| Relation | venom/codegen/defs/codegenRelScript.sml (`venom_asm_rel`, `plan_stack_rel`, `plan_spill_rel`, `memory_rel`, `inst_memory_safe`, `venom_asm_terminal_rel`) | |
| Read ranges | venom/codegen/defs/contextCodegenRelScript.sml (`source_memory_read_ranges`) | |
| Asm semantics | venom/codegen/defs/asmSemScript.sml (`asm_step`, `asm_steps`, `asm_block_at`, `asm_jump`, `asm_jumpi`, `asm_log`) | |
| Venom semantics | venom/defs/venomExecSemanticsScript.sml (`step_inst`, `step_inst_base`) | |
| Closed sibling cases (composition patterns) | genBlockSimScript.sml: `Resume gen_inst_ok_sim[...]` blocks (offset, bump, initial_fmp, istore, phi), `gen_inst_halt_sim`/`gen_inst_abort_sim` Resume blocks (revert, invalid, assert_unreachable abort, returndatacopy) | |
| Plan decomposition helpers | genBlockSimScript.sml: `gen_inst_prefix_decompose`, `gen_inst_terminal_setup(_strong)`, `regular_plan_*` | |
| Emit lemmas | venom/codegen/proofs/emitSimScript.sml, asmOpSimScript.sml (`*_asm_step`), stackOpAsmSimScript.sml (`asm_step_jump`, `asm_step_jumpi`, `asm_step_pushlabel_ok`) | |
| Prefix / postfix simulation | prefixSimScript.sml (`prefix_sim`), prefixExecScript.sml, mixedPrefixSimScript.sml (`mixed_prefix_venom_asm_rel`), strongPrefixSimScript.sml, planAlignScript.sml, stackOpSimScript.sml, spillSimScript.sml, cleanOpsSimScript.sml | all under venom/codegen/proofs/ |
| Reorder / input emission | reorderSimScript.sml (`reorder_plan_venom_asm_rel_residual`), emitInputSimScript.sml, doSwapSimScript.sml | |
| Planner invariants | planWfScript.sml, allocMonoScript.sml, planSpillBoundsScript.sml | |
| Opcode facts | opcodeClassScript.sml, venomStepPropsScript.sml, instSimHelpersScript.sml, blockSimHelpersScript.sml | |
| Built sigs | .holbuild/ (after a build) | |

## Notes

- Built at the starting commit with `step_inst_frame_view` cheated.

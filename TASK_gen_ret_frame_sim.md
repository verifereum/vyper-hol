# TASK: RET against the frame invariant (gen_ret_frame_sim)

## Meta
Status: planned
Priority: P0
Created: 2026-11-04
Location: venom/codegen/proofs/fnFrameBoundaryScript.sml (project root: this directory)

## Theorem Statement (FROZEN)

```sml
Theorem gen_ret_frame_sim:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' ra rest mem0 pc_ret.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode = RET /\
    MEM inst (fn_insts (reachable_fn fn)) /\
    codegen_ready_fn fn /\ opaque_use_ok fn /\ retpc_shape_ok fn /\
    inst_wf inst /\
    generated_plan_state_wf base ps /\
    LENGTH (compute_operands inst) <= 16 /\
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      (?d. stack_get_depth op ps.ps_stack = SOME d /\ d <= 15) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op (frame_view fn ra vs) =
          operand_val (frame_view fn ra vs) lo op) /\
    (!op at. MEM op (compute_operands inst) /\
             (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
              MEM at (compute_operands inst)) /\
             operand_equiv dfg op at ==>
             operand_val (frame_view fn ra vs) lo op =
             operand_val (frame_view fn ra vs) lo at) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      (compute_operands inst) /\
    prefix_spill_wf cp.cp_initial_fmp lo (FRONT ops) ps /\
    (!off. MEM (SORestore off) ops ==> off < dimword(:256)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    (fn_has_retpc fn ==> FLOOKUP o2pc (w2n ra) = SOME pc_ret) /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    ps'.ps_stack = [] /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) ==>
    !ret vs'. step_inst fuel ctx inst vs = IntRet ret vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        as'.as_pc = pc_ret /\
        as'.as_stack = REVERSE ret.iret_values ++ rest /\
        context_memory_rel cp vs'.vs_memory as'.as_memory /\
        (!b. context_spill_byte cp b /\
             ~closure_spill_byte ctx cp fn.fn_name b ==>
             read_byte b as'.as_memory = read_byte b mem0) /\
        shared_state_rel vs' as'
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild --gcthreads 8 -j4 build fnFrameBoundaryTheory` passes with no failure, and `gen_ret_frame_sim` and any helper theory you add have no CHEAT.
2. No duplicate or near-duplicate lemmas: each helper exists once, in its most general form. Search the existing theories (below) before proving a fact.
3. New helper theories, if any, are registered in `holproject.toml` the way the existing ones are.

Scope: only `gen_ret_frame_sim`. `gen_invoke_frame_sim`, `entry_params_frame_sim` (same theory) are other runs' work: leave their `cheat` alone and don't depend on them. Other cheated theorems in neighbouring theories (fnFrameSteps, fnFrameBoundary, fnPlanPlace, fnPlanLineage, venomToAsmProps) are other runs' work too.

**If the theorem is false as stated:**
- Produce a HOL4 counterexample (concrete terms, `EVAL`).
- State the tightest sufficient fix.
- Do NOT silently weaken the statement.

## Build

```
cd <this directory>
holbuild --gcthreads 8 -j4 build fnFrameBoundaryTheory
```

Always pass `--gcthreads 8` (a Poly/ML GC assertion fails without it on this host).

## Background

vyper-hol's Venom-to-EVM code generator plans each block's stack code and
lays the plans out with `codegen_assembly`. The block induction behind
`venomToAsmProps$gen_fn_frame_simulation` needs this theorem as one step.
The comment above the statement in `venom/codegen/proofs/fnFrameBoundaryScript.sml` says where it is used and
why it should hold. A statement check found it provable as stated.

## Domain Constraints

- holbuild only (no Holmake, no `holbuild run`/`repl`). Probe with scratch lemmas ending in `cheat` and rebuild.
- Never raise the tactic timeout (no `--tactic-timeout`, no holproject edits to it). A step that runs over 2.5 s must be split.
- No `TRY`/`ORELSE` around metis or other search.
- No `cheat` left anywhere you touched; no new axioms; no `let` in theorem statements.
- Do not edit definitions in `venom/codegen/defs`, `venom/analysis` or `venom/defs`.
- Keep helpers in `venom/codegen/proofs/`, in a new `fnFrameBoundaryGenRetScript.sml` that `fnFrameBoundary` imports, so parallel runs on the same theory don't collide. Generalizing an existing lemma is fine if you add the general form as a new theorem and leave the old one in place; making an existing `[local]` lemma public is fine.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Frame invariant | venom/codegen/defs/frameRelScript.sml | `fn_frame_inv`, `frame_view`, `fn_has_retpc`, `fn_entry_state_rel`, `fn_return_state_rel` |
| Proved siblings (model to follow) | venom/codegen/proofs/genFrameSimScript.sml, fnFrameTerminalScript.sml (+ fnFrameTerminalPrep/Halt/Abort) | `gen_inst_frame_sim`, `gen_jmp_frame_sim`, `gen_inst_halt_frame_sim`, `gen_inst_abort_frame_sim` |
| Per-instruction sims | venom/codegen/proofs/genBlockSimScript.sml | `gen_inst_ok_sim`, stack prefix lemmas |
| Stack-frame lifting | venom/codegen/proofs/asmFrameScript.sml, frameViewFactsScript.sml, frameViewMemoryScript.sml | running assembly on `top ++ rest` |
| Planner | venom/codegen/defs/stackPlanGenScript.sml | `generate_inst_plan`, `prepare_params_plan`, `emit_input_plan` |

## Notes

- Other runs are proving the sibling theorems in parallel on other branches; don't rely on them.

# TASK: Halt and Abort steps of an instruction against the frame invariant (gen_inst_halt_frame_sim, gen_inst_abort_frame_sim)

## Meta
Status: planned
Priority: P0
Created: 2026-11-04
Location: venom/codegen/proofs/fnFrameTerminalScript.sml (project root: this directory)

## Theorem Statements (FROZEN)

```sml
Theorem gen_inst_halt_frame_sim:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' ra rest mem0.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode <> INVOKE /\
    source_memory_reads_disjoint cp inst vs /\
    opaque_use_ok fn /\
    ~is_param_opcode inst.inst_opcode /\
    generated_plan_state_wf base ps /\
    codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\
    inst_wf inst /\
    LENGTH (compute_operands inst) <= 16 /\
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      (?d. stack_get_depth op ps.ps_stack = SOME d /\ d <= 15) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP lo l)) /\
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
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) ==>
    !vs'. step_inst fuel ctx inst vs = Halt vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmHalt as' /\
        venom_asm_terminal_rel vs' as'
```

```sml
Theorem gen_inst_abort_frame_sim:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' ra rest mem0.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode <> INVOKE /\
    source_memory_reads_disjoint cp inst vs /\
    opaque_use_ok fn /\
    ~is_param_opcode inst.inst_opcode /\
    generated_plan_state_wf base ps /\
    codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\
    inst_wf inst /\
    (inst.inst_opcode = ASSERT ==>
     ?off pc. FLOOKUP lo "revert" = SOME off /\ off < dimword (:256) /\
              FLOOKUP o2pc off = SOME pc /\
              asm_block_at prog pc
                (execute_plan cp.cp_initial_fmp revert_postamble)) /\
    LENGTH (compute_operands inst) <= 16 /\
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      (?d. stack_get_depth op ps.ps_stack = SOME d /\ d <= 15) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP lo l)) /\
    (!lbl i. i < LENGTH (execute_plan cp.cp_initial_fmp ops) /\
             EL i (execute_plan cp.cp_initial_fmp ops) = AsmLabel lbl ==>
             ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
                   FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
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
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) ==>
    !a vs'. step_inst fuel ctx inst vs = Abort a vs' ==>
      ?n as'.
        ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
         (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
        venom_asm_terminal_rel vs' as'
```

**Do not modify these statements.** Prove them as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild --gcthreads 8 -j4 build fnFrameTerminalTheory` passes with zero CHEAT warnings and zero failures in `fnFrameTerminalTheory` and any helper theory you add.
2. No duplicate or near-duplicate lemmas: each helper exists once, in its most general form. Search the existing theories (below) before proving a fact.
3. New helper theories, if any, are registered in `holproject.toml` the way the existing ones are.

Scope: only these two theorems. Other cheated theorems in neighbouring
theories (fnFrameSteps, fnFrameBoundary, fnPlanPlace, fnPlanLineage) are
other runs' work; don't touch them or depend on them.

**If a theorem is false as stated:**
- Produce a HOL4 counterexample (concrete instruction and states, `EVAL`).
- State the tightest sufficient fix.
- Do NOT silently weaken the statement.

## Build

```
cd <this directory>
holbuild --gcthreads 8 -j4 build fnFrameTerminalTheory
```

Always pass `--gcthreads 8` (a Poly/ML GC assertion fails without it on this host).

## Background

vyper-hol's Venom-to-EVM code generator plans each instruction's stack code
(`generate_inst_plan`, venom/codegen/defs/stackPlanGenScript.sml). The
per-instruction simulations in genBlockSim (`gen_inst_halt_sim`,
`gen_inst_abort_sim`, `gen_inst_ok_sim`) relate a planner state to the
whole assembly stack with `venom_asm_rel`. Across internal calls that
doesn't hold: the callee's stack sits above the caller's, and return-PC
variables hold an assembly address while Venom holds an opaque token.
`frameRel$fn_frame_inv` is the frame-aware invariant: the frame's own
stack above the caller's `rest`, the plan relations against
`frame_view fn ra vs`, the context-wide memory relation.

genFrameSim already lifts the OK-result case to `fn_frame_inv`
(`gen_inst_frame_sim`). These two theorems are the Halt and Abort results
of the same step. The conclusion, `venom_asm_terminal_rel`, reads no stack.
Notes on why they should hold are in the SML comments above each theorem.

## Domain Constraints

- holbuild only (no Holmake, no `holbuild run`/`repl`). Probe with scratch lemmas ending in `cheat` and rebuild.
- Never raise the tactic timeout (no `--tactic-timeout`, no holproject edits to it). A step that runs over 2.5 s must be split.
- No `TRY`/`ORELSE` around metis or other search.
- No `cheat` left anywhere you touched; no new axioms; no `let` in theorem statements.
- Do not edit definitions in `venom/codegen/defs`, `venom/analysis` or `venom/defs`.
- Keep helpers in `venom/codegen/proofs/` (in fnFrameTerminalScript.sml or a new `fnFrameTerminal*Script.sml`). Generalizing an existing genBlockSim lemma is fine if you add the general form as a new theorem and leave the old one in place.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Frame invariant | venom/codegen/defs/frameRelScript.sml | `frame_view`, `fn_frame_inv`, `closure_spill_byte` |
| OK-case lift (model to follow) | venom/codegen/proofs/genFrameSimScript.sml | `gen_inst_frame_sim`, `step_inst_frame_view`, `frame_view_safe_step` |
| Per-instruction sims | venom/codegen/proofs/genBlockSimScript.sml | `gen_inst_halt_sim` (:1366), `gen_inst_abort_sim` (:1601), `gen_inst_ok_sim` (:3211) |
| Stack-frame lifting | venom/codegen/proofs/asmFrameScript.sml, asmFrameHelpersScript.sml, deepDupFrameSimScript.sml | running assembly on `top ++ rest` |
| Plan relations | venom/codegen/defs/codegenRelScript.sml, contextCodegenRel (venom/codegen) | `venom_asm_rel`, `venom_asm_terminal_rel`, `context_memory_rel`, `source_memory_reads_disjoint`, `operand_val` |
| Planner | venom/codegen/defs/stackPlanGenScript.sml | `generate_inst_plan`, `emit_input_plan`, `revert_postamble` |
| Semantics | venom/semantics (venomExecSemantics), venom/codegen/defs/asmSemScript.sml | `step_inst`, `asm_steps` |

## Notes

- A statement check found both provable, but not by a direct lift: `gen_inst_halt_sim` wants RETURN's memory range below `ps.ps_alloc.sa_spill_base` (genBlockSim:1470), and `gen_inst_abort_sim` the same for REVERT (genBlockSim:3271). Here `source_memory_reads_disjoint` only says the range misses every spill region. `gen_inst_ok_sim` already handles that form.
- The two share most of their machinery: prove the lift once.

# TASK: a revert forwarding segment against the frame invariant (revert_forward_frame_sim)

## Meta
Status: planned
Priority: P0
Created: 2026-11-04
Location: venom/codegen/proofs/fnFrameStepsScript.sml (project root: this directory)

## Theorem Statement (FROZEN)

```sml
Theorem revert_forward_frame_sim:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn bb i j base ps vs as ops
   ps_end ra rest mem0.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\
    codegen_ready_fn fn /\ opaque_use_ok fn /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    revert_forward_pair bb i j /\ vs.vs_inst_idx = i /\
    LENGTH (get_params bb.bb_instructions) <= i /\
    EVERY (\inst. EVERY (\op. ~is_label_operand op) inst.inst_operands)
      (DROP i bb.bb_instructions) /\
    generated_plan_state_wf base ps /\
    (!k inst op.
       i <= k /\ get_instruction bb k = SOME inst /\
       MEM op (compute_operands inst) /\ is_var_operand op /\
       (!k' inst' x. i <= k' /\ k' < k /\ get_instruction bb k' = SOME inst' /\
                     op = Var x ==> ~MEM x inst'.inst_outputs) ==>
       MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (i - LENGTH (get_params bb.bb_instructions))
      (DROP i bb.bb_instructions) ps = SOME (ops, ps_end) /\
    (!off. ~MEM (SORestore off) ops /\ ~MEM (SOSpill off) ops) /\
    (!name. MEM (AsmOp name) (execute_plan cp.cp_initial_fmp ops) ==>
            IS_SOME (evm_opcode_byte name)) /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) ==>
    !a vs'. exec_block fuel ctx bb vs = Abort a vs' ==>
      ?n as'.
        ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
         (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
        venom_asm_terminal_rel vs' as'
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild --gcthreads 8 -j4 build fnFrameStepsTheory` passes with no failure, and `revert_forward_frame_sim` and any helper theory you add have no CHEAT.
2. No duplicate or near-duplicate lemmas: each helper exists once, in its most general form. Search the existing theories (below) before proving a fact.
3. New helper theories, if any, are registered in `holproject.toml` the way the existing ones are.

Scope: only `revert_forward_frame_sim`. `phi_prefix_frame_sim` (same theory) is other runs' work: leave its `cheat` alone and don't depend on it. Other cheated theorems in neighbouring theories (fnFrameSteps, fnFrameBoundary, fnPlanPlace, fnPlanLineage, venomToAsmProps) are other runs' work too.

**If the theorem is false as stated:**
- Produce a HOL4 counterexample (concrete terms, `EVAL`).
- State the tightest sufficient fix.
- Do NOT silently weaken the statement.

## Build

```
cd <this directory>
holbuild --gcthreads 8 -j4 build fnFrameStepsTheory
```

Always pass `--gcthreads 8` (a Poly/ML GC assertion fails without it on this host).

## Background

vyper-hol's Venom-to-EVM code generator plans each block's stack code and
lays the plans out with `codegen_assembly`. The block induction behind
`venomToAsmProps$gen_fn_frame_simulation` needs this theorem as one step.
The comment above the statement in `venom/codegen/proofs/fnFrameStepsScript.sml` says where it is used and
why it should hold. A statement check found it provable as stated.

## Domain Constraints

- holbuild only (no Holmake, no `holbuild run`/`repl`). Probe with scratch lemmas ending in `cheat` and rebuild.
- Never raise the tactic timeout (no `--tactic-timeout`, no holproject edits to it). A step that runs over 2.5 s must be split.
- No `TRY`/`ORELSE` around metis or other search.
- No `cheat` left anywhere you touched; no new axioms; no `let` in theorem statements.
- Do not edit definitions in `venom/codegen/defs`, `venom/analysis` or `venom/defs`.
- Keep helpers in `venom/codegen/proofs/`, in a new `fnFrameStepsRevertForwardScript.sml` that `fnFrameSteps` imports, so parallel runs on the same theory don't collide. Generalizing an existing lemma is fine if you add the general form as a new theorem and leave the old one in place; making an existing `[local]` lemma public is fine.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Frame invariant | venom/codegen/defs/frameRelScript.sml | `fn_frame_inv`, `frame_view` |
| Proved siblings (model to follow) | venom/codegen/proofs/genFrameSimScript.sml, fnFrameTerminalScript.sml (+ fnFrameTerminalPrep/Halt/Abort) | `gen_inst_frame_sim`, `gen_inst_abort_frame_sim` (REVERT, RETURNDATACOPY fault cases) |
| Per-instruction sims | venom/codegen/proofs/genBlockSimScript.sml | REVERT / RETURNDATACOPY steps |
| Revert forwarding | venom/defs, venom/codegen | `in_revert_forward`, `revert_forward_pair`, `revert_forward_at` (rg for them) |
| Planner | venom/codegen/defs/stackPlanGenScript.sml | `generate_block_plan`, `generate_inst_plan` |

## Notes

- Other runs are proving the sibling theorems in parallel on other branches; don't rely on them.

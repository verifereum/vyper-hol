# TASK: the entry block's parameter prefix against the frame invariant, with the parameter-count bound (entry_params_frame_sim)

## Meta
Status: planned
Priority: P0
Created: 2026-11-04
Location: venom/codegen/proofs/fnFrameBoundaryScript.sml (project root: this directory)

## Theorem Statement (FROZEN)

```sml
Theorem entry_params_frame_sim:
  !fuel ctx cp lo o2pc prog liveness fn ch growth spill_base lbl_ctr ps0
   param_ops ps1 r vs as ra rest.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    liveness = liveness_analyze fn /\
    codegen_ready_fn fn /\ retpc_shape_ok fn /\ opaque_use_ok fn /\
    ps0 = init_cleanup_plan_state ch growth spill_base lbl_ctr /\
    prepare_params_plan liveness fn ps0 = (param_ops, ps1) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= spill_base /\
    ps1.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    (!off. MEM (SOSpill off) param_ops ==> off < dimword (:256)) /\
    LENGTH (get_params (HD fn.fn_blocks).bb_instructions) < dimword (:256) /\
    fn_entry_state_rel cp fn vs as ra rest /\
    asm_block_at prog as.as_pc
      (execute_plan cp.cp_initial_fmp
         (SOLabel (HD fn.fn_blocks).bb_label :: param_ops))
    ==>
    ?n as' vs_p.
      asm_steps lo o2pc prog n as = AsmOK as' /\
      as'.as_pc = as.as_pc +
        LENGTH (execute_plan cp.cp_initial_fmp
                  (SOLabel (HD fn.fn_blocks).bb_label :: param_ops)) /\
      exec_block fuel ctx (HD fn.fn_blocks) (vs with vs_inst_idx := 0) =
        exec_block fuel ctx (HD fn.fn_blocks) vs_p /\
      vs_p.vs_inst_idx = LENGTH (get_params (HD fn.fn_blocks).bb_instructions) /\
      fn_frame_inv ctx cp lo fn ra rest as.as_memory ps1 vs_p as'
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild --gcthreads 8 -j4 build fnFrameBoundaryTheory` passes with no failure, and `entry_params_frame_sim` and any helper theory you add have no CHEAT.
2. No duplicate or near-duplicate lemmas: each helper exists once, in its most general form. Search the existing theories (below) before proving a fact.
3. New helper theories, if any, are registered in `holproject.toml` the way the existing ones are.

Scope: only `entry_params_frame_sim`. `gen_ret_frame_sim`, `gen_invoke_frame_sim` (same theory) are other runs' work: leave their `cheat` alone and don't depend on them. Other cheated theorems in neighbouring theories (fnFrameSteps, fnFrameBoundary, fnPlanPlace, fnPlanLineage, venomToAsmProps) are other runs' work too.

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
why it should hold.

An earlier run refuted the statement without the parameter-count premise
(`entry_params_frame_sim_counterexample` in
`venom/codegen/proofs/fnFrameBoundaryEntryParamsScript.sml`: more than
2^256 ordinary PARAMs make the word ordinal wrap). The premise
`LENGTH (get_params (HD fn.fn_blocks).bb_instructions) < dimword (:256)`
is now added. Keep that counterexample theorem; the positive lemmas in that
theory (parameter prefix execution, block skip boundary) are yours to
reuse, and new helpers go in the same file.

## Domain Constraints

- holbuild only (no Holmake, no `holbuild run`/`repl`). Probe with scratch lemmas ending in `cheat` and rebuild.
- Never raise the tactic timeout (no `--tactic-timeout`, no holproject edits to it). A step that runs over 2.5 s must be split.
- No `TRY`/`ORELSE` around metis or other search.
- No `cheat` left anywhere you touched; no new axioms; no `let` in theorem statements.
- Do not edit definitions in `venom/codegen/defs`, `venom/analysis` or `venom/defs`.
- Keep helpers in `venom/codegen/proofs/fnFrameBoundaryEntryParamsScript.sml` (it exists; `fnFrameBoundary` must import it), so parallel runs on the same theory don't collide. Generalizing an existing lemma is fine if you add the general form as a new theorem and leave the old one in place; making an existing `[local]` lemma public is fine.

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

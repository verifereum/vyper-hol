# TASK: INVOKE step of the frame-aware codegen simulation

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: venom/codegen/proofs/ (theorem in fnFrameBoundaryScript.sml; helpers in fnFrameBoundaryInvokeScript.sml)

## Theorem Statement (FROZEN)

In `venom/codegen/proofs/fnFrameBoundaryScript.sml`:

```sml
Theorem gen_invoke_frame_sim:
  !fuel rpolicy unit cp prog ctx lo o2pc Inv liveness dfg cfg fn inst
   next_liveness is_halting next_is_term bb_label base ps vs as ops ps' r ra
   rest mem0 nm arg_ops.
    ctx = unit.cu_context /\
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    generate_context_plan ctx = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\
    unit_shape_ok unit /\
    codegen_context_obligations Inv ctx cp /\
    reachability_closed Inv ctx /\
    MEM fn ctx.ctx_functions /\
    MEM fn.fn_name (fcg_analyze ctx).fcg_reachable /\
    (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
    Inv ctx fn inst vs /\ active_inst fn inst vs /\
    inst.inst_opcode = INVOKE /\
    inst.inst_operands = Label nm :: arg_ops /\
    ~vs.vs_call_ctx.cc_static /\
    (!f inst callee_name args callee.
       MEM f ctx.ctx_functions /\ MEM f.fn_name (fcg_analyze ctx).fcg_reachable /\
       MEM inst (fn_insts f) /\
       inst.inst_opcode = INVOKE /\
       inst.inst_operands = Label callee_name :: args /\
       lookup_function callee_name ctx.ctx_functions = SOME callee ==>
       fn_has_retpc callee) /\
    (!j. j < LENGTH ctx.ctx_functions /\ (EL j ctx.ctx_functions).fn_name = nm ==>
       ?off pc. FLOOKUP lo nm = SOME off /\ off < dimword (:256) /\
                FLOOKUP o2pc off = SOME pc /\
                asm_block_at prog pc
                  (execute_plan cp.cp_initial_fmp (EL j cp.cp_regions).sr_plan)) /\
    (* The callee's function-level simulation at this fuel. *)
    (!j callee rj cvs cas cra crest cpc.
       j < LENGTH ctx.ctx_functions /\ EL j ctx.ctx_functions = callee /\
       EL j cp.cp_regions = rj /\
       MEM callee.fn_name (fcg_analyze ctx).fcg_reachable /\
       (!l. FLOOKUP cvs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
       fn_entry_inv Inv ctx callee cvs /\
       ~cvs.vs_call_ctx.cc_static /\
       asm_block_at prog cas.as_pc (execute_plan cp.cp_initial_fmp rj.sr_plan) /\
       LENGTH (get_params (HD callee.fn_blocks).bb_instructions) < dimword (:256) /\
       fn_entry_state_rel cp callee cvs cas cra crest /\
       (fn_has_retpc callee ==> FLOOKUP o2pc (w2n cra) = SOME cpc) ==>
       (!vs'. run_blocks fuel ctx callee cvs = Halt vs' ==>
          ?n as'. asm_steps lo o2pc prog n cas = AsmHalt as' /\
                  venom_asm_terminal_rel vs' as') /\
       (!a vs'. run_blocks fuel ctx callee cvs = Abort a vs' ==>
          ?n as'. ((a = Revert_abort /\
                    asm_steps lo o2pc prog n cas = AsmRevert as') \/
                   (a = ExHalt_abort /\
                    asm_steps lo o2pc prog n cas = AsmFault as')) /\
                  venom_asm_terminal_rel vs' as') /\
       (!ret vs'. run_blocks fuel ctx callee cvs = IntRet ret vs' ==>
          ?n as'. asm_steps lo o2pc prog n cas = AsmOK as' /\
                  as'.as_pc = cpc /\
                  as'.as_stack = REVERSE ret.iret_values ++ crest /\
                  fn_return_state_rel ctx cp callee vs' cas as')) /\
    opaque_use_ok fn /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
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
    EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
                      inst.inst_outputs) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
          EVERY (\out. case op of Var x => x <> out | _ => T)
                inst.inst_outputs) /\
    prefix_spill_wf cp.cp_initial_fmp lo (FRONT ops) ps /\
    (!off. MEM (SORestore off) ops ==> off < dimword (:256)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) ==>
    (!vs'. step_inst fuel ctx inst vs = OK vs' ==>
       ?n as'.
         asm_steps lo o2pc prog n as = AsmOK as' /\
         fn_frame_inv ctx cp lo fn ra rest mem0 ps' vs' as' /\
         as'.as_pc = as.as_pc + LENGTH (execute_plan cp.cp_initial_fmp ops)) /\
    (!vs'. step_inst fuel ctx inst vs = Halt vs' ==>
       ?n as'. asm_steps lo o2pc prog n as = AsmHalt as' /\
               venom_asm_terminal_rel vs' as') /\
    (!a vs'. step_inst fuel ctx inst vs = Abort a vs' ==>
       ?n as'. ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
                (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
               venom_asm_terminal_rel vs' as')
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

Definitions it uses: `frameRel` (`fn_frame_inv`, `fn_entry_state_rel`, `fn_return_state_rel`, `frame_view`, `closure_spill_byte`, `shared_state_rel`, `fn_has_retpc`) in `venom/codegen/defs/frameRelScript.sml`; `contextCodegenRel` (`context_venom_asm_rel`, `reachability_closed`, `fn_entry_inv`, `active_inst`, `codegen_context_obligations`) in `venom/codegen/defs/contextCodegenRelScript.sml`; `step_inst` (INVOKE case), `setup_callee`, `merge_callee_state`, `bind_outputs`, `adopt_return_fmp` in `venom/defs/venomExecSemanticsScript.sml`; `generate_inst_plan`, `generate_regular_inst_plan`, `generate_emit_ops` (INVOKE case) in `venom/codegen/defs/stackPlanGenScript.sml`.

## Completion Criteria

1. `holbuild -j4 build fnFrameBoundaryTheory` passes at the default tactic timeout, and `gen_invoke_frame_sim` has no cheat (the build log for fnFrameBoundary shows no CHEAT; it is the only cheat in that theory).
2. The statement above is byte-for-byte unchanged.
3. Helper lemmas go in `venom/codegen/proofs/fnFrameBoundaryInvokeScript.sml` (already an ancestor of fnFrameBoundary), or in fnFrameBoundaryScript.sml itself. No new theory elsewhere, no edits to other existing theories.
4. No duplicate lemmas: search before adding one; reuse existing lemmas.

**If the theorem is false as stated:** produce a concrete counterexample, state the tightest fix, and stop. Do NOT weaken the statement.

## Build

```
holbuild -j4 build fnFrameBoundaryTheory
```

## Background

vyper-hol proves the Venom-to-EVM-assembly code generator correct. The function-level simulation (`venomToAsmProps$gen_fn_frame_simulation`) runs by induction over a function's blocks, with each instruction step preserving the frame invariant `fn_frame_inv`: the frame's own assembly stack above the caller's `rest`, the plan relations against the frame view, the context-wide memory relation, and every spill byte outside the frame's call-graph closure unchanged since the frame was entered (`mem0`). This theorem is the INVOKE (internal call) step. The callee's whole run is given as a hypothesis (the mutual induction hypothesis on fuel). Its siblings in the same theory, `gen_ret_frame_sim` (RET; helpers in `fnFrameBoundaryGenRetScript.sml`) and `entry_params_frame_sim` (helpers in `fnFrameBoundaryEntryParamsScript.sml`), are proved and are the closest models; `genFrameSim$gen_inst_frame_sim` is the ordinary-instruction step. The comments above the theorem and at the top of `fnFrameBoundaryInvokeScript.sml` explain why it should hold.

## Domain Constraints

- Don't edit anything under `semantics/`, `frontend/`, `lowering/`, `venom/defs/`, `venom/compiler/`, `venom/passes/`, `venom/codegen/defs/`, or any existing theory other than `fnFrameBoundaryScript.sml` (proof of this theorem only) and `fnFrameBoundaryInvokeScript.sml`. Lemmas you'd like in a low-level theory go in the leaf instead.
- No new definitions, axioms or cheats; no `TRY`/`ORELSE` around `metis_tac` or other search (select goals with `>-`, `>~`, `>|`); never raise the tactic timeout. Keep each proof under ~50 lines; split into helper lemmas.
- Don't depend on generated variable names; use `rename1`.
- `fnBoundaryProps` and `venomToAsmProps` are downstream of fnFrameBoundary: don't import them (copy nothing from them either; reprove the one-liners you need).

## Available Resources

| Resource | Location | Description |
|---|---|---|
| Target theory | `venom/codegen/proofs/fnFrameBoundaryScript.sml` | the theorem, sibling proofs `gen_ret_frame_sim`, `entry_params_frame_sim` |
| Helper leaf | `venom/codegen/proofs/fnFrameBoundaryInvokeScript.sml` | put helpers here; header comment has the statement-check notes |
| RET helpers | `venom/codegen/proofs/fnFrameBoundaryGenRetScript.sml` | `ret_plan_decompose`, `ret_frame_prefix` (prefix brings operands to the top, lifted below the frame) |
| Entry helpers | `venom/codegen/proofs/fnFrameBoundaryEntryParamsScript.sml` | popmany / optimistic swap against the context relation, `entry_context_popmany_outside_closure` |
| Ordinary step | `venom/codegen/proofs/genFrameSimScript.sml` | `gen_inst_frame_sim`, `frame_local_result`, `venom_asm_rel_context` (local→context memory) |
| Prefix sims | `venom/codegen/proofs/preparedPrefixSimScript.sml`, `generatedPrefixSimScript.sml`, `prefixSimScript.sml`, `strongPrefixSimScript.sml`, `planAlignScript.sml` | `selected_prefix_prepared_sim` (has `opc <> INVOKE`; `emit_one_input_ss_align` in planAlign shows the label-free INVOKE case), `regular_postfix_alloc_frame` |
| Postfix sims | `venom/codegen/proofs/regularPostfixSimScript.sml`, `cleanOpsSimScript.sml`, `planAlignScript.sml` | `optimistic_swap_plan_postfix_sim_structural`, `venom_asm_rel_release_dead_spills`, `popmany_plan_contiguous_sim`, `popmany_plan_top_two_sim` |
| Frame lifting | `venom/codegen/proofs/asmFrameScript.sml`, `fnFrameTerminalPrepScript.sml` | `asm_steps_frame`, `fn_frame_inv_local_state` |
| Asm run composition | `venom/codegen/proofs/blockSimHelpersScript.sml` | `asm_steps_compose_ok/_halt/_revert/_fault` |
| Alloc monotonicity | `venom/codegen/proofs/allocMonoScript.sml` | spill base fixed, next offset grows |
| Call graph | `venom/analysis/fcg/defs/fcgDefsScript.sml`, `venom/analysis/fcg/proofs/fcgPostorderScript.sml` | `fcg_path`, `fcg_reachable_direct_callee`, `reachable_fcg_acyclic_no_reachable_cycle` |
| Shape / layout | `venom/codegen/defs/unitShapeDefsScript.sml`, `venom/defs/fmpWfDefsScript.sml`, `venom/defs/callLayoutDefsScript.sml`, `venom/codegen/defs/stackPlanTypesScript.sml` | `fn_shape_ok`/`label_positions_ok`, `opaque_use_ok`, `invoke_layout_wf`, `invoke_input_arity_ok`, `canonical_param_prefix`, `ordered_spill_regions` |
| Asm semantics | `venom/codegen/defs/asmSemScript.sml` | `asm_steps`, `asm_jump` |

## Notes

- The frozen statement was updated on 2026-11-05 (branch skeleton change): the no-GAS context premise was dropped, `~vs.vs_call_ctx.cc_static` added, and the callee hypothesis now also takes `~cvs.vs_call_ctx.cc_static` and `LENGTH (get_params (HD callee.fn_blocks).bb_instructions) < dimword (:256)`. Both new callee premises follow from the caller's premises (`setup_callee` keeps the call context; INVOKE's argument count is at most 16, and the callee has one more parameter). Lemmas already proved that only depend on the old statement's premises remain valid. A second update scoped the callee return-PC premise to reachable callers (`MEM f.fn_name (fcg_analyze ctx).fcg_reachable`), a weakening; fn itself is reachable.

- The dependency cone of fnFrameBoundary is prebuilt in this worktree; `holbuild -j4 build fnFrameBoundaryInvokeTheory` builds just the helper leaf.

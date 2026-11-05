(*
 * clean_stack_plan's cleanup code against frameRel$fn_frame_inv.
 *
 * cleanOpsSim$clean_ops_sim simulates the cleanup against the whole-stack
 * relation venom_asm_rel, for stacks of at most 17 entries.  This is the
 * frame version, for any depth: the frame's own stack above the caller's
 * rest, spills inside the frame's region, and a stack that may already
 * repeat dead_stack_marker (generated_plan_state_wf_marked).
 *
 * TOP-LEVEL:
 *   clean_stack_plan_frame_sim - CHEATED (a piece helper)
 *)

Theory fnFrameCleanStack
Ancestors
  fnPlanPrefix cleanOpsSim genFrameSim frameRel contextCodegenRel codegenRel
  planSpillBounds stackPlanGen stackPlanTypes planExec asmSem

(* Used by fnFrameSinglePred$single_pred_prefix_frame_sim, for the cleanup
   a single-predecessor block runs before its instructions.

   Why it should hold: the cleanup either emits nothing and only replaces
   stack entries by dead_stack_marker (mark_dead_stack, or the whole stack
   when no variable is needed), which plan_stack_rel accepts at any slot, or
   pops variables by popmany_plan (swaps to the top, spilling when deeper
   than 16, then POP).  Those moves keep every remaining slot's value;
   spills use fresh offsets inside the frame's region (the region premise
   on ps2 and the allocator's monotonicity), so the caller's rest, the
   context memory relation and spill bytes outside the frame's closure are
   unchanged.  The surviving slots are a subset of the old ones plus
   markers. *)
Theorem clean_stack_plan_frame_sim:
  !ctx cp lo o2pc prog liveness cfg fn bb base ps vs as clean_ops ps2
   r ra rest mem0.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    generated_plan_state_wf_marked base ps /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    clean_stack_plan liveness cfg fn bb ps = (clean_ops, ps2) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps2.ps_alloc.sa_spill_base /\
    ps2.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    (!off. MEM (SOSpill off) clean_ops \/ MEM (SORestore off) clean_ops ==>
           off < dimword (:256)) /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp clean_ops)
    ==>
    ?n as2.
      asm_steps lo o2pc prog n as = AsmOK as2 /\
      as2.as_pc = as.as_pc + LENGTH (execute_plan cp.cp_initial_fmp clean_ops) /\
      fn_frame_inv ctx cp lo fn ra rest mem0 ps2 vs as2 /\
      generated_plan_state_wf_marked base ps2 /\
      (!op. MEM op ps2.ps_stack \/ op IN FDOM ps2.ps_spilled ==>
            op = dead_stack_marker \/ MEM op ps.ps_stack \/
            op IN FDOM ps.ps_spilled)
Proof
  cheat
QED

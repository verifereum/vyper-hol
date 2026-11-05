(*
 * The planner's stack at a join block's entry.
 *
 * TOP-LEVEL (CHEATED, a piece):
 *   lineage_entry_join_stack — the lineage entry state of a join is a
 *                              dead_stack_marker prefix followed by exactly
 *                              the edge's live-in variables
 *)

Theory fnPlanLineageJoin
Ancestors
  fnLineageInv fnPlanLineage stackPlanGen stackPlanTypes livenessDefs dfgDefs cfgDefs
  cfgAnalysisProps venomWf venomInst list rich_list simplifyCfgDefs

Theorem join_predecessor_jmp_shape:
  !fn pred pb bb.
    codegen_ready_fn fn /\
    lookup_block pred fn.fn_blocks = SOME pb /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    MEM bb.bb_label (cfg_succs_of (cfg_analyze fn) pred) /\
    LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label) <> 1 ==>
    pb.bb_label = pred /\ pb.bb_instructions <> [] /\
    (LAST pb.bb_instructions).inst_opcode = JMP
Proof
  rpt gen_tac >> strip_tac >>
  imp_res_tac lookup_block_member_label >>
  `MEM pred (cfg_preds_of (cfg_analyze fn) bb.bb_label)` by
    metis_tac[cfg_edge_symmetry_uncond] >>
  `1 < LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label)` by
    (`cfg_preds_of (cfg_analyze fn) bb.bb_label <> []` by
       (strip_tac >> gvs[]) >>
     `LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label) <> 0` by
       metis_tac[LENGTH_NIL] >> decide_tac) >>
  gvs[codegen_ready_fn_def, block_entries_ready_def, EVERY_MEM] >>
  qpat_x_assum `!blk. MEM blk fn.fn_blocks ==> (_ \/ _)` (qspec_then `bb` mp_tac) >>
  simp[] >> strip_tac >>
  first_x_assum (qspec_then `pb.bb_label` mp_tac) >>
  simp[NULL_EQ]
QED

Theorem join_predecessor_single_successor:
  !fn pred pb bb.
    codegen_ready_fn fn /\
    lookup_block pred fn.fn_blocks = SOME pb /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    MEM bb.bb_label (cfg_succs_of (cfg_analyze fn) pred) /\
    LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label) <> 1 ==>
    (LAST pb.bb_instructions).inst_operands = [Label bb.bb_label] /\
    cfg_succs_of (cfg_analyze fn) pred = [bb.bb_label]
Proof
  rpt gen_tac >> strip_tac >>
  drule_all join_predecessor_jmp_shape >> strip_tac >>
  imp_res_tac lookup_block_member_label >>
  `wf_function fn /\ fn_inst_wf fn` by
    gvs[codegen_ready_fn_def] >>
  `inst_wf (LAST pb.bb_instructions)` by
    (gvs[fn_inst_wf_def] >> first_x_assum irule >>
     qexists_tac `pb` >> simp[] >>
     Cases_on `pb.bb_instructions` >> gvs[MEM_LAST]) >>
  `cfg_succs_of (cfg_analyze fn) pred = bb_succs pb` by
    metis_tac[cfg_analyze_preserves_bb_succs] >>
  gvs[inst_wf_def] >>
  Cases_on `pb.bb_instructions` >>
  gvs[bb_succs_def, get_successors_def, is_terminator_def,
      venomStateTheory.get_label_def, nub_def]
QED

(* Used by fnFrameStepsPhi for phi_prefix_frame_sim: the PHI prefix reads
   pred's PHI operands from the top of the stack, and nothing below them
   may be a stale variable whose value the PHIs change.

   Why it should hold: every predecessor of a join ends in a JMP
   (block_entries_ready), whose plan reorders the stack so that it ends in
   the target's live-in variables (join_reached).  Below them only
   dead_stack_marker entries remain: the planner pops dead outputs,
   consumes an operand at its last use, and clean_stack_plan pops or marks
   dead what a single-predecessor block inherits but doesn't need.  This is
   the static lineage_state invariant the comment on
   fnPlanLineage$lineage_state_block_plan describes (a marker prefix, then
   distinct variables that together are the live set at the edge). *)
Theorem lineage_entry_join_stack:
  !liveness dfg cfg fn ch growth spill_base lbl_ctr pred bb ps.
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    LENGTH (cfg_preds_of cfg bb.bb_label) <> 1 /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) pred bb.bb_label ps ==>
    ?pre. ps.ps_stack = pre ++ MAP Var (input_vars_from pred bb.bb_instructions
                                         (live_vars_at liveness bb.bb_label 0)) /\
          EVERY (\op. op = dead_stack_marker) pre
Proof
  cheat
QED

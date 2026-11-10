(*
 * The planner's stack at a join block's entry.
 *
 * TOP-LEVEL (proved using the permitted lineage inventory admission):
 *   lineage_entry_join_stack — the lineage entry state of a join is a
 *                              dead_stack_marker prefix followed by exactly
 *                              the edge's live-in variables
 *)

Theory fnPlanLineageJoin
Ancestors
  fnPlanPrefix fnLineageInv fnPlanLineage stackPlanGen stackPlanTypes livenessDefs dfgDefs cfgDefs
  cfgAnalysisProps venomWf venomInst list rich_list simplifyCfgDefs
  livenessConvergenceProofs livenessBlockProofs livenessTransferProofs

Theorem lineage_state_cfg_path:
  !lv dfg cfg fn ps0 lbl ps.
    lineage_state lv dfg cfg fn ps0 lbl ps ==>
    ?entry. fn_entry_label fn = SOME entry /\ cfg_path cfg entry lbl
Proof
  rpt gen_tac >> qid_spec_tac `ps` >> qid_spec_tac `lbl` >>
  ho_match_mp_tac lineage_state_ind >> conj_tac
  >- (rpt strip_tac >> qexists_tac `lbl` >>
      simp[cfg_path_def]) >>
  rpt strip_tac >> qexists_tac `entry` >> simp[] >>
  gvs[cfg_path_def] >>
  irule relationTheory.RTC_TRANS >> qexists_tac `lbl` >>
  simp[] >> irule relationTheory.RTC_SINGLE >> simp[]
QED

Theorem lineage_state_reachable:
  !lv dfg fn ps0 lbl ps.
    wf_function fn /\
    lineage_state lv dfg (cfg_analyze fn) fn ps0 lbl ps ==>
    cfg_reachable_of (cfg_analyze fn) lbl
Proof
  rpt strip_tac >> drule lineage_state_cfg_path >> strip_tac >>
  gvs[fn_entry_label_def, AllCaseEqs()] >>
  metis_tac[cfg_analyze_semantic_reachability]
QED

Theorem single_successor_exit_live:
  !fn pred pb bb v.
    wf_function fn /\ cfg_reachable_of (cfg_analyze fn) pred /\
    lookup_block pred fn.fn_blocks = SOME pb /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    cfg_succs_of (cfg_analyze fn) pred = [bb.bb_label] /\
    MEM v (live_vars_at (liveness_analyze fn) pred
                          (LENGTH pb.bb_instructions)) ==>
    MEM v (input_vars_from pred bb.bb_instructions
             (live_vars_at (liveness_analyze fn) bb.bb_label 0))
Proof
  rpt strip_tac >> drule_all liveness_recompute_convergence >>
  simp[liveness_instrs_def, liveness_out_def, same_vars_def,
       EVERY_MEM, mem_foldl_list_union, list_union_mem, liveness_edge_transfer_def,
       live_vars_at_def, liveness_analyze_def] >>
  gvs[live_vars_at_def, liveness_analyze_def] >> metis_tac[]
QED

Theorem successful_jmp_join_reached:
  generate_inst_plan lv dfg cfg fn inst next_live halting next_term lbl ps =
    SOME (ops, ps') /\ inst.inst_opcode = JMP ==>
  join_reached lv fn lbl inst ps'
Proof
  strip_tac >>
  gvs[generate_inst_plan_def, is_pre_codegen_opcode_def, is_param_opcode_def,
      AllCaseEqs()]
QED

Theorem successful_insts_last_jmp:
  !insts i ps ops ps'.
    insts <> [] /\ (LAST insts).inst_opcode = JMP /\
    generate_block_insts_plan lv dfg cfg fn lbl halting np blen i insts ps =
      SOME (ops, ps') ==>
    join_reached lv fn lbl (LAST insts) ps'
Proof
  Induct_on `insts` >- simp[] >>
  rpt gen_tac >> Cases_on `insts = []`
  >- (gvs[generate_block_insts_plan_def, AllCaseEqs()] >>
      metis_tac[successful_jmp_join_reached]) >>
  simp[generate_block_insts_plan_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[LAST_DEF] >> first_x_assum irule >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem successful_block_jmp_suffix:
  generate_block_plan lv dfg cfg fn pb ps = SOME (ops, ps') /\
  pb.bb_instructions <> [] /\
  (LAST pb.bb_instructions).inst_opcode = JMP /\
  (LAST pb.bb_instructions).inst_operands = [Label target] /\
  lookup_block target fn.fn_blocks = SOME bb ==>
  ?pre. ps'.ps_stack = pre ++ MAP Var
    (input_vars_from pb.bb_label bb.bb_instructions (live_vars_at lv target 0))
Proof
  strip_tac >> drule_all non_param_insts_last_jmp >> strip_tac >>
  qpat_x_assum `generate_block_plan _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_block_plan_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  `(LAST (non_param_insts pb)).inst_opcode = JMP` by simp[] >>
  drule_all successful_insts_last_jmp >>
  simp[join_reached_def, join_target_ops_def] >> strip_tac >>
  metis_tac[]
QED

Theorem distinct_filtered_prefix_markers:
  ALL_DISTINCT (FILTER (\x. x <> marker) (pre ++ suffix)) /\
  (!x. MEM x pre /\ x <> marker ==> MEM x suffix) ==>
  EVERY (\x. x = marker) pre
Proof
  simp[FILTER_APPEND_DISTRIB, ALL_DISTINCT_APPEND, MEM_FILTER, EVERY_MEM] >>
  metis_tac[]
QED

(* Used by fnFrameStepsPhi for phi_prefix_frame_sim: the PHI prefix reads
   pred's PHI operands from the top of the stack, and nothing below them
   may be a stale variable whose value the PHIs change.

   Every predecessor of a join ends in a JMP (block_entries_ready), whose
   successful plan ends in the target's live-in variables (join_reached).
   The JMP has only one successor, so liveness convergence puts every
   live-out variable in that suffix.  The permitted lineage inventory
   supplies distinctness of the non-marker slots and says each is live-out.
   A non-marker prefix slot would therefore also occur in the suffix,
   contradicting distinctness. *)
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
  rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_assum `lineage_entry _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [lineage_entry_def]) >>
  rename1 `lookup_block pred fn.fn_blocks = SOME pb` >>
  drule_all (SRULE [] lineage_entry_inventory) >> strip_tac >>
  drule_all join_predecessor_jmp_shape >> strip_tac >>
  drule_all join_predecessor_single_successor >> strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  drule_all lineage_state_reachable >> strip_tac >>
  drule_all successful_block_jmp_suffix >> strip_tac >>
  gvs[] >>
  qpat_x_assum `generated_plan_state_wf_marked _ _` mp_tac >>
  simp[fnPlanPrefixTheory.generated_plan_state_wf_marked_def] >>
  strip_tac >> irule distinct_filtered_prefix_markers >>
  goal_assum (drule_at Any) >> rpt strip_tac >>
  qpat_x_assum `!op. _ ==> ?v. _` (qspec_then `x` mp_tac) >>
  simp[] >> strip_tac >> gvs[MEM_MAP] >>
  irule single_successor_exit_live >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

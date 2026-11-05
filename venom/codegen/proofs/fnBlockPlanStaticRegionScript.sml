Theory fnBlockPlanStaticRegion
Ancestors
  fnBlockPlanStaticPromises fnBlockPlanStaticInventory fnPlanLineage fnPlanLineageJoin
  fnLineageInv fnPlanPrefix list stackPlanGen fnFrameBoundaryGenRet

Theorem dfs_saved_parent_origin_mutual[local]:
  (!wl visited pg.
    dfs_aux_call lv dfg cfg fn ps0 wl visited pg ==>
    dfs_aux_call lv dfg cfg fn ps0 wl visited pg) /\
  (!ss sp succs visited pg.
    dfs_succs_call lv dfg cfg fn ps0 ss sp succs visited pg ==>
    dfs_succs_call lv dfg cfg fn ps0 ss sp succs visited pg /\
    ?lbl rest seen pin bb bops pout.
      dfs_aux_call lv dfg cfg fn ps0 (lbl::rest) seen pin /\
      ~MEM lbl seen /\ lookup_block lbl fn.fn_blocks = SOME bb /\
      generate_block_plan lv dfg cfg fn bb pin = SOME (bops,pout) /\
      ss = pout.ps_stack /\ sp = pout.ps_spilled /\
      (!s. MEM s succs ==> MEM s (cfg_succs_of cfg lbl)))
Proof
  ho_match_mp_tac dfs_aux_call_ind >> rpt conj_tac
  >- metis_tac[dfs_aux_call_entry]
  >- metis_tac[dfs_aux_call_visited]
  >- metis_tac[dfs_aux_call_missing]
  >- (rpt gen_tac >> strip_tac >> conj_tac
      >- metis_tac[dfs_aux_call_succs]
      >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[])
  >- metis_tac[dfs_aux_call_rest]
  >- (rpt strip_tac >> irule dfs_aux_call_branch >>
      goal_assum (drule_at Any) >> simp[])
  >> rpt gen_tac >> strip_tac >> conj_tac
  >- metis_tac[dfs_aux_call_sibling]
  >> metis_tac[listTheory.MEM]
QED

Theorem dfs_saved_parent_origin:
  dfs_succs_call lv dfg cfg fn ps0 ss sp succs visited pg ==>
  ?lbl rest seen pin bb bops pout.
    dfs_aux_call lv dfg cfg fn ps0 (lbl::rest) seen pin /\
    ~MEM lbl seen /\ lookup_block lbl fn.fn_blocks = SOME bb /\
    generate_block_plan lv dfg cfg fn bb pin = SOME (bops,pout) /\
    ss = pout.ps_stack /\ sp = pout.ps_spilled /\
    (!s. MEM s succs ==> MEM s (cfg_succs_of cfg lbl))
Proof
  metis_tac[dfs_saved_parent_origin_mutual]
QED

Theorem dfs_saved_parent_block_origin:
  dfs_succs_call lv dfg cfg fn ps0 ss sp succs visited pg ==>
  ?lbl pin bb bops pout.
    dfs_block_state lv dfg cfg fn ps0 lbl pin /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    generate_block_plan lv dfg cfg fn bb pin = SOME (bops,pout) /\
    ss = pout.ps_stack /\ sp = pout.ps_spilled /\
    (!s. MEM s succs ==> MEM s (cfg_succs_of cfg lbl))
Proof
  strip_tac >> drule dfs_saved_parent_origin >>
  simp[dfs_block_state_def] >> metis_tac[]
QED

Theorem regional_lineage_join_input_physical:
  !liveness dfg cfg fn ch growth spill_base lbl_ctr pred bb ps v.
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    LENGTH (cfg_preds_of cfg bb.bb_label) <> 1 /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) pred bb.bb_label ps /\
    MEM v (input_vars_from pred bb.bb_instructions
              (live_vars_at liveness bb.bb_label 0)) ==>
    MEM (Var v) ps.ps_stack
Proof
  rpt gen_tac >> strip_tac >> drule_all lineage_entry_join_stack >>
  strip_tac >> gvs[listTheory.MEM_APPEND, listTheory.MEM_MAP] >> metis_tac[]
QED

Theorem regional_lineage_join_target_distinct:
  !liveness dfg cfg fn ch growth spill_base lbl_ctr pred pred_bb bb ps.
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    lookup_block pred fn.fn_blocks = SOME pred_bb /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    LENGTH (cfg_preds_of cfg bb.bb_label) <> 1 /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) pred bb.bb_label ps ==>
    ALL_DISTINCT (MAP Var (input_vars_from pred bb.bb_instructions
                            (live_vars_at liveness bb.bb_label 0)))
Proof
  rpt strip_tac >>
  drule_all lineage_entry_inventory >> strip_tac >>
  drule_all lineage_entry_join_stack >> strip_tac >>
  gvs[generated_plan_state_wf_marked_def, FILTER_APPEND_DISTRIB,
      dead_stack_marker_def, EVERY_FILTER, ALL_DISTINCT_APPEND] >>
  `FILTER (\op. op <> Label "")
     (MAP Var (input_vars_from pred bb.bb_instructions
       (live_vars_at (liveness_analyze fn) bb.bb_label 0))) =
   MAP Var (input_vars_from pred bb.bb_instructions
       (live_vars_at (liveness_analyze fn) bb.bb_label 0))`
    by simp[FILTER_EQ_ID, EVERY_MAP] >>
  gvs[]
QED

Theorem dfs_lineage_branch[local]:
  lineage_state lv dfg cfg fn ps0 lbl pin /\
  dfs_block_state lv dfg cfg fn ps0 lbl pin /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  generate_block_plan lv dfg cfg fn bb pin = SOME (bops,pout) /\
  MEM succ (cfg_succs_of cfg lbl) /\
  dfs_block_state lv dfg cfg fn ps0 succ pg ==>
  lineage_state lv dfg cfg fn ps0 succ
    (pg with <| ps_stack := pout.ps_stack; ps_spilled := pout.ps_spilled |> )
Proof
  strip_tac >> irule lineage_state_step >> simp[] >>
  goal_assum (drule_at (Pat `lineage_state _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `lookup_block _ _ = _`)) >>
  goal_assum (drule_at (Pat `generate_block_plan _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`pin.ps_cleanup_height`, `pin.ps_cleanup_promised`] >>
  simp[]
QED

Theorem dfs_lineage_mutual[local]:
  (!wl visited pg.
    dfs_aux_call lv dfg cfg fn ps0 wl visited pg ==>
    dfs_aux_call lv dfg cfg fn ps0 wl visited pg /\
    !lbl rest. wl = lbl::rest ==>
      rest = [] /\ (~MEM lbl visited ==>
        lineage_state lv dfg cfg fn ps0 lbl pg)) /\
  (!ss sp succs visited pg.
    dfs_succs_call lv dfg cfg fn ps0 ss sp succs visited pg ==>
    dfs_succs_call lv dfg cfg fn ps0 ss sp succs visited pg /\
    ?lbl pin bb bops pout.
      lineage_state lv dfg cfg fn ps0 lbl pin /\
      dfs_block_state lv dfg cfg fn ps0 lbl pin /\
      lookup_block lbl fn.fn_blocks = SOME bb /\
      generate_block_plan lv dfg cfg fn bb pin = SOME (bops,pout) /\
      ss = pout.ps_stack /\ sp = pout.ps_spilled /\
      (!s. MEM s succs ==> MEM s (cfg_succs_of cfg lbl)))
Proof
  ho_match_mp_tac dfs_aux_call_ind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[dfs_aux_call_entry, lineage_state_entry])
  >- (rpt gen_tac >> strip_tac >> gvs[] >>
      metis_tac[dfs_aux_call_visited])
  >- (rpt gen_tac >> strip_tac >> gvs[] >>
      metis_tac[dfs_aux_call_missing])
  >- (rpt gen_tac >> strip_tac >> conj_tac
      >- metis_tac[dfs_aux_call_succs]
      >> goal_assum (drule_at (Pat `lookup_block _ _ = _`)) >>
      goal_assum (drule_at (Pat `generate_block_plan _ _ _ _ _ _ = _`)) >>
      simp[dfs_block_state_def] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> gvs[] >>
      metis_tac[dfs_aux_call_rest])
  >- (rpt gen_tac >> strip_tac >> conj_asm1_tac
      >- metis_tac[dfs_aux_call_branch]
      >> rpt strip_tac >> gvs[] >>
      rename1 `~MEM next visited` >>
      `dfs_block_state lv dfg cfg fn ps0 next
         (pg with <| ps_stack := pout.ps_stack;
                     ps_spilled := pout.ps_spilled |>)`
        by (simp[dfs_block_state_def] >> metis_tac[]) >>
      `MEM next (cfg_succs_of cfg lbl)` by metis_tac[] >>
      drule_all dfs_lineage_branch >> simp[])
  >> rpt gen_tac >> strip_tac >> conj_tac
  >- metis_tac[dfs_aux_call_sibling]
  >> metis_tac[MEM]
QED

Theorem dfs_block_state_lineage_state:
  dfs_block_state lv dfg cfg fn ps0 lbl ps ==>
  lineage_state lv dfg cfg fn ps0 lbl ps
Proof
  simp[dfs_block_state_def] >> metis_tac[dfs_lineage_mutual]
QED

Theorem dfs_edge_lineage_entry:
  dfs_block_state lv dfg cfg fn ps0 pred pin /\
  lookup_block pred fn.fn_blocks = SOME pred_bb /\
  generate_block_plan lv dfg cfg fn pred_bb pin = SOME (ops,pout) /\
  MEM succ (cfg_succs_of cfg pred) /\
  dfs_block_state lv dfg cfg fn ps0 succ ps_succ ==>
  lineage_entry lv dfg cfg fn ps0 pred succ
    (ps_succ with <| ps_stack := pout.ps_stack;
                    ps_spilled := pout.ps_spilled |>)
Proof
  strip_tac >>
  `lineage_state lv dfg cfg fn ps0 pred pin`
    by metis_tac[dfs_block_state_lineage_state] >>
  simp[lineage_entry_def] >>
  goal_assum (drule_at (Pat `lineage_state _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `generate_block_plan _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`pin.ps_cleanup_height`, `pin.ps_cleanup_promised`] >>
  simp[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem regional_dfs_join_target_distinct:
  !liveness dfg cfg fn ch growth spill_base lbl_ctr pred pred_bb bb pin
   ops pout ps_succ.
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    lookup_block pred fn.fn_blocks = SOME pred_bb /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    LENGTH (cfg_preds_of cfg bb.bb_label) <> 1 /\
    dfs_block_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) pred pin /\
    generate_block_plan liveness dfg cfg fn pred_bb pin = SOME (ops,pout) /\
    MEM bb.bb_label (cfg_succs_of cfg pred) /\
    dfs_block_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) bb.bb_label ps_succ ==>
    ALL_DISTINCT (MAP Var (input_vars_from pred bb.bb_instructions
                            (live_vars_at liveness bb.bb_label 0)))
Proof
  rpt gen_tac >> strip_tac >> drule_all dfs_edge_lineage_entry >>
  strip_tac >> drule_all regional_lineage_join_target_distinct >> simp[]
QED

Theorem regional_ret_operand_support_empty:
  inst.inst_opcode = RET /\ inst.inst_outputs = [] /\
  ALL_DISTINCT ps.ps_stack /\
  DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled) /\
  LENGTH (compute_operands inst) <= 16 /\
  EVERY (\op. ?v. op = Var v /\ MEM op (compute_operands inst)) ps.ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan RET (compute_operands inst) [] ps)).ps_stack /\
  generate_inst_plan lv dfg cfg fn inst [] halting next_term lbl ps = SOME (ops,ps')
  ==> ps'.ps_stack = []
Proof
  strip_tac >>
  Cases_on `emit_input_plan RET (compute_operands inst) [] ps` >>
  rename1 `emit_input_plan _ _ _ _ = (iops,mid)` >>
  Cases_on `reorder_plan dfg (compute_operands inst) mid` >>
  rename1 `reorder_plan _ _ _ = (rops,arranged)` >>
  `EVERY (\op. ?v. op = Var v /\ (MEM v [] \/ MEM op (compute_operands inst)))
     ps.ps_stack` by simp[] >>
  `PERM (compute_operands inst) (compute_operands inst)` by simp[] >>
  `LENGTH (compute_operands inst) <= LENGTH mid.ps_stack` by gvs[] >>
  drule_all inventory_regular_core_live_support_unconditional >>
  simp[] >> strip_tac >>
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_inst_plan_def, is_pre_codegen_opcode_def,
       venomInstTheory.is_param_opcode_def, generate_regular_inst_plan_def,
       venomEffectsTheory.is_commutative_def, generate_emit_ops_def,
       asmIRTheory.venom_to_evm_name_def] >>
  strip_tac >> gvs[release_dead_spills_stack]
QED

Theory fnBlockPlanStaticRegion
Ancestors
  fnBlockPlanStaticPromises fnBlockPlanStaticInventory fnPlanLineage fnPlanLineageJoin
  fnLineageInv fnPlanPrefix list stackPlanGen fnFrameBoundaryGenRet codegenReadyCompute
  fnBlockPlanStaticOffsetLive livenessProofs livenessTransferProofs venomWf venomExecProofs rich_list
  removeUnusedSsaProofs venomInst cfgNormSupplyProofs cfgNormBase
  fnFrameBoundaryEntryParams stackModel genBlockSim fnLineageStatic fnBlockPlanStaticFacts
  dfgAnalysisProps dfgDefs allocaRemapSSA stackPlanOps planSpillBounds doSwapSim pair callLayoutDefs

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

Theorem dfs_call_reachable_mutual[local]:
  (!wl visited pg.
    dfs_aux_call lv dfg (cfg_analyze fn) fn ps0 wl visited pg ==>
    codegen_ready_fn fn ==> EVERY (fn_reachable fn) wl) /\
  (!ss sp succs visited pg.
    dfs_succs_call lv dfg (cfg_analyze fn) fn ps0 ss sp succs visited pg ==>
    codegen_ready_fn fn ==> EVERY (fn_reachable fn) succs)
Proof
  ho_match_mp_tac dfs_aux_call_ind >> rpt conj_tac
  >- (simp[venomWfTheory.fn_reachable_def] >> metis_tac[relationTheory.RTC_REFL])
  >- simp[]
  >- simp[]
  >- (rpt gen_tac >> strip_tac >> strip_tac >>
      gvs[EVERY_MEM] >> rpt strip_tac >>
      `wf_function fn` by fs[codegen_ready_fn_def] >>
      `fn_cfg_edge fn lbl e` by metis_tac[fn_cfg_edge_cfg_analyze] >>
      gvs[venomWfTheory.fn_reachable_def] >>
      metis_tac[relationTheory.RTC_RULES_RIGHT1])
  >- simp[]
  >- simp[]
  >> simp[]
QED

Theorem dfs_block_state_cfg_reachable:
  codegen_ready_fn fn /\
  dfs_block_state lv dfg (cfg_analyze fn) fn ps0 lbl ps ==>
  cfg_reachable_of (cfg_analyze fn) lbl
Proof
  strip_tac >>
  `wf_function fn` by fs[codegen_ready_fn_def] >>
  `fn_reachable fn lbl` suffices_by metis_tac[fn_reachable_cfg_analyze] >>
  qpat_x_assum `dfs_block_state _ _ _ _ _ _ _` mp_tac >>
  simp[dfs_block_state_def] >> rpt strip_tac >>
  drule (cj 1 dfs_call_reachable_mutual) >> simp[]
QED

Theorem ret_region_dfs_params_unpromised:
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  lookup_block target fn.fn_blocks = SOME retbb /\
  MEM ret_inst retbb.bb_instructions /\ ret_inst.inst_opcode = RET /\
  dfs_block_state lv dfg cfg fn
    (init_cleanup_plan_state ch growth spill_base ctr) lbl ps /\
  cfg_path cfg lbl target /\
  (if bb = HD fn.fn_blocks then prepare_params_plan lv fn ps else ([],ps)) =
    (param_ops,ps1) ==>
  ~ps1.ps_cleanup_promised
Proof
  strip_tac >> drule_all ret_region_dfs_block_unpromised >> strip_tac >>
  Cases_on `bb = HD fn.fn_blocks` >> gvs[] >>
  metis_tac[prepare_params_plan_promised, pairTheory.SND]
QED

Theorem ret_region_dfs_cleanup_physical:
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  lookup_block target fn.fn_blocks = SOME retbb /\
  MEM ret_inst retbb.bb_instructions /\ ret_inst.inst_opcode = RET /\
  dfs_block_state lv dfg cfg fn
    (init_cleanup_plan_state ch growth spill_base ctr) lbl ps /\
  cfg_path cfg lbl target /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  (if bb = HD fn.fn_blocks then prepare_params_plan lv fn ps else ([],ps)) =
    (param_ops,ps1) ==>
  clean_stack_plan lv cfg fn bb ps1 =
    case cfg_preds_of cfg bb.bb_label of
      [pred] =>
        if LENGTH (cfg_succs_of cfg pred) <= 1 then ([],ps1)
        else (case lookup_block pred fn.fn_blocks of
          NONE => ([],ps1)
        | SOME pred_bb =>
          popmany_plan (MAP Var (FILTER (\v. ~MEM v
            (input_vars_from pred bb.bb_instructions (live_vars_at lv bb.bb_label 0)))
            (live_vars_at lv pred (LENGTH pred_bb.bb_instructions)))) ps1)
    | _ => ([],ps1)
Proof
  strip_tac >>
  `~ps1.ps_cleanup_promised` by metis_tac[ret_region_dfs_params_unpromised] >>
  `!n. ~cleanup_elision_safe ps1.ps_cleanup_height ps1.ps_cleanup_growth cfg fn bb n` by
    metis_tac[inventory_ret_cleanup_not_safe] >>
  simp[clean_stack_plan_def, LET_THM]
QED

Theorem ret_region_dfs_cleanup_every:
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  lookup_block target fn.fn_blocks = SOME retbb /\
  MEM ret_inst retbb.bb_instructions /\ ret_inst.inst_opcode = RET /\
  dfs_block_state lv dfg cfg fn
    (init_cleanup_plan_state ch growth spill_base ctr) lbl ps /\
  cfg_path cfg lbl target /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  (if bb = HD fn.fn_blocks then prepare_params_plan lv fn ps else ([],ps)) =
    (param_ops,ps1) /\
  ALL_DISTINCT ps1.ps_stack /\ EVERY P ps1.ps_stack /\
  clean_stack_plan lv cfg fn bb ps1 = (ops,qs) ==>
  EVERY P qs.ps_stack
Proof
  strip_tac >> drule_all ret_region_dfs_cleanup_physical >>
  qpat_x_assum `clean_stack_plan _ _ _ _ _ = _` mp_tac >>
  Cases_on `cfg_preds_of cfg bb.bb_label` >> simp[] >>
  rename1 `_ = pred::rest` >> Cases_on `rest` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `lookup_block pred fn.fn_blocks` >> simp[] >>
  rpt strip_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `popmany_plan items ps1` >>
  drule inventory_popmany >> disch_then (qspec_then `items` mp_tac) >>
  gvs[EVERY_MEM] >> metis_tac[pairTheory.SND]
QED

Theorem regional_no_use_dead_range:
  !n fn bb i v.
    wf_function fn /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    i + n <= LENGTH bb.bb_instructions /\
    ~MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (i + n)) /\
    (!j. i <= j /\ j < i + n ==>
      ~MEM v (inst_uses (EL j bb.bb_instructions))) ==>
    ~MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i)
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  `~MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i))` by
    (first_x_assum irule >> fs[arithmeticTheory.ADD_CLAUSES] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  drule live_vars_at_transfer >> simp[] >>
  disch_then (qspecl_then [`bb.bb_label`, `bb`, `i`] mp_tac) >>
  simp[] >> strip_tac >>
  `~MEM v (inst_uses (EL i bb.bb_instructions))` by
    (first_x_assum irule >> decide_tac) >>
  simp[livenessDefsTheory.liveness_transfer_def, live_update_mem]
QED

Theorem regional_phi_later_uses[local]:
  !phis i j v. phi_uses_disjoint phis /\
    i < j /\ j < LENGTH phis /\ MEM v (inst_uses (EL i phis)) ==>
    ~MEM v (inst_uses (EL j phis))
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `i` >> Cases_on `j` >>
  gvs[phi_uses_disjoint_def, EVERY_MEM] >> metis_tac[EL_MEM]
QED

Theorem regional_ready_phi_source_dead:
  !fn bb i v.
    codegen_ready_fn fn /\ fn_reachable fn bb.bb_label /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    i < LENGTH (collect_phis bb.bb_instructions) /\
    MEM v (inst_uses (EL i bb.bb_instructions)) ==>
    ~MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (i + 1))
Proof
  rpt gen_tac >> strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `phi_block_ready (liveness_analyze fn) bb` by
    (irule ready_phi_block >> simp[] >> metis_tac[lookup_block_mem]) >>
  `MEM v (inst_uses (EL i (collect_phis bb.bb_instructions)))` by
    metis_tac[collect_phis_index] >>
  `~MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
      (LENGTH (collect_phis bb.bb_instructions)))` by
    (gvs[phi_block_ready_def, EVERY_MEM] >> metis_tac[EL_MEM]) >>
  irule regional_no_use_dead_range >> simp[] >>
  reverse conj_tac >- metis_tac[ready_reachable_preorder] >>
  qexists_tac `LENGTH (collect_phis bb.bb_instructions) - (i + 1)` >>
  `i + 1 <= LENGTH (collect_phis bb.bb_instructions)` by decide_tac >>
  simp[] >> reverse conj_tac >- metis_tac[collect_phis_length_bound] >>
  rpt strip_tac >>
  `j < LENGTH (collect_phis bb.bb_instructions)` by decide_tac >>
  `i < j` by decide_tac >>
  gvs[phi_block_ready_def] >>
  metis_tac[regional_phi_later_uses, collect_phis_index]
QED

Theorem regional_ready_phi_physical_transfer:
  codegen_ready_fn fn /\ fn_reachable fn bb.bb_label /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  i < LENGTH (collect_phis bb.bb_instructions) /\
  inst = EL i bb.bb_instructions /\ MEM src (inst_uses inst) /\
  nl = live_vars_at (liveness_analyze fn) bb.bb_label (i + 1) /\
  generate_phi_plan inst nl F ps = (ops, qs) /\
  inst.inst_outputs = [out] /\
  stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d /\
  d < LENGTH ps.ps_stack /\ stack_peek d ps.ps_stack = Var src /\
  ALL_DISTINCT ps.ps_stack /\ ~MEM (Var out) ps.ps_stack /\
  Var out NOTIN FDOM ps.ps_spilled /\
  DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled) /\
  EVERY (\op. op = Var src \/ ?v. op = Var v /\ MEM v live_support) ps.ps_stack /\
  (MEM out nl ==> MEM out live_support) ==>
  EVERY (\op. ?v. op = Var v /\ MEM v live_support) qs.ps_stack /\
  ALL_DISTINCT qs.ps_stack /\
  DISJOINT (set qs.ps_stack) (FDOM qs.ps_spilled) /\
  qs.ps_spilled = ps.ps_spilled /\
  (!x. MEM x qs.ps_stack <=>
    (MEM x ps.ps_stack /\ x <> Var src) \/ (x = Var out /\ MEM out nl))
Proof
  strip_tac >>
  `~MEM src nl` by metis_tac[regional_ready_phi_source_dead] >>
  drule_all inventory_phi_mem >> strip_tac >>
  drule_all inventory_phi_distinct >> strip_tac >>
  drule_all inventory_phi_disjoint >> strip_tac >>
  drule_all inventory_phi_spilled >> strip_tac >>
  simp[] >> gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem regional_param_heads_distinct[local]:
  codegen_ready_fn fn ==>
  ALL_DISTINCT (MAP (\i. Var (HD i.inst_outputs))
    (get_params (HD fn.fn_blocks).bb_instructions))
Proof
  strip_tac >> drule ready_entry_param_outputs_distinct >>
  `MAP (\i. Var (HD i.inst_outputs))
      (get_params (HD fn.fn_blocks).bb_instructions) =
    MAP Var (MAP (\i. HD i.inst_outputs)
      (get_params (HD fn.fn_blocks).bb_instructions))` by
    simp[MAP_MAP_o, combinTheory.o_DEF] >>
  simp[] >> strip_tac >> irule ALL_DISTINCT_MAP_INJ >> simp[]
QED

Theorem regional_params_dead_filter[local]:
  ALL_DISTINCT installed.ps_stack /\
  installed.ps_stack = MAP (\i. Var (HD i.inst_outputs)) params /\
  popmany_plan (FILTER is_var_operand
    (FILTER (\v. ~MEM (operand_to_string v) nl) installed.ps_stack)) installed = (ops,qs) ==>
  ALL_DISTINCT qs.ps_stack /\
  EVERY (\op. ?v. op = Var v /\ MEM v nl /\ MEM op installed.ps_stack) qs.ps_stack
Proof
  strip_tac >> conj_tac >- metis_tac[inventory_popmany_distinct] >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  drule_all inventory_popmany_mem >>
  disch_then (qspec_then `op` mp_tac) >>
  simp[] >> strip_tac >>
  gvs[MEM_FILTER, MEM_MAP] >>
  gvs[stackPlanTypesTheory.operand_to_string_def, stackPlanTypesTheory.is_var_operand_def]
QED

Theorem regional_prepare_params_inventory:
  codegen_ready_fn fn /\ lv = liveness_analyze fn /\
  prepare_params_plan lv fn (init_cleanup_plan_state ch growth sb ctr) = (ops,qs) ==>
  ALL_DISTINCT qs.ps_stack /\ qs.ps_spilled = FEMPTY /\
  EVERY (\op. ?v. op = Var v /\
    MEM v (live_vars_at lv (HD fn.fn_blocks).bb_label
      (LENGTH (get_params (HD fn.fn_blocks).bb_instructions))) /\
    MEM op (MAP (\i. Var (HD i.inst_outputs))
      (get_params (HD fn.fn_blocks).bb_instructions))) qs.ps_stack
Proof
  strip_tac >>
  qpat_x_assum `prepare_params_plan _ _ _ = _` mp_tac >>
  simp[prepare_params_plan_def, LET_THM] >>
  qmatch_goalsub_abbrev_tac `get_params entry.bb_instructions` >>
  Cases_on `get_params entry.bb_instructions = []`
  >- (strip_tac >> gvs[init_cleanup_plan_state_def, stackPlanTypesTheory.init_plan_state_def]) >>
  simp[parameter_stack_fold] >>
  qmatch_goalsub_abbrev_tac `popmany_plan items installed` >>
  pairarg_tac >> simp[] >>
  rename1 `popmany_plan items installed = (pops,mid)` >>
  `ALL_DISTINCT installed.ps_stack` by
    (simp[Abbr `installed`, init_cleanup_plan_state_def, stackPlanTypesTheory.init_plan_state_def] >>
     metis_tac[regional_param_heads_distinct]) >>
  `installed.ps_spilled = FEMPTY` by
    simp[Abbr `installed`, init_cleanup_plan_state_def, stackPlanTypesTheory.init_plan_state_def] >>
  `ALL_DISTINCT mid.ps_stack /\
   EVERY (\op. ?v. op = Var v /\
     MEM v (live_vars_at (liveness_analyze fn) entry.bb_label
       (LENGTH (get_params entry.bb_instructions))) /\
     MEM op installed.ps_stack) mid.ps_stack` by
    (irule regional_params_dead_filter >>
     goal_assum (drule_at Any) >>
     simp[Abbr `items`, Abbr `installed`] >>
     qexists_tac `get_params entry.bb_instructions` >> simp[]) >>
  `mid.ps_spilled = FEMPTY` by
    (qspecl_then [`items`, `installed`] mp_tac
       fnFrameStepsRevertForwardTheory.rf_popmany_spilled >> simp[]) >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule inventory_optimistic_swap_resources >> simp[] >> strip_tac >>
  drule inventory_optimistic_swap_every >>
  strip_tac >>
  gvs[Abbr `installed`, init_cleanup_plan_state_def, stackPlanTypesTheory.init_plan_state_def] >>
  metis_tac[fnFrameStepsRevertForwardTheory.rf_optimistic_spilled, pairTheory.SND]
QED

Theorem regional_prepare_params_support:
  codegen_ready_fn fn /\ lv = liveness_analyze fn /\
  prepare_params_plan lv fn (init_cleanup_plan_state ch growth sb ctr) = (ops,qs) ==>
  EVERY (\op. ?v. op = Var v /\
    MEM v (live_vars_at lv (HD fn.fn_blocks).bb_label
      (LENGTH (get_params (HD fn.fn_blocks).bb_instructions))) /\
    MEM op (MAP (\i. Var (HD i.inst_outputs))
      (get_params (HD fn.fn_blocks).bb_instructions))) qs.ps_stack
Proof
  strip_tac >> drule_all regional_prepare_params_inventory >> simp[]
QED

Theorem regional_prepare_params_distinct:
  codegen_ready_fn fn /\ lv = liveness_analyze fn /\
  prepare_params_plan lv fn (init_cleanup_plan_state ch growth sb ctr) = (ops,qs) ==>
  ALL_DISTINCT qs.ps_stack
Proof
  strip_tac >> drule_all regional_prepare_params_inventory >> simp[]
QED

Theorem regional_prepare_params_spilled:
  codegen_ready_fn fn /\ lv = liveness_analyze fn /\
  prepare_params_plan lv fn (init_cleanup_plan_state ch growth sb ctr) = (ops,qs) ==>
  qs.ps_spilled = FEMPTY
Proof
  strip_tac >> drule_all regional_prepare_params_inventory >> simp[]
QED

Theorem regional_stack_find_exists[local]:
  !stk P. (?op. MEM op stk /\ P op) ==> ?d. stack_find P stk = SOME d
Proof
  Induct >> simp[stack_find_def] >> rpt gen_tac >>
  Cases_on `P h` >> simp[] >> strip_tac >>
  `?d. stack_find P stk = SOME d` by metis_tac[] >> simp[]
QED

Theorem regional_phi_physical_depth:
  MEM (Var src) phi.inst_operands /\ MEM (Var src) stk /\
  (!v. MEM (Var v) phi.inst_operands /\ MEM (Var v) stk ==> v = src) ==>
  ?d. stack_get_phi_depth (FILTER is_var_operand phi.inst_operands) stk = SOME d /\
      d < LENGTH stk /\ stack_peek d stk = Var src
Proof
  strip_tac >>
  `?d. stack_find (\op. MEM op (FILTER is_var_operand phi.inst_operands))
       (REVERSE stk) = SOME d` by
    (irule regional_stack_find_exists >> qexists_tac `Var src` >>
     simp[MEM_FILTER, stackPlanTypesTheory.is_var_operand_def]) >>
  qexists_tac `d` >> simp[stack_get_phi_depth_def] >>
  drule planWfTheory.stack_find_bound >> simp[] >> strip_tac >>
  drule genBlockSimTheory.stack_find_el >> simp[MEM_FILTER] >> strip_tac >>
  `stack_peek d stk = EL d (REVERSE stk)` by
    (simp[stack_peek_def, EL_REVERSE] >>
     `PRE (LENGTH stk - d) = LENGTH stk - 1 - d` by decide_tac >> simp[]) >>
  `MEM (EL d (REVERSE stk)) stk` by
    metis_tac[MEM_EL, MEM_REVERSE, LENGTH_REVERSE] >>
  Cases_on `EL d (REVERSE stk)` >> gvs[stackPlanTypesTheory.is_var_operand_def]
QED


Theorem regional_fn_path_first_visit[local]:
  !path fn target. is_fn_path fn path /\ MEM target path ==>
    ?pre. is_fn_path fn (pre ++ [target]) /\
      HD (pre ++ [target]) = HD path /\ ~MEM target pre
Proof
  Induct >- simp[] >> rpt gen_tac >>
  rename1 `is_fn_path fn (head :: rest)` >> strip_tac >>
  Cases_on `head = target`
  >- (qexists_tac `[]` >> gvs[is_fn_path_def]) >>
  `MEM target rest` by gvs[] >>
  `is_fn_path fn rest` by (Cases_on `rest` >> gvs[is_fn_path_def]) >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `head :: pre` >>
  Cases_on `rest` >> Cases_on `pre` >> gvs[is_fn_path_def]
QED

Theorem regional_fn_path_unsnoc[local]:
  !pre fn target. pre <> [] /\ is_fn_path fn (pre ++ [target]) ==>
    is_fn_path fn pre /\ fn_cfg_edge fn (LAST pre) target
Proof
  Induct >- simp[] >> rpt gen_tac >>
  rename1 `is_fn_path fn ((head :: rest) ++ [target])` >>
  Cases_on `rest` >> gvs[is_fn_path_def] >> metis_tac[]
QED

Theorem regional_first_entry_edge:
  !fn target. fn_reachable fn target /\ fn_entry_label fn <> SOME target ==>
    ?pred. fn_reachable fn pred /\ fn_cfg_edge fn pred target /\
      ~fn_dominates fn target pred
Proof
  rpt strip_tac >>
  `?entry. fn_entry_label fn = SOME entry /\
     RTC (fn_cfg_edge fn) entry target` by gvs[fn_reachable_def] >>
  drule rtc_to_fn_path >> strip_tac >>
  `MEM target path` by metis_tac[MEM_LAST_NOT_NIL] >>
  drule_all regional_fn_path_first_visit >> strip_tac >>
  `pre <> []` by (strip_tac >> gvs[]) >>
  `HD pre = entry` by (Cases_on `pre` >> gvs[]) >>
  drule_all regional_fn_path_unsnoc >> strip_tac >>
  qexists_tac `LAST pre` >> simp[] >> conj_tac
  >- (simp[fn_reachable_def] >>
      qspecl_then [`fn`, `pre`] mp_tac is_fn_path_rtc >> simp[]) >>
  strip_tac >> qpat_x_assum `fn_dominates _ _ _` mp_tac >>
  simp[fn_dominates_def] >>
  disj2_tac >> qexists_tac `pre` >> simp[]
QED

Theorem regional_phi_edge_source_fresh:
  !fn bb phi pred w.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
    MEM phi bb.bb_instructions /\ phi.inst_opcode = PHI /\
    MEM (pred,w) (phi_pairs phi.inst_operands) /\
    ~fn_dominates fn bb.bb_label pred ==>
    !inst. MEM inst bb.bb_instructions ==> ~MEM w inst.inst_outputs
Proof
  rpt gen_tac >> strip_tac >>
  `ssa_form fn /\ def_dominates_uses fn` by gvs[codegen_ready_fn_def] >>
  `phi_edge_uses_wf fn bb phi` by
    (gvs[def_dominates_uses_def] >> metis_tac[]) >>
  `?pred_bb. MEM pred_bb fn.fn_blocks /\ pred_bb.bb_label = pred /\
     def_available_at fn pred_bb NONE w` by
    (gvs[phi_edge_uses_wf_def] >> metis_tac[]) >>
  qpat_x_assum `def_available_at _ _ _ _` mp_tac >>
  simp[def_available_at_def] >> strip_tac >>
  rpt strip_tac >>
  `def_bb = bb` by metis_tac[ssa_unique_output_block] >> gvs[]
QED

Theorem regional_phi_nonentry[local]:
  !fn bb phi. codegen_ready_fn fn /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    MEM phi (collect_phis bb.bb_instructions) ==>
    fn_entry_label fn <> SOME bb.bb_label
Proof
  rpt strip_tac >>
  `block_entries_ready (cfg_analyze fn) fn` by gvs[codegen_ready_fn_def] >>
  qpat_x_assum `codegen_ready_fn _` kall_tac >>
  Cases_on `fn.fn_blocks` >>
  gvs[fn_entry_label_def, entry_block_def, lookup_block_def,
      FIND_thm, block_entries_ready_def, NULL_EQ]
QED

Theorem regional_phi_live_trigger:
  !fn bb phi. codegen_ready_fn fn /\ fn_reachable fn bb.bb_label /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    MEM phi (collect_phis bb.bb_instructions) ==>
    ?w. MEM w (MAP SND (phi_pairs phi.inst_operands)) /\
        MEM w (live_vars_at (liveness_analyze fn) bb.bb_label 0)
Proof
  rpt gen_tac >> strip_tac >>
  `fn_entry_label fn <> SOME bb.bb_label` by metis_tac[regional_phi_nonentry] >>
  drule_all regional_first_entry_edge >> strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_mem] >>
  `MEM phi bb.bb_instructions /\ phi.inst_opcode = PHI` by
    metis_tac[collect_phis_mem] >>
  `phi_edge_uses_wf fn bb phi` by
    (gvs[codegen_ready_fn_def, def_dominates_uses_def] >> metis_tac[]) >>
  `?w. MEM (pred,w) (phi_pairs phi.inst_operands)` by
    (gvs[phi_edge_uses_wf_def] >> Cases_on `p` >> gvs[] >> metis_tac[]) >>
  `!inst. MEM inst bb.bb_instructions ==> ~MEM w inst.inst_outputs` by
    metis_tac[regional_phi_edge_source_fresh] >>
  `?idx. idx < LENGTH bb.bb_instructions /\ EL idx bb.bb_instructions = phi` by
    metis_tac[MEM_EL] >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[ready_reachable_preorder] >>
  `MEM w (inst_uses phi)` by
    metis_tac[MEM_phi_pairs_SND_operand_vars, inst_uses_def] >>
  `MEM w (live_vars_at (liveness_analyze fn) bb.bb_label idx)` by
    (drule live_vars_at_uses >> simp[] >> disch_then irule >> metis_tac[]) >>
  qexists_tac `w` >> conj_tac >- (simp[MEM_MAP] >> metis_tac[pairTheory.SND]) >>
  drule live_vars_at_propagate_range >> simp[] >> disch_then irule >>
  simp[] >> qexists_tac `idx` >>
  simp[inst_defs_def] >> rpt strip_tac >>
  `k < LENGTH bb.bb_instructions` by decide_tac >>
  metis_tac[EL_MEM]
QED

Theorem regional_nonentry_lineage_edge[local]:
  !lv dfg cfg fn ps0 lbl ps.
    lineage_state lv dfg cfg fn ps0 lbl ps /\
    fn_entry_label fn <> SOME lbl ==>
    ?pred. lineage_entry lv dfg cfg fn ps0 pred lbl ps /\
           MEM lbl (cfg_succs_of cfg pred)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `lineage_state _ _ _ _ _ _ _` mp_tac >>
  once_rewrite_tac[lineage_state_cases] >>
  simp[lineage_entry_def] >> metis_tac[]
QED

Theorem regional_lineage_phi_source:
  !fn lv dfg cfg bb ch growth sb ctr ps phi.
    codegen_ready_fn fn /\ lv = liveness_analyze fn /\
    dfg = dfg_build_function fn /\ cfg = cfg_analyze fn /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    lineage_state lv dfg cfg fn
      (init_cleanup_plan_state ch growth sb ctr) bb.bb_label ps /\
    MEM phi (collect_phis bb.bb_instructions) ==>
    ?src. MEM (Var src) phi.inst_operands /\ MEM (Var src) ps.ps_stack
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `fn_entry_label fn <> SOME bb.bb_label` by metis_tac[regional_phi_nonentry] >>
  drule_all regional_nonentry_lineage_edge >> strip_tac >>
  `fn_reachable fn bb.bb_label` by
    (drule lineage_state_dfs_fields >> strip_tac >>
     drule_all dfs_block_state_cfg_reachable >>
     metis_tac[fn_reachable_cfg_analyze]) >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_mem] >>
  `MEM phi bb.bb_instructions /\ phi.inst_opcode = PHI` by
    metis_tac[collect_phis_mem] >>
  `phi_edge_uses_wf fn bb phi` by
    (gvs[codegen_ready_fn_def, def_dominates_uses_def] >> metis_tac[]) >>
  `fn_cfg_edge fn pred bb.bb_label` by metis_tac[fn_cfg_edge_cfg_analyze] >>
  `?src. MEM (pred,src) (phi_pairs phi.inst_operands)` by
    (gvs[phi_edge_uses_wf_def] >> Cases_on `p` >> gvs[] >> metis_tac[]) >>
  drule_all regional_phi_live_trigger >> strip_tac >>
  `phi_uses_disjoint (collect_phis bb.bb_instructions)` by
    (drule_all ready_phi_block >> simp[phi_block_ready_def]) >>
  `MEM src (input_vars_from pred bb.bb_instructions
      (live_vars_at (liveness_analyze fn) bb.bb_label 0))` by
    (irule input_vars_from_trigger_phi >> simp[] >> qexistsl_tac [`phi`, `w`] >>
     gvs[phi_edge_uses_wf_def]) >>
  `LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label) <> 1` by
    (strip_tac >>
     `LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label) <= 1` by simp[] >>
     gvs[codegen_ready_fn_def, phis_at_joins_def, EVERY_MEM, NULL_EQ] >>
     metis_tac[MEM]) >>
  qexists_tac `src` >> conj_tac >- metis_tac[phi_pairs_mem_var] >>
  irule regional_lineage_join_input_physical >> simp[] >>
  goal_assum (drule_at (Pat `lineage_entry _ _ _ _ _ _ _ _`)) >> simp[]
QED

Theorem regional_lineage_phi_depth:
  !lv dfg cfg ch growth sb ctr fn fn_ops ps_end bb ps phi.
    lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn sb ctr =
      SOME (fn_ops, ps_end) /\
    EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
      inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    lineage_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
      bb.bb_label ps /\ MEM phi (collect_phis bb.bb_instructions) ==>
    ?src d. MEM (Var src) phi.inst_operands /\ MEM (Var src) ps.ps_stack /\
      stack_get_phi_depth (FILTER is_var_operand phi.inst_operands) ps.ps_stack = SOME d /\
      d < LENGTH ps.ps_stack /\ stack_peek d ps.ps_stack = Var src /\
      (!v. MEM (Var v) phi.inst_operands /\
        (MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) ==> v = src)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all regional_lineage_phi_source >> strip_tac >>
  drule_all lineage_state_static >> strip_tac >>
  `?!v. MEM (Var v) phi.inst_operands /\
      (MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled)` by
    (qpat_x_assum `EVERY _ (collect_phis _)` mp_tac >>
     simp[EVERY_MEM] >> disch_then drule >> simp[]) >>
  `!v. MEM (Var v) phi.inst_operands /\
      (MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) ==> v = src` by
    metis_tac[EXISTS_UNIQUE_THM] >>
  `?d. stack_get_phi_depth (FILTER is_var_operand phi.inst_operands) ps.ps_stack = SOME d /\
       d < LENGTH ps.ps_stack /\ stack_peek d ps.ps_stack = Var src` by
    (irule regional_phi_physical_depth >> simp[]) >>
  qexistsl_tac [`src`, `d`] >> simp[] >> metis_tac[]
QED

(* Frame a future PHI independently of the representation used for the overwrite. *)
Theorem regional_phi_stack_frame:
  (!x. MEM x qs.ps_stack <=>
    (MEM x ps.ps_stack /\ x <> Var removed) \/ (x = Var added /\ keep)) /\
  ~MEM (Var removed) phi.inst_operands /\
  ~MEM (Var added) phi.inst_operands ==>
  !v. MEM (Var v) phi.inst_operands ==>
    (MEM (Var v) qs.ps_stack <=> MEM (Var v) ps.ps_stack)
Proof
  rpt strip_tac >> first_x_assum (qspec_then `Var v` mp_tac) >>
  metis_tac[]
QED

Theorem regional_phi_owned_frame:
  qs.ps_spilled = ps.ps_spilled /\
  (!x. MEM x qs.ps_stack <=>
    (MEM x ps.ps_stack /\ x <> Var removed) \/ (x = Var added /\ keep)) /\
  ~MEM (Var removed) phi.inst_operands /\
  ~MEM (Var added) phi.inst_operands ==>
  !v. MEM (Var v) phi.inst_operands ==>
    ((MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled) <=>
     (MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled))
Proof
  rpt strip_tac >>
  qpat_x_assum `!x. MEM x _ <=> _` (qspec_then `Var v` mp_tac) >>
  metis_tac[]
QED

Theorem regional_phi_selected_frame:
  qs.ps_spilled = ps.ps_spilled /\
  (!x. MEM x qs.ps_stack <=>
    (MEM x ps.ps_stack /\ x <> Var removed) \/ (x = Var added /\ keep)) /\
  ~MEM (Var removed) phi.inst_operands /\
  ~MEM (Var added) phi.inst_operands /\
  MEM (Var src) phi.inst_operands /\ MEM (Var src) ps.ps_stack /\
  (!v. MEM (Var v) phi.inst_operands /\
    (MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) ==> v = src) ==>
  MEM (Var src) qs.ps_stack /\
  (!v. MEM (Var v) phi.inst_operands /\
    (MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled) ==> v = src)
Proof
  strip_tac >>
  drule_all regional_phi_stack_frame >> strip_tac >>
  drule_all regional_phi_owned_frame >> strip_tac >>
  metis_tac[]
QED

(* A PHI output has no further definition after the complete PHI prefix.
   This is independent of whether that output occurs on an incoming edge. *)
Theorem regional_phi_output_no_suffix_def:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
  MEM phi (collect_phis bb.bb_instructions) /\ MEM v phi.inst_outputs ==>
  !p. LENGTH (collect_phis bb.bb_instructions) <= p /\
      p < LENGTH bb.bb_instructions ==>
      ~MEM v (inst_defs (EL p bb.bb_instructions))
Proof
  strip_tac >>
  `?k. k < LENGTH (collect_phis bb.bb_instructions) /\
       EL k (collect_phis bb.bb_instructions) = phi` by metis_tac[MEM_EL] >>
  `EL k bb.bb_instructions = phi` by metis_tac[collect_phis_index] >>
  qx_gen_tac `p` >> strip_tac >> simp[inst_defs_def] >>
  irule ready_output_other_location >> simp[] >>
  qexistsl_tac [`bb`, `fn`, `k`] >> simp[] >>
  mp_tac (Q.SPEC `bb.bb_instructions` collect_phis_length_bound) >> decide_tac
QED

Theorem regional_phi_output_exit_live:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
  MEM phi (collect_phis bb.bb_instructions) /\ MEM v phi.inst_outputs /\
  fn_reachable fn bb.bb_label /\
  MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
    (LENGTH bb.bb_instructions)) ==>
  MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
    (LENGTH (collect_phis bb.bb_instructions)))
Proof
  strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule MEM_lookup_block >> simp[] >> gvs[wf_function_def, fn_labels_def]) >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[ready_reachable_preorder] >>
  drule live_vars_at_propagate_range >> simp[] >> disch_then irule >> simp[] >>
  qexists_tac `LENGTH bb.bb_instructions` >> simp[collect_phis_length_bound] >>
  metis_tac[regional_phi_output_no_suffix_def]
QED

Theorem regional_live_range[local]:
  codegen_ready_fn fn /\ fn_reachable fn lbl /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  i <= j /\ j <= LENGTH bb.bb_instructions /\
  MEM v (live_vars_at (liveness_analyze fn) lbl j) /\
  (!p. i <= p /\ p < j ==> ~MEM v (inst_defs (EL p bb.bb_instructions))) ==>
  MEM v (live_vars_at (liveness_analyze fn) lbl i)
Proof
  strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `MEM lbl (cfg_analyze fn).cfg_dfs_pre` by metis_tac[ready_reachable_preorder] >>
  drule live_vars_at_propagate_range >> simp[] >> disch_then irule >> simp[] >>
  metis_tac[]
QED

Theorem regional_live_edge[local]:
  codegen_ready_fn fn /\ fn_reachable fn pred /\ fn_reachable fn lbl /\
  fn_cfg_edge fn pred lbl /\
  lookup_block pred fn.fn_blocks = SOME pb /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  MEM v (live_vars_at (liveness_analyze fn) lbl
    (LENGTH (collect_phis bb.bb_instructions))) /\
  (!p. p < LENGTH (collect_phis bb.bb_instructions) ==>
    ~MEM v (inst_defs (EL p bb.bb_instructions))) ==>
  MEM v (live_vars_at (liveness_analyze fn) pred (LENGTH pb.bb_instructions))
Proof
  strip_tac >> irule input_vars_from_predecessor_exit >> simp[] >>
  (conj_tac >- gvs[codegen_ready_fn_def]) >>
  qexistsl_tac [`bb`, `lbl`] >> simp[] >>
  irule ready_postprefix_edge >> simp[] >>
  conj_tac >- metis_tac[lookup_block_label] >>
  irule ready_reachable_preorder >> gvs[codegen_ready_fn_def]
QED

Theorem regional_live_clean_path[local]:
  !path fn ub j v.
    codegen_ready_fn fn /\ path <> [] /\ is_fn_path fn path /\
    EVERY (fn_reachable fn) path /\
    lookup_block (LAST path) fn.fn_blocks = SOME ub /\
    LENGTH (collect_phis ub.bb_instructions) <= j /\
    j <= LENGTH ub.bb_instructions /\
    MEM v (live_vars_at (liveness_analyze fn) (LAST path) j) /\
    (!lbl bb p. MEM lbl path /\ lookup_block lbl fn.fn_blocks = SOME bb /\
       p < LENGTH bb.bb_instructions ==> ~MEM v (inst_defs (EL p bb.bb_instructions))) ==>
    !bb. lookup_block (HD path) fn.fn_blocks = SOME bb ==>
      MEM v (live_vars_at (liveness_analyze fn) (HD path)
        (LENGTH (collect_phis bb.bb_instructions)))
Proof
  Induct >- simp[] >> rpt gen_tac >>
  rename1 `is_fn_path fn (lbl :: rest)` >> strip_tac >>
  Cases_on `rest`
  >- (gvs[] >> irule regional_live_range >> simp[] >>
      qexists_tac `j` >> simp[] >> rpt strip_tac >>
      first_x_assum irule >> decide_tac) >>
  rename1 `is_fn_path fn (lbl :: succ :: tail)` >>
  gvs[Once is_fn_path_def] >> rpt strip_tac >>
  `?sb. lookup_block succ fn.fn_blocks = SOME sb` by
    (`wf_function fn` by gvs[codegen_ready_fn_def] >>
     `cfg_reachable_of (cfg_analyze fn) succ` by metis_tac[fn_reachable_cfg_analyze] >>
     drule cfgAnalysisPropsTheory.cfg_analyze_reachable_in_labels >>
     simp[fn_labels_def, MEM_MAP] >> strip_tac >>
     irule_at Any MEM_lookup_block >> simp[] >>
     gvs[wf_function_def, fn_labels_def] >> metis_tac[]) >>
  `MEM v (live_vars_at (liveness_analyze fn) succ
      (LENGTH (collect_phis sb.bb_instructions)))` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  `MEM v (live_vars_at (liveness_analyze fn) lbl
      (LENGTH bb.bb_instructions))` by
    (irule regional_live_edge >> simp[] >>
     qexistsl_tac [`sb`, `succ`] >> simp[] >>
     qx_gen_tac `p` >> disch_tac >>
     qpat_x_assum `!lbl' bb p. _` irule >> simp[] >>
     (conj_tac >- (mp_tac (Q.SPEC `sb.bb_instructions` collect_phis_length_bound) >> decide_tac)) >>
     qexists_tac `succ` >> simp[]) >>
  irule regional_live_range >> simp[] >>
  qexists_tac `LENGTH bb.bb_instructions` >> simp[collect_phis_length_bound] >>
  metis_tac[]
QED

Theorem regional_phi_other_block_no_defs[local]:
  codegen_ready_fn fn /\ MEM db fn.fn_blocks /\
  MEM phi (collect_phis db.bb_instructions) /\ MEM v phi.inst_outputs /\
  lbl <> db.bb_label /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  p < LENGTH bb.bb_instructions ==> ~MEM v (inst_defs (EL p bb.bb_instructions))
Proof
  strip_tac >> simp[inst_defs_def] >>
  `?k. k < LENGTH (collect_phis db.bb_instructions) /\
       EL k (collect_phis db.bb_instructions) = phi` by metis_tac[MEM_EL] >>
  `EL k db.bb_instructions = phi` by metis_tac[collect_phis_index] >>
  irule ready_output_other_location >> simp[] >>
  qexistsl_tac [`db`, `fn`, `k`] >> simp[] >>
  `k < LENGTH db.bb_instructions` by
    (mp_tac (Q.SPEC `db.bb_instructions` collect_phis_length_bound) >> decide_tac) >>
  metis_tac[lookup_block_MEM, lookup_block_label]
QED

Theorem regional_phi_output_dominated_boundary_live:
  codegen_ready_fn fn /\ MEM db fn.fn_blocks /\
  MEM phi (collect_phis db.bb_instructions) /\ MEM v phi.inst_outputs /\
  MEM ub fn.fn_blocks /\ fn_dominates fn db.bb_label ub.bb_label /\
  LENGTH (collect_phis ub.bb_instructions) <= j /\
  j <= LENGTH ub.bb_instructions /\
  MEM v (live_vars_at (liveness_analyze fn) ub.bb_label j) ==>
  MEM v (live_vars_at (liveness_analyze fn) db.bb_label
    (LENGTH (collect_phis db.bb_instructions)))
Proof
  strip_tac >>
  `fn_reachable fn db.bb_label` by metis_tac[fn_dominates_dom_reachable] >>
  `lookup_block db.bb_label fn.fn_blocks = SOME db /\
   lookup_block ub.bb_label fn.fn_blocks = SOME ub` by
    (conj_tac >> irule MEM_lookup_block >> simp[] >>
     gvs[codegen_ready_fn_def, wf_function_def, fn_labels_def]) >>
  Cases_on `ub = db`
  >- (gvs[] >> irule regional_live_range >> simp[] >>
      qexists_tac `j` >> simp[] >>
      qx_gen_tac `p` >> strip_tac >>
      irule regional_phi_output_no_suffix_def >> simp[] >>
      metis_tac[]) >>
  drule fn_dominates_last_visit >> strip_tac >>
  Cases_on `tail` >- (gvs[] >> metis_tac[]) >>
  rename1 `is_fn_path fn (db.bb_label :: first :: rest)` >>
  `?fb. lookup_block first fn.fn_blocks = SOME fb` by
    (`wf_function fn` by gvs[codegen_ready_fn_def] >>
     `cfg_reachable_of (cfg_analyze fn) first` by
       (gvs[] >> metis_tac[fn_reachable_cfg_analyze]) >>
     drule cfgAnalysisPropsTheory.cfg_analyze_reachable_in_labels >>
     simp[fn_labels_def, MEM_MAP] >> strip_tac >>
     irule_at Any MEM_lookup_block >> simp[] >>
     gvs[wf_function_def, fn_labels_def] >> metis_tac[]) >>
  `MEM v (live_vars_at (liveness_analyze fn) first
      (LENGTH (collect_phis fb.bb_instructions)))` by
    (irule (SRULE [] (Q.SPEC `first :: rest` regional_live_clean_path)) >> simp[] >>
     (conj_tac >- gvs[]) >> qexistsl_tac [`j`, `rest`, `ub`] >>
     gvs[Once is_fn_path_def] >> rpt gen_tac >> strip_tac >>
     irule regional_phi_other_block_no_defs >> simp[] >>
     qexistsl_tac [`db`, `fn`, `lbl`, `phi`] >> simp[] >> metis_tac[]) >>
  irule regional_phi_output_exit_live >> simp[] >>
  (conj_tac >- (qexists_tac `phi` >> simp[])) >>
  irule regional_live_edge >> simp[] >>
  qexistsl_tac [`fb`, `first`] >> gvs[Once is_fn_path_def] >>
  qx_gen_tac `p` >> disch_tac >>
  irule regional_phi_other_block_no_defs >> simp[] >>
  (conj_tac >- (mp_tac (Q.SPEC `fb.bb_instructions` collect_phis_length_bound) >> decide_tac)) >>
  qexistsl_tac [`db`, `fn`, `first`, `phi`] >> simp[]
QED

Theorem regional_phi_selected_edge_exit_live:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
  fn_reachable fn bb.bb_label /\
  MEM phi (collect_phis bb.bb_instructions) /\
  MEM (pred,v) (phi_pairs phi.inst_operands) /\
  lookup_block pred fn.fn_blocks = SOME pb /\ fn_reachable fn pred ==>
  MEM v (live_vars_at (liveness_analyze fn) pred
    (LENGTH pb.bb_instructions))
Proof
  strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule MEM_lookup_block >> simp[] >>
     gvs[wf_function_def, fn_labels_def]) >>
  `MEM phi bb.bb_instructions /\ phi.inst_opcode = PHI` by
    metis_tac[collect_phis_mem] >>
  `phi_edge_uses_wf fn bb phi` by
    (gvs[codegen_ready_fn_def, def_dominates_uses_def] >> metis_tac[]) >>
  `fn_cfg_edge fn pred bb.bb_label /\
   ALL_DISTINCT (MAP FST (phi_pairs phi.inst_operands))` by
    (gvs[phi_edge_uses_wf_def] >> metis_tac[]) >>
  drule_all regional_phi_live_trigger >> strip_tac >>
  `phi_block_ready (liveness_analyze fn) bb` by metis_tac[ready_phi_block] >>
  `MEM v (input_vars_from pred bb.bb_instructions
    (live_vars_at (liveness_analyze fn) bb.bb_label 0))` by
    (irule input_vars_from_trigger_phi >>
     (conj_tac >- gvs[phi_block_ready_def]) >>
     qexistsl_tac [`phi`, `w`] >> simp[]) >>
  irule input_vars_from_predecessor_exit >> simp[] >>
  qexistsl_tac [`bb`, `bb.bb_label`] >> simp[]
QED

Theorem regional_phi_output_not_phi_source:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
  fn_reachable fn bb.bb_label /\
  MEM defphi (collect_phis bb.bb_instructions) /\
  MEM v defphi.inst_outputs /\
  MEM usephi (collect_phis bb.bb_instructions) ==>
  ~MEM v (inst_uses usephi)
Proof
  strip_tac >> disch_tac >>
  `MEM usephi bb.bb_instructions /\ usephi.inst_opcode = PHI` by
    metis_tac[collect_phis_mem] >>
  `phi_edge_uses_wf fn bb usephi` by
    (gvs[codegen_ready_fn_def, def_dominates_uses_def] >> metis_tac[]) >>
  `?pred. MEM (pred,v) (phi_pairs usephi.inst_operands)` by
    (irule phi_well_formed_var_pair >>
     gvs[phi_edge_uses_wf_def, inst_uses_def,
         passSharedDefsTheory.MEM_operand_vars_eq_Var]) >>
  `?pb. MEM pb fn.fn_blocks /\ pb.bb_label = pred /\
    fn_cfg_edge fn pred bb.bb_label /\ def_available_at fn pb NONE v` by
    metis_tac[phi_edge_uses_wf_def] >>
  `?k. k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = defphi` by
    metis_tac[collect_phis_mem, MEM_EL] >>
  `fn_dominates fn bb.bb_label pb.bb_label` by
    (irule (cj 1 ready_output_available) >> simp[] >>
     qexistsl_tac [`k`, `NONE`, `v`] >> simp[]) >>
  `fn_reachable fn pred` by metis_tac[fn_dominates_def] >>
  `lookup_block pred fn.fn_blocks = SOME pb` by
    (irule MEM_lookup_block >> simp[] >>
     gvs[codegen_ready_fn_def, wf_function_def, fn_labels_def]) >>
  `MEM v (live_vars_at (liveness_analyze fn) pred
    (LENGTH pb.bb_instructions))` by
    (irule regional_phi_selected_edge_exit_live >> simp[] >>
     qexistsl_tac [`bb`, `usephi`] >> simp[]) >>
  `MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
    (LENGTH (collect_phis bb.bb_instructions)))` by
    (irule regional_phi_output_dominated_boundary_live >> simp[] >>
     (conj_tac >- (qexists_tac `defphi` >> simp[])) >>
     qexistsl_tac [`LENGTH pb.bb_instructions`, `pb`] >>
     simp[collect_phis_length_bound]) >>
  `phi_block_ready (liveness_analyze fn) bb` by metis_tac[ready_phi_block] >>
  gvs[phi_block_ready_def, EVERY_MEM] >> metis_tac[]
QED

Theorem regional_phi_output_normalize:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
  MEM phi (collect_phis bb.bb_instructions) /\ MEM v phi.inst_outputs ==>
  normalize_operand (dfg_build_function fn) [] (Var v) = Var v
Proof
  strip_tac >>
  `MEM phi bb.bb_instructions /\ phi.inst_opcode = PHI` by
    metis_tac[collect_phis_mem] >>
  `MEM phi (fn_insts fn)` by
    (simp[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     metis_tac[]) >>
  drule_all dfg_build_function_defs_complete >> strip_tac >>
  rename1 `dfg_get_def (dfg_build_function fn) v = SOME found` >>
  `found = phi` by
    (drule dfg_build_function_correct >> strip_tac >>
     `ssa_form fn` by gvs[codegen_ready_fn_def] >>
     metis_tac[ssa_unique_output]) >>
  gvs[dfg_get_def_def] >> simp[Once normalize_operand_def]
QED

Theorem regional_fresh_exemption_transfer:
  (!op:operand. op IN old /\ ~(op IN C UNION R) ==>
    fresh op /\ fresh (root op)) /\
  (!op. op IN old /\ op IN C ==> op = removed) /\
  (!op. op IN new ==> (op IN old /\ op <> removed) \/ op = added) /\
  fresh added /\ root added = added ==>
  (!op. op IN new /\ ~(op IN R) ==> fresh op /\ fresh (root op))
Proof
  simp[pred_setTheory.IN_UNION] >> metis_tac[]
QED

Theorem regional_phi_owned_subtraction:
  generate_phi_plan phi nl F ps = (ops,qs) /\ phi.inst_outputs = [out] /\
  stack_get_phi_depth (FILTER is_var_operand phi.inst_operands) ps.ps_stack = SOME d /\
  d < LENGTH ps.ps_stack /\ stack_peek d ps.ps_stack = Var src /\
  ~MEM src nl /\ generated_plan_state_wf_marked sb ps /\
  ~MEM (Var out) ps.ps_stack ==>
  !op. (MEM op qs.ps_stack \/ op IN FDOM qs.ps_spilled) <=>
    ((MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\ op <> Var src) \/
    (op = Var out /\ MEM out nl)
Proof
  strip_tac >>
  `ALL_DISTINCT (FILTER (\op. op <> dead_stack_marker) ps.ps_stack) /\
   DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled)` by
    gvs[generated_plan_state_wf_marked_def] >>
  `MEM (Var src) ps.ps_stack` by
    (qpat_x_assum `stack_peek _ _ = _` (mp_tac o SYM) >>
     simp[stack_peek_def] >> strip_tac >> irule EL_MEM >> decide_tac) >>
  `Var src NOTIN FDOM ps.ps_spilled` by
    (gvs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >> metis_tac[]) >>
  drule_all inventory_marked_phi_mem >> strip_tac >>
  drule_all inventory_marked_phi_spilled >> strip_tac >>
  gvs[] >> metis_tac[]
QED

Theorem regional_phi_freshness_step:
  generate_phi_plan phi nl F ps = (ops,qs) /\ phi.inst_outputs = [out] /\
  stack_get_phi_depth (FILTER is_var_operand phi.inst_operands) ps.ps_stack = SOME d /\
  d < LENGTH ps.ps_stack /\ stack_peek d ps.ps_stack = Var src /\
  ~MEM src nl /\ generated_plan_state_wf_marked sb ps /\
  ~MEM (Var out) ps.ps_stack /\
  (!v. MEM (Var v) phi.inst_operands /\
    (MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) ==> v = src) /\
  (!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    ~MEM op (phi.inst_operands ++ remaining_ops) /\
    (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
    ~MEM v future_outputs) /\
  ~MEM out future_outputs /\ normalize_operand dfg [] (Var out) = Var out ==>
  !op v. (MEM op qs.ps_stack \/ op IN FDOM qs.ps_spilled) /\
    ~MEM op remaining_ops /\
    (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
    ~MEM v future_outputs
Proof
  strip_tac >> drule_all regional_phi_owned_subtraction >> disch_tac >>
  rpt gen_tac >> strip_tac >>
  (Cases_on `op = Var out` >- gvs[] >>
  `(MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\ op <> Var src` by
    metis_tac[] >>
  (Cases_on `MEM op phi.inst_operands`
   >- (Cases_on `op` >> gvs[] >> metis_tac[normalize_operand_def]) >>
   qpat_x_assum `!op v. _ ==> ~MEM v future_outputs` irule >>
   qexists_tac `op` >> simp[]))
QED

(* Lower ownership and freshness at an indexed PHI boundary.  This does not
   assert physical upper support, nor distinctness of the whole stack. *)
Definition regional_selected_phi_inv_def:
  regional_selected_phi_inv lv dfg sb bb i ps <=>
    generated_plan_state_wf_marked sb ps /\
    (!phi. MEM phi (DROP i (collect_phis bb.bb_instructions)) ==>
      ?src. MEM (Var src) phi.inst_operands /\ MEM (Var src) ps.ps_stack /\
        (!v. MEM (Var v) phi.inst_operands /\
          (MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) ==> v = src)) /\
    (!v. MEM v (live_vars_at lv bb.bb_label i) /\
      ~MEM (Var v) (FLAT (MAP (\phi. phi.inst_operands)
        (DROP i (collect_phis bb.bb_instructions)))) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    (!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
      ~MEM op (FLAT (MAP (\phi. phi.inst_operands)
        (DROP i (collect_phis bb.bb_instructions)))) /\
      (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
      ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) (DROP i bb.bb_instructions))))
End

Theorem regional_lineage_selected_phi_inv:
  !lv dfg cfg ch growth sb ctr fn fn_ops ps_end bb ps.
    lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn sb ctr =
      SOME (fn_ops, ps_end) /\
    EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
      inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    lineage_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
      bb.bb_label ps ==>
    regional_selected_phi_inv lv dfg sb bb 0 ps
Proof
  rpt gen_tac >> strip_tac >>
  drule_all lineage_state_static >> strip_tac >>
  pure_rewrite_tac[regional_selected_phi_inv_def, DROP_0] >>
  conj_tac >- simp[] >>
  conj_tac >-
    (rpt strip_tac >> drule_all regional_lineage_phi_depth >> metis_tac[]) >>
  metis_tac[]
QED

Theorem regional_lineage_phi_output_absent:
  !lv dfg cfg ch growth sb ctr fn fn_ops ps_end bb ps phi out.
    lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn sb ctr =
      SOME (fn_ops, ps_end) /\
    EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
      inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    lineage_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
      bb.bb_label ps /\ MEM phi (collect_phis bb.bb_instructions) /\
    MEM out phi.inst_outputs ==>
    ~MEM (Var out) ps.ps_stack /\ Var out NOTIN FDOM ps.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  drule_all lineage_state_static >> strip_tac >> gvs[] >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_mem] >>
  `fn_reachable fn bb.bb_label` by
    (drule lineage_state_dfs_fields >> strip_tac >>
     drule_all dfs_block_state_cfg_reachable >>
     metis_tac[fn_reachable_cfg_analyze]) >>
  `~MEM (Var out) (FLAT (MAP (\p. p.inst_operands)
    (collect_phis bb.bb_instructions)))` by
    (strip_tac >> gvs[MEM_FLAT, MEM_MAP] >>
     rename1 `MEM usephi (collect_phis _)` >>
     `~MEM out (inst_uses usephi)` by
       metis_tac[regional_phi_output_not_phi_source] >>
     gvs[inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var]) >>
  `MEM out (FLAT (MAP (\p. p.inst_outputs) bb.bb_instructions))` by
    (simp[MEM_FLAT, MEM_MAP] >>
     qexists_tac `phi.inst_outputs` >> simp[] >>
     qexists_tac `phi` >> metis_tac[collect_phis_mem]) >>
  metis_tac[]
QED

Theorem regional_pop_singleton_slots_layout:
  plan_slots_bounded sb ps /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled ==>
  plan_slots_bounded sb (SND (popmany_plan [v] ps)) /\
  spill_alloc_layout_wf (SND (popmany_plan [v] ps)).ps_alloc
    (SND (popmany_plan [v] ps)).ps_spilled
Proof
  strip_tac >> Cases_on `stack_get_depth v ps.ps_stack`
  >- simp[popmany_plan_def, popmany_individual_def, sortingTheory.QSORT_DEF,
          sortingTheory.PARTITION_DEF, sortingTheory.PART_DEF] >>
  rename1 `stack_get_depth v ps.ps_stack = SOME d` >>
  drule stack_get_depth_props >> strip_tac >>
  `plan_slots_bounded sb (SND (do_swap d ps))` by
    (irule do_swap_plan_slots_bounded >> metis_tac[PAIR]) >>
  drule_all do_swap_layout_wf >> strip_tac >>
  simp[popmany_plan_def, popmany_individual_def, is_contiguous_top_def,
       sortingTheory.QSORT_DEF, sortingTheory.PARTITION_DEF,
       sortingTheory.PART_DEF, LET_THM] >>
  Cases_on `d = 1`
  >- (gvs[do_swap_def, plan_slots_bounded_def] >> metis_tac[]) >>
  Cases_on `d = 0`
  >- (gvs[do_swap_def, plan_slots_bounded_def] >> metis_tac[]) >>
  gvs[] >> pairarg_tac >> gvs[plan_slots_bounded_def] >> metis_tac[]
QED

Theorem regional_selected_phi_slots_layout:
  generate_phi_plan phi nl F ps = (ops,qs) /\
  phi.inst_outputs = [out] /\
  stack_get_phi_depth (FILTER is_var_operand phi.inst_operands) ps.ps_stack = SOME d /\
  stack_peek d ps.ps_stack = Var src /\ ~MEM src nl /\
  plan_slots_bounded sb ps /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled ==>
  plan_slots_bounded sb qs /\ spill_alloc_layout_wf qs.ps_alloc qs.ps_spilled
Proof
  strip_tac >>
  qpat_x_assum `generate_phi_plan _ _ _ _ = _` mp_tac >>
  simp[generate_phi_plan_def, LET_THM, stackPlanTypesTheory.operand_to_string_def] >>
  Cases_on `MEM out nl`
  >- (simp[plan_slots_bounded_def] >> strip_tac >> gvs[plan_slots_bounded_def] >> metis_tac[]) >>
  simp[] >> pairarg_tac >> strip_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `popmany_plan [Var out] poked` >>
  `plan_slots_bounded sb poked /\
   spill_alloc_layout_wf poked.ps_alloc poked.ps_spilled` by
    (simp[Abbr `poked`, plan_slots_bounded_def] >>
     metis_tac[plan_slots_bounded_def]) >>
  drule_all regional_pop_singleton_slots_layout >>
  disch_then (qspec_then `Var out` mp_tac) >> gvs[]
QED

Theorem regional_selected_phi_wf:
  generate_phi_plan phi nl F ps = (ops,qs) /\
  phi.inst_outputs = [out] /\
  stack_get_phi_depth (FILTER is_var_operand phi.inst_operands) ps.ps_stack = SOME d /\
  d < LENGTH ps.ps_stack /\ stack_peek d ps.ps_stack = Var src /\
  ~MEM src nl /\ generated_plan_state_wf_marked sb ps /\
  ~MEM (Var out) ps.ps_stack /\ Var out NOTIN FDOM ps.ps_spilled ==>
  generated_plan_state_wf_marked sb qs
Proof
  strip_tac >>
  `plan_slots_bounded sb ps /\ spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
   ALL_DISTINCT (FILTER (\op. op <> dead_stack_marker) ps.ps_stack)` by
    gvs[generated_plan_state_wf_marked_def] >>
  drule_all regional_selected_phi_slots_layout >> strip_tac >>
  drule_all inventory_marked_phi_distinct >> strip_tac >>
  drule_all inventory_marked_phi_spilled >> strip_tac >>
  drule_all inventory_marked_phi_mem >> strip_tac >>
  gvs[generated_plan_state_wf_marked_def, pred_setTheory.IN_DISJOINT,
      pred_setTheory.IN_INTER, pred_setTheory.EXTENSION] >>
  metis_tac[]
QED

Theorem regional_selected_phi_output_absent:
  codegen_ready_fn fn /\ fn_reachable fn bb.bb_label /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  i < LENGTH (collect_phis bb.bb_instructions) /\
  regional_selected_phi_inv lv dfg sb bb i ps /\
  MEM out (EL i bb.bb_instructions).inst_outputs ==>
  ~MEM (Var out) ps.ps_stack /\ Var out NOTIN FDOM ps.ps_spilled
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_mem] >>
  `MEM (EL i bb.bb_instructions) (collect_phis bb.bb_instructions)` by
    metis_tac[collect_phis_index, EL_MEM] >>
  `~MEM (Var out) (FLAT (MAP (\p. p.inst_operands)
      (DROP i (collect_phis bb.bb_instructions))))` by
    (strip_tac >> gvs[MEM_FLAT, MEM_MAP] >>
     rename1 `MEM usephi (DROP i _)` >>
     `MEM usephi (collect_phis bb.bb_instructions)` by
       (drule rich_listTheory.MEM_DROP_IMP >> simp[]) >>
     `~MEM out (inst_uses usephi)` by
       metis_tac[regional_phi_output_not_phi_source] >>
     gvs[inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var]) >>
  `i < LENGTH bb.bb_instructions` by
    (mp_tac (Q.SPEC `bb.bb_instructions` collect_phis_length_bound) >> decide_tac) >>
  `MEM out (FLAT (MAP (\p. p.inst_outputs) (DROP i bb.bb_instructions)))` by
    (simp[MEM_FLAT, MEM_MAP] >>
     qexists_tac `(EL i bb.bb_instructions).inst_outputs` >> simp[] >>
     qexists_tac `EL i bb.bb_instructions` >> metis_tac[DROP_CONS_EL, MEM]) >>
  gvs[regional_selected_phi_inv_def] >> metis_tac[]
QED

Theorem regional_selected_phi_next_coverage:
  codegen_ready_fn fn /\ fn_reachable fn bb.bb_label /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  i < LENGTH (collect_phis bb.bb_instructions) /\
  regional_selected_phi_inv (liveness_analyze fn) dfg sb bb i ps /\
  (EL i bb.bb_instructions).inst_outputs = [out] /\
  generate_phi_plan (EL i bb.bb_instructions)
    (live_vars_at (liveness_analyze fn) bb.bb_label (i+1)) F ps = (ops,qs) /\
  stack_get_phi_depth (FILTER is_var_operand (EL i bb.bb_instructions).inst_operands)
    ps.ps_stack = SOME d /\ d < LENGTH ps.ps_stack /\
  stack_peek d ps.ps_stack = Var src /\
  MEM (Var src) (EL i bb.bb_instructions).inst_operands ==>
  !v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (i+1)) /\
    ~MEM (Var v) (FLAT (MAP (\p. p.inst_operands)
      (DROP (i+1) (collect_phis bb.bb_instructions)))) ==>
    MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled
Proof
  strip_tac >>
  `~MEM src (live_vars_at (liveness_analyze fn) bb.bb_label (i+1))` by
    (irule regional_ready_phi_source_dead >> simp[] >>
     gvs[inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var]) >>
  `~MEM (Var out) ps.ps_stack` by metis_tac[regional_selected_phi_output_absent, MEM] >>
  `generated_plan_state_wf_marked sb ps` by gvs[regional_selected_phi_inv_def] >>
  drule_all regional_phi_owned_subtraction >> disch_tac >>
  qx_gen_tac `v` >> strip_tac >>
  Cases_on `v = out` >- metis_tac[] >>
  `~MEM v (inst_defs (EL i bb.bb_instructions))` by simp[inst_defs_def] >>
  `i < LENGTH bb.bb_instructions` by
    (mp_tac (Q.SPEC `bb.bb_instructions` collect_phis_length_bound) >> decide_tac) >>
  `MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i)` by
    (irule (SRULE [LET_THM] live_vars_at_propagate) >> simp[arithmeticTheory.ADD1] >>
     metis_tac[ready_reachable_preorder, codegen_ready_fn_def]) >>
  `~MEM (Var v) (EL i bb.bb_instructions).inst_operands` by
    (strip_tac >>
     `MEM v (inst_uses (EL i bb.bb_instructions))` by
       gvs[inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var] >>
     metis_tac[regional_ready_phi_source_dead]) >>
  `DROP i (collect_phis bb.bb_instructions) =
    EL i bb.bb_instructions :: DROP (i+1) (collect_phis bb.bb_instructions)` by
    metis_tac[DROP_CONS_EL, collect_phis_index, arithmeticTheory.ADD1] >>
  gvs[regional_selected_phi_inv_def] >> metis_tac[]
QED

Theorem regional_indexed_phi_output:
  codegen_ready_fn fn /\ lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  i < LENGTH (collect_phis bb.bb_instructions) ==>
  ?out. (EL i bb.bb_instructions).inst_outputs = [out]
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_mem] >>
  `MEM (EL i bb.bb_instructions) (collect_phis bb.bb_instructions)` by
    metis_tac[collect_phis_index, EL_MEM] >>
  `MEM (EL i bb.bb_instructions) bb.bb_instructions /\
   (EL i bb.bb_instructions).inst_opcode = PHI` by metis_tac[collect_phis_mem] >>
  `inst_wf (EL i bb.bb_instructions)` by
    (gvs[codegen_ready_fn_def, fn_inst_wf_def] >> metis_tac[]) >>
  gvs[inst_wf_def, LENGTH_EQ_NUM_compute]
QED

Theorem regional_selected_phi_remaining:
  codegen_ready_fn fn /\ fn_reachable fn bb.bb_label /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  i < LENGTH (collect_phis bb.bb_instructions) /\
  regional_selected_phi_inv lv dfg sb bb i ps /\
  MEM (Var src) (EL i bb.bb_instructions).inst_operands /\
  MEM out (EL i bb.bb_instructions).inst_outputs /\
  qs.ps_spilled = ps.ps_spilled /\
  (!x. MEM x qs.ps_stack <=>
    (MEM x ps.ps_stack /\ x <> Var src) \/ (x = Var out /\ keep)) ==>
  !phi. MEM phi (DROP (i+1) (collect_phis bb.bb_instructions)) ==>
    ?v. MEM (Var v) phi.inst_operands /\ MEM (Var v) qs.ps_stack /\
      (!w. MEM (Var w) phi.inst_operands /\
        (MEM (Var w) qs.ps_stack \/ Var w IN FDOM qs.ps_spilled) ==> w = v)
Proof
  strip_tac >> qx_gen_tac `phi` >> disch_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_mem] >>
  `phi_uses_disjoint (collect_phis bb.bb_instructions)` by
    (drule_all ready_phi_block >> simp[phi_block_ready_def]) >>
  `MEM phi (collect_phis bb.bb_instructions)` by
    (drule rich_listTheory.MEM_DROP_IMP >> simp[]) >>
  `MEM (EL i bb.bb_instructions) (collect_phis bb.bb_instructions)` by
    metis_tac[collect_phis_index, EL_MEM] >>
  `~MEM (Var out) phi.inst_operands` by
    (strip_tac >>
     `~MEM out (inst_uses phi)` by metis_tac[regional_phi_output_not_phi_source] >>
     gvs[inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var]) >>
  `~MEM (Var src) phi.inst_operands` by
    (`?j. j < LENGTH (DROP (i+1) (collect_phis bb.bb_instructions)) /\
       EL j (DROP (i+1) (collect_phis bb.bb_instructions)) = phi` by
       metis_tac[MEM_EL] >>
     `i < j + (i+1) /\ j + (i+1) < LENGTH (collect_phis bb.bb_instructions)` by
       (gvs[LENGTH_DROP] >> decide_tac) >>
     `EL (j + (i+1)) (collect_phis bb.bb_instructions) = phi` by
       metis_tac[EL_DROP] >>
     `MEM src (inst_uses (EL i (collect_phis bb.bb_instructions)))` by
       metis_tac[collect_phis_index, inst_uses_def,
         passSharedDefsTheory.MEM_operand_vars_eq_Var] >>
     drule_all regional_phi_later_uses >>
     gvs[inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var]) >>
  `MEM phi (DROP i (collect_phis bb.bb_instructions))` by
    metis_tac[DROP_CONS_EL, collect_phis_index, MEM, arithmeticTheory.ADD1] >>
  `?v. MEM (Var v) phi.inst_operands /\ MEM (Var v) ps.ps_stack /\
    (!w. MEM (Var w) phi.inst_operands /\
      (MEM (Var w) ps.ps_stack \/ Var w IN FDOM ps.ps_spilled) ==> w = v)` by
    metis_tac[regional_selected_phi_inv_def] >>
  qexists_tac `v` >> conj_tac >- simp[] >>
  irule regional_phi_selected_frame >> simp[] >>
  qexistsl_tac [`out`, `keep`, `ps`, `src`] >> simp[] >> metis_tac[]
QED

Theorem regional_indexed_output_not_later:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ i < LENGTH bb.bb_instructions /\
  MEM out (EL i bb.bb_instructions).inst_outputs ==>
  ~MEM out (FLAT (MAP (\p. p.inst_outputs) (DROP (i+1) bb.bb_instructions)))
Proof
  strip_tac >> strip_tac >> gvs[MEM_FLAT, MEM_MAP] >>
  rename1 `MEM later (DROP (i+1) bb.bb_instructions)` >>
  `?j. j < LENGTH (DROP (i+1) bb.bb_instructions) /\
    EL j (DROP (i+1) bb.bb_instructions) = later` by metis_tac[MEM_EL] >>
  `j + (i+1) < LENGTH bb.bb_instructions /\ i <> j + (i+1)` by
    (gvs[LENGTH_DROP] >> decide_tac) >>
  `EL (j + (i+1)) bb.bb_instructions = later` by metis_tac[EL_DROP] >>
  metis_tac[ready_output_other_location]
QED


Theorem regional_indexed_phi_freshness:
  regional_selected_phi_inv lv dfg sb bb i ps /\
  DROP i (collect_phis bb.bb_instructions) =
    phi :: DROP (i+1) (collect_phis bb.bb_instructions) /\
  DROP i bb.bb_instructions = phi :: DROP (i+1) bb.bb_instructions /\
  (!v. MEM (Var v) phi.inst_operands /\
    (MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) ==> v = src) /\
  (!op. (MEM op qs.ps_stack \/ op IN FDOM qs.ps_spilled) ==>
    op = Var out \/ ((MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\ op <> Var src)) /\
  ~MEM out (FLAT (MAP (\p. p.inst_outputs) (DROP (i+1) bb.bb_instructions))) /\
  normalize_operand dfg [] (Var out) = Var out ==>
  !op v. (MEM op qs.ps_stack \/ op IN FDOM qs.ps_spilled) /\
    ~MEM op (FLAT (MAP (\p. p.inst_operands)
      (DROP (i+1) (collect_phis bb.bb_instructions)))) /\
    (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
    ~MEM v (FLAT (MAP (\p. p.inst_outputs) (DROP (i+1) bb.bb_instructions)))
Proof
  strip_tac >>
  `!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    ~MEM op (phi.inst_operands ++ FLAT (MAP (\p. p.inst_operands)
      (DROP (i+1) (collect_phis bb.bb_instructions)))) /\
    (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
    ~MEM v (FLAT (MAP (\p. p.inst_outputs) (DROP (i+1) bb.bb_instructions)))` by
    (gvs[regional_selected_phi_inv_def] >> metis_tac[MEM]) >>
  rpt gen_tac >> strip_tac >>
  (Cases_on `op = Var out` >- gvs[] >>
   `(MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\ op <> Var src` by
     metis_tac[] >>
   (Cases_on `MEM op phi.inst_operands`
    >- (Cases_on `op` >> gvs[] >> metis_tac[normalize_operand_def]) >>
    qpat_x_assum `!op v. _ ==> ~MEM v _` irule >>
    qexists_tac `op` >> simp[]))
QED

Theorem regional_selected_phi_inv_step:
  !fn bb dfg sb i ps ops qs.
  codegen_ready_fn fn /\ fn_reachable fn bb.bb_label /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  dfg = dfg_build_function fn /\
  i < LENGTH (collect_phis bb.bb_instructions) /\
  regional_selected_phi_inv (liveness_analyze fn) dfg sb bb i ps /\
  generate_phi_plan (EL i bb.bb_instructions)
    (live_vars_at (liveness_analyze fn) bb.bb_label (i+1)) F ps = (ops,qs) ==>
  regional_selected_phi_inv (liveness_analyze fn) dfg sb bb (i+1) qs
Proof
  rpt gen_tac >> strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_mem] >>
  `MEM (EL i bb.bb_instructions) (collect_phis bb.bb_instructions)` by
    metis_tac[collect_phis_index, EL_MEM] >>
  `DROP i (collect_phis bb.bb_instructions) =
    EL i bb.bb_instructions :: DROP (i+1) (collect_phis bb.bb_instructions)` by
    metis_tac[DROP_CONS_EL, collect_phis_index, arithmeticTheory.ADD1] >>
  drule_all regional_indexed_phi_output >> strip_tac >>
  `?src. MEM (Var src) (EL i bb.bb_instructions).inst_operands /\
    MEM (Var src) ps.ps_stack /\
    (!v. MEM (Var v) (EL i bb.bb_instructions).inst_operands /\
      (MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) ==> v = src)` by
    (gvs[regional_selected_phi_inv_def] >> metis_tac[MEM]) >>
  `?d. stack_get_phi_depth
    (FILTER is_var_operand (EL i bb.bb_instructions).inst_operands) ps.ps_stack = SOME d /\
    d < LENGTH ps.ps_stack /\ stack_peek d ps.ps_stack = Var src` by
    (irule regional_phi_physical_depth >> metis_tac[]) >>
  `~MEM src (live_vars_at (liveness_analyze fn) bb.bb_label (i+1))` by
    (irule regional_ready_phi_source_dead >> simp[] >>
     gvs[inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var]) >>
  `~MEM (Var out) ps.ps_stack /\ Var out NOTIN FDOM ps.ps_spilled` by
    metis_tac[regional_selected_phi_output_absent, MEM] >>
  `generated_plan_state_wf_marked sb ps /\
   ALL_DISTINCT (FILTER (\op. op <> dead_stack_marker) ps.ps_stack)` by
    gvs[regional_selected_phi_inv_def, generated_plan_state_wf_marked_def] >>
  drule_all inventory_marked_phi_mem >> disch_tac >>
  drule_all inventory_marked_phi_spilled >> disch_tac >>
  `MEM out (EL i bb.bb_instructions).inst_outputs` by simp[] >>
  mp_tac (Q.INST
    [`lv` |-> `liveness_analyze fn`,
     `keep` |-> `MEM out (live_vars_at (liveness_analyze fn) bb.bb_label (i+1))`]
    (SPEC_ALL regional_selected_phi_remaining)) >>
  (impl_tac >- simp[]) >> disch_tac >>
  pure_rewrite_tac[regional_selected_phi_inv_def] >>
  conj_tac >- (irule regional_selected_phi_wf >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (rpt strip_tac >> irule regional_selected_phi_next_coverage >> metis_tac[]) >>
  `i < LENGTH bb.bb_instructions` by
    (mp_tac (Q.SPEC `bb.bb_instructions` collect_phis_length_bound) >> decide_tac) >>
  `~MEM out (FLAT (MAP (\p. p.inst_outputs) (DROP (i+1) bb.bb_instructions)))` by
    metis_tac[regional_indexed_output_not_later] >>
  `normalize_operand dfg [] (Var out) = Var out` by
    metis_tac[regional_phi_output_normalize] >>
  `DROP i bb.bb_instructions = EL i bb.bb_instructions :: DROP (i+1) bb.bb_instructions` by
    metis_tac[DROP_CONS_EL, arithmeticTheory.ADD1] >>
  drule_all regional_phi_owned_subtraction >> disch_tac >>
  `!op. (MEM op qs.ps_stack \/ op IN FDOM qs.ps_spilled) ==>
    op = Var out \/ ((MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\ op <> Var src)` by
    metis_tac[] >>
  mp_tac (Q.INST [`lv` |-> `liveness_analyze fn`,
    `phi` |-> `EL i bb.bb_instructions`] (SPEC_ALL regional_indexed_phi_freshness)) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> simp[]
QED

Theorem regional_selected_phi_inv_prefix:
  !fn bb dfg cfg sb i j ps ops qs.
  codegen_ready_fn fn /\ fn_reachable fn bb.bb_label /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  dfg = dfg_build_function fn /\
  i + j <= LENGTH (collect_phis bb.bb_instructions) /\
  regional_selected_phi_inv (liveness_analyze fn) dfg sb bb i ps /\
  generate_block_insts_prefix (liveness_analyze fn) dfg cfg fn bb.bb_label
    F 0 (LENGTH bb.bb_instructions) i j (DROP i bb.bb_instructions) ps =
      SOME (ops, qs) ==>
  regional_selected_phi_inv (liveness_analyze fn) dfg sb bb (i+j) qs
Proof
  Induct_on `j`
  >- simp[generate_block_insts_prefix_def] >>
  rpt gen_tac >> strip_tac >>
  `i < LENGTH (collect_phis bb.bb_instructions)` by decide_tac >>
  `i < LENGTH bb.bb_instructions` by
    (mp_tac (Q.SPEC `bb.bb_instructions` collect_phis_length_bound) >> decide_tac) >>
  `DROP i bb.bb_instructions = EL i bb.bb_instructions :: DROP (i+1) bb.bb_instructions` by
    metis_tac[DROP_CONS_EL, arithmeticTheory.ADD1] >>
  `(EL i bb.bb_instructions).inst_opcode = PHI` by
    metis_tac[collect_phis_index, collect_phis_mem, EL_MEM] >>
  `DROP (i+1) bb.bb_instructions = [] ==> i+1 = LENGTH bb.bb_instructions` by
    (simp[DROP_EQ_NIL] >> decide_tac) >>
  `i+1 <= LENGTH bb.bb_instructions` by decide_tac >>
  `live_vars_at (liveness_analyze fn) bb.bb_label
    (if DROP (i+1) bb.bb_instructions = [] then LENGTH bb.bb_instructions else i+1) =
    live_vars_at (liveness_analyze fn) bb.bb_label (i+1)` by metis_tac[] >>
  qpat_x_assum `generate_block_insts_prefix _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once generate_block_insts_prefix_def, generate_inst_plan_def,
    is_pre_codegen_opcode_def, LET_THM] >>
  simp[AllCaseEqs()] >> strip_tac >>
  `i+1 = LENGTH bb.bb_instructions \/ ~(LENGTH bb.bb_instructions <= i+1)` by decide_tac >>
  gvs[] >>
  rename1 `generate_phi_plan _ _ _ ps = (step_ops, mid)` >>
  `regional_selected_phi_inv (liveness_analyze fn) (dfg_build_function fn) sb bb (i+1) mid` by
    (irule regional_selected_phi_inv_step >> simp[] >>
     qexistsl [`step_ops`, `ps`] >> gvs[]) >>
  `i + SUC j = (i+1)+j` by decide_tac >>
  pop_assum SUBST1_TAC >> first_x_assum irule >> simp[] >>
  metis_tac[arithmeticTheory.ADD_CLAUSES, arithmeticTheory.ADD1]
QED

Theorem regional_selected_phi_inv_block_prefix:
  !fn bb dfg cfg sb j ps0 ops qs.
  codegen_ready_fn fn /\ fn_reachable fn bb.bb_label /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  dfg = dfg_build_function fn /\
  LENGTH (get_params bb.bb_instructions) = 0 /\
  non_param_insts bb = bb.bb_instructions /\ bb_is_halting bb = F /\
  j <= LENGTH (collect_phis bb.bb_instructions) /\
  regional_selected_phi_inv (liveness_analyze fn) dfg sb bb 0 ps0 /\
  generate_block_insts_prefix (liveness_analyze fn) dfg cfg fn bb.bb_label
    (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
    (LENGTH bb.bb_instructions) 0 j (non_param_insts bb) ps0 =
      SOME (ops, qs) ==>
  regional_selected_phi_inv (liveness_analyze fn) dfg sb bb j qs
Proof
  rpt strip_tac >>
  mp_tac (Q.INST [`i` |-> `0`, `ps` |-> `ps0`]
    (SPEC_ALL regional_selected_phi_inv_prefix)) >>
  gvs[]
QED

Theorem regional_phi_preparation_identity:
  !fn bb lv ps.
    codegen_ready_fn fn /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    collect_phis bb.bb_instructions <> [] ==>
    (if bb = HD fn.fn_blocks then prepare_params_plan lv fn ps else ([],ps)) = ([],ps) /\
    (if LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label) = 1
     then clean_stack_plan lv (cfg_analyze fn) fn bb ps else ([],ps)) = ([],ps)
Proof
  rpt gen_tac >> strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_mem] >>
  `fn_entry_label fn <> SOME bb.bb_label` by
    (Cases_on `collect_phis bb.bb_instructions` >> gvs[] >>
     metis_tac[regional_phi_nonentry, MEM]) >>
  `bb <> HD fn.fn_blocks` by
    (Cases_on `fn.fn_blocks` >>
     gvs[fn_entry_label_def, entry_block_def] >> metis_tac[]) >>
  `~(LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label) = 1)` by
    (gvs[codegen_ready_fn_def, phis_at_joins_def, EVERY_MEM, NULL_EQ] >>
     strip_tac >>
     qpat_x_assum `!bb'. MEM bb' _ ==> _` (qspec_then `bb` mp_tac) >> simp[]) >>
  simp[]
QED

Theorem regional_selected_phi_inv_cleanup_fields:
  !lv dfg sb bb i ps h promised.
    regional_selected_phi_inv lv dfg sb bb i
      (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) <=>
    regional_selected_phi_inv lv dfg sb bb i ps
Proof
  simp[regional_selected_phi_inv_def, generated_plan_state_wf_marked_def,
    plan_slots_bounded_def]
QED

Theorem regional_lineage_prepared_selected_phi_inv:
  !lv dfg cfg ch growth sb ctr fn fn_ops ps_end bb ps_l h promised
    param_ops ps1 clean_ops ps2.
    lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn sb ctr =
      SOME (fn_ops, ps_end) /\
    EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
      inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    lineage_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
      bb.bb_label ps_l /\ collect_phis bb.bb_instructions <> [] /\
    (if bb = HD fn.fn_blocks then prepare_params_plan lv fn
       (ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
     else ([], ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)) =
      (param_ops, ps1) /\
    (if LENGTH (cfg_preds_of cfg bb.bb_label) = 1
     then clean_stack_plan lv cfg fn bb ps1 else ([], ps1)) = (clean_ops, ps2) ==>
    regional_selected_phi_inv lv dfg sb bb 0 ps2
Proof
  rpt gen_tac >> strip_tac >>
  `regional_selected_phi_inv lv dfg sb bb 0 ps_l` by
    (drule_all regional_lineage_selected_phi_inv >> simp[]) >>
  drule_all regional_phi_preparation_identity >>
  disch_then (qspecl_then [`lv`,
    `ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>`] mp_tac) >>
  strip_tac >> gvs[] >>
  drule_all regional_phi_preparation_identity >>
  disch_then (qspecl_then [`lv`, `ps1`] mp_tac) >>
  gvs[regional_selected_phi_inv_cleanup_fields]
QED

(* nonentry_block_no_params is downstream of the target, so cannot be imported. *)
Theorem regional_phi_no_params:
  !fn bb. codegen_ready_fn fn /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    collect_phis bb.bb_instructions <> [] ==>
    get_params bb.bb_instructions = [] /\
    non_param_insts bb = bb.bb_instructions
Proof
  rpt gen_tac >> strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_mem] >>
  `fn_entry_label fn <> SOME bb.bb_label` by
    (Cases_on `collect_phis bb.bb_instructions` >> gvs[] >>
     metis_tac[regional_phi_nonentry, MEM]) >>
  `bb <> HD fn.fn_blocks` by
    (Cases_on `fn.fn_blocks` >>
     gvs[fn_entry_label_def, entry_block_def] >> metis_tac[]) >>
  `canonical_param_prefix fn` by gvs[codegen_ready_fn_def] >>
  `no_param_insts bb.bb_instructions` by
    (Cases_on `fn.fn_blocks` >> gvs[canonical_param_prefix_def, EVERY_MEM]) >>
  gvs[no_param_insts_def] >>
  conj_tac >- (Cases_on `bb.bb_instructions` >> gvs[get_params_def]) >>
  irule non_param_insts_all_neq >> simp[]
QED

Theorem regional_lineage_selected_phi_prefix:
  !lv dfg cfg ch growth sb ctr fn fn_ops ps_end bb ps_l h promised
    param_ops ps1 clean_ops ps2 j ops qs.
    lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn sb ctr =
      SOME (fn_ops, ps_end) /\
    EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
      inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    lineage_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
      bb.bb_label ps_l /\ collect_phis bb.bb_instructions <> [] /\
    ~bb_is_halting bb /\
    (if bb = HD fn.fn_blocks then prepare_params_plan lv fn
       (ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
     else ([], ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)) =
      (param_ops, ps1) /\
    (if LENGTH (cfg_preds_of cfg bb.bb_label) = 1
     then clean_stack_plan lv cfg fn bb ps1 else ([], ps1)) = (clean_ops, ps2) /\
    j <= LENGTH (collect_phis bb.bb_instructions) /\
    generate_block_insts_prefix lv dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) 0 j (non_param_insts bb) ps2 = SOME (ops, qs) ==>
    regional_selected_phi_inv lv dfg sb bb j qs
Proof
  rpt gen_tac >> strip_tac >>
  `regional_selected_phi_inv lv dfg sb bb 0 ps2` by
    (drule_all regional_lineage_prepared_selected_phi_inv >> simp[]) >>
  `get_params bb.bb_instructions = [] /\
   non_param_insts bb = bb.bb_instructions` by
    (drule_all regional_phi_no_params >> simp[]) >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `fn_reachable fn bb.bb_label` by
    (drule lineage_state_dfs_fields >> strip_tac >> gvs[] >>
     drule_all dfs_block_state_cfg_reachable >>
     metis_tac[fn_reachable_cfg_analyze]) >>
  gvs[] >>
  irule (INST_TYPE [alpha |-> ``:cfg_analysis``]
    regional_selected_phi_inv_block_prefix) >> simp[] >>
  qexistsl [`cfg_analyze fn`, `ops`, `ps2`] >> simp[]
QED

Theorem regional_selected_phi_exit_wf:
  !lv dfg sb bb ps.
    regional_selected_phi_inv lv dfg sb bb
      (LENGTH (collect_phis bb.bb_instructions)) ps ==>
    generated_plan_state_wf_marked sb ps
Proof
  simp[regional_selected_phi_inv_def]
QED

Theorem regional_selected_phi_exit_coverage:
  !lv dfg sb bb ps v.
    regional_selected_phi_inv lv dfg sb bb
      (LENGTH (collect_phis bb.bb_instructions)) ps /\
    MEM v (live_vars_at lv bb.bb_label (LENGTH (collect_phis bb.bb_instructions))) ==>
    MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled
Proof
  simp[regional_selected_phi_inv_def] >> metis_tac[]
QED

Theorem regional_selected_phi_exit_freshness:
  !lv dfg sb bb ps op v.
    regional_selected_phi_inv lv dfg sb bb
      (LENGTH (collect_phis bb.bb_instructions)) ps /\
    (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
    ~MEM v (FLAT (MAP (\inst. inst.inst_outputs)
      (DROP (LENGTH (collect_phis bb.bb_instructions)) bb.bb_instructions)))
Proof
  simp[regional_selected_phi_inv_def] >> metis_tac[]
QED

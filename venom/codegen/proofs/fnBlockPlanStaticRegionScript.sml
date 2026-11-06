Theory fnBlockPlanStaticRegion
Ancestors
  fnBlockPlanStaticPromises fnBlockPlanStaticInventory fnPlanLineage fnPlanLineageJoin
  fnLineageInv fnPlanPrefix list stackPlanGen fnFrameBoundaryGenRet codegenReadyCompute
  fnBlockPlanStaticOffsetLive livenessProofs livenessTransferProofs venomWf venomExecProofs rich_list
  removeUnusedSsaProofs venomInst cfgNormSupplyProofs cfgNormBase
  fnFrameBoundaryEntryParams stackModel genBlockSim fnLineageStatic fnBlockPlanStaticFacts

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

Theory fnBlockPlanStaticRegion
Ancestors
  fnBlockPlanStaticPromises fnBlockPlanStaticInventory fnPlanLineage fnPlanLineageJoin
  fnLineageInv fnPlanPrefix list stackPlanGen fnFrameBoundaryGenRet codegenReadyCompute
  fnBlockPlanStaticOffsetLive livenessProofs livenessTransferProofs
  fnFrameBoundaryEntryParams

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

Theory fnPlanLineageSetup
Ancestors
  fnPlanLineageDemand fnPlanLineageInventory stackPlanGen stackModel stackPlanTypes venomState reorderSim list rich_list venomWf venomInst callLayoutDefs
Libs
  pred_setTheory finite_mapTheory stackPlanOpsTheory

Theorem optimistic_swap_plan_inventory:
  !dfg inst live term ps.
    ALL_DISTINCT ps.ps_stack ==>
    ALL_DISTINCT (SND (optimistic_swap_plan dfg inst live term ps)).ps_stack /\
    set (SND (optimistic_swap_plan dfg inst live term ps)).ps_stack = set ps.ps_stack /\
    (SND (optimistic_swap_plan dfg inst live term ps)).ps_spilled = ps.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  simp[optimistic_swap_plan_def, LET_THM] >>
  rpt IF_CASES_TAC >> simp[] >>
  Cases_on `stack_get_depth (Var (LAST live)) ps.ps_stack` >> simp[] >>
  drule stack_get_depth_props >> strip_tac >>
  `ps.ps_stack = [] ++ ps.ps_stack` by simp[] >>
  drule_all do_swap_core >> simp[] >>
  metis_tac[do_swap_spilled_unchanged]
QED

Theorem parameter_push_fold:
  !xs ps f.
    FOLDL (\p x. p with ps_stack := stack_push (f x) p.ps_stack) ps xs =
    ps with ps_stack := ps.ps_stack ++ MAP f xs
Proof
  Induct >> simp[stack_push_def, SNOC_APPEND] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[]
QED

Theorem ready_parameter_names_distinct:
  !fn. codegen_ready_fn fn /\ fn.fn_blocks <> [] ==>
    ALL_DISTINCT (MAP (\inst. HD inst.inst_outputs)
      (get_params (HD fn.fn_blocks).bb_instructions))
Proof
  rpt strip_tac >>
  `ssa_form fn /\ canonical_param_prefix fn` by
    gvs[codegen_ready_fn_def] >>
  qpat_x_assum `canonical_param_prefix fn` mp_tac >>
  rewrite_tac[canonical_param_prefix_iff] >>
  disch_then (qx_choose_then `entry` (qx_choose_then `rest`
    (qx_choose_then `users` (qx_choose_then `fmp` (qx_choose_then `retpc`
      (qx_choose_then `tail_insts` (map_every assume_tac o CONJUNCTS))))))) >>
  gnvs[] >>
  `get_params entry.bb_instructions = users ++ fmp ++ retpc` by
    (gnvs[] >> rewrite_tac[APPEND_ASSOC] >>
     irule get_params_canonical_prefix >> simp[] >>
     qexists_tac `0` >> simp[APPEND_ASSOC]) >>
  `ALL_DISTINCT (FLAT (MAP inst_defs (users ++ fmp ++ retpc)))` by
    (gvs[ssa_form_def, fn_insts_def, fn_insts_blocks_def,
         lambdify inst_defs_def, MAP_APPEND, FLAT_APPEND, ALL_DISTINCT_APPEND] >>
     metis_tac[]) >>
  drule param_insts_from_defs >> disch_then assume_tac >>
  metis_tac[]
QED

Theorem popmany_dead_variables_inventory:
  !ps names live.
    ps.ps_stack = MAP Var names /\ ALL_DISTINCT names /\
    EVERY (\v. MEM v names) live ==>
    ALL_DISTINCT (SND (popmany_plan
      (FILTER is_var_operand (FILTER
        (\v. ~MEM (operand_to_string v) live) ps.ps_stack)) ps)).ps_stack /\
    set (SND (popmany_plan
      (FILTER is_var_operand (FILTER
        (\v. ~MEM (operand_to_string v) live) ps.ps_stack)) ps)).ps_stack =
      set (MAP Var live) /\
    (SND (popmany_plan
      (FILTER is_var_operand (FILTER
        (\v. ~MEM (operand_to_string v) live) ps.ps_stack)) ps)).ps_spilled = ps.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  qmatch_goalsub_abbrev_tac `popmany_plan dead ps` >>
  `ALL_DISTINCT ps.ps_stack` by
    (simp[] >> irule ALL_DISTINCT_MAP_INJ >> simp[]) >>
  mp_tac (Q.SPECL [`dead`, `[]`, `ps.ps_stack`, `ps`] popmany_plan_core) >>
  simp[] >> strip_tac >>
  `set ps.ps_stack DIFF set dead = set (MAP Var live)` by
    (simp[Abbr `dead`, EXTENSION, MEM_FILTER, MEM_MAP, EVERY_MEM] >>
     gen_tac >> Cases_on `x` >>
     gvs[stackPlanTypesTheory.is_var_operand_def,
         stackPlanTypesTheory.operand_to_string_def, EVERY_MEM] >> metis_tac[]) >>
  gvs[popmany_plan_spilled_unchanged]
QED

Theorem prepare_params_plan_inventory:
  !liveness fn ps.
    ps.ps_stack = [] /\
    ALL_DISTINCT (MAP (\inst. HD inst.inst_outputs)
      (get_params (HD fn.fn_blocks).bb_instructions)) /\
    EVERY (\v. MEM v (MAP (\inst. HD inst.inst_outputs)
      (get_params (HD fn.fn_blocks).bb_instructions)))
      (live_vars_at liveness (HD fn.fn_blocks).bb_label
        (LENGTH (get_params (HD fn.fn_blocks).bb_instructions))) ==>
    ALL_DISTINCT (SND (prepare_params_plan liveness fn ps)).ps_stack /\
    set (SND (prepare_params_plan liveness fn ps)).ps_stack =
      set (MAP Var (live_vars_at liveness (HD fn.fn_blocks).bb_label
        (LENGTH (get_params (HD fn.fn_blocks).bb_instructions)))) /\
    (SND (prepare_params_plan liveness fn ps)).ps_spilled = ps.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `get_params (HD fn.fn_blocks).bb_instructions = []`
  >- (gvs[prepare_params_plan_def, EVERY_MEM, LET_THM] >>
      `live_vars_at liveness (HD fn.fn_blocks).bb_label 0 = []` by
        (Cases_on `live_vars_at liveness (HD fn.fn_blocks).bb_label 0` >> gvs[] >> metis_tac[]) >> simp[]) >>
  simp[prepare_params_plan_def, LET_THM, parameter_push_fold] >>
  qmatch_goalsub_abbrev_tac `popmany_plan dead pushed` >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  `pushed.ps_stack = MAP Var (MAP (\inst. HD inst.inst_outputs)
     (get_params (HD fn.fn_blocks).bb_instructions))` by
    simp[Abbr `pushed`, MAP_MAP_o, combinTheory.o_DEF] >>
  drule_all popmany_dead_variables_inventory >>
  simp[Abbr `dead`, Abbr `pushed`, MAP_MAP_o, combinTheory.o_DEF] >>
  strip_tac >>
  qpat_x_assum `ps.ps_stack = []` kall_tac >>
  qpat_x_assum `ALL_DISTINCT (MAP _ _)` kall_tac >>
  qpat_x_assum `EVERY _ _` kall_tac >>
  qpat_x_assum `get_params _ <> []` kall_tac >>
  qmatch_goalsub_abbrev_tac `set (MAP Var live)` >>
  drule optimistic_swap_plan_inventory >>
  disch_then (qspecl_then [`dfg_empty`, `LAST (get_params (HD fn.fn_blocks).bb_instructions)`,
    `live`, `case FIND (\inst. ~is_param_opcode inst.inst_opcode)
      (HD fn.fn_blocks).bb_instructions of NONE => F | SOME inst => is_terminator inst.inst_opcode`] mp_tac) >>
  gvs[]
QED

Theorem native_parameter_inventory:
  !fn ch growth spill_base lbl_ctr.
    codegen_ready_fn fn /\ fn.fn_blocks <> [] ==>
    ALL_DISTINCT (SND (prepare_params_plan (liveness_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr))).ps_stack /\
    set (SND (prepare_params_plan (liveness_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr))).ps_stack =
      set (MAP Var (live_vars_at (liveness_analyze fn) (HD fn.fn_blocks).bb_label
        (LENGTH (get_params (HD fn.fn_blocks).bb_instructions)))) /\
    (SND (prepare_params_plan (liveness_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr))).ps_spilled = FEMPTY
Proof
  rpt gen_tac >> strip_tac >>
  drule_all ready_parameter_names_distinct >> strip_tac >>
  drule_all post_parameter_demand_ready >> strip_tac >>
  mp_tac (Q.SPECL [`liveness_analyze fn`, `fn`,
    `init_cleanup_plan_state ch growth spill_base lbl_ctr`] prepare_params_plan_inventory) >>
  simp[init_cleanup_plan_state_def, init_plan_state_def]
QED

Theorem native_parameter_coverage:
  !fn ch growth spill_base lbl_ctr.
    codegen_ready_fn fn /\ fn.fn_blocks <> [] ==>
    EVERY (\v. MEM (Var v)
      (SND (prepare_params_plan (liveness_analyze fn) fn
        (init_cleanup_plan_state ch growth spill_base lbl_ctr))).ps_stack)
      (live_vars_at (liveness_analyze fn) (HD fn.fn_blocks).bb_label
        (LENGTH (get_params (HD fn.fn_blocks).bb_instructions)))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all native_parameter_inventory >> strip_tac >>
  simp[EVERY_MEM, MEM_MAP] >> metis_tac[]
QED

Theorem native_parameter_lineage_inventory:
  !fn ch growth spill_base lbl_ctr.
    codegen_ready_fn fn /\ fn.fn_blocks <> [] ==>
    lineage_inventory
      (set (MAP Var (live_vars_at (liveness_analyze fn) (HD fn.fn_blocks).bb_label
        (LENGTH (get_params (HD fn.fn_blocks).bb_instructions)))))
      (SND (prepare_params_plan (liveness_analyze fn) fn
        (init_cleanup_plan_state ch growth spill_base lbl_ctr)))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all native_parameter_inventory >>
  disch_then (qspecl_then [`ch`, `growth`, `spill_base`, `lbl_ctr`] strip_assume_tac) >>
  qmatch_goalsub_abbrev_tac `lineage_inventory inventory_set p` >>
  simp[lineage_inventory_def] >>
  qexistsl_tac [`0`, `p.ps_stack`] >>
  simp[lineage_core_def, EVERY_MEM] >>
  qpat_x_assum `set _ = _` mp_tac >>
  simp[Abbr `inventory_set`, EXTENSION, MEM_MAP] >> metis_tac[is_var_operand_def]
QED

Theorem native_parameter_depth_exists:
  !fn ch growth spill_base lbl_ctr v.
    codegen_ready_fn fn /\ fn.fn_blocks <> [] /\
    MEM v (live_vars_at (liveness_analyze fn) (HD fn.fn_blocks).bb_label
      (LENGTH (get_params (HD fn.fn_blocks).bb_instructions))) ==>
    ?d. stack_get_depth (Var v)
      (SND (prepare_params_plan (liveness_analyze fn) fn
        (init_cleanup_plan_state ch growth spill_base lbl_ctr))).ps_stack = SOME d
Proof
  rpt gen_tac >> strip_tac >>
  drule_all native_parameter_coverage >>
  disch_then (qspecl_then [`ch`, `growth`, `spill_base`, `lbl_ctr`] mp_tac) >>
  simp[EVERY_MEM] >> strip_tac >>
  `MEM (Var v) (SND (prepare_params_plan (liveness_analyze fn) fn
     (init_cleanup_plan_state ch growth spill_base lbl_ctr))).ps_stack` by metis_tac[] >>
  gvs[GSYM stack_get_depth_is_some, optionTheory.IS_SOME_EXISTS]
QED

Theorem native_parameter_spill_inventory:
  !fn ch growth spill_base lbl_ctr v d.
    codegen_ready_fn fn /\ fn.fn_blocks <> [] /\
    stack_get_depth (Var v)
      (SND (prepare_params_plan (liveness_analyze fn) fn
        (init_cleanup_plan_state ch growth spill_base lbl_ctr))).ps_stack = SOME d /\
    d <= 16 ==>
    lineage_inventory
      (set (MAP Var (live_vars_at (liveness_analyze fn) (HD fn.fn_blocks).bb_label
        (LENGTH (get_params (HD fn.fn_blocks).bb_instructions)))))
      (SND (do_spill_at d (SND (prepare_params_plan (liveness_analyze fn) fn
        (init_cleanup_plan_state ch growth spill_base lbl_ctr)))))
Proof
  rpt gen_tac >> strip_tac >>
  irule do_spill_at_lineage_inventory >>
  simp[] >> conj_tac >- (qexists_tac `v` >> simp[]) >>
  irule native_parameter_lineage_inventory >> simp[]
QED

(* Fresh output insertion does not change persistent resources. *)
Theorem fresh_outputs_residual_budget:
  !outputs ps spillbase.
    residual_budget_wf spillbase [] ps /\ ALL_DISTINCT outputs /\
    EVERY (\v. ~MEM (Var v) ps.ps_stack /\
      Var v NOTIN FDOM ps.ps_spilled) outputs ==>
    residual_budget_wf spillbase []
      (ps with ps_stack := ps.ps_stack ++ MAP Var outputs)
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  `residual_budget_wf spillbase []
     (ps with ps_stack := ps.ps_stack ++ [Var h])` by
    (gvs[residual_budget_wf_def, elem_count_append, LIST_ELEM_COUNT_THM] >>
     conj_tac >> rpt strip_tac >> Cases_on `op = Var h` >>
     gvs[GSYM LIST_ELEM_COUNT_MEM, LIST_ELEM_COUNT_DEF] >>
     first_x_assum (qspec_then `op` mp_tac) >> simp[] >> decide_tac) >>
  first_x_assum (qspecl_then
    [`ps with ps_stack := ps.ps_stack ++ [Var h]`, `spillbase`] mp_tac) >>
  simp[EVERY_MEM, MEM_MAP, APPEND_ASSOC] >>
  impl_tac >- (rpt strip_tac >> gvs[EVERY_MEM] >> metis_tac[]) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[]
QED

Theorem output_push_marker_core:
  !ps m core spillbase outputs qs.
    ps.ps_stack = REPLICATE m dead_stack_marker ++ core /\
    residual_budget_wf spillbase [] (ps with ps_stack := core) /\
    ALL_DISTINCT outputs /\
    EVERY (\v. ~MEM (Var v) core /\ Var v NOTIN FDOM ps.ps_spilled) outputs /\
    qs = FOLDL (\p v. p with ps_stack := stack_push (Var v) p.ps_stack)
      ps outputs ==>
    qs.ps_stack = REPLICATE m dead_stack_marker ++ (core ++ MAP Var outputs) /\
    qs.ps_spilled = ps.ps_spilled /\ qs.ps_alloc = ps.ps_alloc /\
    residual_budget_wf spillbase [] (qs with ps_stack := core ++ MAP Var outputs)
Proof
  rpt gen_tac >> strip_tac >>
  drule fresh_outputs_residual_budget >>
  disch_then (qspec_then `outputs` mp_tac) >>
  simp[] >> strip_tac >>
  gvs[parameter_push_fold, APPEND_ASSOC]
QED

Theorem output_push_core_coverage:
  !ps core outputs qs nl.
    (!v. MEM v nl ==> MEM v outputs \/ MEM (Var v) core \/
      Var v IN FDOM ps.ps_spilled) /\
    qs = FOLDL (\p v. p with ps_stack := stack_push (Var v) p.ps_stack)
      ps outputs ==>
    !v. MEM v nl ==> MEM (Var v) (core ++ MAP Var outputs) \/
      Var v IN FDOM qs.ps_spilled
Proof
  simp[parameter_push_fold, MEM_MAP] >> metis_tac[]
QED

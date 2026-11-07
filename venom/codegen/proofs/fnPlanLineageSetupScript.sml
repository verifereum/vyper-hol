Theory fnPlanLineageSetup
Ancestors
  fnPlanLineageSuffix fnPlanLineageDemand fnPlanLineageInventory stackPlanGen stackModel stackPlanTypes venomState reorderSim list rich_list venomWf venomInst callLayoutDefs
Libs
  pred_setTheory finite_mapTheory stackPlanOpsTheory fnPlanLineageReplayTheory doSwapSimTheory planSpillBoundsTheory cleanOpsSimTheory

Theorem optimistic_swap_plan_core_step[local]:
  !ps m core dfg inst live term qs.
    ps.ps_stack = REPLICATE m dead_stack_marker ++ core /\
    qs = SND (optimistic_swap_plan dfg inst live term ps) ==>
    qs = ps \/ ?d. d < LENGTH core /\ qs = SND (do_swap d ps)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[optimistic_swap_plan_def, LET_THM] >>
  rpt IF_CASES_TAC >> gvs[] >>
  Cases_on `stack_get_depth (Var (LAST live)) ps.ps_stack` >> gvs[] >>
  disj2_tac >> qexists_tac `x` >> simp[] >>
  `Var (LAST live) <> dead_stack_marker` by simp[dead_stack_marker_def] >>
  `stack_get_depth (Var (LAST live)) core = SOME x` by
    metis_tac[stack_get_depth_bottom_dead] >>
  metis_tac[stack_get_depth_props]
QED

Theorem optimistic_swap_plan_core_inventory:
  !ps m core dfg inst live term qs.
    ps.ps_stack = REPLICATE m dead_stack_marker ++ core /\
    ALL_DISTINCT core /\
    qs = SND (optimistic_swap_plan dfg inst live term ps) ==>
    ?rest. qs.ps_stack = REPLICATE m dead_stack_marker ++ rest /\
      ALL_DISTINCT rest /\ set rest = set core /\ qs.ps_spilled = ps.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  drule_all optimistic_swap_plan_core_step >> strip_tac
  >- (gvs[] >> qexists_tac `core` >> simp[]) >>
  qexists_tac `stack_swap d core` >>
  drule_all do_swap_core >> simp[do_swap_spilled_unchanged]
QED

Theorem optimistic_swap_plan_inventory:
  !dfg inst live term ps.
    ALL_DISTINCT ps.ps_stack ==>
    ALL_DISTINCT (SND (optimistic_swap_plan dfg inst live term ps)).ps_stack /\
    set (SND (optimistic_swap_plan dfg inst live term ps)).ps_stack = set ps.ps_stack /\
    (SND (optimistic_swap_plan dfg inst live term ps)).ps_spilled = ps.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  `ps.ps_stack = REPLICATE 0 dead_stack_marker ++ ps.ps_stack` by simp[] >>
  drule optimistic_swap_plan_core_inventory >> simp[]
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

Theorem regular_post_emit_tail_core_sets:
  !ps m core outputs live halting dfg inst term deleted ps8 ps9 final.
    ps.ps_stack = REPLICATE m dead_stack_marker ++ core /\ ALL_DISTINCT core /\
    deleted = (if outputs <> [] /\ (~halting \/ LENGTH outputs > 1)
      then MAP Var (FILTER (\v. ~MEM v live) outputs) else []) /\
    ps8 = (if outputs <> [] /\ (~halting \/ LENGTH outputs > 1)
      then SND (popmany_plan (MAP Var (FILTER (\v. ~MEM v live) outputs)) ps)
      else ps) /\
    ps9 = (if outputs <> [] /\ FILTER (\v. MEM v live) outputs <> []
      then SND (optimistic_swap_plan dfg inst live term ps8) else ps8) /\
    final = release_dead_spills live ps9 ==>
    ?rest. final.ps_stack = REPLICATE m dead_stack_marker ++ rest /\
      ALL_DISTINCT rest /\ set rest = set core DIFF set deleted /\
      FDOM final.ps_spilled = FDOM ps.ps_spilled INTER set (MAP Var live)
Proof
  rpt gen_tac >> strip_tac >>
  `?core8. ps8.ps_stack = REPLICATE m dead_stack_marker ++ core8 /\
     ALL_DISTINCT core8 /\ set core8 = set core DIFF set deleted /\
     ps8.ps_spilled = ps.ps_spilled` by
    (Cases_on `outputs <> [] /\ (~halting \/ LENGTH outputs > 1)`
     >- (gvs[] >> drule popmany_plan_core >>
         disch_then (qspec_then `MAP Var (FILTER (\v. ~MEM v live) outputs)` mp_tac) >>
         simp[DISJOINT_DEF, EXTENSION, MEM_MAP, dead_stack_marker_def,
              popmany_plan_spilled_unchanged]) >>
     gvs[] >> qexists_tac `core` >> simp[]) >>
  `?core9. ps9.ps_stack = REPLICATE m dead_stack_marker ++ core9 /\
     ALL_DISTINCT core9 /\ set core9 = set core8 /\
     ps9.ps_spilled = ps8.ps_spilled` by
    (Cases_on `outputs <> [] /\ FILTER (\v. MEM v live) outputs <> []` >> gvs[]
     >- (drule optimistic_swap_plan_core_inventory >> simp[]) >>
     qexists_tac `core8` >> simp[]) >>
  `final.ps_stack = ps9.ps_stack` by
    (qpat_x_assum `final = _` SUBST_ALL_TAC >>
     rpt (pop_assum kall_tac) >> simp[release_dead_spills_def] >>
     qspec_tac (`FILTER (\(op,off). case op of Lit v => T | Var v => ~MEM v live | Label v => T)
       (fmap_to_alist ps9.ps_spilled)`, `xs`) >>
     qid_spec_tac `ps9` >> Induct_on `xs` >> simp[] >>
     Cases_on `h` >> simp[]) >>
  qexists_tac `core9` >> gvs[release_dead_spills_domain]
QED

Theorem regular_post_emit_tail_sets:
  !ps outputs live halting dfg inst term deleted ps8 ps9 final.
    ALL_DISTINCT ps.ps_stack /\
    deleted = (if outputs <> [] /\ (~halting \/ LENGTH outputs > 1)
      then MAP Var (FILTER (\v. ~MEM v live) outputs) else []) /\
    ps8 = (if outputs <> [] /\ (~halting \/ LENGTH outputs > 1)
      then SND (popmany_plan (MAP Var (FILTER (\v. ~MEM v live) outputs)) ps)
      else ps) /\
    ps9 = (if outputs <> [] /\ FILTER (\v. MEM v live) outputs <> []
      then SND (optimistic_swap_plan dfg inst live term ps8) else ps8) /\
    final = release_dead_spills live ps9 ==>
    ALL_DISTINCT final.ps_stack /\
    set final.ps_stack = set ps.ps_stack DIFF set deleted /\
    FDOM final.ps_spilled = FDOM ps.ps_spilled INTER set (MAP Var live)
Proof
  rpt gen_tac >> strip_tac >>
  `ps.ps_stack = REPLICATE 0 dead_stack_marker ++ ps.ps_stack` by simp[] >>
  drule_all regular_post_emit_tail_core_sets >> simp[]
QED

(* Deep swaps use scratch allocation; it is not an unchanged-state field. *)
Theorem deep_swap_changes_allocator_probe:
  (SND (do_swap 17
    ((init_cleanup_plan_state NONE [] 0 0) with ps_stack :=
      MAP Var ["a";"b";"c";"d";"e";"f";"g";"h";"i";
               "j";"k";"l";"m";"n";"o";"p";"q";"r"]))).ps_alloc <>
    (init_cleanup_plan_state NONE [] 0 0).ps_alloc
Proof
  EVAL_TAC
QED

Theorem residual_budget_wf_optimistic_swap_plan:
  !base pending dfg inst live term ps.
    residual_budget_wf base pending ps ==>
    residual_budget_wf base pending
      (SND (optimistic_swap_plan dfg inst live term ps))
Proof
  rpt gen_tac >> strip_tac >>
  simp[optimistic_swap_plan_def, LET_THM] >>
  rpt IF_CASES_TAC >> simp[] >>
  Cases_on `stack_get_depth (Var (LAST live)) ps.ps_stack` >> simp[] >>
  drule stack_get_depth_props >> strip_tac >>
  Cases_on `do_swap x ps` >>
  drule_all residual_budget_wf_do_swap >> simp[]
QED

Theorem optimistic_swap_plan_core_resource:
  !ps m core base dfg inst live term qs.
    ps.ps_stack = REPLICATE m dead_stack_marker ++ core /\
    residual_budget_wf base [] (ps with ps_stack := core) /\
    qs = SND (optimistic_swap_plan dfg inst live term ps) ==>
    ?rest.
      qs.ps_stack = REPLICATE m dead_stack_marker ++ rest /\
      set rest = set core /\ qs.ps_spilled = ps.ps_spilled /\
      residual_budget_wf base [] (qs with ps_stack := rest)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all optimistic_swap_plan_core_step >> strip_tac
  >- (gvs[] >> qexists_tac `core` >> simp[]) >>
  rename1 `x < LENGTH core` >> gvs[] >>
  qexists_tac `stack_swap x core` >>
  `!op. LIST_ELEM_COUNT op (stack_swap x core) = LIST_ELEM_COUNT op core` by
    (gen_tac >> qspecl_then [`x`, `ps`, `op`] mp_tac do_swap_multiplicity >>
     simp[do_swap_stack_result, stack_swap_bottom_extension, elem_count_append]) >>
  `set (stack_swap x core) = set core` by
    (simp[EXTENSION] >> metis_tac[LIST_ELEM_COUNT_MEM]) >>
  rename1 `residual_budget_wf spillbase [] (ps with ps_stack := core)` >>
  `plan_slots_bounded spillbase ps /\
   spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled` by
    (gvs[residual_budget_wf_def, plan_slots_bounded_def] >> metis_tac[]) >>
  `x < LENGTH ps.ps_stack` by simp[] >>
  Cases_on `do_swap x ps` >>
  drule_all do_swap_slots_bounded >> strip_tac >>
  drule_all do_swap_multiplicity_layout >> strip_tac >>
  drule do_swap_stack_result >> simp[] >> strip_tac >>
  gvs[stack_swap_bottom_extension,
      residual_budget_wf_def, plan_slots_bounded_def] >> metis_tac[]
QED

Theorem popmany_individual_resources[local]:
  !spillbase ps to_pop.
    plan_slots_bounded spillbase ps /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled ==>
    plan_slots_bounded spillbase (SND (popmany_individual to_pop ps)) /\
    spill_alloc_layout_wf (SND (popmany_individual to_pop ps)).ps_alloc
      (SND (popmany_individual to_pop ps)).ps_spilled
Proof
  rpt gen_tac >> simp[popmany_individual_def, LET_THM] >>
  qmatch_goalsub_abbrev_tac `FOLDL popstep ([], ps) sorted` >>
  qsuff_tac `!xs acc.
    plan_slots_bounded spillbase (SND acc) /\
    spill_alloc_layout_wf (SND acc).ps_alloc (SND acc).ps_spilled ==>
    plan_slots_bounded spillbase (SND (FOLDL popstep acc xs)) /\
    spill_alloc_layout_wf (SND (FOLDL popstep acc xs)).ps_alloc
      (SND (FOLDL popstep acc xs)).ps_spilled`
  >- (disch_then (qspecl_then [`sorted`, `([],ps)`] mp_tac) >> simp[]) >>
  Induct >> simp[] >> rpt gen_tac >> PairCases_on `acc` >> strip_tac >>
  gvs[] >> first_x_assum irule >> simp[Abbr `popstep`, LET_THM] >>
  Cases_on `stack_get_depth h acc1.ps_stack`
  >- gvs[] >>
  Cases_on `x = 0`
  >- (gvs[plan_slots_bounded_def] >> metis_tac[]) >>
  simp[] >>
  drule stack_get_depth_props >> strip_tac >>
  Cases_on `do_swap x acc1` >>
  drule_all do_swap_slots_bounded >> strip_tac >>
  drule_all do_swap_multiplicity_layout >> strip_tac >>
  gvs[plan_slots_bounded_def] >> metis_tac[]
QED

Theorem popmany_plan_resources[local]:
  !spillbase ps to_pop.
    plan_slots_bounded spillbase ps /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled ==>
    plan_slots_bounded spillbase (SND (popmany_plan to_pop ps)) /\
    spill_alloc_layout_wf (SND (popmany_plan to_pop ps)).ps_alloc
      (SND (popmany_plan to_pop ps)).ps_spilled
Proof
  rpt gen_tac >> strip_tac >> Cases_on `to_pop`
  >- simp[popmany_plan_def] >>
  simp[popmany_plan_def, LET_THM] >>
  IF_CASES_TAC
  >- (IF_CASES_TAC
      >- (`LENGTH (h::t) < LENGTH ps.ps_stack` by
            (qspecl_then [`h::t`, `ps.ps_stack`] mp_tac contiguous_top_stack_bound >>
             simp[]) >>
          Cases_on `do_swap (LENGTH (h::t)) ps` >>
          drule_all do_swap_slots_bounded >> strip_tac >>
          drule_all do_swap_multiplicity_layout >> strip_tac >>
          gvs[plan_slots_bounded_def] >> metis_tac[]) >>
      metis_tac[popmany_individual_resources]) >>
  metis_tac[popmany_individual_resources]
QED

Theorem popmany_plan_core_resource:
  !ps prefix core spillbase to_pop qs.
    ps.ps_stack = prefix ++ core /\
    DISJOINT (set prefix) (set to_pop) /\
    residual_budget_wf spillbase [] (ps with ps_stack := core) /\
    qs = SND (popmany_plan to_pop ps) ==>
    ?rest. qs.ps_stack = prefix ++ rest /\
      set rest = set core DIFF set to_pop /\
      qs.ps_spilled = ps.ps_spilled /\
      residual_budget_wf spillbase [] (qs with ps_stack := rest)
Proof
  rpt gen_tac >> strip_tac >>
  drule residual_budget_wf_empty_inventory >> simp[] >> strip_tac >>
  drule_all popmany_plan_core >> strip_tac >>
  rename1 `ALL_DISTINCT rest` >> qexists_tac `rest` >>
  `qs.ps_spilled = ps.ps_spilled` by gvs[popmany_plan_spilled_unchanged] >>
  `plan_slots_bounded spillbase ps /\
   spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled` by
    (gvs[residual_budget_wf_def, plan_slots_bounded_def] >> metis_tac[]) >>
  drule_all popmany_plan_resources >>
  disch_then (qspec_then `to_pop` strip_assume_tac) >>
  gvs[popmany_plan_spilled_unchanged] >> irule residual_budget_wf_canonical >>
  gvs[plan_slots_bounded_def, popmany_plan_spilled_unchanged] >> ASM_SET_TAC[]
QED

Theorem residual_budget_wf_remove_free[local]:
  !spillbase pending ps op off.
    residual_budget_wf spillbase pending ps /\
    FLOOKUP ps.ps_spilled op = SOME off ==>
    residual_budget_wf spillbase pending
      (ps with <| ps_spilled := ps.ps_spilled \\ op;
                  ps_alloc := free_spill_slot off ps.ps_alloc |>)
Proof
  rpt gen_tac >> strip_tac >> fs[residual_budget_wf_def] >>
  rpt conj_tac
  >- (fs[plan_slots_bounded_def, alloc_slots_bounded_def] >>
      simp[plan_slots_bounded_def, alloc_slots_bounded_def,
           free_spill_slot_def, EVERY_SNOC, DOMSUB_FLOOKUP_THM] >>
      metis_tac[])
  >- metis_tac[spill_alloc_layout_wf_after_free]
  >> fs[DOMSUB_FLOOKUP_THM] >> metis_tac[]
QED

Theorem residual_budget_wf_release_fold[local]:
  !dead spillbase pending ps.
    residual_budget_wf spillbase pending ps /\
    ALL_DISTINCT (MAP FST dead) /\
    (!op off. MEM (op,off) dead ==>
       FLOOKUP ps.ps_spilled op = SOME off) ==>
    residual_budget_wf spillbase pending
      (FOLDL (\ps' (op,off).
         ps' with <| ps_spilled := ps'.ps_spilled \\ op;
                     ps_alloc := free_spill_slot off ps'.ps_alloc |>) ps dead)
Proof
  Induct >- simp[] >> rpt gen_tac >> PairCases_on `h` >> simp[] >> strip_tac >>
  `FLOOKUP ps.ps_spilled h0 = SOME h1` by metis_tac[] >>
  `residual_budget_wf spillbase pending
     (ps with <| ps_spilled := ps.ps_spilled \\ h0;
                 ps_alloc := free_spill_slot h1 ps.ps_alloc |>)` by
    metis_tac[residual_budget_wf_remove_free] >>
  `!op off. MEM (op,off) dead ==>
     FLOOKUP (ps.ps_spilled \\ h0) op = SOME off` by
    (rpt gen_tac >> strip_tac >>
     `op <> h0` by
       (strip_tac >> qpat_x_assum `~MEM h0 (MAP FST dead)` mp_tac >>
        simp[MEM_MAP] >> qexists_tac `(op,off)` >> simp[]) >>
     simp[DOMSUB_FLOOKUP_THM] >> metis_tac[]) >>
  first_x_assum irule >> simp[]
QED

Theorem residual_budget_wf_release_dead_spills:
  !spillbase pending live ps.
    residual_budget_wf spillbase pending ps ==>
    residual_budget_wf spillbase pending (release_dead_spills live ps)
Proof
  rpt gen_tac >> strip_tac >> simp[release_dead_spills_def] >>
  irule residual_budget_wf_release_fold >>
  rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      fs[MEM_FILTER, alistTheory.MEM_pair_fmap_to_alist_FLOOKUP])
  >- (`MAP FST (FILTER (\(op,off). case op of
          Var v => ~MEM v live | _ => T) (fmap_to_alist ps.ps_spilled)) =
       FILTER (\op. case op of Var v => ~MEM v live | _ => T)
         (MAP FST (fmap_to_alist ps.ps_spilled))` by
        simp[FILTER_MAP, combinTheory.o_DEF, pairTheory.LAMBDA_PROD] >>
      pop_assum SUBST1_TAC >>
      irule FILTER_ALL_DISTINCT >>
      simp[alistTheory.ALL_DISTINCT_fmap_to_alist_keys])
  >> first_assum ACCEPT_TAC
QED

Theorem release_fold_stack_update[local]:
  !dead ps core.
    FOLDL (\ps' (op,off).
      ps' with <| ps_spilled := ps'.ps_spilled \\ op;
                  ps_alloc := free_spill_slot off ps'.ps_alloc |>)
      (ps with ps_stack := core) dead =
    (FOLDL (\ps' (op,off).
      ps' with <| ps_spilled := ps'.ps_spilled \\ op;
                  ps_alloc := free_spill_slot off ps'.ps_alloc |>) ps dead)
      with ps_stack := core
Proof
  Induct >- simp[] >> rpt gen_tac >> PairCases_on `h` >>
  simp[] >> first_x_assum (qspecl_then
    [`ps with <| ps_spilled := ps.ps_spilled \\ h0;
                 ps_alloc := free_spill_slot h1 ps.ps_alloc |>`, `core`] mp_tac) >>
  simp[]
QED

Theorem residual_budget_wf_release_dead_spills_core:
  !spillbase pending live ps core.
    residual_budget_wf spillbase pending (ps with ps_stack := core) ==>
    residual_budget_wf spillbase pending
      ((release_dead_spills live ps) with ps_stack := core)
Proof
  rpt gen_tac >> strip_tac >> drule residual_budget_wf_release_dead_spills >>
  disch_then (qspec_then `live` mp_tac) >>
  simp[release_dead_spills_def, release_fold_stack_update]
QED

Theorem regular_post_emit_tail_core_resource:
  !ps m core spillbase outputs live halting dfg inst term deleted ps8 ps9 final.
    ps.ps_stack = REPLICATE m dead_stack_marker ++ core /\
    residual_budget_wf spillbase [] (ps with ps_stack := core) /\
    deleted = (if outputs <> [] /\ (~halting \/ LENGTH outputs > 1)
      then MAP Var (FILTER (\v. ~MEM v live) outputs) else []) /\
    ps8 = (if outputs <> [] /\ (~halting \/ LENGTH outputs > 1)
      then SND (popmany_plan (MAP Var (FILTER (\v. ~MEM v live) outputs)) ps)
      else ps) /\
    ps9 = (if outputs <> [] /\ FILTER (\v. MEM v live) outputs <> []
      then SND (optimistic_swap_plan dfg inst live term ps8) else ps8) /\
    final = release_dead_spills live ps9 ==>
    ?rest. final.ps_stack = REPLICATE m dead_stack_marker ++ rest /\
      ALL_DISTINCT rest /\ set rest = set core DIFF set deleted /\
      FDOM final.ps_spilled = FDOM ps.ps_spilled INTER set (MAP Var live) /\
      residual_budget_wf spillbase [] (final with ps_stack := rest)
Proof
  rpt gen_tac >> strip_tac >>
  drule residual_budget_wf_empty_inventory >> simp[] >> strip_tac >>
  `?core8. ps8.ps_stack = REPLICATE m dead_stack_marker ++ core8 /\
     set core8 = set core DIFF set deleted /\
     residual_budget_wf spillbase [] (ps8 with ps_stack := core8)` by
    (Cases_on `outputs <> [] /\ (~halting \/ LENGTH outputs > 1)`
     >- (gvs[] >> drule popmany_plan_core_resource >>
         disch_then (qspecl_then [`spillbase`,
           `MAP Var (FILTER (\v. ~MEM v live) outputs)`,
           `SND (popmany_plan (MAP Var (FILTER (\v. ~MEM v live) outputs)) ps)`] mp_tac) >>
         simp[DISJOINT_DEF, EXTENSION, MEM_MAP, dead_stack_marker_def] >>
         metis_tac[]) >>
     gvs[] >> qexists_tac `core` >> simp[]) >>
  `?core9. ps9.ps_stack = REPLICATE m dead_stack_marker ++ core9 /\
     set core9 = set core8 /\
     residual_budget_wf spillbase [] (ps9 with ps_stack := core9)` by
    (Cases_on `outputs <> [] /\ FILTER (\v. MEM v live) outputs <> []` >> gvs[]
     >- (drule optimistic_swap_plan_core_resource >> simp[] >>
         disch_then drule >>
         disch_then (qspecl_then [`dfg`, `inst`, `live`, `term`] mp_tac) >>
         metis_tac[]) >>
     qexists_tac `core8` >> simp[]) >>
  `residual_budget_wf spillbase [] (final with ps_stack := core9)` by
    (gvs[] >> irule residual_budget_wf_release_dead_spills_core >> simp[]) >>
  drule residual_budget_wf_empty_inventory >> simp[] >> strip_tac >>
  drule_all regular_post_emit_tail_core_sets >> strip_tac >>
  `residual_budget_wf spillbase [] (final with ps_stack := rest)` by
    (irule residual_budget_wf_canonical >>
     qpat_x_assum `residual_budget_wf _ _ (final with ps_stack := core9)` mp_tac >>
     simp[residual_budget_wf_def, plan_slots_bounded_def] >>
     strip_tac >> ASM_SET_TAC[]) >>
  qexists_tac `rest` >> metis_tac[]
QED

Theorem regular_post_emit_tail_live_inventory:
  !ps m core spillbase outputs live halting dfg inst term deleted ps8 ps9 final.
    ps.ps_stack = REPLICATE m dead_stack_marker ++ core /\
    residual_budget_wf spillbase [] (ps with ps_stack := core) /\
    deleted = (if outputs <> [] /\ (~halting \/ LENGTH outputs > 1)
      then MAP Var (FILTER (\v. ~MEM v live) outputs) else []) /\
    ps8 = (if outputs <> [] /\ (~halting \/ LENGTH outputs > 1)
      then SND (popmany_plan (MAP Var (FILTER (\v. ~MEM v live) outputs)) ps)
      else ps) /\
    ps9 = (if outputs <> [] /\ FILTER (\v. MEM v live) outputs <> []
      then SND (optimistic_swap_plan dfg inst live term ps8) else ps8) /\
    final = release_dead_spills live ps9 /\
    set core DIFF set deleted SUBSET set (MAP Var live) /\
    set (MAP Var live) SUBSET set core UNION FDOM ps.ps_spilled ==>
    lineage_inventory (set (MAP Var live)) final /\
    ?rest. lineage_core m rest final /\
      residual_budget_wf spillbase [] (final with ps_stack := rest)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all regular_post_emit_tail_core_resource >> strip_tac >>
  `DISJOINT (set deleted) (set (MAP Var live))` by
    (qpat_x_assum `deleted = _` SUBST1_TAC >>
     Cases_on `outputs <> [] /\ (~halting \/ LENGTH outputs > 1)` >>
     simp[DISJOINT_DEF, EXTENSION, MEM_MAP, MEM_FILTER] >>
     Cases >> simp[] >> metis_tac[]) >>
  `set rest UNION FDOM final.ps_spilled = set (MAP Var live)` by ASM_SET_TAC[] >>
  drule residual_budget_wf_empty_inventory >> simp[] >> strip_tac >>
  conj_tac
  >- (simp[lineage_inventory_def] >> qexistsl_tac [`m`, `rest`] >>
      simp[lineage_core_def] >>
      `!op. MEM op (MAP Var live) ==> is_var_operand op` by
        (simp[MEM_MAP] >> rpt strip_tac >> gvs[is_var_operand_def]) >>
      simp[EVERY_MEM] >> ASM_SET_TAC[]) >>
  qexists_tac `rest` >> metis_tac[lineage_core_def]
QED

Theorem optimistic_swap_plan_slots:
  !dfg inst live term ps.
    set (SND (optimistic_swap_plan dfg inst live term ps)).ps_stack = set ps.ps_stack /\
    (SND (optimistic_swap_plan dfg inst live term ps)).ps_spilled = ps.ps_spilled
Proof
  rpt gen_tac >>
  `ps.ps_stack = REPLICATE 0 dead_stack_marker ++ ps.ps_stack` by simp[] >>
  drule optimistic_swap_plan_core_step >> simp[] >>
  disch_then (qspecl_then [`dfg`, `inst`, `live`, `term`] strip_assume_tac) >> gvs[] >>
  simp[do_swap_spilled_unchanged] >>
  metis_tac[do_swap_stack_perm, sortingTheory.PERM_LIST_TO_SET]
QED

Theorem dead_output_pop_live_coverage:
  !ps outputs nl halting qs.
    (!v. MEM v nl ==> MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    qs = (if outputs <> [] /\ (~halting \/ LENGTH outputs > 1)
      then SND (popmany_plan (MAP Var (FILTER (\v. ~MEM v nl) outputs)) ps)
      else ps) ==>
    !v. MEM v nl ==> MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `outputs <> [] /\ (~halting \/ LENGTH outputs > 1)`
  >- (qpat_x_assum `qs = _` SUBST_ALL_TAC >>
      simp[popmany_plan_spilled_unchanged] >>
      rpt strip_tac >> first_x_assum drule >> strip_tac
      >- (disj1_tac >> irule popmany_plan_retains_other >>
          simp[MEM_MAP, MEM_FILTER] >> metis_tac[]) >> simp[]) >>
  gvs[]
QED

Theorem regular_post_emit_tail_live_coverage:
  !ps outputs live halting dfg inst term ps8 ps9 final.
    (!v. MEM v live ==> MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    ps8 = (if outputs <> [] /\ (~halting \/ LENGTH outputs > 1)
      then SND (popmany_plan (MAP Var (FILTER (\v. ~MEM v live) outputs)) ps)
      else ps) /\
    ps9 = (if outputs <> [] /\ FILTER (\v. MEM v live) outputs <> []
      then SND (optimistic_swap_plan dfg inst live term ps8) else ps8) /\
    final = release_dead_spills live ps9 ==>
    !v. MEM v live ==> MEM (Var v) final.ps_stack \/ Var v IN FDOM final.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  `!v. MEM v live ==> MEM (Var v) ps8.ps_stack \/ Var v IN FDOM ps8.ps_spilled` by
    (metis_tac[dead_output_pop_live_coverage]) >>
  `!v. MEM v live ==> MEM (Var v) ps9.ps_stack \/ Var v IN FDOM ps9.ps_spilled` by
    (qspecl_then [`dfg`, `inst`, `live`, `term`, `ps8`] strip_assume_tac
       optimistic_swap_plan_slots >>
     Cases_on `outputs <> [] /\ FILTER (\v. MEM v live) outputs <> []` >>
     qpat_x_assum `ps9 = _` SUBST_ALL_TAC >> simp[] >> ASM_SET_TAC[]) >>
  `final.ps_stack = ps9.ps_stack` by
    (qpat_x_assum `final = _` SUBST_ALL_TAC >>
     rpt (pop_assum kall_tac) >> simp[release_dead_spills_def] >>
     qspec_tac (`FILTER (\(op,off). case op of Lit v => T | Var v => ~MEM v live | Label v => T)
       (fmap_to_alist ps9.ps_spilled)`, `xs`) >>
     qid_spec_tac `ps9` >> Induct_on `xs` >> simp[] >>
     Cases_on `h` >> simp[]) >>
  gvs[release_dead_spills_domain, MEM_MAP] >> metis_tac[]
QED

Theorem emit_reorder_output_live_coverage:
  !ps operands selected opc nl outputs dfg iops ps1 rops ps4.
    reorder_plan dfg selected ps1 = (rops,ps4) ==>
    emit_input_plan opc operands nl ps = (iops,ps1) ==>
    LENGTH operands <= 16 /\
    (!v. MEM (Var v) operands \/ (MEM v nl /\ ~MEM v outputs) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    PERM operands selected ==>
    !v. MEM v nl ==>
      MEM (Var v) ((stack_pop (LENGTH operands) ps4.ps_stack) ++ MAP Var outputs) \/
      Var v IN FDOM ps4.ps_spilled
Proof
  rpt gen_tac >> ntac 2 disch_tac >> strip_tac >>
  qabbrev_tac `keep = FILTER (\v. ~MEM v outputs) nl` >>
  `set keep SUBSET set nl` by (simp[Abbr `keep`, SUBSET_DEF, MEM_FILTER]) >>
  `!v. MEM (Var v) operands \/ MEM v keep ==>
     MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled` by
    (simp_tac bool_ss [Abbr `keep`, MEM_FILTER] >> metis_tac[]) >>
  `!v. MEM v keep ==>
    MEM (Var v) (stack_pop (LENGTH selected) ps4.ps_stack) \/
    Var v IN FDOM ps4.ps_spilled` by
    metis_tac[emit_reorder_plan_bounded_protected_consumption] >>
  drule sortingTheory.PERM_LENGTH >> strip_tac >>
  rpt strip_tac >> Cases_on `MEM v outputs` >- simp[MEM_MAP] >>
  `MEM v keep` by simp[Abbr `keep`, MEM_FILTER] >>
  first_x_assum drule >> simp[MEM_MAP] >> metis_tac[]
QED

(* Shared decomposition of the actual non-JMP planner, including its tail. *)
Theorem native_regular_stages:
  !liveness dfg cfg fn inst nl halting term lbl ps ops qs.
    (inst.inst_opcode <> JMP \/ join_target_ops liveness fn lbl inst = NONE) /\
    generate_regular_inst_plan liveness dfg cfg fn inst nl halting term lbl ps = (ops,qs) ==>
    ?selected iops ps1 rops ps4 topic eops ps7 ps8 ps9.
      PERM (compute_operands inst) selected /\
      emit_input_plan inst.inst_opcode (compute_operands inst) nl ps = (iops,ps1) /\
      reorder_plan dfg selected ps1 = (rops,ps4) /\
      generate_emit_ops inst topic
        (FOLDL (\p v. p with ps_stack := stack_push (Var v) p.ps_stack)
          (ps4 with ps_stack := stack_pop (LENGTH (compute_operands inst)) ps4.ps_stack)
          inst.inst_outputs) = (eops,ps7) /\
      ps8 = (if inst.inst_outputs <> [] /\ (~halting \/ LENGTH inst.inst_outputs > 1)
        then SND (popmany_plan (MAP Var (FILTER (\v. ~MEM v nl) inst.inst_outputs)) ps7)
        else ps7) /\
      ps9 = (if inst.inst_outputs <> [] /\ FILTER (\v. MEM v nl) inst.inst_outputs <> []
        then SND (optimistic_swap_plan dfg inst nl term ps8) else ps8) /\
      qs = release_dead_spills nl ps9
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = JMP` >> gvs[] >>
  namedCases_on `emit_input_plan inst.inst_opcode (compute_operands inst) nl ps` ["iops ps1"] >>
  (Cases_on `is_commutative inst.inst_opcode /\ 2 <= LENGTH (compute_operands inst)`
  >- (Cases_on `reorder_cost (FST (reorder_plan dfg (compute_operands inst) ps1)) <
       reorder_cost (FST (reorder_plan dfg
         (TAKE (LENGTH (compute_operands inst) - 2) (compute_operands inst) ++
          [EL (LENGTH (compute_operands inst) - 1) (compute_operands inst);
           EL (LENGTH (compute_operands inst) - 2) (compute_operands inst)]) ps1))`
      >- (namedCases_on `reorder_plan dfg (compute_operands inst) ps1` ["rops ps4"] >>
          qexistsl_tac [`compute_operands inst`, `iops`, `ps1`, `rops`, `ps4`] >>
          simp[] >> (qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
      asm_simp_tac bool_ss [generate_regular_inst_plan_def, LET_THM,
        pairTheory.pair_CASE_def, pairTheory.UNCURRY, pairTheory.FST, pairTheory.SND,
        pairTheory.PAIR, arithmeticTheory.GREATER_EQ] >>
      Cases_on `inst.inst_outputs = []` >> asm_simp_tac bool_ss [] >>
      qmatch_goalsub_abbrev_tac `generate_emit_ops inst topic emitted` >>
      qpat_x_assum `Abbrev (topic = _)` kall_tac >>
      namedCases_on `generate_emit_ops inst topic emitted` ["eops ps7"] >>
      simp_tac bool_ss [pairTheory.FST, pairTheory.SND] >>
      Cases_on `~halting \/ LENGTH inst.inst_outputs > 1` >>
      Cases_on `FILTER (\v. MEM v nl) inst.inst_outputs = []` >>
      simp[Abbr `emitted`] >> rpt strip_tac >> gvs[] >>
      qexistsl_tac [`topic`, `eops`] >> simp[])) >>
      namedCases_on `reorder_plan dfg
        (TAKE (LENGTH (compute_operands inst) - 2) (compute_operands inst) ++
         [EL (LENGTH (compute_operands inst) - 1) (compute_operands inst);
          EL (LENGTH (compute_operands inst) - 2) (compute_operands inst)]) ps1` ["rops ps4"] >>
      `PERM (compute_operands inst)
        (TAKE (LENGTH (compute_operands inst) - 2) (compute_operands inst) ++
         [EL (LENGTH (compute_operands inst) - 1) (compute_operands inst);
          EL (LENGTH (compute_operands inst) - 2) (compute_operands inst)])` by
        (irule genericInputReadyTheory.last_two_reorder_perm >> gvs[]) >>
      qexistsl_tac [`TAKE (LENGTH (compute_operands inst) - 2) (compute_operands inst) ++
         [EL (LENGTH (compute_operands inst) - 1) (compute_operands inst);
          EL (LENGTH (compute_operands inst) - 2) (compute_operands inst)]`,
        `iops`, `ps1`, `rops`, `ps4`] >>
      simp[] >>
      (qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
      asm_simp_tac bool_ss [generate_regular_inst_plan_def, LET_THM,
        pairTheory.pair_CASE_def, pairTheory.UNCURRY, pairTheory.FST, pairTheory.SND,
        pairTheory.PAIR, arithmeticTheory.GREATER_EQ] >>
      Cases_on `inst.inst_outputs = []` >> asm_simp_tac bool_ss [] >>
      qmatch_goalsub_abbrev_tac `generate_emit_ops inst topic emitted` >>
      qpat_x_assum `Abbrev (topic = _)` kall_tac >>
      namedCases_on `generate_emit_ops inst topic emitted` ["eops ps7"] >>
      simp_tac bool_ss [pairTheory.FST, pairTheory.SND] >>
      Cases_on `~halting \/ LENGTH inst.inst_outputs > 1` >>
      Cases_on `FILTER (\v. MEM v nl) inst.inst_outputs = []` >>
      simp[Abbr `emitted`] >> rpt strip_tac >> gvs[] >>
      qexistsl_tac [`topic`, `eops`] >> simp[])) >>
  namedCases_on `reorder_plan dfg (compute_operands inst) ps1` ["rops ps4"] >>
  qexistsl_tac [`compute_operands inst`, `iops`, `ps1`, `rops`, `ps4`] >>
  simp[] >> (qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
      asm_simp_tac bool_ss [generate_regular_inst_plan_def, LET_THM,
        pairTheory.pair_CASE_def, pairTheory.UNCURRY, pairTheory.FST, pairTheory.SND,
        pairTheory.PAIR, arithmeticTheory.GREATER_EQ] >>
      Cases_on `inst.inst_outputs = []` >> asm_simp_tac bool_ss [] >>
      qmatch_goalsub_abbrev_tac `generate_emit_ops inst topic emitted` >>
      qpat_x_assum `Abbrev (topic = _)` kall_tac >>
      namedCases_on `generate_emit_ops inst topic emitted` ["eops ps7"] >>
      simp_tac bool_ss [pairTheory.FST, pairTheory.SND] >>
      Cases_on `~halting \/ LENGTH inst.inst_outputs > 1` >>
      Cases_on `FILTER (\v. MEM v nl) inst.inst_outputs = []` >>
      simp[Abbr `emitted`] >> rpt strip_tac >> gvs[] >>
      qexistsl_tac [`topic`, `eops`] >> simp[]))
QED


Theorem native_regular_live_lower:
  !liveness dfg cfg fn inst nl halting term lbl ps ops qs.
    inst.inst_opcode <> JMP /\ LENGTH (compute_operands inst) <= 16 /\
    (!v. MEM (Var v) (compute_operands inst) \/
      (MEM v nl /\ ~MEM v inst.inst_outputs) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    generate_regular_inst_plan liveness dfg cfg fn inst nl halting term lbl ps = (ops,qs)
    ==> !v. MEM v nl ==> MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  drule_at (Pos last) native_regular_stages >>
  (impl_tac >- simp[]) >> strip_tac >>
  `!v. MEM v nl ==>
    MEM (Var v) (stack_pop (LENGTH (compute_operands inst)) ps4.ps_stack ++ MAP Var inst.inst_outputs) \/
    Var v IN FDOM ps4.ps_spilled` by
    metis_tac[emit_reorder_output_live_coverage] >>
  drule fnPlanLineageReorderTheory.generate_emit_ops_slots >>
  disch_then (strip_assume_tac o SRULE [parameter_push_fold]) >>
  `!v. MEM v nl ==> MEM (Var v) ps7.ps_stack \/ Var v IN FDOM ps7.ps_spilled` by
    metis_tac[] >>
  drule (SRULE [] regular_post_emit_tail_live_coverage) >>
  disch_then (qspecl_then [`inst.inst_outputs`, `halting`, `dfg`, `inst`, `term`] mp_tac) >>
  Cases_on `inst.inst_outputs = []` >>
  Cases_on `~halting \/ LENGTH inst.inst_outputs > 1` >>
  Cases_on `FILTER (\v. MEM v nl) inst.inst_outputs = []` >>
  simp[] >> rpt strip_tac >> gvs[]
QED

(* Native opcode emission changes neither storage nor allocator resources. *)
Theorem generate_emit_ops_residual_budget_wf:
  !inst topics ps ops qs base pending.
    generate_emit_ops inst topics ps = (ops,qs) /\
    residual_budget_wf base pending ps ==>
    residual_budget_wf base pending qs
Proof
  rpt gen_tac >> strip_tac >>
  drule allocMonoTheory.generate_emit_ops_alloc >> strip_tac >>
  drule fnPlanLineageReorderTheory.generate_emit_ops_slots >> strip_tac >>
  gvs[residual_budget_wf_def, plan_slots_bounded_def] >> metis_tac[]
QED

Theorem generate_emit_ops_core_resource:
  !inst topics ps ops qs base pending core.
    generate_emit_ops inst topics ps = (ops,qs) /\
    residual_budget_wf base pending (ps with ps_stack := core) ==>
    residual_budget_wf base pending (qs with ps_stack := core)
Proof
  rpt gen_tac >> strip_tac >>
  drule allocMonoTheory.generate_emit_ops_alloc >> strip_tac >>
  drule fnPlanLineageReorderTheory.generate_emit_ops_slots >> strip_tac >>
  gvs[residual_budget_wf_def, plan_slots_bounded_def] >> metis_tac[]
QED

Theorem native_regular_live_inventory:
  !liveness dfg cfg fn inst nl halting term lbl ps m core spillbase ops qs.
    ps.ps_stack = REPLICATE m dead_stack_marker ++ core /\
    residual_budget_wf spillbase [] (ps with ps_stack := core) /\
    inst.inst_opcode <> JMP /\ LENGTH (compute_operands inst) <= 16 /\
    EVERY (\x. x <> dead_stack_marker) (compute_operands inst) /\
    (!v. MEM (Var v) (compute_operands inst) \/
      (MEM v nl /\ ~MEM v inst.inst_outputs) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    generate_regular_inst_plan liveness dfg cfg fn inst nl halting term lbl ps = (ops,qs) /\
    set core UNION FDOM ps.ps_spilled SUBSET
      set (MAP Var (operand_vars (compute_operands inst) ++ nl)) /\
    ALL_DISTINCT inst.inst_outputs /\
    EVERY (\v. ~MEM (Var v) (compute_operands inst) /\ ~MEM (Var v) core /\
      Var v NOTIN FDOM ps.ps_spilled) inst.inst_outputs /\
    (~halting \/ LENGTH inst.inst_outputs > 1 \/ EVERY (\v. MEM v nl) inst.inst_outputs) ==>
    lineage_inventory (set (MAP Var nl)) qs /\
    ?rest. lineage_core m rest qs /\
      residual_budget_wf spillbase [] (qs with ps_stack := rest)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_at (Pos last) native_regular_stages >>
  (impl_tac >- simp[]) >> strip_tac >>
  `!v. MEM (Var v) (compute_operands inst) ==>
    MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled` by metis_tac[] >>
  qabbrev_tac `consumed = ps4 with ps_stack :=
    stack_pop (LENGTH (compute_operands inst)) ps4.ps_stack` >>
  `consumed = ps4 with ps_stack :=
    stack_pop (LENGTH (compute_operands inst)) ps4.ps_stack` by simp[Abbr `consumed`] >>
  drule_all emit_reorder_pop_marker_core_live_upper >> strip_tac >>
  `EVERY (\v. ~MEM (Var v) rest /\ Var v NOTIN FDOM consumed.ps_spilled)
    inst.inst_outputs` by
    (drule_all emit_reorder_pop_marker_core_fresh >> strip_tac >>
     metis_tac[APPEND_11]) >>
  qabbrev_tac `emitted = FOLDL (\p v. p with ps_stack := stack_push (Var v) p.ps_stack)
    consumed inst.inst_outputs` >>
  `emitted = FOLDL (\p v. p with ps_stack := stack_push (Var v) p.ps_stack)
    consumed inst.inst_outputs` by simp[Abbr `emitted`] >>
  drule_all output_push_marker_core >> strip_tac >>
  `generate_emit_ops inst topic emitted = (eops,ps7)` by simp[Abbr `emitted`, Abbr `consumed`] >>
  drule_all generate_emit_ops_core_resource >> strip_tac >>
  suspend "tail"
QED

Resume native_regular_live_inventory[tail]:
  `!v. MEM v nl ==>
    MEM (Var v) (stack_pop (LENGTH (compute_operands inst)) ps4.ps_stack ++ MAP Var inst.inst_outputs) \/
    Var v IN FDOM ps4.ps_spilled` by
    metis_tac[emit_reorder_output_live_coverage] >>
  drule fnPlanLineageReorderTheory.generate_emit_ops_slots >> strip_tac >>
  `ps7.ps_stack = REPLICATE m dead_stack_marker ++ (rest ++ MAP Var inst.inst_outputs)` by metis_tac[] >>
  `stack_pop (LENGTH (compute_operands inst)) ps4.ps_stack =
    REPLICATE m dead_stack_marker ++ rest` by
    (qpat_x_assum `consumed.ps_stack = _` mp_tac >> simp[Abbr `consumed`]) >>
  `ps7.ps_spilled = ps4.ps_spilled` by simp[Abbr `consumed`] >>
  `set (MAP Var nl) SUBSET set (rest ++ MAP Var inst.inst_outputs) UNION FDOM ps7.ps_spilled` by
    (simp[SUBSET_DEF, MEM_MAP] >> rpt strip_tac >> rename1 `MEM v nl` >>
     qpat_x_assum `!v. MEM v nl ==> MEM (Var v) (_ ++ _) \/ _`
       (qspec_then `v` mp_tac) >>
     simp[MEM_REPLICATE, dead_stack_marker_def, MEM_MAP] >> metis_tac[]) >>
  `set rest SUBSET set (MAP Var nl)` by
    (qpat_x_assum `!x. LIST_ELEM_COUNT x rest + _ <= _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     simp[SUBSET_DEF] >> rpt strip_tac >>
     first_x_assum (qspec_then `x` mp_tac) >>
     Cases_on `MEM x (MAP Var nl)` >> gvs[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac) >>
  qabbrev_tac `deleted = if inst.inst_outputs <> [] /\ (~halting \/ LENGTH inst.inst_outputs > 1)
    then MAP Var (FILTER (\v. ~MEM v nl) inst.inst_outputs) else []` >>
  `set (rest ++ MAP Var inst.inst_outputs) DIFF set deleted SUBSET set (MAP Var nl)` by
    (qpat_x_assum `set rest SUBSET _` mp_tac >>
     qpat_x_assum `~halting \/ _` mp_tac >>
     qpat_x_assum `Abbrev (deleted = _)` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp_tac bool_ss [markerTheory.Abbrev_def] >> rpt strip_tac >>
     Cases_on `inst.inst_outputs <> [] /\ (~halting \/ LENGTH inst.inst_outputs > 1)` >>
     gvs[SUBSET_DEF, MEM_MAP, MEM_FILTER, EVERY_MEM] >> metis_tac[]) >>
  qpat_x_assum `set (_ ++ _) DIFF _ SUBSET _` mp_tac >>
  qpat_x_assum `set (MAP Var nl) SUBSET _` mp_tac >>
  qpat_x_assum `Abbrev (deleted = _)` (mp_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_x_assum `ps7.ps_stack = REPLICATE _ _ ++ _` mp_tac >>
  qpat_x_assum `residual_budget_wf _ [] (ps7 with ps_stack := _)` mp_tac >>
  qpat_x_assum `ps8 = _` mp_tac >>
  qpat_x_assum `ps9 = _` mp_tac >>
  qpat_x_assum `qs = release_dead_spills _ _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  rpt disch_tac >>
  drule_all regular_post_emit_tail_live_inventory >> simp[]
QED

Finalise native_regular_live_inventory

Theorem native_regular_variable_origins:
  !liveness dfg cfg fn inst nl halting term lbl ps ops qs.
    inst.inst_opcode <> JMP /\ LENGTH (compute_operands inst) <= 16 /\
    (!v. MEM (Var v) (compute_operands inst) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    generate_regular_inst_plan liveness dfg cfg fn inst nl halting term lbl ps = (ops,qs) ==>
    !v. MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled \/
      MEM (Var v) (compute_operands inst) \/ MEM v inst.inst_outputs
Proof
  rpt gen_tac >> strip_tac >>
  drule_at (Pos last) native_regular_stages >>
  (impl_tac >- simp[]) >> strip_tac >>
  `!v. MEM (Var v) (stack_pop (LENGTH (compute_operands inst)) ps4.ps_stack) \/
    Var v IN FDOM ps4.ps_spilled ==>
    MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled \/
    MEM (Var v) (compute_operands inst)` by
    (`!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
        MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
       (Cases >> gvs[stackPlanTypesTheory.is_var_operand_def]) >>
     drule_all fnPlanLineageReorderTheory.available_input_plan_length >> strip_tac >>
     drule sortingTheory.PERM_LENGTH >> strip_tac >>
     `LENGTH selected <= LENGTH ps1.ps_stack` by simp[] >>
     `!x. MEM x ps4.ps_stack \/ x IN FDOM ps4.ps_spilled ==>
       MEM x ps1.ps_stack \/ x IN FDOM ps1.ps_spilled` by
       (drule_at (Pat `reorder_plan _ _ _ = _`)
          fnPlanLineageInventoryTheory.reorder_plan_inventory_subset_nb >> simp[]) >>
     rpt strip_tac >>
     `MEM (Var v) ps4.ps_stack \/ Var v IN FDOM ps4.ps_spilled` by
       (gvs[stack_pop_def] >> metis_tac[MEM_TAKE]) >>
     `MEM (Var v) ps1.ps_stack \/ Var v IN FDOM ps1.ps_spilled` by metis_tac[] >>
     metis_tac[emit_input_plan_variable_origins]) >>
  drule fnPlanLineageReorderTheory.generate_emit_ops_slots >>
  disch_then (strip_assume_tac o SRULE [parameter_push_fold]) >>
  `!v. MEM (Var v) ps8.ps_stack \/ Var v IN FDOM ps8.ps_spilled ==>
    MEM (Var v) ps7.ps_stack \/ Var v IN FDOM ps7.ps_spilled` by
    (Cases_on `popmany_plan (MAP Var (FILTER (\v. ~MEM v nl) inst.inst_outputs)) ps7` >>
     drule popmany_plan_inventory_subset >> strip_tac >>
     Cases_on `inst.inst_outputs <> [] /\ (~halting \/ LENGTH inst.inst_outputs > 1)` >>
     gvs[] >> metis_tac[]) >>
  `!v. MEM (Var v) ps9.ps_stack \/ Var v IN FDOM ps9.ps_spilled ==>
    MEM (Var v) ps8.ps_stack \/ Var v IN FDOM ps8.ps_spilled` by
    (Cases_on `optimistic_swap_plan dfg inst nl term ps8` >>
     drule optimistic_swap_plan_inventory_subset >> strip_tac >>
     Cases_on `inst.inst_outputs <> [] /\ FILTER (\v. MEM v nl) inst.inst_outputs <> []` >>
     gvs[] >> metis_tac[]) >>
  rpt strip_tac >>
  `MEM (Var v) ps9.ps_stack \/ Var v IN FDOM ps9.ps_spilled` by
    metis_tac[release_dead_spills_inventory_subset] >>
  `MEM (Var v) ps7.ps_stack \/ Var v IN FDOM ps7.ps_spilled` by metis_tac[] >>
  gvs[MEM_MAP] >> metis_tac[]
QED

Theorem native_regular_variable_support:
  !liveness dfg cfg fn inst nl halting term lbl ps ops qs P.
    inst.inst_opcode <> JMP /\ LENGTH (compute_operands inst) <= 16 /\ 
    (!v. MEM (Var v) (compute_operands inst) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    generate_regular_inst_plan liveness dfg cfg fn inst nl halting term lbl ps = (ops,qs) /\
    (!v. MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled \/
      MEM (Var v) (compute_operands inst) \/ MEM v inst.inst_outputs ==> P v) ==>
    !v. MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled ==> P v
Proof
  rpt gen_tac >> strip_tac >>
  rpt strip_tac >>
  `MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled \/
   MEM (Var v) (compute_operands inst) \/ MEM v inst.inst_outputs` by
    (drule_at (Pat `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
       native_regular_variable_origins >> simp[]) >>
  metis_tac[]
QED

Theorem native_regular_core_resource:
  !liveness dfg cfg fn inst nl halting term lbl ps m core spillbase ops qs.
    ps.ps_stack = REPLICATE m dead_stack_marker ++ core /\
    residual_budget_wf spillbase [] (ps with ps_stack := core) /\
    inst.inst_opcode <> JMP /\ LENGTH (compute_operands inst) <= 16 /\
    EVERY (\x. x <> dead_stack_marker) (compute_operands inst) /\
    (!v. MEM (Var v) (compute_operands inst) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    generate_regular_inst_plan liveness dfg cfg fn inst nl halting term lbl ps = (ops,qs) /\
    ALL_DISTINCT inst.inst_outputs /\
    EVERY (\v. ~MEM (Var v) (compute_operands inst) /\ ~MEM (Var v) core /\
      Var v NOTIN FDOM ps.ps_spilled) inst.inst_outputs ==>
    ?rest. lineage_core m rest qs /\
      residual_budget_wf spillbase [] (qs with ps_stack := rest)
Proof
  rpt gen_tac >> strip_tac >>
  drule_at (Pos last) native_regular_stages >>
  (impl_tac >- simp[]) >> strip_tac >>
  qabbrev_tac `consumed = ps4 with ps_stack :=
    stack_pop (LENGTH (compute_operands inst)) ps4.ps_stack` >>
  `consumed = ps4 with ps_stack :=
    stack_pop (LENGTH (compute_operands inst)) ps4.ps_stack` by simp[Abbr `consumed`] >>
  drule_all emit_reorder_pop_marker_core_fresh >> strip_tac >>
  qabbrev_tac `emitted = FOLDL (\p v. p with ps_stack := stack_push (Var v) p.ps_stack)
    consumed inst.inst_outputs` >>
  `emitted = FOLDL (\p v. p with ps_stack := stack_push (Var v) p.ps_stack)
    consumed inst.inst_outputs` by simp[Abbr `emitted`] >>
  drule_all output_push_marker_core >> strip_tac >>
  `generate_emit_ops inst topic emitted = (eops,ps7)` by simp[Abbr `emitted`, Abbr `consumed`] >>
  drule_all generate_emit_ops_core_resource >> strip_tac >>
  drule fnPlanLineageReorderTheory.generate_emit_ops_slots >> strip_tac >>
  `ps7.ps_stack = REPLICATE m dead_stack_marker ++ (rest ++ MAP Var inst.inst_outputs)` by metis_tac[] >>
  qabbrev_tac `deleted = if inst.inst_outputs <> [] /\ (~halting \/ LENGTH inst.inst_outputs > 1)
    then MAP Var (FILTER (\v. ~MEM v nl) inst.inst_outputs) else []` >>
  `deleted = if inst.inst_outputs <> [] /\ (~halting \/ LENGTH inst.inst_outputs > 1)
    then MAP Var (FILTER (\v. ~MEM v nl) inst.inst_outputs) else []` by simp[Abbr `deleted`] >>
  drule_all regular_post_emit_tail_core_resource >> strip_tac >>
  qexists_tac `rest'` >> simp[lineage_core_def]
QED

(* Every native regular return passes through spill release, independently of
   stack resources, opcode shape, or the initial spill domain. *)
Theorem native_regular_spilled_live_upper:
  !lv dfg cfg fn inst next halting term lbl ps ops qs v.
    generate_regular_inst_plan lv dfg cfg fn inst next halting term lbl ps = (ops,qs) /\
    Var v IN FDOM qs.ps_spilled ==> MEM v next
Proof
  rpt gen_tac >>
  simp_tac bool_ss [generate_regular_inst_plan_def, LET_THM,
    pairTheory.pair_CASE_def, pairTheory.UNCURRY] >>
  rpt pairarg_tac >>
  Cases_on `inst.inst_outputs = []` >> simp[] >>
  rpt strip_tac >> gvs[release_dead_spills_domain, MEM_MAP]
QED

Theorem regular_post_emit_tail_resource_nonincrease:
  !outputs nl halting dfg inst term ps ps8 ps9 qs.
    ps8 = (if outputs <> [] /\ (~halting \/ LENGTH outputs > 1) then
      SND (popmany_plan (MAP Var (FILTER (\v. ~MEM v nl) outputs)) ps) else ps) /\
    ps9 = (if outputs <> [] /\ FILTER (\v. MEM v nl) outputs <> [] then
      SND (optimistic_swap_plan dfg inst nl term ps8) else ps8) /\
    qs = release_dead_spills nl ps9 ==>
    !x. LIST_ELEM_COUNT x qs.ps_stack + (if x IN FDOM qs.ps_spilled then 1 else 0) <=
      LIST_ELEM_COUNT x ps.ps_stack + (if x IN FDOM ps.ps_spilled then 1 else 0)
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  `LIST_ELEM_COUNT x ps8.ps_stack + (if x IN FDOM ps8.ps_spilled then 1 else 0) <=
    LIST_ELEM_COUNT x ps.ps_stack + (if x IN FDOM ps.ps_spilled then 1 else 0)` by
    (namedCases_on `popmany_plan (MAP Var (FILTER (\v. ~MEM v nl) outputs)) ps` ["pops p"] >>
     drule popmany_plan_resource_nonincrease >>
     Cases_on `outputs <> [] /\ (~halting \/ LENGTH outputs > 1)` >> gvs[]) >>
  `LIST_ELEM_COUNT x ps9.ps_stack + (if x IN FDOM ps9.ps_spilled then 1 else 0) =
    LIST_ELEM_COUNT x ps8.ps_stack + (if x IN FDOM ps8.ps_spilled then 1 else 0)` by
    (namedCases_on `optimistic_swap_plan dfg inst nl term ps8` ["sops p"] >>
     drule optimistic_swap_plan_resource_count >>
     Cases_on `outputs <> [] /\ FILTER (\v. MEM v nl) outputs <> []` >> gvs[]) >>
  qpat_x_assum `qs = _` SUBST1_TAC >>
  irule arithmeticTheory.LESS_EQ_TRANS >>
  qexists_tac `LIST_ELEM_COUNT x ps9.ps_stack + (if x IN FDOM ps9.ps_spilled then 1 else 0)` >>
  conj_tac >- irule release_dead_spills_resource_nonincrease >>
  qpat_x_assum `ps8 = _` kall_tac >>
  qpat_x_assum `ps9 = _` kall_tac >> asm_rewrite_tac []
QED

Theorem native_regular_next_live_upper:
  !lv dfg cfg fn inst nl halting term lbl ps ops qs.
    inst.inst_opcode <> JMP /\ LENGTH (compute_operands inst) <= 16 /\
    (!v. MEM v (operand_vars (compute_operands inst) ++ nl) ==>
      LIST_ELEM_COUNT (Var v) ps.ps_stack +
        (if Var v IN FDOM ps.ps_spilled then 1 else 0) <= 1) /\
    (!v. MEM (Var v) (compute_operands inst) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    ALL_DISTINCT inst.inst_outputs /\
    EVERY (\v. ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled /\
      ~MEM (Var v) (compute_operands inst)) inst.inst_outputs /\
    generate_regular_inst_plan lv dfg cfg fn inst nl halting term lbl ps = (ops,qs)
    ==> !v. MEM v nl ==>
      LIST_ELEM_COUNT (Var v) qs.ps_stack +
        (if Var v IN FDOM qs.ps_spilled then 1 else 0) <= 1
Proof
  rpt gen_tac >> strip_tac >>
  drule_at (Pos last) native_regular_stages >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule sortingTheory.PERM_LENGTH >> strip_tac >>
  `!v. MEM v nl ==>
    LIST_ELEM_COUNT (Var v) (stack_pop (LENGTH selected) ps4.ps_stack) +
      (if Var v IN FDOM ps4.ps_spilled then 1 else 0) <= 1` by
    (rpt strip_tac >> irule emit_reorder_pop_next_live_upper >>
     goal_assum (drule_at (Pat `reorder_plan _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_input_plan _ _ _ _ = _`)) >> simp[]) >>
  `!v. MEM v inst.inst_outputs ==>
    ~MEM (Var v) (stack_pop (LENGTH selected) ps4.ps_stack) /\
    Var v NOTIN FDOM ps4.ps_spilled` by
    (gen_tac >> disch_tac >> irule emit_reorder_pop_variable_absent >>
     goal_assum (drule_at (Pat `reorder_plan _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_input_plan _ _ _ _ = _`)) >>
     gvs[EVERY_MEM] >> metis_tac[]) >>
  drule fnPlanLineageReorderTheory.generate_emit_ops_slots >>
  disch_then (strip_assume_tac o SRULE [parameter_push_fold]) >>
  `!v. MEM v nl ==>
    LIST_ELEM_COUNT (Var v) ps7.ps_stack +
      (if Var v IN FDOM ps7.ps_spilled then 1 else 0) <= 1` by
    (rpt strip_tac >>
     Cases_on `MEM v inst.inst_outputs`
     >- (`~MEM (Var v) (stack_pop (LENGTH selected) ps4.ps_stack) /\
          Var v NOTIN FDOM ps4.ps_spilled` by metis_tac[] >>
         `LIST_ELEM_COUNT (Var v) (stack_pop (LENGTH selected) ps4.ps_stack) = 0` by
           (qpat_x_assum `~MEM (Var v) (stack_pop _ _)` mp_tac >>
            simp_tac std_ss [GSYM LIST_ELEM_COUNT_MEM, arithmeticTheory.GREATER_DEF]) >>
         `ALL_DISTINCT (MAP Var inst.inst_outputs)` by
           (irule ALL_DISTINCT_MAP_INJ >> simp[]) >>
         drule all_distinct_elem_count_le_one >>
         disch_then (qspec_then `Var v` mp_tac) >> gvs[elem_count_append]) >>
     `~MEM (Var v) (MAP Var inst.inst_outputs)` by simp[MEM_MAP] >>
     `LIST_ELEM_COUNT (Var v) (MAP Var inst.inst_outputs) = 0` by
       gvs[GSYM LIST_ELEM_COUNT_MEM] >>
     gvs[elem_count_append]) >>
  drule_all regular_post_emit_tail_resource_nonincrease >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem native_regular_last_use_extinction:
  !lv dfg cfg fn inst nl halting term lbl ps ops qs v.
    inst.inst_opcode <> JMP /\ LENGTH (compute_operands inst) <= 16 /\
    MEM (Var v) (compute_operands inst) /\ ~MEM v nl /\
    ~MEM v inst.inst_outputs /\
    LIST_ELEM_COUNT (Var v) ps.ps_stack +
      (if Var v IN FDOM ps.ps_spilled then 1 else 0) <= 1 /\
    (!w. MEM (Var w) (compute_operands inst) ==>
      MEM (Var w) ps.ps_stack \/ Var w IN FDOM ps.ps_spilled) /\
    generate_regular_inst_plan lv dfg cfg fn inst nl halting term lbl ps = (ops,qs)
    ==> ~MEM (Var v) qs.ps_stack /\ Var v NOTIN FDOM qs.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  drule_at (Pos last) native_regular_stages >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule sortingTheory.PERM_LENGTH >> strip_tac >>
  `LIST_ELEM_COUNT (Var v) (stack_pop (LENGTH selected) ps4.ps_stack) = 0 /\
    Var v NOTIN FDOM ps4.ps_spilled` by
    (irule emit_reorder_pop_last_use_extinction >>
     goal_assum (drule_at (Pat `reorder_plan _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_input_plan _ _ _ _ = _`)) >> simp[]) >>
  drule fnPlanLineageReorderTheory.generate_emit_ops_slots >>
  disch_then (strip_assume_tac o SRULE [parameter_push_fold]) >>
  `~MEM (Var v) (MAP Var inst.inst_outputs)` by simp[MEM_MAP] >>
  `LIST_ELEM_COUNT (Var v) (MAP Var inst.inst_outputs) = 0` by
    gvs[GSYM LIST_ELEM_COUNT_MEM] >>
  `LIST_ELEM_COUNT (Var v) ps7.ps_stack +
    (if Var v IN FDOM ps7.ps_spilled then 1 else 0) = 0` by
    gvs[elem_count_append] >>
  drule_all regular_post_emit_tail_resource_nonincrease >>
  disch_then (qspec_then `Var v` mp_tac) >>
  Cases_on `Var v IN FDOM qs.ps_spilled` >>
  gvs[GSYM LIST_ELEM_COUNT_MEM]
QED

(* Only LAST live is looked up. Either prefix exclusion or a suffix hit
   shields that observation; the suffix need not be distinct. The exact
   do_swap_bottom_frame handles deep spill/allocator effects as well. *)
Theorem optimistic_swap_plan_shielded_bottom_frame:
  !dfg inst live term ps prefix ops qs.
    (live = [] \/ ~MEM (Var (LAST live)) prefix \/
      MEM (Var (LAST live)) ps.ps_stack) /\
    optimistic_swap_plan dfg inst live term ps = (ops,qs) ==>
    optimistic_swap_plan dfg inst live term
      (ps with ps_stack := prefix ++ ps.ps_stack) =
      (ops,qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `live = []` >- gvs[optimistic_swap_plan_def] >>
  `stack_get_depth (Var (LAST live)) (prefix ++ ps.ps_stack) =
   stack_get_depth (Var (LAST live)) ps.ps_stack` by
    (Cases_on `~MEM (Var (LAST live)) prefix`
     >- metis_tac[stack_get_depth_bottom_excluded] >>
     `IS_SOME (stack_get_depth (Var (LAST live)) ps.ps_stack)` by
       gvs[stack_get_depth_is_some] >>
     Cases_on `stack_get_depth (Var (LAST live)) ps.ps_stack` >> gvs[] >>
     metis_tac[stack_get_depth_suffix_hit]) >>
  gvs[optimistic_swap_plan_def, LET_THM] >>
  rpt IF_CASES_TAC >> gvs[] >>
  Cases_on `stack_get_depth (Var (LAST live)) ps.ps_stack` >> gvs[] >>
  `x < LENGTH ps.ps_stack` by metis_tac[stack_get_depth_props] >>
  drule_all do_swap_bottom_frame >> simp[]
QED

(* Legacy prefix-exclusion interface is a projection of observation shielding. *)
Theorem optimistic_swap_plan_bottom_frame:
  !dfg inst live term ps prefix ops qs.
    EVERY (\v. ~MEM (Var v) prefix) live /\
    optimistic_swap_plan dfg inst live term ps = (ops,qs) ==>
    optimistic_swap_plan dfg inst live term
      (ps with ps_stack := prefix ++ ps.ps_stack) =
      (ops,qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  rpt strip_tac >> irule optimistic_swap_plan_shielded_bottom_frame >>
  goal_assum (drule_at Any) >>
  Cases_on `live = []` >> gvs[EVERY_MEM] >>
  metis_tac[rich_listTheory.MEM_LAST_NOT_NIL]
QED

Theorem optimistic_swap_plan_suffix_hit_frame:
  !dfg inst live term ps prefix ops qs.
    (live = [] \/ MEM (Var (LAST live)) ps.ps_stack) /\
    optimistic_swap_plan dfg inst live term ps = (ops,qs) ==>
    optimistic_swap_plan dfg inst live term
      (ps with ps_stack := prefix ++ ps.ps_stack) =
      (ops,qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  rpt strip_tac >> irule optimistic_swap_plan_shielded_bottom_frame >>
  goal_assum (drule_at Any) >> simp[]
QED

(* E0381's native common-suffix coverage implies this EVERY premise by
   EVERY_MEM when live is the post-PHI live list and ps.ps_stack is the
   shared suffix. It does NOT establish coverage after preparation/pop. *)
Theorem optimistic_swap_plan_demand_covered_frame:
  !dfg inst live term ps prefix ops qs.
    EVERY (\v. MEM (Var v) ps.ps_stack) live /\
    optimistic_swap_plan dfg inst live term ps = (ops,qs) ==>
    optimistic_swap_plan dfg inst live term
      (ps with ps_stack := prefix ++ ps.ps_stack) =
      (ops,qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  rpt strip_tac >> irule optimistic_swap_plan_suffix_hit_frame >>
  goal_assum (drule_at Any) >>
  Cases_on `live = []` >> gvs[EVERY_MEM] >>
  metis_tac[rich_listTheory.MEM_LAST_NOT_NIL]
QED

Theorem popmany_plan_bottom_frame:
  !requests ps prefix ops qs.
    DISJOINT (set prefix) (set requests) /\
    popmany_plan requests ps = (ops,qs) ==>
    popmany_plan requests (ps with ps_stack := prefix ++ ps.ps_stack) =
      (ops,qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  qspec_then `requests` mp_tac popmany_plan_shared_core_replay >>
  disch_then (qspecl_then [`ps`,
    `ps with ps_stack := prefix ++ ps.ps_stack`] mp_tac) >>
  disch_then (qspecl_then [`[]`, `prefix`, `ps.ps_stack`] mp_tac) >>
  simp[] >> strip_tac >>
  gvs[stackPlanTypesTheory.plan_state_component_equality]
QED

Theorem generate_emit_ops_stack_update:
  !inst n ps stack ops qs.
    generate_emit_ops inst n ps = (ops,qs) ==>
    generate_emit_ops inst n (ps with ps_stack := stack) =
      (ops,qs with ps_stack := stack)
Proof
  rpt gen_tac >>
  simp[generate_emit_ops_def, fresh_label_def, LET_THM] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  Cases_on `venom_to_evm_name inst.inst_opcode` >> gvs[] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem release_dead_spills_stack_update:
  !live ps stack.
    release_dead_spills live (ps with ps_stack := stack) =
      (release_dead_spills live ps) with ps_stack := stack
Proof
  rpt gen_tac >> simp[release_dead_spills_def] >>
  qmatch_goalsub_abbrev_tac `FOLDL f _ dead` >>
  `!ps. FOLDL f (ps with ps_stack := stack) dead =
        (FOLDL f ps dead) with ps_stack := stack` suffices_by simp[] >>
  qpat_x_assum `Abbrev (dead = _)` kall_tac >>
  Induct_on `dead` >- simp[] >>
  Cases_on `h` >> simp[Abbr `f`] >>
  gen_tac >> first_x_assum (qspec_then
    `ps' with <|ps_spilled := ps'.ps_spilled \\ q;
                ps_alloc := free_spill_slot r ps'.ps_alloc|>` mp_tac) >> simp[]
QED

(* Literal non-JMP preparation prefix; planner definitions stay unchanged. *)
Definition lineage_regular_prepare_def:
  lineage_regular_prepare dfg inst nl ps =
    let operands = compute_operands inst in
    let topic = case inst.inst_opcode of LOG =>
      (case HD inst.inst_operands of Lit v => w2n v | _ => 0) | _ => 0 in
    let (iops,ps1) = emit_input_plan inst.inst_opcode operands nl ps in
    let (rops,ps4) =
      if is_commutative inst.inst_opcode /\ LENGTH operands >= 2 then
        let (oa,pa) = reorder_plan dfg operands ps1 in
        let swapped = TAKE (LENGTH operands - 2) operands ++
          [EL (LENGTH operands - 1) operands; EL (LENGTH operands - 2) operands] in
        let (ob,pb) = reorder_plan dfg swapped ps1 in
        if reorder_cost oa < reorder_cost ob then (oa,pa) else (ob,pb)
      else reorder_plan dfg operands ps1 in
    let ps5 = ps4 with ps_stack := stack_pop (LENGTH operands) ps4.ps_stack in
    let ps6 = FOLDL (\s out.
      s with ps_stack := stack_push (Var out) s.ps_stack) ps5 inst.inst_outputs in
    let (eops,ps7) = generate_emit_ops inst topic ps6 in
    (iops ++ rops ++ eops,ps7)
End

Theorem lineage_regular_prepare_live_coverage:
  !dfg inst nl ps ops qs.
    LENGTH (compute_operands inst) <= 16 /\
    (!v. MEM (Var v) (compute_operands inst) \/
      (MEM v nl /\ ~MEM v inst.inst_outputs) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    lineage_regular_prepare dfg inst nl ps = (ops,qs) ==>
    !v. MEM v nl ==> MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `lineage_regular_prepare _ _ _ _ = _` mp_tac >>
  simp[lineage_regular_prepare_def, LET_THM, parameter_push_fold] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  drule fnPlanLineageReorderTheory.generate_emit_ops_slots >> simp[] >> strip_tac >>
  qpat_x_assum `generate_emit_ops _ _ _ = _` kall_tac >>
  reverse (Cases_on `is_commutative inst.inst_opcode /\ LENGTH (compute_operands inst) >= 2`)
  >- (gvs[] >>
      qpat_assum `reorder_plan dfg (compute_operands inst) ps1 = _`
        (mp_then Any mp_tac emit_reorder_output_live_coverage) >>
      disch_then drule >> simp[] >>
      disch_then (qspec_then `inst.inst_outputs` mp_tac) >> metis_tac[]) >>
  gvs[] >>
  Cases_on `reorder_cost oa < reorder_cost ob`
  >- (gvs[] >>
      qpat_assum `reorder_plan dfg (compute_operands inst) ps1 = _`
        (mp_then Any mp_tac emit_reorder_output_live_coverage) >>
      disch_then drule >> simp[] >>
      disch_then (qspec_then `inst.inst_outputs` mp_tac) >> metis_tac[]) >>
  gvs[] >>
  `PERM (compute_operands inst)
    (TAKE (LENGTH (compute_operands inst) - 2) (compute_operands inst) ++
      [EL (LENGTH (compute_operands inst) - 1) (compute_operands inst);
       EL (LENGTH (compute_operands inst) - 2) (compute_operands inst)])` by
    (irule genericInputReadyTheory.last_two_reorder_perm >> gvs[]) >>
  qpat_assum `reorder_plan dfg (_ ++ _) ps1 = _`
    (mp_then Any mp_tac emit_reorder_output_live_coverage) >>
  disch_then drule >> simp[] >>
  disch_then (qspec_then `inst.inst_outputs` mp_tac) >> metis_tac[]
QED

Theorem lineage_regular_preoptimistic_live_coverage:
  !dfg inst nl ps ops qs halting ps8.
    LENGTH (compute_operands inst) <= 16 /\
    (!v. MEM (Var v) (compute_operands inst) \/
      (MEM v nl /\ ~MEM v inst.inst_outputs) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    lineage_regular_prepare dfg inst nl ps = (ops,qs) /\
    ps8 = (if inst.inst_outputs <> [] /\ (~halting \/ LENGTH inst.inst_outputs > 1)
      then SND (popmany_plan (MAP Var (FILTER (\v. ~MEM v nl) inst.inst_outputs)) qs)
      else qs) ==>
    !v. MEM v nl ==> MEM (Var v) ps8.ps_stack \/ Var v IN FDOM ps8.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  `!v. MEM v nl ==> MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled` by
    metis_tac[lineage_regular_prepare_live_coverage] >>
  metis_tac[dead_output_pop_live_coverage]
QED

Theorem lineage_regular_prepare_decompose:
  !liveness dfg cfg fn inst nl halting term lbl ps.
    inst.inst_opcode <> JMP ==>
    generate_regular_inst_plan liveness dfg cfg fn inst nl halting term lbl ps =
    case lineage_regular_prepare dfg inst nl ps of (ops,ps7) =>
      if inst.inst_outputs = [] then (ops, release_dead_spills nl ps7)
      else
        case (if ~halting \/ LENGTH inst.inst_outputs > 1 then
            popmany_plan (MAP Var (FILTER (\out. ~MEM out nl) inst.inst_outputs)) ps7
          else ([],ps7)) of (pops,ps8) =>
        case (if FILTER (\out. MEM out nl) inst.inst_outputs = [] then ([],ps8)
          else optimistic_swap_plan dfg inst nl term ps8) of (opts,ps9) =>
        (ops ++ pops ++ opts,release_dead_spills nl ps9)
Proof
  rpt strip_tac >>
  simp[lineage_regular_prepare_def, generate_regular_inst_plan_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt (IF_CASES_TAC >> gvs[]) >> simp[APPEND_ASSOC]
QED

Theorem lineage_regular_prepare_bottom_frame:
  !dfg inst nl ps prefix ops qs.
    LENGTH (compute_operands inst) <= 16 /\
    (!x. MEM x (compute_operands inst) /\ is_var_operand x ==>
      MEM x ps.ps_stack \/ x IN FDOM ps.ps_spilled) /\
    lineage_regular_prepare dfg inst nl ps = (ops,qs) ==>
    lineage_regular_prepare dfg inst nl
      (ps with ps_stack := prefix ++ ps.ps_stack) =
      (ops,qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  namedCases_on `emit_input_plan inst.inst_opcode (compute_operands inst) nl ps`
    ["iops ps1"] >>
  `!v. MEM (Var v) (compute_operands inst) ==>
    ~MEM (Var v) prefix \/ MEM (Var v) ps.ps_stack \/
    Var v IN FDOM ps.ps_spilled` by
    (gvs[stackPlanTypesTheory.is_var_operand_def] >> metis_tac[]) >>
  drule_all emit_input_plan_shielded_bottom_frame >> strip_tac >>
  qabbrev_tac `choice =
    if is_commutative inst.inst_opcode /\ 2 <= LENGTH (compute_operands inst) then
      case reorder_plan dfg (compute_operands inst) ps1 of (oa,pa) =>
      case reorder_plan dfg
        (TAKE (LENGTH (compute_operands inst) - 2) (compute_operands inst) ++
          [EL (LENGTH (compute_operands inst) - 1) (compute_operands inst);
           EL (LENGTH (compute_operands inst) - 2) (compute_operands inst)]) ps1 of (ob,pb) =>
      if reorder_cost oa < reorder_cost ob then (oa,pa) else (ob,pb)
    else reorder_plan dfg (compute_operands inst) ps1` >>
  namedCases_on `choice` ["rops ps4"] >>
  qpat_x_assum `Abbrev ((rops,ps4) = _)`
    (assume_tac o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all emitted_commutative_preparation_bottom_frame >>
  disch_then (qspec_then `prefix` strip_assume_tac) >>
  `stack_pop (LENGTH (compute_operands inst)) (prefix ++ ps4.ps_stack) =
    prefix ++ stack_pop (LENGTH (compute_operands inst)) ps4.ps_stack` by
    (irule stack_pop_bottom_extension >> simp[]) >>
  rule_assum_tac (SIMP_RULE bool_ss [pairTheory.pair_CASE_def,
    pairTheory.UNCURRY, pairTheory.PAIR]) >>
  qpat_x_assum `lineage_regular_prepare _ _ _ _ = _` mp_tac >>
  simp[lineage_regular_prepare_def, LET_THM, parameter_push_fold,
       arithmeticTheory.GREATER_EQ, APPEND_ASSOC, pairTheory.pair_CASE_def,
       pairTheory.UNCURRY, pairTheory.PAIR] >>
  qmatch_goalsub_abbrev_tac `generate_emit_ops inst topic (ps4 with ps_stack := core)` >>
  namedCases_on `generate_emit_ops inst topic (ps4 with ps_stack := core)` ["eops ps7"] >>
  drule generate_emit_ops_stack_update >>
  disch_then (qspec_then `prefix ++ core` assume_tac) >>
  qpat_assum `generate_emit_ops inst topic (ps4 with ps_stack := core) = _`
    (mp_then Any strip_assume_tac fnPlanLineageReorderTheory.generate_emit_ops_slots) >>
  simp[] >> strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  asm_rewrite_tac[]
QED

Theorem lineage_regular_prepare_output_suffix:
  !dfg inst nl ps ops qs.
    lineage_regular_prepare dfg inst nl ps = (ops,qs) ==>
    ?core. qs.ps_stack = core ++ MAP Var inst.inst_outputs
Proof
  rpt gen_tac >>
  simp[lineage_regular_prepare_def, LET_THM, parameter_push_fold] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  drule fnPlanLineageReorderTheory.generate_emit_ops_slots >> simp[] >>
  strip_tac >> goal_assum (drule_at Any)
QED

(* This is a code/metadata frame, not an inventory or future-demand theorem.
   In particular, neither core distinctness nor output freshness is needed. *)
Theorem native_regular_bottom_frame:
  !liveness dfg cfg fn inst nl halting term lbl ps prefix ops qs.
    inst.inst_opcode <> JMP /\ LENGTH (compute_operands inst) <= 16 /\
    (!x. MEM x (compute_operands inst) /\ is_var_operand x ==>
      MEM x ps.ps_stack \/ x IN FDOM ps.ps_spilled) /\
    EVERY (\v. ~MEM (Var v) prefix) (nl ++ inst.inst_outputs) /\
    generate_regular_inst_plan liveness dfg cfg fn inst nl halting term lbl ps = (ops,qs) ==>
    generate_regular_inst_plan liveness dfg cfg fn inst nl halting term lbl
      (ps with ps_stack := prefix ++ ps.ps_stack) =
      (ops,qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  fs[EVERY_APPEND] >>
  namedCases_on `lineage_regular_prepare dfg inst nl ps` ["preops ps7"] >>
  drule_all lineage_regular_prepare_bottom_frame >> strip_tac >>
  qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[lineage_regular_prepare_decompose] >>
  Cases_on `inst.inst_outputs = []`
  >- (simp[] >> strip_tac >>
      gvs[release_dead_spills_stack_update, release_dead_spills_stack]) >>
  simp[] >>
  `DISJOINT (set prefix)
    (set (MAP Var (FILTER (\v. ~MEM v nl) inst.inst_outputs)))` by
    (gvs[DISJOINT_ALT, EVERY_MEM, MEM_MAP, MEM_FILTER] >> metis_tac[]) >>
  namedCases_on `popmany_plan (MAP Var (FILTER (\v. ~MEM v nl) inst.inst_outputs)) ps7`
    ["pops ps8"] >>
  drule_all popmany_plan_bottom_frame >> strip_tac >>
  Cases_on `~halting \/ LENGTH inst.inst_outputs > 1` >> simp[] >>
  Cases_on `FILTER (\out. MEM out nl) inst.inst_outputs = []` >> simp[] >>
  TRY (strip_tac >> gvs[release_dead_spills_stack_update,
                        release_dead_spills_stack] >> NO_TAC) >>
  qmatch_goalsub_abbrev_tac `optimistic_swap_plan dfg inst nl term tailps` >>
  namedCases_on `optimistic_swap_plan dfg inst nl term tailps` ["oops ps9"] >>
  drule_all optimistic_swap_plan_bottom_frame >> strip_tac >>
  strip_tac >> gvs[release_dead_spills_stack_update, release_dead_spills_stack]
QED

(* Paired replay exposes one shared resulting core and identical metadata.
   This does not assert preservation of availability for a later instruction. *)
Theorem native_regular_shared_core_replay:
  !liveness dfg cfg fn inst nl halting term lbl ps prefixP prefixQ.
    inst.inst_opcode <> JMP /\ LENGTH (compute_operands inst) <= 16 /\
    (!x. MEM x (compute_operands inst) /\ is_var_operand x ==>
      MEM x ps.ps_stack \/ x IN FDOM ps.ps_spilled) /\
    EVERY (\v. ~MEM (Var v) prefixP) (nl ++ inst.inst_outputs) /\
    EVERY (\v. ~MEM (Var v) prefixQ) (nl ++ inst.inst_outputs) ==>
    ?ops qs.
      generate_regular_inst_plan liveness dfg cfg fn inst nl halting term lbl
        (ps with ps_stack := prefixP ++ ps.ps_stack) =
        (ops,qs with ps_stack := prefixP ++ qs.ps_stack) /\
      generate_regular_inst_plan liveness dfg cfg fn inst nl halting term lbl
        (ps with ps_stack := prefixQ ++ ps.ps_stack) =
        (ops,qs with ps_stack := prefixQ ++ qs.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  namedCases_on `generate_regular_inst_plan liveness dfg cfg fn inst nl halting term lbl ps`
    ["ops qs"] >>
  qexistsl [`ops`, `qs`] >> conj_tac >>
  irule native_regular_bottom_frame >> simp[]
QED

Theorem popmany_plan_appended_singleton:
  !x ps. popmany_plan [x] (ps with ps_stack := ps.ps_stack ++ [x]) =
    ([SOPop 1], ps)
Proof
  rpt gen_tac >>
  `stack_get_depth x (ps.ps_stack ++ [x]) = SOME 0` by
    simp[stack_get_depth_def, REVERSE_APPEND, stack_find_def] >>
  mp_tac (Q.INST [`ps` |-> `ps with ps_stack := ps.ps_stack ++ [x]`,
                  `v` |-> `x`] popmany_plan_top_singleton) >>
  simp[stack_pop_def, TAKE_APPEND]
QED

Theorem native_regular_singleton_bottom_frame:
  !liveness dfg cfg fn inst nl halting term lbl ps prefix ops qs.
    inst.inst_opcode <> JMP /\ LENGTH (compute_operands inst) <= 16 /\
    LENGTH inst.inst_outputs <= 1 /\
    (!x. MEM x (compute_operands inst) /\ is_var_operand x ==>
      MEM x ps.ps_stack \/ x IN FDOM ps.ps_spilled) /\
    EVERY (\v. ~MEM (Var v) prefix) nl /\
    generate_regular_inst_plan liveness dfg cfg fn inst nl halting term lbl ps = (ops,qs) ==>
    generate_regular_inst_plan liveness dfg cfg fn inst nl halting term lbl
      (ps with ps_stack := prefix ++ ps.ps_stack) =
      (ops,qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_outputs = []`
  >- (irule native_regular_bottom_frame >> simp[]) >>
  `?v. inst.inst_outputs = [v]` by
    (Cases_on `inst.inst_outputs` >> gvs[] >> Cases_on `t` >> gvs[]) >>
  Cases_on `MEM v nl`
  >- (irule native_regular_bottom_frame >> simp[] >> gvs[EVERY_MEM]) >>
  namedCases_on `lineage_regular_prepare dfg inst nl ps` ["preops ps7"] >>
  drule_all lineage_regular_prepare_bottom_frame >> strip_tac >>
  drule lineage_regular_prepare_output_suffix >> strip_tac >>
  qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[lineage_regular_prepare_decompose] >>
  `popmany_plan [Var v] ps7 = ([SOPop 1], ps7 with ps_stack := core)` by
    (`stack_get_depth (Var v) ps7.ps_stack = SOME 0` by
       simp[stack_get_depth_def, REVERSE_APPEND, stack_find_def] >>
     drule popmany_plan_top_singleton >>
     simp[stack_pop_def, TAKE_APPEND]) >>
  `popmany_plan [Var v] (ps7 with ps_stack := prefix ++ core ++ [Var v]) =
     ([SOPop 1], ps7 with ps_stack := prefix ++ core)` by
    (mp_tac (Q.SPECL [`Var v`, `ps7 with ps_stack := prefix ++ core`]
       popmany_plan_appended_singleton) >> simp[]) >>
  Cases_on `halting` >> simp[] >> strip_tac >>
  gvs[release_dead_spills_stack_update, release_dead_spills_stack, APPEND_ASSOC]
QED

(* Exact copies of planWf's local stack_swap_get_depth_deep and
   stack_pop_get_depth boundaries and their local dependencies. *)
Theorem stack_find_lupdate[local]:
  !xs p d i v.
    stack_find p xs = SOME d /\ i < d /\ i < LENGTH xs /\ ~p v ==>
    stack_find p (LUPDATE v i xs) = SOME d
Proof
  Induct >> simp[stack_find_def, LUPDATE_def] >>
  rpt gen_tac >>
  Cases_on `p h` >> simp[stack_find_def]
  >- (rpt strip_tac >> gvs[]) >>
  Cases_on `stack_find p xs` >> simp[] >>
  rename1 `stack_find p xs = SOME d1` >>
  rpt strip_tac >>
  Cases_on `i` >> simp[LUPDATE_def, stack_find_def] >>
  first_x_assum (qspecl_then [`p`, `d1`, `n`, `v`] mp_tac) >> simp[]
QED

Theorem reverse_lupdate[local]:
  !xs (v:'a) i. i < LENGTH xs ==>
    REVERSE (LUPDATE v i xs) =
    LUPDATE v (LENGTH xs - 1 - i) (REVERSE xs)
Proof
  Induct >> simp[LUPDATE_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `i` >> simp[LUPDATE_def, REVERSE_DEF, SNOC_APPEND]
  >- (`LENGTH (REVERSE xs) <= LENGTH xs` by simp[] >>
      simp[LUPDATE_APPEND2, LENGTH_REVERSE, LUPDATE_def]) >>
  rename1 `SUC n < SUC (LENGTH xs)` >>
  `n < LENGTH xs` by simp[] >>
  first_x_assum (qspecl_then [`v`, `n`] mp_tac) >>
  simp[] >> strip_tac >>
  simp[REVERSE_DEF, SNOC_APPEND] >>
  `LENGTH xs - 1 - n < LENGTH (REVERSE xs)` by simp[] >>
  simp[LUPDATE_APPEND1] >>
  `LENGTH xs - SUC n = LENGTH xs - 1 - n` by simp[] >> simp[]
QED

Theorem stack_find_no_earlier_match[local]:
  !xs p d. stack_find p xs = SOME d ==>
    !i. i < d ==> i < LENGTH xs ==> ~p (EL i xs)
Proof
  Induct >> simp[stack_find_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `p h` >> gvs[] >>
  Cases_on `stack_find p xs` >> gvs[] >>
  rename1 `stack_find p xs = SOME d1` >>
  rpt strip_tac >> Cases_on `i` >> gvs[EL] >>
  first_x_assum irule >> simp[]
QED

Theorem lupdate_commutes[local]:
  !i j (a:'a) b xs.
    i <> j ==>
    LUPDATE a i (LUPDATE b j xs) = LUPDATE b j (LUPDATE a i xs)
Proof
  Induct_on `xs` >> simp[LUPDATE_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `i` >> Cases_on `j` >> gvs[LUPDATE_def]
QED

Theorem reverse_stack_swap[local]:
  !cand stk. cand < LENGTH stk /\ 0 < LENGTH stk ==>
    REVERSE (stack_swap cand stk) =
    LUPDATE (EL cand (REVERSE stk)) 0
      (LUPDATE (EL 0 (REVERSE stk)) cand (REVERSE stk))
Proof
  rpt strip_tac >> simp[stack_swap_def, LET_THM] >>
  `LENGTH stk - 1 < LENGTH stk` by simp[] >>
  `LENGTH stk - 1 - cand < LENGTH stk` by simp[] >>
  simp[reverse_lupdate, LENGTH_LUPDATE] >>
  `EL (LENGTH stk - 1) stk = EL 0 (REVERSE stk)` by
    simp[Once EL_REVERSE, arithmeticTheory.PRE_SUB1] >>
  `EL (LENGTH stk - 1 - cand) stk = EL cand (REVERSE stk)` by
    (`LENGTH stk - 1 - cand = PRE (LENGTH stk - cand)` by simp[] >>
     pop_assum SUBST1_TAC >> simp[Once EL_REVERSE]) >>
  `LENGTH stk - (cand + 1) = LENGTH stk - 1 - cand` by simp[] >>
  `HD (REVERSE stk) = EL 0 (REVERSE stk)` by simp[EL] >>
  ntac 4 (pop_assum (fn th => CONV_TAC (DEPTH_CONV (REWR_CONV th)))) >>
  Cases_on `cand = 0` >> simp[] >> simp[Once lupdate_commutes]
QED

Theorem stack_swap_get_depth_deep:
  !cand stk op d.
    stack_get_depth op stk = SOME d /\
    cand < d /\ cand < LENGTH stk ==>
    stack_get_depth op (stack_swap cand stk) = SOME d
Proof
  rpt strip_tac >> imp_res_tac planWfTheory.stack_get_depth_bound >>
  `0 < LENGTH stk` by simp[] >>
  simp[stack_get_depth_def, reverse_stack_swap] >>
  fs[stack_get_depth_def] >>
  `~((\x. x = op) (EL 0 (REVERSE stk)))` by
    (drule stack_find_no_earlier_match >>
     disch_then (qspec_then `0` mp_tac) >> simp[LENGTH_REVERSE]) >>
  `~((\x. x = op) (EL cand (REVERSE stk)))` by
    (drule stack_find_no_earlier_match >>
     disch_then (qspec_then `cand` mp_tac) >> simp[LENGTH_REVERSE]) >>
  `stack_find (\x. x = op)
     (LUPDATE (EL 0 (REVERSE stk)) cand (REVERSE stk)) = SOME d` by
    (irule stack_find_lupdate >> simp[LENGTH_REVERSE]) >>
  `HD (REVERSE stk) = EL 0 (REVERSE stk)` by simp[EL] >>
  pop_assum (fn th => fs[GSYM th]) >>
  irule stack_find_lupdate >> simp[LENGTH_LUPDATE, LENGTH_REVERSE]
QED

Theorem stack_pop_get_depth:
  !stk op d.
    stack_get_depth op stk = SOME d /\ d > 0 ==>
    stack_get_depth op (stack_pop 1 stk) = SOME (d - 1)
Proof
  rpt strip_tac >> imp_res_tac planWfTheory.stack_get_depth_bound >>
  simp[stack_get_depth_def, stack_pop_def] >>
  `stk <> []` by (Cases_on `stk` >> fs[]) >>
  `TAKE (LENGTH stk - 1) stk = FRONT stk` by simp[GSYM FRONT_BY_TAKE] >>
  `REVERSE (FRONT stk) = TL (REVERSE stk)` by simp[GSYM REVERSE_TL] >>
  simp[] >> fs[stack_get_depth_def] >>
  `REVERSE stk <> []` by simp[REVERSE_EQ_NIL] >>
  Cases_on `REVERSE stk` >> gvs[] >> simp[stack_find_def] >>
  Cases_on `h = op` >- gvs[stack_find_def] >>
  fs[stack_find_def] >>
  Cases_on `stack_find (\x. x = op) (REVERSE (FRONT stk))` >> gvs[]
QED

Theorem stack_swap_pop_deeper_query:
  !cand stk op d.
    stack_get_depth op stk = SOME d /\ cand < d /\ cand < LENGTH stk ==>
    stack_get_depth op (stack_pop 1 (stack_swap cand stk)) = SOME (d - 1)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all stack_swap_get_depth_deep >> strip_tac >>
  irule stack_pop_get_depth >> simp[]
QED

(* Executable shielding probes: a contiguous fast path, a mixed >16-output
   individual path, and a bulk swap at depth 19. Old query copies remain. *)
Theorem popmany_fresh_output_shielding_probes:
  (!dead outs prefix.
    (dead = [Var "a"; Var "b"; Var "c"] /\
     outs = [Var "a"; Var "b"; Var "c"; Var "d"] /\
     prefix = [Var "a"; Var "c"]) \/
    (dead = MAP Var ["a";"c";"e";"g";"i";"k";"m";"o";"q";"s"] /\
     outs = MAP Var ["a";"b";"c";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m";"n";"o";"p";"q";"r";"s";"t"] /\
     prefix = [Var "a"; Var "s"]) \/
    (dead = [Var "a"] /\
     outs = MAP Var ["a";"b";"c";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m";"n";"o";"p";"q";"r";"s";"t"] /\
     prefix = [Var "a"]) ==>
    popmany_plan dead ((init_plan_state 0) with ps_stack := prefix ++ outs) =
      (FST (popmany_plan dead ((init_plan_state 0) with ps_stack := outs)),
       (SND (popmany_plan dead ((init_plan_state 0) with ps_stack := outs))) with
         ps_stack := prefix ++
           (SND (popmany_plan dead ((init_plan_state 0) with ps_stack := outs))).ps_stack))
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  CONV_TAC (LAND_CONV EVAL) >>
  CONV_TAC (RAND_CONV EVAL) >> REFL_TAC
QED

(* The exact accumulator step used by popmany_individual. *)
Definition lineage_delete_step_def:
  lineage_delete_step (ops, ps) v =
    case stack_get_depth v ps.ps_stack of
      NONE => (ops, ps)
    | SOME dist =>
        let (swap_ops, ps') =
          if dist = 0 then ([], ps) else do_swap dist ps in
        (ops ++ swap_ops ++ [SOPop 1],
         ps' with ps_stack := stack_pop 1 ps'.ps_stack)
End

Theorem lineage_delete_step_deeper:
  !ps v d w e acc ops qs.
    stack_get_depth v ps.ps_stack = SOME d /\
    stack_get_depth w ps.ps_stack = SOME e /\ d < e /\
    lineage_delete_step (acc,ps) v = (ops,qs) ==>
    stack_get_depth w qs.ps_stack = SOME (e - 1)
Proof
  rpt gen_tac >> strip_tac >>
  `d < LENGTH ps.ps_stack` by metis_tac[stack_get_depth_props] >>
  Cases_on `d = 0`
  >- (gvs[lineage_delete_step_def] >>
      irule stack_pop_get_depth >> simp[]) >>
  ` (SND (do_swap d ps)).ps_stack = stack_swap d ps.ps_stack` by
    simp[do_swap_stack_result] >>
  namedCases_on `do_swap d ps` ["swaps ps1"] >>
  gvs[lineage_delete_step_def] >>
  irule stack_swap_pop_deeper_query >> simp[]
QED

Theorem lineage_delete_step_bottom_frame:
  !ps v d acc prefix ops qs.
    stack_get_depth v ps.ps_stack = SOME d /\
    lineage_delete_step (acc,ps) v = (ops,qs) ==>
    lineage_delete_step (acc, ps with ps_stack := prefix ++ ps.ps_stack) v =
      (ops, qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  `d < LENGTH ps.ps_stack` by metis_tac[stack_get_depth_props] >>
  `stack_get_depth v (prefix ++ ps.ps_stack) = SOME d` by
    metis_tac[fnPlanLineageSuffixTheory.stack_get_depth_suffix_hit] >>
  Cases_on `d = 0`
  >- (gvs[lineage_delete_step_def] >>
      simp[stack_pop_bottom_extension]) >>
  namedCases_on `do_swap d ps` ["swaps ps1"] >>
  drule_all do_swap_bottom_frame >> strip_tac >>
  `LENGTH ps1.ps_stack = LENGTH ps.ps_stack` by
    (drule do_swap_stack_result >> simp[]) >>
  gvs[lineage_delete_step_def] >> simp[stack_pop_bottom_extension]
QED

Theorem sorted_pred_above[local]:
  !(ds:num list) d. sorting$SORTED ($<) ds /\ EVERY (\e. d < e) ds ==>
    sorting$SORTED ($<) (MAP (\e. e - 1) ds)
Proof
  `transitive ($< :num -> num -> bool)` by
    (simp[relationTheory.transitive_def] >> decide_tac) >>
  Induct >> simp[sortingTheory.SORTED_EQ, MEM_MAP] >> rpt strip_tac
  >- (first_x_assum irule >> simp[] >> qexists_tac `d` >> simp[]) >>
  gvs[] >> res_tac >> decide_tac
QED

Theorem lineage_ordered_delete_fold_frame:
  !requests depths ps acc prefix ops qs.
    LIST_REL (\x d. stack_get_depth x ps.ps_stack = SOME d) requests depths /\
    sorting$SORTED ($<) depths /\
    FOLDL lineage_delete_step (acc,ps) requests = (ops,qs) ==>
    FOLDL lineage_delete_step (acc,ps with ps_stack := prefix ++ ps.ps_stack) requests =
      (ops,qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[] >>
  Cases_on `depths` >> gvs[sortingTheory.SORTED_EQ] >>
  rename1 `stack_get_depth h ps.ps_stack = SOME d` >>
  namedCases_on `lineage_delete_step (acc,ps) h` ["acc1 ps1"] >>
  drule_all lineage_delete_step_bottom_frame >> strip_tac >> simp[] >>
  `LIST_REL (\x e. stack_get_depth x ps1.ps_stack = SOME e)
     requests (MAP (\e. e - 1) t)` by
    (gvs[LIST_REL_MAP2, LIST_REL_EL_EQN] >> rpt strip_tac >>
     irule lineage_delete_step_deeper >>
     goal_assum (drule_at (Pat `lineage_delete_step _ _ = _`)) >>
     qexists_tac `d` >> simp[] >> metis_tac[MEM_EL]) >>
  `sorting$SORTED ($<) (MAP (\e. e - 1) t)` by
    (irule sorted_pred_above >> simp[] >> qexists_tac `d` >> simp[EVERY_MEM]) >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `MAP (\e. e - 1) t` >> simp[]
QED

Theorem sorted_distinct_depths[local]:
  !xs (f:'a -> num).
    sorting$SORTED (\x y. f x <= f y) xs /\ ALL_DISTINCT xs /\
    (!x y. MEM x xs /\ MEM y xs /\ f x = f y ==> x = y) ==>
    sorting$SORTED ($<) (MAP f xs)
Proof
  Induct >> rpt gen_tac >>
  `transitive (\x y. (f:'a -> num) x <= f y)` by
    (simp[relationTheory.transitive_def] >> decide_tac) >>
  `transitive ($< : num -> num -> bool)` by
    (simp[relationTheory.transitive_def] >> decide_tac) >>
  simp[sortingTheory.SORTED_EQ, MEM_MAP] >> rpt strip_tac
  >- (gvs[] >> `f h <> f y'` by metis_tac[] >> res_tac >> decide_tac) >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem popmany_sorted_depths[local]:
  !requests stk.
    ALL_DISTINCT requests /\
    EVERY (\x. IS_SOME (stack_get_depth x stk)) requests ==>
    sorting$SORTED ($<)
      (MAP (\x. THE (stack_get_depth x stk))
        (QSORT (\a b. case (stack_get_depth a stk, stack_get_depth b stk) of
           (SOME da,SOME db) => da <= db | _ => T) requests))
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `f = \x. THE (stack_get_depth x stk)` >>
  `QSORT (\a b. case (stack_get_depth a stk, stack_get_depth b stk) of
     (SOME da,SOME db) => da <= db | _ => T) requests =
   QSORT (\a b. f a <= f b) requests` by
    (irule fnPlanLineageSortTheory.qsort_relation_on >> rpt strip_tac >>
     `IS_SOME (stack_get_depth x stk) /\ IS_SOME (stack_get_depth y stk)` by
       (fs[EVERY_MEM] >> metis_tac[]) >>
     simp[Abbr `f`] >>
     Cases_on `stack_get_depth x stk` >>
     Cases_on `stack_get_depth y stk` >> gvs[]) >>
  simp[] >> irule sorted_distinct_depths >>
  reverse conj_tac
  >- (conj_tac
      >- metis_tac[sortingTheory.QSORT_PERM, sortingTheory.ALL_DISTINCT_PERM] >>
      irule sortingTheory.QSORT_SORTED >>
      simp[relationTheory.transitive_def, relationTheory.total_def] >> decide_tac) >>
  rpt gen_tac >> simp[sortingTheory.QSORT_MEM] >> strip_tac >>
  `IS_SOME (stack_get_depth x stk) /\ IS_SOME (stack_get_depth y stk)` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  Cases_on `stack_get_depth x stk` >> Cases_on `stack_get_depth y stk` >>
  gvs[Abbr `f`] >> metis_tac[stack_get_depth_props]
QED

Theorem popmany_individual_incore_bottom_frame:
  !requests ps prefix ops qs.
    ALL_DISTINCT requests /\
    EVERY (\x. IS_SOME (stack_get_depth x ps.ps_stack)) requests /\
    popmany_individual requests ps = (ops,qs) ==>
    popmany_individual requests (ps with ps_stack := prefix ++ ps.ps_stack) =
      (ops,qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  `!x. MEM x requests ==>
    stack_get_depth x (prefix ++ ps.ps_stack) = stack_get_depth x ps.ps_stack` by
    (fs[EVERY_MEM] >> rpt strip_tac >>
     `IS_SOME (stack_get_depth x ps.ps_stack)` by metis_tac[] >>
     Cases_on `stack_get_depth x ps.ps_stack` >> gvs[] >>
     metis_tac[fnPlanLineageSuffixTheory.stack_get_depth_suffix_hit]) >>
  `QSORT (\a b. case (stack_get_depth a (prefix ++ ps.ps_stack),
      stack_get_depth b (prefix ++ ps.ps_stack)) of
      (SOME da,SOME db) => da <= db | _ => T) requests =
   QSORT (\a b. case (stack_get_depth a ps.ps_stack,
      stack_get_depth b ps.ps_stack) of
      (SOME da,SOME db) => da <= db | _ => T) requests` by
    (irule fnPlanLineageSortTheory.qsort_relation_on >> simp[]) >>
  `(\(acc,s). lineage_delete_step (acc,s)) = lineage_delete_step` by
    (simp[FUN_EQ_THM] >> Cases >> simp[]) >>
  gvs[popmany_individual_def, GSYM lineage_delete_step_def, SF ETA_ss] >>
  irule lineage_ordered_delete_fold_frame >>
  goal_assum (drule_at Any) >>
  qexists_tac `MAP (\x. THE (stack_get_depth x ps.ps_stack))
    (QSORT (\a b. case (stack_get_depth a ps.ps_stack,
      stack_get_depth b ps.ps_stack) of
      (SOME da,SOME db) => da <= db | _ => T) requests)` >>
  conj_tac >- (irule popmany_sorted_depths >> simp[]) >>
  simp[LIST_REL_EL_EQN, EL_MAP, SF ETA_ss] >> rpt strip_tac >>
  rename1 `i < LENGTH requests` >>
  qmatch_goalsub_abbrev_tac `stack_get_depth item _` >>
  `MEM item requests` by
    (qmatch_asmsub_abbrev_tac `FOLDL _ _ sorted` >>
     `MEM item sorted` by
       (simp[Abbr `item`, Abbr `sorted`] >>
        metis_tac[MEM_EL, sortingTheory.LENGTH_QSORT]) >>
     gvs[Abbr `sorted`, sortingTheory.QSORT_MEM]) >>
  `IS_SOME (stack_get_depth item ps.ps_stack)` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  Cases_on `stack_get_depth item ps.ps_stack` >> gvs[]
QED

Theorem popmany_plan_incore_bottom_frame:
  !requests ps prefix ops qs.
    ALL_DISTINCT requests /\
    EVERY (\x. IS_SOME (stack_get_depth x ps.ps_stack)) requests /\
    popmany_plan requests ps = (ops,qs) ==>
    popmany_plan requests (ps with ps_stack := prefix ++ ps.ps_stack) =
      (ops,qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  Cases >- simp[popmany_plan_def] >> rpt gen_tac >> strip_tac >>
  `MAP (\x. stack_get_depth x (prefix ++ ps.ps_stack)) (h::t) =
   MAP (\x. stack_get_depth x ps.ps_stack) (h::t)` by
    (irule MAP_CONG >> simp[] >> rpt strip_tac >>
     `IS_SOME (stack_get_depth x ps.ps_stack)` by
       (fs[EVERY_MEM] >> metis_tac[]) >>
     Cases_on `stack_get_depth x ps.ps_stack` >> gvs[] >>
     metis_tac[fnPlanLineageSuffixTheory.stack_get_depth_suffix_hit]) >>
  `EVERY IS_SOME (MAP (\x. stack_get_depth x ps.ps_stack) (h::t))` by
    simp[EVERY_MAP] >>
  gvs[popmany_plan_def, LET_THM] >>
  Cases_on `is_contiguous_top (MAP THE (MAP (\x. stack_get_depth x ps.ps_stack) (h::t)))`
  >- (gvs[] >>
      `LENGTH (h::t) < LENGTH ps.ps_stack` by
        (irule contiguous_top_depth_floor >> simp[]) >>
      namedCases_on `do_swap (LENGTH (h::t)) ps` ["swaps ps1"] >>
      drule_all do_swap_bottom_frame >> strip_tac >>
      `LENGTH ps1.ps_stack = LENGTH ps.ps_stack` by
        (drule do_swap_stack_result >> simp[]) >>
      gvs[] >> simp[stack_pop_bottom_extension]) >>
  gvs[] >> irule popmany_individual_incore_bottom_frame >> simp[]
QED

(* Output membership shields deletion even if older copies occur in prefix. *)
Theorem popmany_plan_output_suffix_bottom_frame:
  !requests outs core ps prefix ops qs.
    ALL_DISTINCT requests /\ EVERY (\x. MEM x outs) requests /\
    ps.ps_stack = core ++ outs /\ popmany_plan requests ps = (ops,qs) ==>
    popmany_plan requests (ps with ps_stack := prefix ++ ps.ps_stack) =
      (ops,qs with ps_stack := prefix ++ qs.ps_stack)
Proof
  rpt gen_tac >> strip_tac >> irule popmany_plan_incore_bottom_frame >>
  goal_assum (drule_at Any) >> simp[] >>
  fs[EVERY_MEM] >> rpt strip_tac >>
  `MEM x (core ++ outs)` by (simp[] >> metis_tac[]) >>
  metis_tac[stack_get_depth_is_some]
QED

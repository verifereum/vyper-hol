Theory fnPlanLineageSetup
Ancestors
  fnPlanPrefix fnPlanLineageDemand fnPlanLineageInventory stackPlanGen stackModel stackPlanTypes venomState reorderSim list rich_list venomWf venomInst callLayoutDefs
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
  qexists_tac `core9` >>
  gvs[EXTENSION, phi_release_dead_spills_domain, MEM_MAP]
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

Theorem release_fold_stack_update:
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
    (Cases_on `outputs <> [] /\ (~halting \/ LENGTH outputs > 1)`
     >- (qpat_x_assum `ps8 = _` SUBST_ALL_TAC >>
         simp[popmany_plan_spilled_unchanged] >>
         rpt strip_tac >> first_x_assum drule >> strip_tac
         >- (disj1_tac >> irule popmany_plan_retains_other >>
             simp[MEM_MAP, MEM_FILTER] >> metis_tac[]) >> simp[]) >>
     gvs[]) >>
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
  gvs[phi_release_dead_spills_domain, MEM_MAP] >> metis_tac[]
QED

Theorem emit_reorder_output_live_coverage:
  !ps m core spillbase operands selected opc nl outputs dfg iops ps1 rops ps4.
    ps.ps_stack = REPLICATE m dead_stack_marker ++ core /\
    residual_budget_wf spillbase [] (ps with ps_stack := core) /\
    EVERY (\x. x <> dead_stack_marker) operands /\ LENGTH operands <= 16 /\
    (!v. MEM (Var v) operands \/ (MEM v nl /\ ~MEM v outputs) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    PERM operands selected /\ emit_input_plan opc operands nl ps = (iops,ps1) /\
    reorder_plan dfg selected ps1 = (rops,ps4) ==>
    !v. MEM v nl ==>
      MEM (Var v) ((stack_pop (LENGTH operands) ps4.ps_stack) ++ MAP Var outputs) \/
      Var v IN FDOM ps4.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `keep = FILTER (\v. ~MEM v outputs) nl` >>
  `set keep SUBSET set nl` by (simp[Abbr `keep`, SUBSET_DEF, MEM_FILTER]) >>
  `!v. MEM (Var v) operands \/ MEM v keep ==>
     MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled` by
    (simp_tac bool_ss [Abbr `keep`, MEM_FILTER] >> metis_tac[]) >>
  drule emit_reorder_pop_marker_core_protected_reserve >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then drule >> disch_then drule >>
  simp[] >> strip_tac >>
  rpt strip_tac >> Cases_on `MEM v outputs` >- simp[MEM_MAP] >>
  `MEM v keep` by simp[Abbr `keep`, MEM_FILTER] >>
  first_x_assum drule >> simp[MEM_MAP] >> metis_tac[]
QED

(* Shared decomposition of the actual non-JMP planner, including its tail. *)
Theorem native_regular_stages[local]:
  !liveness dfg cfg fn inst nl halting term lbl ps ops qs.
    inst.inst_opcode <> JMP /\
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
  namedCases_on `emit_input_plan inst.inst_opcode (compute_operands inst) nl ps` ["iops ps1"] >>
  qabbrev_tac `swapped = TAKE (LENGTH (compute_operands inst) - 2) (compute_operands inst) ++
    [EL (LENGTH (compute_operands inst) - 1) (compute_operands inst);
     EL (LENGTH (compute_operands inst) - 2) (compute_operands inst)]` >>
  qabbrev_tac `choice =
    if is_commutative inst.inst_opcode /\ 2 <= LENGTH (compute_operands inst) then
      if reorder_cost (FST (reorder_plan dfg (compute_operands inst) ps1)) <
         reorder_cost (FST (reorder_plan dfg swapped ps1))
      then reorder_plan dfg (compute_operands inst) ps1 else reorder_plan dfg swapped ps1
    else reorder_plan dfg (compute_operands inst) ps1` >>
  namedCases_on `choice` ["rops ps4"] >>
  `?selected. PERM (compute_operands inst) selected /\
    reorder_plan dfg selected ps1 = (rops,ps4)` by
    (Cases_on `is_commutative inst.inst_opcode /\ 2 <= LENGTH (compute_operands inst)`
     >- (Cases_on `reorder_cost (FST (reorder_plan dfg (compute_operands inst) ps1)) <
           reorder_cost (FST (reorder_plan dfg swapped ps1))`
         >- (qexists_tac `compute_operands inst` >> gvs[markerTheory.Abbrev_def]) >>
         qexists_tac `swapped` >> gvs[markerTheory.Abbrev_def] >>
         irule genericInputReadyTheory.last_two_reorder_perm >> simp[]) >>
     qexists_tac `compute_operands inst` >> gvs[markerTheory.Abbrev_def]) >>
  qexistsl_tac [`selected`, `iops`, `ps1`, `rops`, `ps4`] >> simp[] >>
  qpat_x_assum `Abbrev ((rops,ps4) = _)`
    (assume_tac o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [generate_regular_inst_plan_def, LET_THM,
    pairTheory.pair_CASE_def, pairTheory.UNCURRY, pairTheory.FST, pairTheory.SND,
    pairTheory.PAIR, arithmeticTheory.GREATER_EQ] >>
  asm_simp_tac bool_ss [] >>
  qpat_x_assum `(if is_commutative _ /\ _ then _ else _) = _`
    (fn th => pure_rewrite_tac [th, pairTheory.FST, pairTheory.SND]) >>
  Cases_on `inst.inst_outputs = []` >> asm_simp_tac bool_ss [] >>
  qmatch_goalsub_abbrev_tac `generate_emit_ops inst topic emitted` >>
  qpat_x_assum `Abbrev (topic = _)` kall_tac >>
  namedCases_on `generate_emit_ops inst topic emitted` ["eops ps7"] >>
  simp_tac bool_ss [pairTheory.FST, pairTheory.SND] >>
  Cases_on `~halting \/ LENGTH inst.inst_outputs > 1` >>
  Cases_on `FILTER (\v. MEM v nl) inst.inst_outputs = []` >>
  simp[Abbr `emitted`] >> rpt strip_tac >> gvs[] >>
  qexistsl_tac [`topic`, `eops`] >> simp[]
QED

Theorem native_regular_live_lower:
  !liveness dfg cfg fn inst nl halting term lbl ps m core spillbase ops qs.
    ps.ps_stack = REPLICATE m dead_stack_marker ++ core /\
    residual_budget_wf spillbase [] (ps with ps_stack := core) /\
    inst.inst_opcode <> JMP /\ LENGTH (compute_operands inst) <= 16 /\
    EVERY (\x. x <> dead_stack_marker) (compute_operands inst) /\
    (!v. MEM (Var v) (compute_operands inst) \/
      (MEM v nl /\ ~MEM v inst.inst_outputs) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    generate_regular_inst_plan liveness dfg cfg fn inst nl halting term lbl ps = (ops,qs)
    ==> !v. MEM v nl ==> MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  drule_all native_regular_stages >> strip_tac >>
  `!v. MEM v nl ==>
    MEM (Var v) (stack_pop (LENGTH (compute_operands inst)) ps4.ps_stack ++ MAP Var inst.inst_outputs) \/
    Var v IN FDOM ps4.ps_spilled` by
    (drule emit_reorder_output_live_coverage >>
     disch_then drule >> disch_then drule >> disch_then drule >>
     disch_then drule >> disch_then drule >> disch_then drule >>
     disch_then drule >> simp[]) >>
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
  drule_all native_regular_stages >> strip_tac >>
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
    (qpat_assum `ps.ps_stack = _` (mp_then Any mp_tac emit_reorder_output_live_coverage) >>
     disch_then drule >> disch_then drule >> disch_then drule >>
     disch_then drule >> disch_then drule >> disch_then drule >>
     disch_then drule >> simp[]) >>
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
  !liveness dfg cfg fn inst nl halting term lbl ps m core base ops qs.
    ps.ps_stack = REPLICATE m dead_stack_marker ++ core /\
    residual_budget_wf base [] (ps with ps_stack := core) /\
    inst.inst_opcode <> JMP /\ LENGTH (compute_operands inst) <= 16 /\
    EVERY (\x. x <> dead_stack_marker) (compute_operands inst) /\
    (!v. MEM (Var v) (compute_operands inst) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    generate_regular_inst_plan liveness dfg cfg fn inst nl halting term lbl ps = (ops,qs) ==>
    !v. MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled \/
      MEM (Var v) (compute_operands inst) \/ MEM v inst.inst_outputs
Proof
  rpt gen_tac >> strip_tac >>
  drule_all native_regular_stages >> strip_tac >>
  `!v. MEM (Var v) (stack_pop (LENGTH (compute_operands inst)) ps4.ps_stack) \/
    Var v IN FDOM ps4.ps_spilled ==>
    MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled \/
    MEM (Var v) (compute_operands inst)` by
    (drule (PURE_REWRITE_RULE [GSYM AND_IMP_INTRO] emit_reorder_pop_marker_variable_origins) >>
     ntac 7 (disch_then drule) >>
     disch_then (qspec_then `ps4 with ps_stack := stack_pop (LENGTH (compute_operands inst)) ps4.ps_stack` mp_tac) >> simp[]) >>
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
  !liveness dfg cfg fn inst nl halting term lbl ps m core base ops qs P.
    ps.ps_stack = REPLICATE m dead_stack_marker ++ core /\
    residual_budget_wf base [] (ps with ps_stack := core) /\
    inst.inst_opcode <> JMP /\ LENGTH (compute_operands inst) <= 16 /\
    EVERY (\x. x <> dead_stack_marker) (compute_operands inst) /\
    (!v. MEM (Var v) (compute_operands inst) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    generate_regular_inst_plan liveness dfg cfg fn inst nl halting term lbl ps = (ops,qs) /\
    (!v. MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled \/
      MEM (Var v) (compute_operands inst) \/ MEM v inst.inst_outputs ==> P v) ==>
    !v. MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled ==> P v
Proof
  rpt gen_tac >> strip_tac >>
  drule (PURE_REWRITE_RULE [GSYM AND_IMP_INTRO] native_regular_variable_origins) >>
  ntac 6 (disch_then drule) >> metis_tac[]
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
  drule_all native_regular_stages >> strip_tac >>
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
  rpt strip_tac >> gvs[phi_release_dead_spills_domain, MEM_MAP]
QED

(*
 * The function-schedule runner, decomposed into stage contexts.
 *
 * run_named_fn_schedules takes each named function through the pass list
 * in turn, on the unit as the earlier functions left it; each function's
 * run is a fn_chain (o1FnScheduleDecomp).  Reading the chains pass-major
 * gives the stage contexts (stage_ctx), and consecutive stage contexts
 * are related by ctx_pass_stage (chain_facts_stages): with any_view
 * always, and with the walk view when the names are callee first.
 *)
Theory o1ScheduleDecomp
Ancestors
  o1PassContract o1FnScheduleDecomp venomPipelineRunner
  venomFnScheduleRunner venomFnScheduleRunnerProps venomPassDispatcher
  venomInst irSupply venomCompilerWf venomWf unitShapeDefs fcgDefs
  list rich_list o1ScheduleDecompHelpers o1PartialSchedule o1FnScheduleDecompHelpers


Theorem chain_facts_length:
  chain_facts R rpolicy passes unit order chains i ==>
  LENGTH (FST (EL i chains)) = SUC (LENGTH passes) /\
  LENGTH (SND (EL i chains)) = LENGTH passes
Proof
  simp[chain_facts_def] >> metis_tac[fn_chain_length]
QED

Theorem chain_facts_name:
  chain_facts R rpolicy passes unit order chains i /\ k <= LENGTH passes ==>
  (EL k (FST (EL i chains))).fn_name =
    (EL i unit.cu_context.ctx_functions).fn_name
Proof
  simp[chain_facts_def] >> rpt strip_tac >>
  drule fn_chain_names >> drule fn_chain_length >> rpt strip_tac >>
  gvs[EVERY_EL] >> first_x_assum (qspec_then `k` mp_tac) >> simp[]
QED

Theorem chain_facts_shape:
  chain_facts R rpolicy passes unit order chains i /\ k <= LENGTH passes ==>
  o1_fn_shape unit.cu_context (EL k (FST (EL i chains)))
Proof
  strip_tac >> drule chain_facts_length >> strip_tac >>
  gvs[chain_facts_def, EVERY_EL] >> first_x_assum irule >> simp[]
QED

Theorem chain_facts_row:
  chain_facts R rpolicy passes unit order chains i /\ k <= LENGTH passes ==>
  R k (EL k (FST (EL i chains)))
Proof
  strip_tac >> drule chain_facts_length >> strip_tac >>
  gvs[chain_facts_def]
QED

Theorem chain_facts_step:
  chain_facts R rpolicy passes unit order chains i /\ k < LENGTH passes ==>
  ?s out. fn_pass_step rpolicy (EL k passes) (EL k (SND (EL i chains)))
    s (EL k (FST (EL i chains))) out /\
    out.fpo_function = EL (SUC k) (FST (EL i chains))
Proof
  simp[chain_facts_def] >> metis_tac[fn_chain_step]
QED

Theorem chain_facts_suffix:
  chain_facts R rpolicy passes unit order chains i /\ k <= LENGTH passes ==>
  fn_steps rpolicy (DROP k passes) (EL k (FST (EL i chains)))
    (LAST (FST (EL i chains)))
Proof
  simp[chain_facts_def] >> metis_tac[fn_chain_fn_steps]
QED

Theorem chain_facts_invoke_targets:
  chain_facts R rpolicy passes unit order chains i /\ k <= LENGTH passes /\
  MEM n (fn_invoke_targets (EL k (FST (EL i chains)))) ==>
  MEM n (fn_invoke_targets (EL i unit.cu_context.ctx_functions))
Proof
  simp[chain_facts_def] >> rpt strip_tac >>
  drule fn_chain_invoke_targets >> drule fn_chain_length >> rpt strip_tac >>
  first_x_assum (qspec_then `EL k (FST (EL i chains))` mp_tac) >>
  simp[MEM_EL] >>
  impl_tac >- (qexists_tac `k` >> simp[]) >>
  simp[list_subset_def, EVERY_MEM, GSYM MEM_EL] >> metis_tac[]
QED

Theorem stage_ctx_names:
  LENGTH chains = LENGTH unit.cu_context.ctx_functions /\
  (!i. i < LENGTH chains ==> chain_facts R rpolicy passes unit order chains i) /\
  k <= LENGTH passes ==>
  ctx_fn_names (stage_ctx unit.cu_context chains k) = ctx_fn_names unit.cu_context
Proof
  strip_tac >> simp[ctx_fn_names_def, stage_ctx_def] >>
  irule LIST_EQ >> simp[stage_fns_def, EL_MAP] >>
  qx_gen_tac `i` >> strip_tac >> irule chain_facts_name >> metis_tac[]
QED

Theorem stage_ctx_inst_ids_distinct:
  LENGTH chains = LENGTH unit.cu_context.ctx_functions /\
  (!i. i < LENGTH chains ==> chain_facts R rpolicy passes unit order chains i) /\
  chains_ids_apart chains /\ k <= LENGTH passes ==>
  ctx_inst_ids_distinct (stage_ctx unit.cu_context chains k)
Proof
  strip_tac >>
  `!i. i < LENGTH chains ==> k < LENGTH (FST (EL i chains))` by
    (rpt strip_tac >> res_tac >> imp_res_tac chain_facts_length >> simp[]) >>
  simp[ctx_inst_ids_distinct_ir_ids, stage_ctx_def, stage_fns_def, MAP_MAP_o] >>
  match_mp_tac ALL_DISTINCT_FLAT_EL_apart >> conj_tac
  >- (simp[EVERY_MEM, MEM_MAP, PULL_EXISTS, MEM_EL] >> rpt strip_tac >>
      irule o1_fn_shape_inst_ids >> qexists_tac `unit.cu_context` >>
      irule chain_facts_shape >> metis_tac[]) >>
  simp[EL_MAP] >> rpt strip_tac >>
  `i < LENGTH chains /\ j < LENGTH chains` by simp[] >>
  qpat_x_assum `chains_ids_apart _` mp_tac >> rewrite_tac[chains_ids_apart_def] >>
  disch_then (qspecl_then [`i`,`j`,`EL k (FST (EL i chains))`,
                           `EL k (FST (EL j chains))`,`x`] mp_tac) >>
  fs[EL_MAP, EL_MEM]
QED

Theorem stage_ctx_shape:
  LENGTH chains = LENGTH unit.cu_context.ctx_functions /\
  o1_ctx_shape unit.cu_context /\
  (!i. i < LENGTH chains ==> chain_facts R rpolicy passes unit order chains i) /\
  chains_ids_apart chains /\ k <= LENGTH passes ==>
  o1_ctx_shape (stage_ctx unit.cu_context chains k)
Proof
  strip_tac >>
  `ctx_fn_names (stage_ctx unit.cu_context chains k) =
     ctx_fn_names unit.cu_context` by (irule stage_ctx_names >> metis_tac[]) >>
  `ctx_inst_ids_distinct (stage_ctx unit.cu_context chains k)` by
    (irule stage_ctx_inst_ids_distinct >> metis_tac[]) >>
  irule o1_ctx_shape_transport >> conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `unit.cu_context` >> simp[GSYM stage_ctx_def] >>
  simp[stage_ctx_def] >>
  simp[stage_fns_def, EVERY_MAP, EVERY_EL] >> rpt strip_tac >>
  simp[EL_MAP] >> irule chain_facts_shape >> metis_tac[]
QED

Theorem stage_ctx_rows:
  LENGTH chains = LENGTH unit.cu_context.ctx_functions /\
  (!i. i < LENGTH chains ==> chain_facts R rpolicy passes unit order chains i) /\
  k <= LENGTH passes ==>
  EVERY (R k) (stage_ctx unit.cu_context chains k).ctx_functions
Proof
  strip_tac >> simp[stage_ctx_def, stage_fns_def, EVERY_MAP, EVERY_EL] >>
  qx_gen_tac `i` >> strip_tac >> `i < LENGTH chains` by simp[] >>
  simp[EL_MAP] >> irule chain_facts_row >> metis_tac[]
QED

Theorem stage_lookup_index:
  LENGTH chains = LENGTH unit.cu_context.ctx_functions /\
  (!i. i < LENGTH chains ==> chain_facts R rpolicy passes unit order chains i) /\
  ALL_DISTINCT (ctx_fn_names unit.cu_context) /\ k <= LENGTH passes /\
  lookup_function n (stage_fns chains k) = SOME g ==>
  ?j. j < LENGTH chains /\ g = EL k (FST (EL j chains)) /\
      (EL j unit.cu_context.ctx_functions).fn_name = n
Proof
  strip_tac >>
  `ctx_fn_names (stage_ctx unit.cu_context chains k) =
     ctx_fn_names unit.cu_context` by (irule stage_ctx_names >> metis_tac[]) >>
  `ALL_DISTINCT (MAP (\f. f.fn_name) (stage_fns chains k))` by
    gvs[ctx_fn_names_def, stage_ctx_def] >>
  drule lookup_function_index_iff >>
  disch_then (qspecl_then [`n`,`g`] mp_tac) >> simp[] >>
  disch_then (qx_choose_then `j` strip_assume_tac) >>
  qexists_tac `j` >> gvs[stage_fns_def, EL_MAP] >>
  sym_tac >> irule chain_facts_name >> metis_tac[]
QED
Theorem ctx_pass_stage_indexed:
  C'.ctx_entry = C.ctx_entry /\
  C'.ctx_global_reserved = C.ctx_global_reserved /\
  LENGTH C.ctx_functions = LENGTH C'.ctx_functions /\
  (!i. i < LENGTH C.ctx_functions ==>
    ?observed s out.
      fn_pass_step rpolicy pass observed s (EL i C.ctx_functions) out /\
      out.fpo_function = EL i C'.ctx_functions /\
      observed.cu_context.ctx_entry = C.ctx_entry /\
      observed.cu_context.ctx_global_reserved = C.ctx_global_reserved /\
      ctx_fn_names observed.cu_context = ctx_fn_names C /\
      view C' (EL i C.ctx_functions) observed) ==>
  ctx_pass_stage rpolicy pass view C C'
Proof
  simp[ctx_pass_stage_def, LIST_REL_EL_EQN]
QED


Theorem run_named_fn_schedules_decomp:
  rows_step_contracts_from R rpolicy 0 passes /\
  EVERY (R 0) unit.cu_context.ctx_functions /\
  run_named_fn_schedules execute_configured_fn_pass rpolicy passes names
    unit s = SOME (unit', s') /\
  o1_ctx_shape unit.cu_context /\
  ALL_DISTINCT (unit_label_namespace unit) /\
  ALL_DISTINCT names /\
  (!n. MEM n names <=> MEM n (ctx_fn_names unit.cu_context)) /\
  ir_supply_inst_ok s ==>
  ?chains.
    LENGTH chains = LENGTH unit.cu_context.ctx_functions /\
    (!i. i < LENGTH chains ==>
         chain_facts R rpolicy passes unit names chains i) /\
    unit'.cu_context = stage_ctx unit.cu_context chains (LENGTH passes) /\
    (names <> [] ==> unit_labels_wf unit') /\
    chains_ids_apart chains /\
  ir_supply_inst_ok s'
Proof
  strip_tac >>
  `partial_schedule R rpolicy passes unit names []
    (MAP (\f. ([f],[])) unit.cu_context.ctx_functions) unit` by
    (irule partial_schedule_initial >> simp[]) >>
  drule_at (Pat `partial_schedule _ _ _ _ _ _ _ _`) partial_schedule_suffix >>
  disch_then (drule_at (Pat `run_named_fn_schedules _ _ _ _ _ _ = _`)) >>
  simp[] >> impl_tac >- simp[chains_ids_used_def] >>
  disch_then (qx_choose_then `chains` strip_assume_tac) >>
  qexists_tac `chains` >>
  drule partial_schedule_exhausted >> simp[] >> strip_tac >>
  drule partial_schedule_final_context >> simp[] >> strip_tac >>
  gvs[partial_schedule_def]
QED

(* ===== Stage contexts ===== *)

Theorem stage_ctx_zero:
  LENGTH chains = LENGTH ctx.ctx_functions /\
  (!i. i < LENGTH chains ==> HD (FST (EL i chains)) = EL i ctx.ctx_functions) /\
  (!i. i < LENGTH chains ==> FST (EL i chains) <> []) ==>
  stage_ctx ctx chains 0 = ctx
Proof
  rw[stage_ctx_def, stage_fns_def, venomInstTheory.venom_context_component_equality] >>
  simp[LIST_EQ_REWRITE, EL_MAP] >> rw[] >> rename1 `FST (EL i chains)` >>
  Cases_on `FST (EL i chains)` >> gvs[] >> metis_tac[]
QED

Theorem chain_facts_stage_shape:
  LENGTH chains = LENGTH unit.cu_context.ctx_functions /\
  o1_ctx_shape unit.cu_context /\
  (!i. i < LENGTH chains ==> chain_facts R rpolicy passes unit order chains i) /\
  chains_ids_apart chains /\ k <= LENGTH passes ==>
  ctx_fn_names (stage_ctx unit.cu_context chains k) =
    ctx_fn_names unit.cu_context /\
  o1_ctx_shape (stage_ctx unit.cu_context chains k)
Proof
  strip_tac >> conj_tac
  >- (irule stage_ctx_names >> metis_tac[]) >>
  irule stage_ctx_shape >> metis_tac[]
QED

Theorem chain_facts_walk_view:
  LENGTH chains = LENGTH unit.cu_context.ctx_functions /\
  o1_ctx_shape unit.cu_context /\
  (!i. i < LENGTH chains ==> chain_facts R rpolicy passes unit names chains i) /\
  callee_first names unit.cu_context.ctx_functions /\
  i < LENGTH chains /\ k < LENGTH passes ==>
  walk_view rpolicy (DROP (SUC k) passes)
    (stage_ctx unit.cu_context chains (SUC k))
    (EL k (FST (EL i chains))) (EL k (SND (EL i chains)))
Proof
  strip_tac >> simp[walk_view_def, stage_ctx_def] >>
  qx_gen_tac `n` >> qx_gen_tac `g` >> strip_tac >>
  `ALL_DISTINCT (ctx_fn_names unit.cu_context)` by
    gvs[o1_ctx_shape_def, ctx_wf_def, ctx_distinct_fn_names_def] >>
  `SUC k <= LENGTH passes` by simp[] >>
  drule_all stage_lookup_index >>
  disch_then (qx_choose_then `j` strip_assume_tac) >>
  `MEM n (fn_invoke_targets (EL i unit.cu_context.ctx_functions))` by
    (irule chain_facts_invoke_targets >>
     qexistsl_tac [`R`,`chains`,`k`,`names`,`passes`,`rpolicy`] >> simp[]) >>
  `list_precedes n (EL i unit.cu_context.ctx_functions).fn_name names` by
    (gvs[callee_first_def] >> first_x_assum irule >>
     simp[MEM_EL] >> qexists_tac `i` >> simp[]) >>
  `j <> i` by
    (strip_tac >> gvs[list_precedes_iff] >> metis_tac[]) >>
  qexists_tac `LAST (FST (EL j chains))` >> conj_tac
  >- (qpat_x_assum `!i. i < LENGTH chains ==> _`
        (qspec_then `i` mp_tac) >> simp[chain_facts_def] >>
      rpt strip_tac >> first_x_assum (qspec_then `k` mp_tac) >>
      simp[] >> metis_tac[]) >>
  gvs[] >> irule chain_facts_suffix >> metis_tac[]
QED

Theorem chain_facts_stages:
  LENGTH chains = LENGTH unit.cu_context.ctx_functions /\
  o1_ctx_shape unit.cu_context /\
  (!i. i < LENGTH chains ==> chain_facts R rpolicy passes unit names chains i) /\
  k < LENGTH passes ==>
  ctx_pass_stage rpolicy (EL k passes) any_view
    (stage_ctx unit.cu_context chains k)
    (stage_ctx unit.cu_context chains (SUC k)) /\
  (callee_first names unit.cu_context.ctx_functions ==>
   ctx_pass_stage rpolicy (EL k passes) (walk_view rpolicy (DROP (SUC k) passes))
     (stage_ctx unit.cu_context chains k)
     (stage_ctx unit.cu_context chains (SUC k)))
Proof
  strip_tac >> conj_tac
  >- suspend "any_stage" >>
  strip_tac >> suspend "walk_stage"
QED

Resume chain_facts_stages[any_stage]:
  `k <= LENGTH passes` by simp[] >>
  irule ctx_pass_stage_indexed >> simp[stage_ctx_def, stage_fns_def] >>
  qx_gen_tac `i` >> strip_tac >> simp[EL_MAP] >>
  `chain_facts R rpolicy passes unit names chains i` by simp[] >>
  drule chain_facts_step >> disch_then (qspec_then `k` mp_tac) >> simp[] >>
  disch_then (qx_choose_then `s` (qx_choose_then `out` strip_assume_tac)) >>
  qexistsl_tac [`EL k (SND (EL i chains))`,`s`,`out`] >>
  simp[any_view_def] >>
  `ctx_fn_names (stage_ctx unit.cu_context chains k) =
     ctx_fn_names unit.cu_context` by (irule stage_ctx_names >> metis_tac[]) >>
  gvs[stage_ctx_def, stage_fns_def, chain_facts_def]
QED

Resume chain_facts_stages[walk_stage]:
  `k <= LENGTH passes` by simp[] >>
  irule ctx_pass_stage_indexed >> simp[stage_ctx_def, stage_fns_def] >>
  qx_gen_tac `i` >> strip_tac >> simp[EL_MAP] >>
  `chain_facts R rpolicy passes unit names chains i` by simp[] >>
  drule chain_facts_step >> disch_then (qspec_then `k` mp_tac) >> simp[] >>
  disch_then (qx_choose_then `s` (qx_choose_then `out` strip_assume_tac)) >>
  qexistsl_tac [`EL k (SND (EL i chains))`,`s`,`out`] >> simp[] >>
  `ctx_fn_names (stage_ctx unit.cu_context chains k) =
     ctx_fn_names unit.cu_context` by (irule stage_ctx_names >> metis_tac[]) >>
  `walk_view rpolicy (DROP (SUC k) passes)
     (stage_ctx unit.cu_context chains (SUC k))
     (EL k (FST (EL i chains))) (EL k (SND (EL i chains)))` by
    (irule chain_facts_walk_view >> metis_tac[]) >>
  gvs[stage_ctx_def, stage_fns_def, chain_facts_def] >>
  first_x_assum (qspec_then `k` mp_tac) >> simp[]
QED

Finalise chain_facts_stages

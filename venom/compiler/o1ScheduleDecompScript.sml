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
  list rich_list o1ScheduleDecompHelpers

(* ===== The whole schedule ===== *)

(* chains has one (fs, obs) per function of the unit, in order; the
   stage-k context takes every function's k-th form. *)
Definition stage_fns_def:
  stage_fns chains k = MAP (\c. EL k (FST c)) chains
End

Definition stage_ctx_def:
  stage_ctx ctx chains k = ctx with ctx_functions := stage_fns chains k
End

(* What the schedule establishes for the i-th function's chain, with the
   names in the order the schedule took them: the units its passes
   observed have the unit's entry, reservations and names, and show every
   function scheduled earlier in its final form. *)
Definition chain_facts_def:
  chain_facts rpolicy passes unit order chains i <=>
    (?s0. fn_chain rpolicy passes s0 (FST (EL i chains)) (SND (EL i chains))) /\
    HD (FST (EL i chains)) = EL i unit.cu_context.ctx_functions /\
    EVERY (o1_fn_shape unit.cu_context) (FST (EL i chains)) /\
    !k. k < LENGTH passes ==>
      (EL k (SND (EL i chains))).cu_context.ctx_entry =
        unit.cu_context.ctx_entry /\
      (EL k (SND (EL i chains))).cu_context.ctx_global_reserved =
        unit.cu_context.ctx_global_reserved /\
      ctx_fn_names (EL k (SND (EL i chains))).cu_context =
        ctx_fn_names unit.cu_context /\
      !j. j < LENGTH chains /\ j <> i /\
          list_precedes (EL j unit.cu_context.ctx_functions).fn_name
                        (EL i unit.cu_context.ctx_functions).fn_name order ==>
          lookup_function (EL j unit.cu_context.ctx_functions).fn_name
            (EL k (SND (EL i chains))).cu_context.ctx_functions =
          SOME (LAST (FST (EL j chains)))
End

(* Partial schedules keep chains in the original function order. *)
Definition mixed_fns_def:
  mixed_fns ctx done chains =
    GENLIST (\i. if MEM (EL i ctx.ctx_functions).fn_name done
                 then LAST (FST (EL i chains))
                 else EL i ctx.ctx_functions) (LENGTH ctx.ctx_functions)
End

Definition partial_schedule_def:
  partial_schedule rpolicy passes original order done chains current <=>
    LENGTH chains = LENGTH original.cu_context.ctx_functions /\
    (!i. i < LENGTH chains /\
         MEM (EL i original.cu_context.ctx_functions).fn_name done ==>
         chain_facts rpolicy passes original order chains i) /\
    current.cu_context = original.cu_context with ctx_functions :=
      mixed_fns original.cu_context done chains /\
    o1_ctx_shape current.cu_context
End

Theorem mixed_fns_length[simp]:
  LENGTH (mixed_fns ctx done chains) = LENGTH ctx.ctx_functions
Proof
  simp[mixed_fns_def]
QED

Theorem mixed_fns_EL:
  i < LENGTH ctx.ctx_functions ==>
  EL i (mixed_fns ctx done chains) =
    if MEM (EL i ctx.ctx_functions).fn_name done
    then LAST (FST (EL i chains)) else EL i ctx.ctx_functions
Proof
  simp[mixed_fns_def, EL_GENLIST]
QED

Theorem mixed_fns_nil[simp]:
  mixed_fns ctx [] chains = ctx.ctx_functions
Proof
  simp[mixed_fns_def, LIST_EQ_REWRITE, EL_GENLIST]
QED

Theorem partial_schedule_initial:
  o1_ctx_shape original.cu_context ==>
  partial_schedule rpolicy passes original order []
    (MAP (\f. ([f],[])) original.cu_context.ctx_functions) original
Proof
  simp[partial_schedule_def]
QED

Theorem partial_schedule_names:
  partial_schedule rpolicy passes original order done chains current ==>
  ctx_fn_names current.cu_context = ctx_fn_names original.cu_context
Proof
  rw[partial_schedule_def, ctx_fn_names_def] >>
  irule LIST_EQ >> simp[EL_MAP] >> qx_gen_tac `i` >> strip_tac >>
  simp[mixed_fns_EL] >> IF_CASES_TAC >> simp[] >>
  qpat_x_assum `!i. _` (qspec_then `i` mp_tac) >>
  simp[chain_facts_def] >> rpt strip_tac >>
  drule fn_chain_names >> drule fn_chain_length >> rpt strip_tac >>
  gvs[EVERY_MEM] >> first_x_assum irule >>
  simp[MEM_EL] >> qexists_tac `LENGTH passes` >> simp[] >>
  `FST (EL i chains) <> []` by (strip_tac >> gvs[]) >>
  drule LAST_EL >> simp[]
QED

Theorem chain_facts_update_unobserved:
  i < LENGTH chains /\ t <> i /\
  ~list_precedes (EL t unit.cu_context.ctx_functions).fn_name
                 (EL i unit.cu_context.ctx_functions).fn_name order /\
  chain_facts rpolicy passes unit order chains i ==>
  chain_facts rpolicy passes unit order (LUPDATE c t chains) i
Proof
  simp[chain_facts_def, EL_LUPDATE] >> rpt strip_tac >>
  Cases_on `j = t` >> gvs[]
QED

Theorem partial_schedule_completed_update:
  partial_schedule rpolicy passes original (done ++ n::todo) done chains current /\
  ALL_DISTINCT (done ++ n::todo) /\
  t < LENGTH chains /\
  (EL t original.cu_context.ctx_functions).fn_name = n ==>
  !i. i < LENGTH chains /\
      MEM (EL i original.cu_context.ctx_functions).fn_name done ==>
      chain_facts rpolicy passes original (done ++ n::todo) (LUPDATE c t chains) i
Proof
  rpt strip_tac >> irule chain_facts_update_unobserved >>
  gvs[partial_schedule_def] >>
  drule list_precedes_prefix >> rpt strip_tac >>
  gvs[] >> metis_tac[]
QED

Theorem partial_schedule_pending_lookup:
  partial_schedule rpolicy passes original order done chains current /\
  t < LENGTH original.cu_context.ctx_functions /\
  ~MEM (EL t original.cu_context.ctx_functions).fn_name done ==>
  lookup_unique_function (EL t original.cu_context.ctx_functions).fn_name
    current.cu_context.ctx_functions = SOME (EL t original.cu_context.ctx_functions)
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (MAP (\f. f.fn_name) current.cu_context.ctx_functions)` by
    gvs[partial_schedule_def, o1_ctx_shape_def, ctx_wf_def,
        ctx_distinct_fn_names_def, ctx_fn_names_def] >>
  simp[lookup_unique_function_member_iff] >>
  qpat_x_assum `partial_schedule _ _ _ _ _ _ _` mp_tac >>
  simp[partial_schedule_def] >> strip_tac >>
  simp[MEM_EL] >> qexists_tac `t` >> simp[mixed_fns_EL]
QED

Theorem partial_schedule_mixed_name:
  partial_schedule rpolicy passes original order done chains current /\
  j < LENGTH original.cu_context.ctx_functions ==>
  (EL j (mixed_fns original.cu_context done chains)).fn_name =
    (EL j original.cu_context.ctx_functions).fn_name
Proof
  strip_tac >> drule partial_schedule_names >>
  disch_then (mp_tac o Q.AP_TERM `EL j`) >>
  gvs[partial_schedule_def, ctx_fn_names_def, EL_MAP]
QED

Theorem partial_schedule_mixed_update:
  partial_schedule rpolicy passes original order done chains current /\
  ALL_DISTINCT (ctx_fn_names original.cu_context) /\
  t < LENGTH chains /\
  (EL t original.cu_context.ctx_functions).fn_name = n /\ ~MEM n done ==>
  mixed_fns original.cu_context (done ++ [n]) (LUPDATE (fs,obs) t chains) =
  replace_fn n (LAST fs) (mixed_fns original.cu_context done chains)
Proof
  rpt strip_tac >> irule LIST_EQ >> simp[] >>
  qx_gen_tac `j` >> strip_tac >>
  `LENGTH chains = LENGTH original.cu_context.ctx_functions` by
    gvs[partial_schedule_def] >>
  `(EL j (mixed_fns original.cu_context done chains)).fn_name =
   (EL j original.cu_context.ctx_functions).fn_name` by
    (irule partial_schedule_mixed_name >> metis_tac[]) >>
  `(EL j original.cu_context.ctx_functions).fn_name = n <=> j = t` by
    (gvs[ctx_fn_names_def] >> irule distinct_fn_name_index >> simp[]) >>
  simp[replace_fn_EL, mixed_fns_EL, EL_LUPDATE] >>
  Cases_on `j = t` >> gvs[]
QED

Theorem partial_schedule_fields:
  partial_schedule rpolicy passes original order done chains current ==>
  current.cu_context.ctx_entry = original.cu_context.ctx_entry /\
  current.cu_context.ctx_global_reserved = original.cu_context.ctx_global_reserved
Proof
  simp[partial_schedule_def] >> rpt strip_tac >> simp[]
QED

Theorem partial_schedule_completed_lookup:
  partial_schedule rpolicy passes original order done chains current /\
  j < LENGTH chains /\
  MEM (EL j original.cu_context.ctx_functions).fn_name done ==>
  lookup_function (EL j original.cu_context.ctx_functions).fn_name
    current.cu_context.ctx_functions = SOME (LAST (FST (EL j chains)))
Proof
  rpt strip_tac >>
  `LENGTH chains = LENGTH original.cu_context.ctx_functions` by
    gvs[partial_schedule_def] >>
  `j < LENGTH original.cu_context.ctx_functions` by simp[] >>
  drule_all partial_schedule_mixed_name >>
  simp[mixed_fns_EL] >> strip_tac >>
  `ALL_DISTINCT (MAP (\f. f.fn_name) current.cu_context.ctx_functions)` by
    gvs[partial_schedule_def, o1_ctx_shape_def, ctx_wf_def,
        ctx_distinct_fn_names_def, ctx_fn_names_def] >>
  simp[lookup_function_member_iff] >>
  qpat_x_assum `partial_schedule _ _ _ _ _ _ _` mp_tac >>
  simp[partial_schedule_def] >> strip_tac >>
  simp[MEM_EL] >> qexists_tac `j` >> simp[mixed_fns_EL]
QED

Theorem partial_schedule_observed_fields:
  partial_schedule rpolicy passes original order done chains current /\
  g.fn_name = n ==>
  (unit_with_fns current (replace_fn n g current.cu_context.ctx_functions)).cu_context.ctx_entry =
    original.cu_context.ctx_entry /\
  (unit_with_fns current (replace_fn n g current.cu_context.ctx_functions)).cu_context.ctx_global_reserved =
    original.cu_context.ctx_global_reserved /\
  ctx_fn_names (unit_with_fns current (replace_fn n g current.cu_context.ctx_functions)).cu_context =
    ctx_fn_names original.cu_context
Proof
  strip_tac >> drule partial_schedule_fields >>
  drule partial_schedule_names >> rpt strip_tac >>
  simp[unit_with_fns_def, ctx_fn_names_def, replace_fn_names] >>
  gvs[ctx_fn_names_def]
QED

Theorem partial_schedule_observed_lookup:
  partial_schedule rpolicy passes original order done chains current /\
  j < LENGTH chains /\
  MEM (EL j original.cu_context.ctx_functions).fn_name done /\
  (EL j original.cu_context.ctx_functions).fn_name <> n /\ g.fn_name = n ==>
  lookup_function (EL j original.cu_context.ctx_functions).fn_name
    (unit_with_fns current (replace_fn n g current.cu_context.ctx_functions)).cu_context.ctx_functions =
      SOME (LAST (FST (EL j chains)))
Proof
  strip_tac >> simp[unit_with_fns_def, replace_fn_lookup_other] >>
  irule partial_schedule_completed_lookup >> metis_tac[]
QED

Theorem partial_schedule_chain_observations:
  partial_schedule rpolicy passes original (done ++ n::todo) done chains current /\
  ALL_DISTINCT (done ++ n::todo) /\
  i < LENGTH chains /\ (EL i original.cu_context.ctx_functions).fn_name = n /\
  fn_chain rpolicy passes s fs obs /\ HD fs = EL i original.cu_context.ctx_functions /\
  (!k. k < LENGTH obs ==> EL k obs =
    unit_with_fns current (replace_fn n (EL k fs) current.cu_context.ctx_functions)) ==>
  !k. k < LENGTH passes ==>
    (EL k obs).cu_context.ctx_entry = original.cu_context.ctx_entry /\
    (EL k obs).cu_context.ctx_global_reserved = original.cu_context.ctx_global_reserved /\
    ctx_fn_names (EL k obs).cu_context = ctx_fn_names original.cu_context /\
    !j. j < LENGTH chains /\ j <> i /\
      list_precedes (EL j original.cu_context.ctx_functions).fn_name
                    (EL i original.cu_context.ctx_functions).fn_name (done ++ n::todo) ==>
      lookup_function (EL j original.cu_context.ctx_functions).fn_name
        (EL k obs).cu_context.ctx_functions = SOME (LAST (FST (EL j chains)))
Proof
  strip_tac >> qx_gen_tac `k` >> strip_tac >>
  drule fn_chain_length >> strip_tac >>
  `(EL k fs).fn_name = n` by
    (drule fn_chain_names >> simp[EVERY_EL] >>
     disch_then (qspec_then `k` mp_tac) >> simp[]) >>
  `EL k obs = unit_with_fns current
     (replace_fn n (EL k fs) current.cu_context.ctx_functions)` by simp[] >>
  asm_rewrite_tac[] >>
  conj_tac >- (irule (cj 1 partial_schedule_observed_fields) >> metis_tac[]) >>
  conj_tac >- (irule (cj 2 partial_schedule_observed_fields) >> metis_tac[]) >>
  conj_tac >- (irule (cj 3 partial_schedule_observed_fields) >> metis_tac[]) >>
  rpt strip_tac >> irule partial_schedule_observed_lookup >>
  drule list_precedes_prefix >> rpt strip_tac >>
  metis_tac[]
QED

Theorem partial_schedule_shapes:
  partial_schedule rpolicy passes original order done chains current /\
  EVERY (o1_fn_shape current.cu_context) fs ==>
  EVERY (o1_fn_shape original.cu_context) fs
Proof
  strip_tac >> drule partial_schedule_names >>
  drule partial_schedule_fields >> rpt strip_tac >>
  gvs[EVERY_MEM] >> metis_tac[o1_fn_shape_ctx_eq]
QED

Theorem partial_schedule_new_chain:
  partial_schedule rpolicy passes original (done ++ n::todo) done chains current /\
  ALL_DISTINCT (done ++ n::todo) /\
  i < LENGTH chains /\ (EL i original.cu_context.ctx_functions).fn_name = n /\
  fn_chain rpolicy passes s fs obs /\ HD fs = EL i original.cu_context.ctx_functions /\
  EVERY (o1_fn_shape current.cu_context) fs /\
  (!k. k < LENGTH obs ==> EL k obs =
    unit_with_fns current (replace_fn n (EL k fs) current.cu_context.ctx_functions)) ==>
  chain_facts rpolicy passes original (done ++ n::todo) (LUPDATE (fs,obs) i chains) i
Proof
  strip_tac >> drule partial_schedule_chain_observations >> simp[] >> strip_tac >>
  drule_all partial_schedule_shapes >> strip_tac >>
  simp[chain_facts_def, EL_LUPDATE] >> conj_tac
  >- (qexists_tac `s` >> simp[]) >>
  simp[] >> rpt strip_tac >> simp[EL_LUPDATE] >> metis_tac[]
QED

Theorem partial_schedule_extend:
  partial_schedule rpolicy passes original (done ++ n::todo) done chains current /\
  ALL_DISTINCT (done ++ n::todo) /\
  ALL_DISTINCT (ctx_fn_names original.cu_context) /\
  i < LENGTH chains /\ (EL i original.cu_context.ctx_functions).fn_name = n /\
  fn_chain rpolicy passes s fs obs /\ HD fs = EL i original.cu_context.ctx_functions /\
  EVERY (o1_fn_shape current.cu_context) fs /\
  (!k. k < LENGTH obs ==> EL k obs =
    unit_with_fns current (replace_fn n (EL k fs) current.cu_context.ctx_functions)) /\
  next.cu_context = current.cu_context with ctx_functions :=
    replace_fn n (LAST fs) current.cu_context.ctx_functions ==>
  partial_schedule rpolicy passes original (done ++ n::todo) (done ++ [n])
    (LUPDATE (fs,obs) i chains) next
Proof
  strip_tac >>
  drule list_precedes_prefix >> strip_tac >>
  drule_all fn_chain_last_properties >> strip_tac >>
  `o1_ctx_shape next.cu_context` by
    (asm_rewrite_tac[] >> irule o1_ctx_shape_replace >>
     gvs[partial_schedule_def]) >>
  `LENGTH chains = LENGTH original.cu_context.ctx_functions` by
    gvs[partial_schedule_def] >>
  `chain_facts rpolicy passes original (done ++ n::todo)
     (LUPDATE (fs,obs) i chains) i` by
    (irule partial_schedule_new_chain >> metis_tac[]) >>
  `!j. j < LENGTH chains /\
       MEM (EL j original.cu_context.ctx_functions).fn_name done ==>
       chain_facts rpolicy passes original (done ++ n::todo)
         (LUPDATE (fs,obs) i chains) j` by
    (rpt strip_tac >> irule partial_schedule_completed_update >> metis_tac[]) >>
  `!j. j < LENGTH chains /\
       (EL j original.cu_context.ctx_functions).fn_name = n ==> j = i` by
    (rpt strip_tac >>
     `((EL j original.cu_context.ctx_functions).fn_name =
       (EL i original.cu_context.ctx_functions).fn_name <=> j = i)` by
       (irule distinct_fn_name_index >> gvs[ctx_fn_names_def]) >> metis_tac[]) >>
  drule partial_schedule_mixed_update >> simp[] >> strip_tac >>
  simp[partial_schedule_def] >> conj_tac
  >- (rpt strip_tac >> metis_tac[]) >>
  gvs[partial_schedule_def]
QED
Theorem partial_schedule_step:
  EVERY (o1_step_contract rpolicy) passes /\
  partial_schedule rpolicy passes original (done ++ n::todo) done chains current /\
  ALL_DISTINCT (done ++ n::todo) /\
  (!name. MEM name (done ++ n::todo) <=>
          MEM name (ctx_fn_names original.cu_context)) /\
  ALL_DISTINCT (unit_label_namespace current) /\
  run_configured_fn_passes execute_configured_fn_pass rpolicy passes n
    current s = SOME (next,s') ==>
  ?chains'. partial_schedule rpolicy passes original (done ++ n::todo)
    (done ++ [n]) chains' next /\ unit_labels_wf next
Proof
  strip_tac >>
  `o1_ctx_shape current.cu_context` by gvs[partial_schedule_def] >>
  drule_all run_configured_fn_passes_decomp >> strip_tac >>
  `ALL_DISTINCT (ctx_fn_names original.cu_context)` by
    (drule partial_schedule_names >> strip_tac >>
     gvs[o1_ctx_shape_def, ctx_wf_def, ctx_distinct_fn_names_def]) >>
  `LENGTH chains = LENGTH original.cu_context.ctx_functions` by
    gvs[partial_schedule_def] >>
  `MEM n (ctx_fn_names original.cu_context)` by metis_tac[MEM_APPEND, MEM] >>
  `?i. i < LENGTH original.cu_context.ctx_functions /\
       (EL i original.cu_context.ctx_functions).fn_name = n` by
    (qpat_x_assum `MEM n (ctx_fn_names _)` mp_tac >>
     simp[ctx_fn_names_def, MEM_EL] >>
     disch_then (qx_choose_then `idx` strip_assume_tac) >>
     qexists_tac `idx` >> gvs[EL_MAP]) >>
  drule list_precedes_prefix >> strip_tac >>
  `lookup_unique_function n current.cu_context.ctx_functions =
     SOME (EL i original.cu_context.ctx_functions)` by
    (drule partial_schedule_pending_lookup >>
     disch_then (qspec_then `i` mp_tac) >> simp[]) >>
  `HD fs = EL i original.cu_context.ctx_functions` by metis_tac[optionTheory.SOME_11] >>
  qexists_tac `LUPDATE (fs,obs) i chains` >> simp[] >>
  irule partial_schedule_extend >> metis_tac[]
QED

Theorem partial_schedule_suffix:
  !todo done chains current s final sf order.
  EVERY (o1_step_contract rpolicy) passes /\
  order = done ++ todo /\
  partial_schedule rpolicy passes original order done chains current /\
  ALL_DISTINCT order /\
  (!name. MEM name order <=> MEM name (ctx_fn_names original.cu_context)) /\
  ALL_DISTINCT (unit_label_namespace current) /\
  run_named_fn_schedules execute_configured_fn_pass rpolicy passes todo
    current s = SOME (final,sf) ==>
  ?chains'. partial_schedule rpolicy passes original order order chains' final /\
    (todo <> [] ==> unit_labels_wf final)
Proof
  Induct
  >- (simp[run_named_fn_schedules_def] >> rpt strip_tac >>
      qexists_tac `chains` >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  gvs[Once run_named_fn_schedules_def, AllCaseEqs()] >>
  rename1 `run_configured_fn_passes _ _ _ h current s = SOME (mid,sm)` >>
  rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  `!name. MEM name (done ++ h::todo) <=>
          MEM name (ctx_fn_names original.cu_context)` by
    (simp[] >> metis_tac[]) >>
  drule_all partial_schedule_step >>
  disch_then (qx_choose_then `nextchains` strip_assume_tac) >>
  `ALL_DISTINCT (unit_label_namespace mid)` by gvs[unit_labels_wf_def] >>
  `partial_schedule rpolicy passes original ((done ++ [h]) ++ todo)
     (done ++ [h]) nextchains mid` by (pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> asm_rewrite_tac[]) >>
  `ALL_DISTINCT ((done ++ [h]) ++ todo)` by
    (pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> asm_rewrite_tac[]) >>
  first_x_assum (drule_at (Pat `partial_schedule _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `run_named_fn_schedules _ _ _ _ _ _ = _`)) >>
  simp[APPEND_ASSOC] >>
  disch_then (qx_choose_then `finalchains` strip_assume_tac) >>
  qexists_tac `finalchains` >> simp[] >> Cases_on `todo` >> gvs[run_named_fn_schedules_def]
QED

Theorem partial_schedule_exhausted:
  partial_schedule rpolicy passes original order order chains final /\
  (!n. MEM n order <=> MEM n (ctx_fn_names original.cu_context)) ==>
  !i. i < LENGTH chains ==> chain_facts rpolicy passes original order chains i
Proof
  rw[partial_schedule_def] >> first_x_assum irule >> simp[] >>
  simp[ctx_fn_names_def, MEM_MAP] >>
  qexists_tac `EL i original.cu_context.ctx_functions` >> simp[MEM_EL] >>
  qexists_tac `i` >> simp[]
QED

Theorem chain_facts_last:
  chain_facts rpolicy passes unit order chains i ==>
  LAST (FST (EL i chains)) = EL (LENGTH passes) (FST (EL i chains))
Proof
  simp[chain_facts_def] >> rpt strip_tac >>
  drule fn_chain_length >> strip_tac >>
  `FST (EL i chains) <> []` by (strip_tac >> gvs[]) >>
  drule LAST_EL >> simp[]
QED

Theorem partial_schedule_final_context:
  partial_schedule rpolicy passes original order order chains final /\
  (!n. MEM n order <=> MEM n (ctx_fn_names original.cu_context)) ==>
  final.cu_context = stage_ctx original.cu_context chains (LENGTH passes)
Proof
  strip_tac >> drule partial_schedule_exhausted >> simp[] >> strip_tac >>
  gvs[partial_schedule_def, stage_ctx_def] >>
  simp[venom_context_component_equality] >>
  irule LIST_EQ >> simp[stage_fns_def, EL_MAP] >>
  qx_gen_tac `i` >> strip_tac >> simp[mixed_fns_EL] >>
  `MEM (EL i original.cu_context.ctx_functions).fn_name
       (ctx_fn_names original.cu_context)` by
    (simp[ctx_fn_names_def, MEM_MAP] >>
     qexists_tac `EL i original.cu_context.ctx_functions` >> simp[MEM_EL] >>
     qexists_tac `i` >> simp[]) >>
  qpat_x_assum `!n. MEM n order <=> _` kall_tac >>
  simp[] >> irule chain_facts_last >> metis_tac[]
QED

Theorem chain_facts_length:
  chain_facts rpolicy passes unit order chains i ==>
  LENGTH (FST (EL i chains)) = SUC (LENGTH passes) /\
  LENGTH (SND (EL i chains)) = LENGTH passes
Proof
  simp[chain_facts_def] >> metis_tac[fn_chain_length]
QED

Theorem chain_facts_name:
  chain_facts rpolicy passes unit order chains i /\ k <= LENGTH passes ==>
  (EL k (FST (EL i chains))).fn_name =
    (EL i unit.cu_context.ctx_functions).fn_name
Proof
  simp[chain_facts_def] >> rpt strip_tac >>
  drule fn_chain_names >> drule fn_chain_length >> rpt strip_tac >>
  gvs[EVERY_EL] >> first_x_assum (qspec_then `k` mp_tac) >> simp[]
QED

Theorem chain_facts_shape:
  chain_facts rpolicy passes unit order chains i /\ k <= LENGTH passes ==>
  o1_fn_shape unit.cu_context (EL k (FST (EL i chains)))
Proof
  strip_tac >> drule chain_facts_length >> strip_tac >>
  gvs[chain_facts_def, EVERY_EL] >> first_x_assum irule >> simp[]
QED

Theorem chain_facts_step:
  chain_facts rpolicy passes unit order chains i /\ k < LENGTH passes ==>
  ?s out. fn_pass_step rpolicy (EL k passes) (EL k (SND (EL i chains)))
    s (EL k (FST (EL i chains))) out /\
    out.fpo_function = EL (SUC k) (FST (EL i chains))
Proof
  simp[chain_facts_def] >> metis_tac[fn_chain_step]
QED

Theorem chain_facts_suffix:
  chain_facts rpolicy passes unit order chains i /\ k <= LENGTH passes ==>
  fn_steps rpolicy (DROP k passes) (EL k (FST (EL i chains)))
    (LAST (FST (EL i chains)))
Proof
  simp[chain_facts_def] >> metis_tac[fn_chain_fn_steps]
QED

Theorem chain_facts_invoke_targets:
  chain_facts rpolicy passes unit order chains i /\ k <= LENGTH passes /\
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
  (!i. i < LENGTH chains ==> chain_facts rpolicy passes unit order chains i) /\
  k <= LENGTH passes ==>
  ctx_fn_names (stage_ctx unit.cu_context chains k) = ctx_fn_names unit.cu_context
Proof
  strip_tac >> simp[ctx_fn_names_def, stage_ctx_def] >>
  irule LIST_EQ >> simp[stage_fns_def, EL_MAP] >>
  qx_gen_tac `i` >> strip_tac >> irule chain_facts_name >> metis_tac[]
QED

Theorem stage_ctx_shape:
  LENGTH chains = LENGTH unit.cu_context.ctx_functions /\
  o1_ctx_shape unit.cu_context /\
  (!i. i < LENGTH chains ==> chain_facts rpolicy passes unit order chains i) /\
  k <= LENGTH passes ==>
  o1_ctx_shape (stage_ctx unit.cu_context chains k)
Proof
  strip_tac >>
  `ctx_fn_names (stage_ctx unit.cu_context chains k) =
     ctx_fn_names unit.cu_context` by (irule stage_ctx_names >> metis_tac[]) >>
  irule o1_ctx_shape_transport >>
  qexists_tac `unit.cu_context` >> simp[GSYM stage_ctx_def] >>
  simp[stage_ctx_def] >>
  simp[stage_fns_def, EVERY_MAP, EVERY_EL] >> rpt strip_tac >>
  simp[EL_MAP] >> irule chain_facts_shape >> metis_tac[]
QED

Theorem stage_lookup_index:
  LENGTH chains = LENGTH unit.cu_context.ctx_functions /\
  (!i. i < LENGTH chains ==> chain_facts rpolicy passes unit order chains i) /\
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
  EVERY (o1_step_contract rpolicy) passes /\
  run_named_fn_schedules execute_configured_fn_pass rpolicy passes names
    unit s = SOME (unit', s') /\
  o1_ctx_shape unit.cu_context /\
  ALL_DISTINCT (unit_label_namespace unit) /\
  ALL_DISTINCT names /\
  (!n. MEM n names <=> MEM n (ctx_fn_names unit.cu_context)) ==>
  ?chains.
    LENGTH chains = LENGTH unit.cu_context.ctx_functions /\
    (!i. i < LENGTH chains ==>
         chain_facts rpolicy passes unit names chains i) /\
    unit'.cu_context = stage_ctx unit.cu_context chains (LENGTH passes) /\
    (names <> [] ==> unit_labels_wf unit')
Proof
  strip_tac >>
  `partial_schedule rpolicy passes unit names []
    (MAP (\f. ([f],[])) unit.cu_context.ctx_functions) unit` by
    (irule partial_schedule_initial >> simp[]) >>
  drule_at (Pat `partial_schedule _ _ _ _ _ _ _`) partial_schedule_suffix >>
  disch_then (drule_at (Pat `run_named_fn_schedules _ _ _ _ _ _ = _`)) >>
  simp[] >> disch_then (qx_choose_then `chains` strip_assume_tac) >>
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
  simp[LIST_EQ_REWRITE, EL_MAP] >> rw[] >>
  Cases_on `FST (EL x chains)` >> gvs[] >> metis_tac[]
QED

Theorem chain_facts_stage_shape:
  LENGTH chains = LENGTH unit.cu_context.ctx_functions /\
  o1_ctx_shape unit.cu_context /\
  (!i. i < LENGTH chains ==> chain_facts rpolicy passes unit order chains i) /\
  k <= LENGTH passes ==>
  ctx_fn_names (stage_ctx unit.cu_context chains k) =
    ctx_fn_names unit.cu_context /\
  o1_ctx_shape (stage_ctx unit.cu_context chains k)
Proof
  strip_tac >> conj_tac
  >- (irule stage_ctx_names >> metis_tac[]) >>
  irule stage_ctx_shape >> metis_tac[]
QED

(* Every call goes to a function scheduled earlier. *)
Definition callee_first_def:
  callee_first names fns <=>
    !g callee. MEM g fns /\ MEM callee (fn_invoke_targets g) ==>
      list_precedes callee g.fn_name names
End

Theorem chain_facts_walk_view:
  LENGTH chains = LENGTH unit.cu_context.ctx_functions /\
  o1_ctx_shape unit.cu_context /\
  (!i. i < LENGTH chains ==> chain_facts rpolicy passes unit names chains i) /\
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
     qexistsl_tac [`chains`,`k`,`names`,`passes`,`rpolicy`] >> simp[]) >>
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
  (!i. i < LENGTH chains ==> chain_facts rpolicy passes unit names chains i) /\
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
  `chain_facts rpolicy passes unit names chains i` by simp[] >>
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
  `chain_facts rpolicy passes unit names chains i` by simp[] >>
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

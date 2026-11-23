(* The selected common body occurs in both installed runtime functions. *)
Theory groupedRuntimeBodyCode
Ancestors
  groupedInternalLabels entryCodeOwnership gasShadowRuntimeBodies gasShadowRuntimeOps
  gasShadowModuleDefs gasShadowState gasShadow emitHelperProps moduleLowering compileEnv pair list
  entryRejectCode entryCompileIntervals entryInternalAppend entryPrefixRetention
  entryRawFunction loweringShapeDefs fragExec emitHelper vyperCompiler venomInst
  gasShadowRunLowering gasShadowUnitGuards gasShadowRuntimeDispatch gasShadowUnitExtract
  gasShadowUnit compileVyper bodyFullShadowInternalRun loweringShapeProps vyperLoweringCorrect
  gasShadowRuntimeKwargEnv gasShadowRuntimeRegisterEnv gasShadowCompileStmtBase

val shadow_group = ``\group. case group of
  ExternalSingle selector package =>
    ExternalSingle selector (gas_shadow_external_package package)
| ExternalDefaults common entries specs off =>
    ExternalDefaults (common with <| ec_env := gas_shadow_env T common.ec_env;
                    ec_body := MAP gas_shadow_stmt common.ec_body |>)
      entries (MAP (\(n,ty,e). (n,ty,gas_shadow_expr e)) specs) off``;

val shadow_job = ``\job. case job of
  ExternalLegacyJob package => ExternalLegacyJob (gas_shadow_external_package package)
| ExternalCommonJob common kwvars => ExternalCommonJob
    (common with <| ec_env := gas_shadow_env T common.ec_env;
                    ec_body := MAP gas_shadow_stmt common.ec_body |>)
    (MAP (\(n,p,ty,e). (n,p,ty,gas_shadow_expr e)) kwvars)``;

Theorem grouped_common_job_guarded_code:
  compile_external_jobs (pre ++ ExternalCommonJob common kwvars::post) sd = ((),sj) /\
  compile_external_jobs (MAP ^shadow_job (pre ++ ExternalCommonJob common kwvars::post))
    shadow_sd = ((),shadow_sj) /\
  EVERY group_job_label_ok (pre ++ ExternalCommonJob common kwvars::post) /\
  EVERY group_job_label_ok (MAP ^shadow_job (pre ++ ExternalCommonJob common kwvars::post)) /\
  gas_shadow_state sd shadow_sd /\
  cs_extends sj se /\ cs_extends shadow_sj shadow_se /\
  (!bb. MEM bb (all_blocks se) ==> lookup_block bb.bb_label fn.fn_blocks = SOME bb) /\
  (!bb. MEM bb (all_blocks shadow_se) ==>
     lookup_block bb.bb_label shadow_fn.fn_blocks = SOME bb) ==>
  ?ce job_start entry sa done shadow_entry shadow_sa shadow_done.
    compile_external_jobs pre sd = ((),job_start) /\
    new_block common.ec_common_label job_start = (job_start.cs_current_bb,entry) /\
    cs_extends sd entry /\ cs_extends entry done /\
    entry.cs_current_bb = common.ec_common_label /\ entry.cs_current_insts = [] /\
    compile_register_positional_args
      (compile_register_kwarg_vars common.ec_env kwvars) common.ec_pos_args 4 entry = (ce,sa) /\
    fn_has_code entry sa fn /\
    compile_guarded_body ce common.ec_nonreentrant common.ec_nkey common.ec_transient
      common.ec_view common.ec_body common.ec_return sa = ((),done) /\
    fn_has_code sa done fn /\
    shadow_entry.cs_current_bb = common.ec_common_label /\ shadow_entry.cs_current_insts = [] /\
    compile_register_positional_args
      (gas_shadow_env T (compile_register_kwarg_vars common.ec_env kwvars))
      common.ec_pos_args 4 shadow_entry = (gas_shadow_env T ce,shadow_sa) /\
    fn_has_code shadow_entry shadow_sa shadow_fn /\
    compile_guarded_body (gas_shadow_env T ce) common.ec_nonreentrant
      common.ec_nkey common.ec_transient
      common.ec_view (MAP gas_shadow_stmt common.ec_body) common.ec_return shadow_sa =
      ((),shadow_done) /\
    fn_has_code shadow_sa shadow_done shadow_fn /\
    gas_shadow_state entry shadow_entry /\ gas_shadow_state sa shadow_sa
Proof
  strip_tac >>
  drule_all compile_external_common_job_interval >>
  disch_then (qx_choosel_then [`start`,`entry`,`ce`,`sa`,`done`] strip_assume_tac) >>
  qpat_assum `EVERY group_job_label_ok (MAP _ _)` mp_tac >>
  qpat_assum `compile_external_jobs (MAP _ _) _ = _` mp_tac >>
  simp_tac (srw_ss()) [MAP_APPEND] >>
  rpt strip_tac >>
  drule_at (Pat `compile_external_jobs _ shadow_sd = _`)
    compile_external_common_job_interval >>
  impl_tac >- (asm_simp_tac (srw_ss()) [EVERY_APPEND]) >>
  disch_then (qx_choosel_then
    [`shadow_start`,`shadow_entry`,`shadow_ce`,`shadow_sa`,`shadow_done`] strip_assume_tac) >>
  fs[external_common_accfupds, combinTheory.K_THM,
    gas_shadow_compile_register_kwarg_vars,
    compile_register_kwarg_vars_gas_shadow_env] >>
  `gas_shadow_state start shadow_start` by
    (qspecl_then [`T`,`pre`]
       (drule_then (mp_tac o SPEC_ALL) o Q.SPECL [`sd`,`shadow_sd`] o
        REWRITE_RULE [gas_shadow_compiles_def])
       gas_shadow_compiles_compile_external_jobs >>
     asm_rewrite_tac[SND]) >>
  `gas_shadow_state entry shadow_entry` by
    (qspec_then `common.ec_common_label` mp_tac
       (GEN_ALL gas_shadow_compiles_new_block) >>
     simp_tac (srw_ss()) [gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`start`,`shadow_start`] mp_tac) >>
     asm_rewrite_tac[SND] >> strip_tac >> asm_rewrite_tac[]) >>
  `gas_shadow_env T ce = shadow_ce /\ gas_shadow_state sa shadow_sa` by
    (qspecl_then [`common.ec_pos_args`,
       `compile_register_kwarg_vars common.ec_env kwvars`,`4`]
       (drule_then (mp_tac o SPEC_ALL) o Q.SPECL [`entry`,`shadow_entry`] o
        REWRITE_RULE [gas_shadow_compiles_env_def])
       (Q.INST [`sd` |-> `T`] gas_shadow_compiles_env_register_positional_args) >>
     asm_rewrite_tac[FST,SND]) >>
  qexistsl_tac [`shadow_entry`,`shadow_sa`,`shadow_done`] >>
  `cs_extends sd entry /\ cs_extends entry done` by metis_tac[cs_extends_trans] >>
  fs[] >>
  `entry.cs_current_bb = common.ec_common_label /\ entry.cs_current_insts = [] /\
   shadow_entry.cs_current_bb = common.ec_common_label /\ shadow_entry.cs_current_insts = []` by
    metis_tac[new_block_props] >>
  simp[] >>
  rpt conj_tac >> irule fn_has_code_retained_interval
  >- (simp[] >> qexists_tac `se` >> simp[] >> metis_tac[cs_extends_trans])
  >- (simp[] >> qexists_tac `se` >> simp[] >> metis_tac[cs_extends_trans])
  >- (simp[] >> qexists_tac `shadow_se` >> simp[] >> metis_tac[cs_extends_trans])
  >> simp[] >> qexists_tac `shadow_se` >> simp[] >> metis_tac[cs_extends_trans]
QED

val grouped_shadow_dispatch_statement = ``
  run_grouped_lowering groups ips fb rp "__entry" = SOME unit /\
  EVERY group_entry_labels_ok groups /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ips) /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn ==>
  ?shadow_unit shadow_fn sf fallback jobs sd shd sx shx sn shn se she.
    run_grouped_lowering (MAP ^shadow_group groups) (MAP gas_shadow_internal_package ips)
      (OPTION_MAP gas_shadow_fallback_package fb) rp "__entry" = SOME shadow_unit /\
    gas_shadow_unit unit shadow_unit /\
    lookup_function "__entry" shadow_unit.cu_context.ctx_functions = SOME shadow_fn /\
    gas_shadow_function fn shadow_fn /\
    fresh_label "fallback" (initial_compile_state "__entry") = (fallback,sf) /\
    sf.cs_current_bb = "__entry" /\ sf.cs_current_insts = [] /\
    sf.cs_next_var = 0 /\ sf.cs_next_id = 0 /\
    compile_group_dispatch_linear groups fallback sf = (jobs,sd) /\
    fn_has_code sf sd fn /\
    compile_group_dispatch_linear (MAP ^shadow_group groups) fallback sf =
      (MAP ^shadow_job jobs,shd) /\ fn_has_code sf shd shadow_fn /\
    gas_shadow_state sd shd /\
    compile_external_jobs jobs sd = ((),sx) /\
    compile_external_jobs (MAP ^shadow_job jobs) shd = ((),shx) /\
    EVERY group_job_label_ok jobs /\ EVERY group_job_label_ok (MAP ^shadow_job jobs) /\
    cs_extends sx se /\ cs_extends shx she /\
    (!bb. MEM bb (all_blocks se) ==> lookup_block bb.bb_label fn.fn_blocks = SOME bb) /\
    (!bb. MEM bb (all_blocks she) ==>
      lookup_block bb.bb_label shadow_fn.fn_blocks = SOME bb) /\
    new_block fallback sx = (sx.cs_current_bb,sn) /\
    sn.cs_current_bb = fallback /\ sn.cs_current_insts = [] /\
    (case fb of
       NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
     | SOME (ce,pay,nr,key,tr,view,stmts,rt) =>
         compile_fallback_body ce pay nr key tr view stmts rt) sn = ((),se) /\
    fn_has_code sn se fn /\
    new_block fallback shx = (shx.cs_current_bb,shn) /\
    shn.cs_current_bb = fallback /\ shn.cs_current_insts = [] /\
    (case OPTION_MAP gas_shadow_fallback_package fb of
       NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
     | SOME (ce,pay,nr,key,tr,view,stmts,rt) =>
         compile_fallback_body ce pay nr key tr view stmts rt) shn = ((),she) /\
    fn_has_code shn she shadow_fn /\ gas_shadow_state sn shn``;

val (grouped_shadow_dispatch_input, grouped_shadow_dispatch_output) =
  boolSyntax.dest_imp grouped_shadow_dispatch_statement;
val (grouped_shadow_dispatch_witnesses, grouped_shadow_dispatch_facts) =
  boolSyntax.strip_exists grouped_shadow_dispatch_output;
val grouped_shadow_dispatch_end =
  valOf (List.find (fn v => fst (dest_var v) = "se") grouped_shadow_dispatch_witnesses);
val grouped_shadow_dispatch_retained = boolSyntax.list_mk_exists
  (grouped_shadow_dispatch_witnesses,
   ``^grouped_shadow_dispatch_facts /\
     cs_extends ^(valOf (List.find (fn v => fst (dest_var v) = "sd")
       grouped_shadow_dispatch_witnesses)) ^grouped_shadow_dispatch_end /\
     ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks ^grouped_shadow_dispatch_end))``);

Theorem grouped_shadow_entry_dispatch_with_layout:
  ^grouped_shadow_dispatch_input ==> ^grouped_shadow_dispatch_retained
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qspecl_then [`groups`,`ips`,`fb`,`rp`,`"__entry"`] mp_tac
    gas_shadow_run_grouped_lowering >>
  asm_rewrite_tac[] >>
  Cases_on `run_grouped_lowering (MAP ^shadow_group groups)
    (MAP gas_shadow_internal_package ips)
    (OPTION_MAP gas_shadow_fallback_package fb) rp "__entry"` >>
  simp[optionTheory.OPTREL_def] >> strip_tac >>
  rename1 `gas_shadow_unit unit shadow_unit` >>
  `OPTREL gas_shadow_function (SOME fn)
      (lookup_function "__entry" shadow_unit.cu_context.ctx_functions)` by
    (qpat_assum `lookup_function "__entry" _ = SOME fn` (SUBST1_TAC o SYM) >>
     irule gas_shadow_lookup_function >> fs[gas_shadow_unit_def, gas_shadow_context_def]) >>
  Cases_on `lookup_function "__entry" shadow_unit.cu_context.ctx_functions` >>
  fs[optionTheory.OPTREL_def] >> rename1 `gas_shadow_function fn shadow_fn` >>
  `EVERY group_entry_labels_ok (MAP ^shadow_group groups)` by
    (fs[EVERY_MAP, EVERY_MEM] >> gen_tac >> strip_tac >>
     qpat_assum `!e. MEM e groups ==> _` (drule_then mp_tac) >>
     Cases_on `group`
     >- (rename1 `ExternalSingle _ pkg` >> PairCases_on `pkg` >>
         simp[group_entry_labels_ok_def, gas_shadow_external_package_def]) >>
     simp[group_entry_labels_ok_def]) >>
  mp_tac (Q.INST [`groups` |-> `groups`, `ips` |-> `ips`, `fb` |-> `fb`,
    `rp` |-> `rp`, `unit` |-> `unit`, `fn` |-> `fn`]
    (SPEC_ALL run_grouped_lowering_dispatch_code)) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`sf`,`fallback`,`jobs`,`sd`,`sx`,`sn`,`se`]
    (map_every assume_tac o CONJUNCTS)) >>
  mp_tac (Q.INST [`groups` |-> `MAP ^shadow_group groups`,
    `ips` |-> `MAP gas_shadow_internal_package ips`,
    `fb` |-> `OPTION_MAP gas_shadow_fallback_package fb`,
    `rp` |-> `rp`, `unit` |-> `shadow_unit`, `fn` |-> `shadow_fn`]
    (SPEC_ALL run_grouped_lowering_dispatch_code)) >>
  impl_tac >- asm_rewrite_tac[gas_shadow_internal_fn_descriptors] >>
  disch_then (qx_choosel_then [`ssf`,`sfb`,`shjobs`,`shd`,`shx`,`shn`,`she`]
    (map_every assume_tac o CONJUNCTS)) >>
  `ssf = sf /\ sfb = fallback` by metis_tac[pairTheory.PAIR_EQ] >>
  qpat_x_assum `ssf = sf` SUBST_ALL_TAC >>
  qpat_x_assum `sfb = fallback` SUBST_ALL_TAC >>
  `gas_shadow_state sf sf` by simp[gas_shadow_state_refl] >>
  `shjobs = MAP ^shadow_job jobs /\ gas_shadow_state sd shd` by
    (drule_then (mp_tac o SPEC_ALL)
      (Q.SPECL [`groups`,`fallback`,`sf`,`sf`]
        (Q.SPEC `gasShadowModuleDefs$gas_shadow_external_package`
          (GEN_ALL (Q.INST [`sd` |-> `T`] gas_shadow_compile_group_dispatch_linear)))) >>
     asm_rewrite_tac[FST,SND]) >>
  pop_assum strip_assume_tac >>
  `gas_shadow_state sx shx` by
    (qspecl_then [`T`,`jobs`]
       (drule_then (mp_tac o SPEC_ALL) o Q.SPECL [`sd`,`shd`] o
        REWRITE_RULE [gas_shadow_compiles_def])
       gas_shadow_compiles_compile_external_jobs >>
     fs[pairTheory.SND]) >>
  `gas_shadow_state sn shn` by
    (qspec_then `fallback` mp_tac (GEN_ALL gas_shadow_compiles_new_block) >>
     simp_tac bool_ss [gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sx`,`shx`] mp_tac) >>
     asm_rewrite_tac[SND] >> simp[]) >>
  qpat_x_assum `shjobs = MAP _ jobs` SUBST_ALL_TAC >>
  qexistsl_tac [`sf`,`jobs`,`sd`,`shd`,`sx`,`shx`,`sn`,`shn`,`se`,`she`] >>
  qpat_assum `sn.cs_current_bb = fallback` SUBST1_TAC >>
  simp[]
QED

Theorem grouped_shadow_entry_dispatch:
  ^grouped_shadow_dispatch_statement
Proof
  disch_then (mp_tac o MATCH_MP grouped_shadow_entry_dispatch_with_layout) >>
  disch_then (qx_choosel_then [`shu`,`shfn`,`sf`,`fl`,`jobs`,`sd`,`shd`,
    `sx`,`shx`,`sn`,`shn`,`se`,`she`] strip_assume_tac) >>
  qexistsl_tac [`shu`,`shfn`,`sf`,`fl`,`jobs`,`sd`,`shd`,`sx`,`shx`,`sn`,`shn`,`se`,`she`] >>
  asm_rewrite_tac[]
QED

Theorem cs_appends_grouped_jobs[local]:
  !jobs. cs_appends (compile_external_jobs jobs)
Proof
  Induct >> simp[compile_external_jobs_def, cs_appends_return] >>
  Cases_on `h` >> simp[compile_external_jobs_def] >>
  irule cs_appends_ignore_bind >> simp[cs_appends_external_fn_bodies, cs_appends_prims] >>
  irule cs_appends_ignore_bind >> simp[compile_common_function_body_def] >>
  irule cs_appends_bind >> simp[cs_appends_register_positional_args, cs_appends_guarded_body]
QED

val grouped_legacy_job_statement = ``
  compile_external_jobs
    (pre ++ ExternalLegacyJob (lbl,ce,pa,mc,pay,nr,key,ut,view,ss,rt)::post)
    sd = ((),sj) /\
  cs_extends sj se /\
  (!bb. MEM bb (all_blocks se) ==> lookup_block bb.bb_label fn.fn_blocks = SOME bb) ==>
  ?job_start checks register body_start done cenv.
    compile_external_jobs pre sd = ((),job_start) /\
    new_block lbl job_start = (job_start.cs_current_bb,checks) /\
    checks.cs_current_bb = lbl /\ checks.cs_current_insts = [] /\
    compile_entry_checks mc pay checks = ((),register) /\
    fn_has_code checks register fn /\
    compile_register_positional_args ce pa 4 register = (cenv,body_start) /\
    fn_has_code register body_start fn /\
    compile_guarded_body cenv nr key ut view ss rt body_start = ((),done) /\
    fn_has_code body_start done fn /\ cs_extends sd checks``;

val (grouped_legacy_job_input, grouped_legacy_job_output) =
  boolSyntax.dest_imp grouped_legacy_job_statement;
val (grouped_legacy_job_witnesses, grouped_legacy_job_facts) =
  boolSyntax.strip_exists grouped_legacy_job_output;
val grouped_legacy_job_end =
  valOf (List.find (fn v => fst (dest_var v) = "done") grouped_legacy_job_witnesses);
val grouped_legacy_job_retained = boolSyntax.list_mk_exists
  (grouped_legacy_job_witnesses, ``^grouped_legacy_job_facts /\ cs_extends ^grouped_legacy_job_end se``);

Theorem grouped_legacy_job_code_with_end:
  ^grouped_legacy_job_input ==> ^grouped_legacy_job_retained
Proof
  strip_tac >>
  Cases_on `compile_external_jobs pre sd` >>
  Cases_on `q` >>
  qpat_x_assum `compile_external_jobs (_ ++ _) _ = _` mp_tac >>
  simp[compile_external_jobs_append, compile_external_jobs_def, comp_ignore_bind_def,
    comp_bind_def] >> rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rename1 `compile_external_fn_bodies [_] r = ((),job_end)` >>
  rename1 `compile_external_jobs pre _ = ((),r)` >>
  rename1 `cs_extends sj runtime_end` >>
  rename1 `compile_external_jobs pre dispatch_end = ((),r)` >>
  `cs_extends dispatch_end r /\ cs_extends job_end sj` by
    metis_tac[cs_appends_def, cs_appends_grouped_jobs] >>
  mp_tac (Q.SPECL [`[(lbl,ce,pa,mc,pay,nr,key,ut,view,ss,rt)]`, `r`, `job_end`]
    (Q.INST [`tr` |-> `ut`, `stmts` |-> `ss`] external_fn_selected_check_intervals)) >>
  simp[] >>
  disch_then (qx_choosel_then
    [`check_state`,`reg_state`,`local_env`,`start_state`,`done_state`] strip_assume_tac) >>
  `cs_extends reg_state start_state` by
    metis_tac[cs_appends_def, cs_appends_register_positional_args] >>
  `cs_extends job_end runtime_end` by metis_tac[cs_extends_trans] >>
  `cs_extends done_state runtime_end` by metis_tac[cs_extends_trans] >>
  `cs_extends dispatch_end check_state` by metis_tac[cs_extends_trans] >>
  `new_block lbl r = (r.cs_current_bb,check_state)` by
    (rename1 `[_] = earlier ++ [_] ++ later` >>
     Cases_on `earlier` >> gvs[compile_external_fn_bodies_def, comp_return_def]) >>
  qexistsl_tac [`check_state`,`reg_state`,`start_state`,`done_state`,`local_env`] >>
  asm_rewrite_tac[] >>
  rpt conj_tac >>
  irule fn_has_code_retained_interval >> asm_rewrite_tac[] >>
  qexists_tac `runtime_end` >> asm_rewrite_tac[] >>
  metis_tac[cs_extends_trans]
QED

Theorem grouped_legacy_job_code:
  ^grouped_legacy_job_statement
Proof
  disch_then (mp_tac o MATCH_MP grouped_legacy_job_code_with_end) >>
  disch_then (qx_choosel_then [`start`,`checks`,`reg`,`sa`,`done`,`cf`] strip_assume_tac) >>
  qexistsl_tac [`start`,`checks`,`reg`,`sa`,`done`,`cf`] >> asm_rewrite_tac[]
QED

Theorem grouped_fallback_guarded_code:
  compile_fallback_body ce pay nr key ut view ss rt checks = ((),done) /\
  fn_has_code checks done fn ==>
  ?body_start.
    compile_entry_checks 4 pay checks = ((),body_start) /\
    compile_guarded_body ce nr key ut view ss rt body_start = ((),done) /\
    fn_has_code checks body_start fn /\ fn_has_code body_start done fn
Proof
  strip_tac >>
  Cases_on `compile_entry_checks 4 pay checks` >>
  rename1 `compile_entry_checks 4 pay checks = (result,body_start)` >>
  Cases_on `result` >>
  `compile_guarded_body ce nr key ut view ss rt body_start = ((),done)` by
    (qpat_x_assum `compile_fallback_body _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     qpat_assum `compile_entry_checks _ _ _ = _` mp_tac >>
     simp[compile_fallback_body_def, compile_entry_checks_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def, ELIM_UNCURRY] >>
     rpt strip_tac >> gvs[compile_entry_checks_def, comp_bind_def,
                          comp_ignore_bind_def, comp_return_def, ELIM_UNCURRY]) >>
  qexists_tac `body_start` >> asm_rewrite_tac[] >>
  imp_res_tac (SRULE [cs_appends_def] cs_appends_entry_checks) >>
  imp_res_tac (SRULE [cs_appends_def] cs_appends_guarded_body) >>
  metis_tac[fn_has_code_split]
QED

Theorem lower_grouped_runtime_pair:
  lower_vyper_runtime_unit tops rp = SOME unit /\
  classify_functions tops = (exts,ints,fb,ctor) /\
  EXISTS external_has_defaults exts ==>
  ?groups ips fall shadow_unit fn bb.
    groups = MAP
      (package_external_group tops rp.rpol_target T (K global_nonreentrant_slot)) exts /\
    ips = MAP (set_internal_package_target rp.rpol_target o
      package_internal_fn tops T (K global_nonreentrant_slot) F 0)
      (order_internals (runtime_internal_order tops ints) ints) /\
    fall = set_fallback_package_target rp.rpol_target
      (package_fallback_fn tops T (K global_nonreentrant_slot) fb) /\
    run_grouped_lowering groups ips fall rp "__entry" = SOME unit /\
    run_grouped_lowering (MAP ^shadow_group groups) (MAP gas_shadow_internal_package ips)
      (OPTION_MAP gas_shadow_fallback_package fall) rp "__entry" = SOME shadow_unit /\
    EVERY group_entry_labels_ok groups /\
    EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ips) /\
    runtime_gas_shadow_unit tops rp = SOME shadow_unit /\
    gas_shadow_unit unit shadow_unit /\
    unit.cu_context.ctx_entry = SOME "__entry" /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME "__entry" /\
    lookup_block "__entry" fn.fn_blocks = SOME bb
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all runtime_gas_shadow_unit_exists >>
  disch_then (qx_choose_then `shadow_unit` (map_every assume_tac o CONJUNCTS)) >>
  drule lower_vyper_runtime_unit_context_entry >>
  disch_then strip_assume_tac >>
  rename1 `lookup_function "__entry" _ = SOME fn` >>
  `fn_entry_label fn = SOME "__entry"` by
    (drule_all_then ACCEPT_TAC lower_vyper_runtime_unit_entry_label) >>
  `?bb. lookup_block "__entry" fn.fn_blocks = SOME bb` by
    (Cases_on `fn.fn_blocks` >>
     fs[fn_entry_label_def, entry_block_def, lookup_block_def, FIND_thm]) >>
  pop_assum strip_assume_tac >>
  qpat_assum `lower_vyper_runtime_unit _ _ = _`
    (mp_tac o REWRITE_RULE [lower_vyper_runtime_unit_def]) >>
  simp[LET_THM, AllCaseEqs()] >> strip_tac >>
  simp[EVERY_MAP, package_external_group_labels, package_internal_labels] >>
  qpat_assum `runtime_gas_shadow_unit tops rp = SOME shadow_unit`
    (mp_tac o REWRITE_RULE [runtime_gas_shadow_unit_def]) >>
  simp[LET_THM]
QED

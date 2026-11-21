(* The selected common body occurs in both installed runtime functions. *)
Theory groupedRuntimeBodyCode
Ancestors
  groupedInternalLabels entryCodeOwnership gasShadowRuntimeBodies gasShadowRuntimeOps
  gasShadowModuleDefs gasShadowState emitHelperProps moduleLowering compileEnv pair list
  entryRejectCode entryCompileIntervals entryInternalAppend entryPrefixRetention
  entryRawFunction loweringShapeDefs fragExec emitHelper vyperCompiler venomInst

val shadow_job = ``\job. case job of
  ExternalLegacyJob package => ExternalLegacyJob (gas_shadow_external_package package)
| ExternalCommonJob common kwvars => ExternalCommonJob
    (common with ec_body := MAP gas_shadow_stmt common.ec_body)
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
  ?ce entry sa done shadow_entry shadow_sa shadow_done.
    entry.cs_current_bb = common.ec_common_label /\ entry.cs_current_insts = [] /\
    compile_register_positional_args
      (compile_register_kwarg_vars common.ec_env kwvars) common.ec_pos_args 4 entry = (ce,sa) /\
    fn_has_code entry sa fn /\
    compile_guarded_body ce common.ec_nonreentrant common.ec_nkey common.ec_transient
      common.ec_view common.ec_body common.ec_return sa = ((),done) /\
    fn_has_code sa done fn /\
    shadow_entry.cs_current_bb = common.ec_common_label /\ shadow_entry.cs_current_insts = [] /\
    compile_register_positional_args
      (compile_register_kwarg_vars common.ec_env kwvars) common.ec_pos_args 4 shadow_entry =
      (ce,shadow_sa) /\
    fn_has_code shadow_entry shadow_sa shadow_fn /\
    compile_guarded_body ce common.ec_nonreentrant common.ec_nkey common.ec_transient
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
    gas_shadow_compile_register_kwarg_vars] >>
  `gas_shadow_state start shadow_start` by
    (qspec_then `pre` mp_tac gas_shadow_compiles_compile_external_jobs >>
     simp_tac (srw_ss()) [gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sd`,`shadow_sd`] mp_tac) >>
     asm_rewrite_tac[SND]) >>
  `gas_shadow_state entry shadow_entry` by
    (qspec_then `common.ec_common_label` mp_tac
       (GEN_ALL gas_shadow_compiles_new_block) >>
     simp_tac (srw_ss()) [gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`start`,`shadow_start`] mp_tac) >>
     asm_rewrite_tac[SND] >> strip_tac >> asm_rewrite_tac[]) >>
  `ce = shadow_ce /\ gas_shadow_state sa shadow_sa` by
    (mp_tac (Q.SPECL [`common.ec_pos_args`,
       `compile_register_kwarg_vars common.ec_env
          (kwvars : (string # operand # type # expr) list)`,`4`]
       gas_shadow_compiles_compile_register_positional_args) >>
     simp_tac bool_ss [gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`entry`,`shadow_entry`] mp_tac) >>
     asm_rewrite_tac[FST,SND] >> strip_tac >> simp[]) >>
  qexistsl_tac [`ce`,`entry`,`sa`,`done`,`shadow_entry`,`shadow_sa`,`shadow_done`] >>
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

Theorem run_grouped_lowering_dispatch_code:
  run_grouped_lowering groups ips fb rp "__entry" = SOME unit /\
  EVERY group_entry_labels_ok groups /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ips) /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn ==>
  ?sf fallback jobs sd sx sn se.
    sf.cs_current_bb = "__entry" /\ sf.cs_current_insts = [] /\
    sf.cs_next_var = 0 /\ sf.cs_next_id = 0 /\
    compile_group_dispatch_linear groups fallback sf = (jobs,sd) /\
    fn_has_code sf sd fn /\
    compile_external_jobs jobs sd = ((),sx) /\
    new_block fallback sx = (sx.cs_current_bb,sn) /\
    sn.cs_current_bb = fallback /\ sn.cs_current_insts = [] /\
    (case fb of
       NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
     | SOME (ce,pay,nr,key,tr,view,stmts,rt) =>
         compile_fallback_body ce pay nr key tr view stmts rt) sn = ((),se) /\
    fn_has_code sn se fn /\
    EVERY group_job_label_ok jobs /\ cs_extends sx se /\
    (!bb. MEM bb (all_blocks se) ==>
       lookup_block bb.bb_label fn.fn_blocks = SOME bb)
Proof
  strip_tac >> drule_all run_grouped_lowering_retained_entry >> strip_tac >>
  drule_all compile_grouped_runtime_entry_layout >> strip_tac >>
  `fn_has_code sf sd fn` by metis_tac[fn_has_code_retained_interval, cs_extends_trans] >>
  `fn_has_code sn se fn` by metis_tac[fn_has_code_endpoint_coverage] >>
  qexistsl_tac [`sf`,`fl`,`jobs`,`sd`,`sx`,`sn`,`se`] >>
  asm_rewrite_tac[] >>
  qpat_x_assum `fresh_label _ _ = _` mp_tac >>
  simp[fresh_label_def, initial_compile_state_def] >>
  metis_tac[new_block_props]
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

Theorem grouped_legacy_job_code:
  compile_external_jobs
    (pre ++ ExternalLegacyJob (lbl,ce,pa,mc,pay,nr,key,ut,view,ss,rt)::post)
    sd = ((),sj) /\
  cs_extends sj se /\
  (!bb. MEM bb (all_blocks se) ==> lookup_block bb.bb_label fn.fn_blocks = SOME bb) ==>
  ?checks register body_start done cenv.
    checks.cs_current_bb = lbl /\ checks.cs_current_insts = [] /\
    compile_entry_checks mc pay checks = ((),register) /\
    fn_has_code checks register fn /\
    compile_register_positional_args ce pa 4 register = (cenv,body_start) /\
    fn_has_code register body_start fn /\
    compile_guarded_body cenv nr key ut view ss rt body_start = ((),done) /\
    fn_has_code body_start done fn /\ cs_extends sd checks
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
  `cs_extends dispatch_end check_state` by metis_tac[cs_extends_trans] >>
  qexistsl_tac [`check_state`,`reg_state`,`start_state`,`done_state`,`local_env`] >>
  asm_rewrite_tac[] >>
  rpt conj_tac >>
  irule fn_has_code_retained_interval >> asm_rewrite_tac[] >>
  qexists_tac `runtime_end` >> asm_rewrite_tac[] >>
  metis_tac[cs_extends_trans]
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

Theorem grouped_runtime_entry_compile_labels:
  run_grouped_lowering groups ips fb rp "__entry" = SOME unit /\
  EVERY group_entry_labels_ok groups /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ips) /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
  compile_generate_grouped_runtime groups [] fb
    (initial_compile_state "__entry") = ((),se) ==>
  ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks se))
Proof
  strip_tac >> drule_all grouped_internal_run_labels >>
  disch_then (qx_choosel_then [`start`,`final`,`data`] strip_assume_tac) >> gvs[] >>
  drule lowering_context_ok_bridge >> strip_tac >>
  `MEM fn unit.cu_context.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    (fs[EVERY_MEM, fn_labels_def] >> metis_tac[]) >>
  qpat_assum `extract_context_with_internals _ _ _ = _`
    (mp_tac o REWRITE_RULE [extract_context_with_internals_def]) >>
  simp[AllCaseEqs(), GSYM all_blocks_def] >> strip_tac >>
  qpat_x_assum `v = (entry_blocks,functions)` SUBST_ALL_TAC >>
  `?tail. all_blocks final = all_blocks se ++ tail` by
    (Cases_on `ips = []` >- fs[compile_internal_fn_bodies_def, comp_return_def] >>
     metis_tac[internal_fn_bodies_retains_prefix]) >>
  `!d. MEM d (internal_fn_descriptors ips) ==>
    ~MEM (FST d) (MAP (\bb. bb.bb_label) (all_blocks se))` by
    (simp[MEM_MAP] >> fs[EVERY_MEM] >> metis_tac[]) >>
  `fn.fn_blocks = entry_blocks` by (drule_all extracted_entry_blocks >> simp[]) >>
  `?rest. entry_blocks = all_blocks se ++ rest` by
    metis_tac[package_internal_blocks_prefix] >>
  gvs[MAP_APPEND, ALL_DISTINCT_APPEND]
QED

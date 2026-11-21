(* The selected common body occurs in both installed runtime functions. *)
Theory groupedRuntimeBodyCode
Ancestors
  groupedInternalLabels entryCodeOwnership gasShadowRuntimeBodies gasShadowRuntimeOps
  gasShadowModuleDefs gasShadowState emitHelperProps moduleLowering compileEnv pair list

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

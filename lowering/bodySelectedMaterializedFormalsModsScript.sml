Theory bodySelectedMaterializedFormalsMods
Ancestors
  bodySimEntry intCallCallee compileUnit compileVyper compileEnv emitHelper
  constSubstMods context list pair finite_map

Theorem selected_unit_env_formal_domain[local]:
  FLOOKUP (build_compile_env_unit mods src vis mut name args ret ss ut).ce_vars id = SOME loc ==>
  MEM id (MAP FST args)
Proof
  simp[build_compile_env_unit_def, ELIM_UNCURRY] >>
  qmatch_goalsub_abbrev_tac `FST (allocate_args sft args 0 FEMPTY)` >>
  strip_tac >> CCONTR_TAC >>
  Cases_on `allocate_args sft args 0 FEMPTY` >> gvs[] >>
  drule_all allocate_args_FLOOKUP_other >> simp[]
QED

Theorem selected_package_formal_domain:
  set_internal_package_target target
    (package_internal_fn_unit mods T (K global_nonreentrant_slot) deploy ilen
      (src,subst_consts_fn_mods (consts_env_mods mods)
        (mut,nr,rr,name,args,dflts,ret,ss))) =
    (label,ce,params,has_rb,nr',key,trans,view,ctor,ilen',ss_comp,rt) ==>
  MAP FST params = MAP FST args /\
  (!id loc. FLOOKUP ce.ce_vars id = SOME loc ==> MEM id (MAP FST args))
Proof
  simp[subst_consts_fn_mods_def, package_internal_fn_unit_def,
       set_internal_package_target_def, update_cenv_nonreentrant_def] >>
  strip_tac >> gvs[] >>
  simp[MAP_ZIP, LENGTH_compute_pass_via_stack] >>
  rpt strip_tac >> drule selected_unit_env_formal_domain >> simp[]
QED

Theorem selected_prefix_formal_names[local]:
  compile_internal_entry_prefix ce params has_rb entry = ((ce1,caps,rpc),capture) ==>
  MAP FST caps = MAP FST params
Proof
  Cases_on `has_rb` >>
  simp[compile_internal_entry_prefix_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rename1 `compile_internal_param_decls _ _ _ = (pr,mid)` >> PairCases_on `pr` >>
  gvs[] >> drule internal_param_decls_projection >> simp[]
QED

Theorem selected_materialized_formal_domain_mods:
  set_internal_package_target target
    (package_internal_fn_unit mods T (K global_nonreentrant_slot) deploy ilen
      (src,subst_consts_fn_mods (consts_env_mods mods)
        (mut,nr,rr,name,args,dflts,ret,ss))) =
    (label,ce,params,has_rb,nr',key,trans,view,ctor,ilen',ss_comp,rt) /\
  compile_internal_entry_prefix ce params has_rb entry = ((ce1,caps,rpc),capture) /\
  materialize_internal_params ce1 caps reserved = (ce2,materialized) /\
  body_ce = ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|> ==>
  !id loc. FLOOKUP body_ce.ce_vars id = SOME loc ==> MEM id (MAP FST args)
Proof
  strip_tac >>
  drule_then strip_assume_tac selected_package_formal_domain >>
  drule_then assume_tac selected_prefix_formal_names >>
  drule_then assume_tac (cj 4 compile_internal_entry_prefix_shape) >>
  simp[] >> rpt strip_tac >>
  drule_all materialize_internal_params_bound >> simp[] >>
  metis_tac[]
QED

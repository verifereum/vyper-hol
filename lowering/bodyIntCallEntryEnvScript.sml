(* Compiler projections used at internal function entry. *)
Theory bodyIntCallEntryEnv
Ancestors
  compileVyper compileEnv moduleLowering supportedStmtTraverse supportedNames
  supportedProgram intCallCallee list alist

Theorem internal_param_type_lookup:
  ALL_DISTINCT (MAP FST args) /\
  (!n ty. MEM (n,ty) args ==> ~MEM n (MAP FST (collect_locals ss))) /\
  MEM (n,ty) args ==>
  ALOOKUP (REVERSE (args ++ collect_locals ss)) n = SOME ty
Proof
  strip_tac >>
  simp[REVERSE_APPEND, ALOOKUP_APPEND] >>
  `ALOOKUP (REVERSE (collect_locals ss)) n = NONE` by
    (simp[ALOOKUP_NONE, MAP_REVERSE] >> metis_tac[]) >>
  simp[] >> irule ALOOKUP_ALL_DISTINCT_MEM >>
  simp[MAP_REVERSE, ALL_DISTINCT_REVERSE]
QED

Theorem build_internal_env_param_type:
  ALL_DISTINCT (MAP FST args) /\
  (!n ty. MEM (n,ty) args ==> ~MEM n (MAP FST (collect_locals ss))) /\
  MEM (n,ty) args ==>
  (build_compile_env tops Internal mut name args ret ss use_trans).ce_var_type n =
    SOME ty
Proof
  strip_tac >> simp[build_compile_env_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  irule internal_param_type_lookup >> metis_tac[]
QED

Theorem collect_locals_supported_bindings:
  !ss. MEM p (collect_locals ss) <=>
       MEM p (supported_stmts_bindings T ss) \/
       MEM p (supported_stmts_bindings F ss)
Proof
  recInduct collect_locals_ind >>
  simp[collect_locals_def, supported_stmt_bindings_def] >> metis_tac[]
QED

Theorem supported_body_param_separation:
  supported_function_body tops vis args ss ==>
  ALL_DISTINCT (MAP FST args) /\
  (!n ty. MEM (n,ty) args ==> ~MEM n (MAP FST (collect_locals ss)))
Proof
  simp[supported_function_body_def, supported_function_bindings_def,
       ALL_DISTINCT_APPEND] >> rpt strip_tac >>
  gvs[MEM_MAP] >>
  drule (iffLR collect_locals_supported_bindings) >> strip_tac >>
  metis_tac[MEM_MAP, pairTheory.FST]
QED

Theorem supported_build_internal_env_param_type:
  supported_function_body tops vis args ss /\ MEM (n,ty) args ==>
  (build_compile_env tops Internal mut name args ret ss use_trans).ce_var_type n =
    SOME ty
Proof
  strip_tac >> drule supported_body_param_separation >> strip_tac >>
  irule build_internal_env_param_type >> metis_tac[]
QED

Theorem materialize_internal_params_fields:
  !params cenv st cenv' st'.
    materialize_internal_params cenv params st = (cenv',st') ==>
    cenv' with ce_vars := cenv.ce_vars = cenv
Proof
  Induct >- simp[materialize_internal_params_def, comp_return_def] >>
  PairCases >> rpt gen_tac >> simp[Once materialize_internal_params_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >>
  simp[comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  first_x_assum drule >>
  simp[compile_env_component_equality] >> metis_tac[]
QED

Theorem compile_internal_prologue_fields:
  compile_internal_prologue cenv params has_rb ret st = ((cenv',pc),st') ==>
  cenv' with <| ce_vars := cenv.ce_vars;
                ce_return_buf := cenv.ce_return_buf;
                ce_return_pc := cenv.ce_return_pc |> = cenv
Proof
  simp[compile_internal_prologue_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  drule materialize_internal_params_fields >>
  simp[compile_env_component_equality]
QED

Theorem compile_internal_prologue_param_type:
  supported_function_body tops vis args ss /\ MEM (n,ty) args /\
  compile_internal_prologue
    (build_compile_env tops Internal mut name args ret ss use_trans)
    params has_rb ret_type st = ((cenv',pc),st') ==>
  cenv'.ce_var_type n = SOME ty
Proof
  strip_tac >> drule compile_internal_prologue_fields >>
  simp[compile_env_component_equality] >> strip_tac >>
  irule supported_build_internal_env_param_type >> metis_tac[]
QED

Theorem runtime_internal_prologue_param_type:
  supported_function_body tops Internal args ss /\ MEM (n,ty) args /\
  set_internal_package_target target
    (package_internal_fn tops use_trans nkeys F 0
      (mut,nr,rr,name,args,dflts,ret,ss)) =
    (lbl,ce,params,has_rb,is_nr,key,trans,view,ctor,imm_len,ss',rt) /\
  compile_internal_prologue ce params has_rb rt st = ((cenv',pc),st') ==>
  cenv'.ce_var_type n = SOME ty
Proof
  strip_tac >> drule compile_internal_prologue_fields >>
  simp[compile_env_component_equality] >> strip_tac >>
  gvs[package_internal_fn_def, set_internal_package_target_def,
      update_cenv_nonreentrant_def] >>
  irule supported_build_internal_env_param_type >> metis_tac[]
QED

Theorem runtime_internal_package_fields:
  set_internal_package_target target
    (package_internal_fn tops use_trans nkeys F 0
      (mut,nr,rr,name,args,dflts,ret,ss)) =
    (lbl,ce,params,has_rb,is_nr,key,trans,view,ctor,imm_len,ss',rt) ==>
  let base = build_compile_env tops Internal mut name args ret ss use_trans in
  ce with <| ce_target := base.ce_target; ce_is_ctor := base.ce_is_ctor;
             ce_raw_return := base.ce_raw_return;
             ce_nonreentrant := base.ce_nonreentrant |> = base
Proof
  simp[package_internal_fn_def, set_internal_package_target_def,
       update_cenv_nonreentrant_def] >> strip_tac >> gvs[] >>
  simp[compile_env_component_equality]
QED

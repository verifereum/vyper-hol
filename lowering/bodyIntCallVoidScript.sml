(* Compiler boundaries for supported void bodies. *)
Theory bodyIntCallVoid
Ancestors
  supportedStmts supportedDecls bodyAppendStorageFacts compileVyper
  stmtLowering compileEnv context finite_map list

Theorem supported_variable_decl_type_map:
  !tops src id vis mut ty slot.
    supported_variable_decl tops (src,id) = SOME (vis,mut,ty,slot) ==>
    src = NONE /\ build_var_type_map tops (src,id) = SOME ty
Proof
  Induct >> simp[supported_variable_decl_def] >> Cases >>
  simp[supported_variable_decl_def, build_var_type_map_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem supported_append_root_array:
  supported_append_target tops target /\
  (!id. cenv.ce_module_var_type (NONE,id) = build_var_type_map tops (NONE,id)) ==>
  ?elem n. target_root_type cenv target = SOME (ArrayT elem (Dynamic n))
Proof
  Cases_on `target` >> simp[supported_append_target_def] >> strip_tac >>
  rename1 `supported_storage_dynamic_array tops nid` >>
  PairCases_on `nid` >>
  drule supported_append_storage_decl >> strip_tac >>
  drule supported_variable_decl_type_map >> strip_tac >>
  gvs[target_root_type_def] >> metis_tac[]
QED

Theorem supported_append_compile_type_independent:
  supported_append_target tops target /\
  (!id. cenv.ce_module_var_type (NONE,id) = build_var_type_map tops (NONE,id)) ==>
  compile_stmt cenv lctx ty (Append target e) =
  compile_stmt cenv lctx ty' (Append target e)
Proof
  strip_tac >> drule_all supported_append_root_array >> strip_tac >>
  simp[Once compile_stmt_def] >> simp[Once compile_stmt_def]
QED

Theorem declare_local_module_var_type:
  declare_local cenv id ty sa = (cenv',sb) ==>
  cenv'.ce_module_var_type = cenv.ce_module_var_type
Proof
  Cases_on `cenv.ce_alloca_locals` >>
  simp[declare_local_def, comp_bind_def, comp_return_def, fresh_var_def,
       comp_get_def, LET_THM] >> rpt strip_tac >> gvs[]
QED

Theorem declare_stmt_local_module_var_type:
  declare_stmt_local cenv s sa = (cenv',sb) ==>
  cenv'.ce_module_var_type = cenv.ce_module_var_type
Proof
  Cases_on `s` >> simp[declare_stmt_local_def, comp_return_def] >>
  metis_tac[declare_local_module_var_type]
QED

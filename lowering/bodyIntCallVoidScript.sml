(* Compiler boundaries for supported void bodies. *)
Theory bodyIntCallVoid
Ancestors
  supportedStmts supportedDecls bodyAppendStorageFacts compileVyper
  stmtLowering compileEnv context finite_map list vyperTypeSystem
  bodyIntCallReturn stmtSim bodyIntCallStmtHelperSoundLabels

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

Theorem supported_void_compile_mutual:
  (!tops bindings s.
    supported_stmt tops bindings s ==>
    !env ce lc ty.
      IS_SOME (type_stmt env NoneT s) /\
      (!id. ce.ce_module_var_type (NONE,id) = build_var_type_map tops (NONE,id)) ==>
      compile_stmt ce lc NoneT s = compile_stmt ce lc ty s) /\
  (!tops bindings ss.
    supported_stmts tops bindings ss ==>
    !env ce lc ty.
      IS_SOME (type_stmts env NoneT ss) /\
      (!id. ce.ce_module_var_type (NONE,id) = build_var_type_map tops (NONE,id)) ==>
      compile_stmts ce lc NoneT ss = compile_stmts ce lc ty ss)
Proof
  ho_match_mp_tac supported_stmt_ind >>
  rpt conj_tac >> rpt strip_tac
  >~ [`compile_stmt ce lc NoneT (Return NONE)`]
  >- simp[compile_return_none_type_independent]
  >~ [`compile_stmt ce lc NoneT (Return (SOME e))`]
  >- gvs[type_stmt_def]
  >~ [`compile_stmt ce lc NoneT (Append target e)`]
  >- (irule supported_append_compile_type_independent >>
      gvs[supported_stmt_def] >> metis_tac[])
  >~ [`compile_stmt ce lc NoneT (If c yes no)`]
  >- suspend "if_case"
  >~ [`compile_stmt ce lc NoneT (For name fty iter n ss)`]
  >- suspend "for_case"
  >~ [`compile_stmts ce lc NoneT (s::ss)`]
  >- suspend "cons_case"
  >~ [`compile_stmt ce lc NoneT Break`]
  >- (Cases_on `lc` >> simp[compile_stmt_def])
  >~ [`compile_stmt ce lc NoneT Continue`]
  >- (Cases_on `lc` >> simp[compile_stmt_def])
  >~ [`compile_stmt ce lc NoneT (Assign target e)`]
  >- (Cases_on `target` >> simp[compile_stmt_def])
  >~ [`compile_stmt ce lc NoneT (Assert c reason)`]
  >- (Cases_on `reason` >> simp[compile_stmt_def])
  >~ [`compile_stmt ce lc NoneT (Raise reason)`]
  >- (Cases_on `reason` >> simp[compile_stmt_def])
  >> simp[compile_stmt_def]
QED

Resume supported_void_compile_mutual[if_case]:
  gvs[supported_stmt_def, type_stmt_def] >>
  `compile_stmts ce lc NoneT yes = compile_stmts ce lc ty yes` by metis_tac[] >>
  `compile_stmts ce lc NoneT no = compile_stmts ce lc ty no` by metis_tac[] >>
  simp[Once compile_stmt_def] >> simp[Once compile_stmt_def]
QED

Resume supported_void_compile_mutual[for_case]:
  rename1 `compile_stmt ce lc NoneT (For name fty iter n ss) =
           compile_stmt ce lc rt (For name fty iter n ss)` >>
  gvs[supported_stmt_def, type_stmt_def] >>
  `!ce' lc'.
    (!id. ce'.ce_module_var_type (NONE,id) = build_var_type_map tops (NONE,id)) ==>
    compile_stmts ce' lc' NoneT ss = compile_stmts ce' lc' rt ss`
    by metis_tac[] >>
  qpat_x_assum `!env ce lc ty. _` kall_tac >>
  qpat_x_assum `!ce' lc'. _` mp_tac >>
  qpat_x_assum `!id. _` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  Cases_on `iter` >> Cases_on `ce.ce_alloca_locals` >>
  simp[Once compile_stmt_def] >> simp[Once compile_stmt_def] >>
  simp[declare_local_def, comp_bind_assoc, tuple_comp_return_bind,
       LET_THM]
QED

Resume supported_void_compile_mutual[cons_case]:
  gvs[supported_stmt_def, type_stmt_def] >>
  Cases_on `type_stmt env NoneT s` >> gvs[] >>
  `!ce'.
    (!id. ce'.ce_module_var_type (NONE,id) = build_var_type_map tops (NONE,id)) ==>
    compile_stmt ce' lc NoneT s = compile_stmt ce' lc ty s /\
    compile_stmts ce' lc NoneT ss = compile_stmts ce' lc ty ss`
    by metis_tac[optionTheory.IS_SOME_EXISTS] >>
  qpat_x_assum `!ce'. _` mp_tac >>
  qpat_x_assum `!id. _` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  pure_once_rewrite_tac[compile_stmt_def] >>
  Cases_on `s` >> Cases_on `ce.ce_alloca_locals` >>
  simp[declare_stmt_local_def, declare_local_def, comp_bind_assoc,
       tuple_comp_return_bind, LET_THM]
QED

Finalise supported_void_compile_mutual

Theorem supported_void_stmts_env:
  !ss tops bindings env ce lc ty.
    supported_stmts tops bindings ss /\
    IS_SOME (type_stmts env NoneT ss) /\
    (!id. ce.ce_module_var_type (NONE,id) = build_var_type_map tops (NONE,id)) ==>
    stmts_env ce lc NoneT ss = stmts_env ce lc ty ss
Proof
  Induct >> rpt strip_tac >- simp[stmts_env_def] >>
  gvs[supported_stmt_def, type_stmt_def] >>
  Cases_on `type_stmt env NoneT h` >> gvs[] >>
  `!ce'.
    (!id. ce'.ce_module_var_type (NONE,id) = build_var_type_map tops (NONE,id)) ==>
    compile_stmt ce' lc NoneT h = compile_stmt ce' lc ty h /\
    stmts_env ce' lc NoneT ss = stmts_env ce' lc ty ss`
    by metis_tac[supported_void_compile_mutual, optionTheory.IS_SOME_EXISTS] >>
  qpat_x_assum `!ce'. _` mp_tac >>
  qpat_x_assum `!id. _` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  pure_once_rewrite_tac[stmts_env_def] >>
  Cases_on `h` >> Cases_on `ce.ce_alloca_locals` >>
  simp[declare_stmt_local_def, declare_local_def, comp_bind_assoc,
       tuple_comp_return_bind, LET_THM]
QED

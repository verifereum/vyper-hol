(* Statement-environment and supported-fragment shadow boundaries. *)
Theory gasShadowStmtEnv
Ancestors
  gasShadowCompileStmt gasShadowCompileStmtBase loweringPosts supportedStmts
  compileVyper gasShadow gasShadowState compileEnv vyperAST list
  gasShadowSupportedExpr gasShadowSupportedStmts

Theorem gas_shadow_stmts_env:
  !ss ce lc ty.
    gas_shadow_compiles (stmts_env ce lc ty ss)
      (stmts_env ce lc ty (MAP gas_shadow_stmt ss))
Proof
  Induct >> simp[stmts_env_def, gas_shadow_compiles_return] >>
  rpt gen_tac >> ho_match_mp_tac gas_shadow_compiles_get_terminated >>
  gen_tac >> Cases_on `b` >> simp[gas_shadow_compiles_return] >>
  ho_match_mp_tac gas_shadow_compiles_bind >> conj_tac
  >- simp[gas_shadow_compiles_declare_stmt_local] >>
  gen_tac >> simp[comp_ignore_bind_def] >>
  ho_match_mp_tac gas_shadow_compiles_bind >> simp[gas_shadow_compile_stmt]
QED

Theorem gas_shadow_valued_return:
  (!s. stmt_valued_return (gas_shadow_stmt s) = stmt_valued_return s) /\
  (!ss. stmts_valued_return (MAP gas_shadow_stmt ss) = stmts_valued_return ss)
Proof
  ho_match_mp_tac (legacyInduction.mutual_ind_from_ops stmt_induction) >>
  rpt conj_tac >> rpt gen_tac >>
  simp[gas_shadow_stmt_def, stmt_valued_return_def] >>
  rename1 `OPTION_MAP gas_shadow_expr opt` >> Cases_on `opt` >> simp[stmt_valued_return_def]
QED

Theorem gas_shadow_supported_stmts:
  supported_stmts tops bindings ss ==>
    supported_stmts tops bindings (MAP gas_shadow_stmt ss)
Proof
  strip_tac >> irule gas_shadow_supported_stmts_from_expr >>
  simp[gas_shadow_supported_pure_expr, gas_shadow_supported_effect_expr,
       gas_shadow_supported_expr]
QED

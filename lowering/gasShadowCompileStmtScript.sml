(* Structural shadow correspondence for statements and statement lists. *)
Theory gasShadowCompileStmt
Ancestors
  gasShadow gasShadowState gasShadowCenv gasShadowCompile gasShadowCompileStmtCases
  gasShadowCompileStmtBase stmtLowering vyperAST list

Theorem gas_shadow_compile_stmt:
  (!cenv lctx ty stmt.
    gas_shadow_compiles (compile_stmt cenv lctx ty stmt)
      (compile_stmt (gas_shadow_cenv cenv) lctx ty (gas_shadow_stmt stmt))) /\
  (!cenv lctx ty stmts.
    gas_shadow_compiles (compile_stmts cenv lctx ty stmts)
      (compile_stmts (gas_shadow_cenv cenv) lctx ty (MAP gas_shadow_stmt stmts)))
Proof
  `(!stmt cenv lctx ty.
      gas_shadow_compiles (compile_stmt cenv lctx ty stmt)
        (compile_stmt (gas_shadow_cenv cenv) lctx ty (gas_shadow_stmt stmt))) /\
   (!stmts cenv lctx ty.
      gas_shadow_compiles (compile_stmts cenv lctx ty stmts)
        (compile_stmts (gas_shadow_cenv cenv) lctx ty (MAP gas_shadow_stmt stmts)))`
    suffices_by metis_tac[] >>
  ho_match_mp_tac (legacyInduction.mutual_ind_from_ops stmt_induction) >>
  rpt conj_tac >>
  simp[gas_shadow_stmt_pass, gas_shadow_stmt_continue, gas_shadow_stmt_break,
       gas_shadow_stmt_expr, gas_shadow_stmt_assert, gas_shadow_stmt_log,
       gas_shadow_stmt_raise, gas_shadow_stmt_augassign, gas_shadow_stmt_append,
       gas_shadow_stmt_annassign] >>
  rpt strip_tac >>
  simp[gas_shadow_stmt_if, gas_shadow_stmts_cons]
  >~ [`For id fty iter bound loop_body`]
  >- (Cases_on `iter` >> simp[gas_shadow_stmt_for_range, gas_shadow_stmt_for_array])
  >~ [`Return opt`]
  >- (Cases_on `opt` >> simp[gas_shadow_stmt_return_none, gas_shadow_stmt_return_some])
  >~ [`Assign target e`]
  >- (Cases_on `target` >> simp[gas_shadow_stmt_assign_base, gas_shadow_stmt_assign_tuple])
  >~ [`compile_stmts _ _ _ []`]
  >- simp[compile_stmt_def, gas_shadow_compiles_return] >>
  irule (SRULE [] gas_shadow_stmts_cons) >> simp[]
QED


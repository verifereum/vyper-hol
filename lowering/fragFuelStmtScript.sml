(*
 * Fuel bounds for statements: compile_stmt and compile_stmts.
 *
 * A statement starts from a state where its environment's pointer
 * variables are allocated (cenv_ptrs_below) and may write them
 * (cenv_ptrs_in), and may jump to the labels of stmt_exits_in.  The proof
 * is by structural induction over statements: an If and a statement list
 * compose their parts (fragFuelStmtGlue), a loop is a leaf over its body
 * (fragFuelLoopForRange, fragFuelLoopForIter), and every other statement
 * is straight-line code over expression and statement helpers
 * (fragFuelStmtSimple).
 *
 * TOP-LEVEL:
 *   fuel_okS_compile_stmt
 *)

Theory fragFuelStmt
Ancestors
  fragFuel fragFuelStmtBase fragFuelStmtGlue fragFuelStmtSimple
  fragFuelLoopForRange fragFuelLoopForIter fragFuelExpr stmtLowering
  exprLowering compileEnv vyperAST
Libs
  fragFuelLib

Theorem fuel_okS_compile_stmt:
  (!s cenv lctx ty Wv E.
     cenv_ptrs_in Wv cenv /\ stmt_exits_in E cenv lctx ==>
     fuel_okS (\st. cenv_ptrs_below st.cs_next_var cenv) Wv {} E
       (compile_stmt cenv lctx ty s)) /\
  (!ss cenv lctx ty Wv E.
     cenv_ptrs_in Wv cenv /\ stmt_exits_in E cenv lctx ==>
     fuel_okS (\st. cenv_ptrs_below st.cs_next_var cenv) Wv {} E
       (compile_stmts cenv lctx ty ss))
Proof
  ho_match_mp_tac (legacyInduction.mutual_ind_from_ops stmt_induction) >>
  rpt conj_tac >> rpt gen_tac >>
  rpt strip_tac
  >~ [`compile_stmt _ _ _ (If _ _ _)`]
  >- (irule fuel_okS_compile_if >>
      simp[next_stable_cenv_ptrs_below, fuel_ok_lower_value_compile_expr] >>
      conj_tac >> first_x_assum irule >> simp[])
  >~ [`compile_stmt _ _ _ (For _ _ _ _ _)`]
  >- (rename1 `For _ _ it _ _` >> Cases_on `it`
      >- (irule fuel_okS_compile_for_iter >> simp[fuel_ok_compile_expr])
      >> irule fuel_okS_compile_for_range >>
      simp[fuel_ok_lower_value_compile_expr])
  >~ [`compile_stmts _ _ _ []`]
  >- (simp[compile_stmt_def] >> irule fuel_okS_of_ok >>
      simp[fuel_ok_return])
  >~ [`compile_stmts _ _ _ (_ :: _)`]
  >- (irule fuel_okS_compile_stmts_cons >> simp[]) >>
  irule fuel_okS_of_ok >> irule fuel_ok_compile_stmt_simple >> simp[]
QED

(* A piece of S1 (loweringRuntimeCorrect's lower_vyper_runtime_unit_correct). *)
Theory stmtsEnvRetTy
Ancestors
  stmtSimProps
  stmtSimDefs
  exprSimDefs
  loweringPosts
  list pair fragExec  bodySim bodySimMain loweringHalt stmtLoweringMono  exprLoweringProps
  compileEnv compileVyper moduleLowering stmtLowering
  e2eDefs supportedProgram supportedDecls supportedExprForms supportedStmts
  vyperLoweringCorrect rawReturnHeader
  vyperTypeSelectedEntrySoundness vyperTypeSystem
  vyperInterpreter vyperState vyperContext
  venomState venomExecSemantics venomWf

val _ = Parse.hide "body";

(* Only a valued return reads the enclosing function's return type. *)
Theorem compile_stmt_ret_ty[local]:
  (!cenv lctx ty s.
     supported_stmt tops bindings s /\
     ~stmt_valued_return s ==>
     compile_stmt cenv lctx ty s = compile_stmt cenv lctx ty' s) /\
  (!cenv lctx ty ss.
     supported_stmts tops bindings ss /\
     ~stmts_valued_return ss ==>
     compile_stmts cenv lctx ty ss = compile_stmts cenv lctx ty' ss)
Proof
  ho_match_mp_tac compile_stmt_ind >> rpt conj_tac >> rpt gen_tac
  >~ [`compile_stmts _ _ _ (_::_)`]
  >- (rpt strip_tac >> simp[FUN_EQ_THM] >> qx_gen_tac `cs0` >>
      ONCE_REWRITE_TAC [compile_stmt_def] >>
      simp[comp_bind_def, comp_get_def] >>
      IF_CASES_TAC >> simp[] >>
      rpt (qpat_x_assum `!cs cenv. _` (qspec_then `cs0` mp_tac)) >>
      gvs[supported_stmt_def, stmt_valued_return_def] >> rpt strip_tac >>
      simp[]) >>
  rpt strip_tac >> gvs[supported_stmt_def, stmt_valued_return_def] >>
  ONCE_REWRITE_TAC [compile_stmt_def] >>
  simp[]
QED

(* A supported body without a valued return compiles the same at every
   return type. *)

Theorem stmts_env_ret_ty:
  !ss tops bindings ctx cenv cx lctx ty ty'.
    supported_stmts tops bindings ss /\ body_inv tops ctx cenv cx /\
    ~stmts_valued_return ss ==>
    stmts_env cenv lctx ty ss = stmts_env cenv lctx ty' ss
Proof
  rpt strip_tac >>
  qpat_x_assum `body_inv _ _ _ _` kall_tac >>
  pop_assum mp_tac >> pop_assum mp_tac >>
  qid_spec_tac `cenv` >> Induct_on `ss` >> simp[stmts_env_def] >>
  rpt strip_tac >> simp[FUN_EQ_THM] >> qx_gen_tac `cs0` >>
  gvs[supported_stmt_def, stmt_valued_return_def] >>
  simp[comp_bind_def, comp_get_def] >>
  IF_CASES_TAC >> simp[] >>
  `!c. compile_stmt c lctx ty h = compile_stmt c lctx ty' h` by
    (rpt strip_tac >> irule (cj 1 compile_stmt_ret_ty) >> simp[] >> metis_tac[]) >>
  simp[]
QED


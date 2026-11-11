(* S1 Log dispatch: exact argument types retain the original proof;
   compatible bounds use the widened scalar-event leaf. *)
Theory bodySimLog
Ancestors
  bodySimLogArgs whitelistLogWiden
  allocLimits allocLimitsProps
  exprSimSource bodyExprPreFacts exprSimHypsDefs list bodySim bodySimStmtCases stmtSimLog exprSimHyps
  compileEnv compileVyper supportedStmts supportedDecls supportedTypes
  supportedExprs supportedExprTraverse supportedStmtTraverse vyperEvent vyperInterpreter
  vyperState vyperTypeSystem supportedProgram supportedNames vyperContext
  vyperABI vyperTypeInvariants vyperTypeExprSoundness vyperTypeCallGraph
  vyperTypeCallStackSoundness

Theorem body_log_case:
  !cx id es. body_exprs_ok cx es ==> body_stmt_ok cx (Log id es)
Proof
  rw[body_stmt_ok_def] >>
  reverse (Cases_on `supported_log_exact tops id es`)
  >- (`?fields. supported_event_fields tops id = SOME fields /\
               supported_pure_exprs tops es /\
               LIST_REL (\e ((_,fty),_).
                 event_arg_compatible fty (expr_type e)) es fields` by
        (gvs[supported_stmt_def, supported_log_def, AllCaseEqs()] >>
         Cases_on `supported_event_fields tops id` >> gvs[]) >>
      drule_all body_log_widen_case >> simp[]) >>
  `?fields. supported_event_fields tops id = SOME fields /\
            supported_pure_exprs tops es /\
            MAP expr_type es = MAP (SND o FST) fields` by
    (gvs[supported_log_exact_def, AllCaseEqs()] >>
     Cases_on `supported_event_fields tops id` >> gvs[]) >>
  drule_all body_log_metadata >> strip_tac >>
  `SUM (MAP (type_memory_bytes cenv)
          (log_non_indexed_types (MAP SND fields)
             (MAP (SND o FST) fields))) < dimword (:256) /\
   abi_size_bound cenv.ce_struct_fields
     (TupleT (log_non_indexed_types (MAP SND fields)
                (MAP (SND o FST) fields))) < dimword (:256)` by
    (gvs[stmt_exprs_ok_def, allocLimitsTheory.alloc_limits_stmt_def,
         allocLimitsTheory.log_alloc_ok_def] >>
     conj_tac >> irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
     qexists_tac `2 ** 64` >> gvs[wordsTheory.dimword_def]) >>
  `well_typed_exprs env es /\
   !id t. FLOOKUP env.var_types id = SOME t ==>
     ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    gvs[type_stmt_def, expr_sim_inv_def, AllCaseEqs()] >>
  `alloc_limits_exprs cenv es` by
    fs[stmt_exprs_ok_def, alloc_limits_stmt_def] >>
  `EVERY (\e. body_stmt_safe tops (Expr e) /\ ~is_extcode e) es` by
    (fs[body_stmt_safe_log_args, EVERY_CONJ] >>
     rw[EVERY_MEM] >> irule alloc_limits_expr_not_extcode >>
     metis_tac[exprSimSourceTheory.alloc_limits_exprs_mem]) >>
  irule compile_log_stmt_frag >> simp[] >>
  conj_tac
  >- (qpat_x_assum `MAP expr_type _ = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
      simp[]) >>
  conj_tac >- (qexists_tac `env` >> simp[]) >>
  qexists_tac `\s. expr_sim_inv cenv cx env s` >> simp[] >>
  irule body_log_args_ready >>
  gvs[type_stmt_def, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
      int_calls_stmt_def, AllCaseEqs()] >>
  metis_tac[]
QED

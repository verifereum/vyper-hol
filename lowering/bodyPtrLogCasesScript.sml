(*
 * The pointer twin of bodySimMain's induction: the cases for log and append.
 * Each is the pointer twin of the S1 case of the same name (bodySim*Cases),
 * over bodyPtrPreds's predicates; bodySimPtrMain's body_sim_ptr_mutual
 * uses them.
 *
 * TOP-LEVEL:
 *   body_log_case_ptr
 *   body_append_case_ptr
 *)
Theory bodyPtrLogCases
Ancestors
  bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST vyperInterpreter
  vyperState vyperContext vyperTypeCallGraph list bodyAppendStoragePtr
  supportedStmts bodyLogReadyPtr logStmtComposePtr bodySimLog allocLimits
  exprSimHypsDefs supportedExprs supportedExprTraverse supportedStmtTraverse
  vyperTypeSystem compileEnv

val _ = Parse.hide "body";

(* ADMITTED: a piece of the body induction. *)
Theorem body_log_case_ptr:
  !cx id es. body_exprs_ptr_ok cx es ==> body_stmt_ptr_ok cx (Log id es)
Proof
  rw[body_stmt_ptr_ok_def] >>
  `?fields. supported_event_fields tops id = SOME fields /\
            supported_pure_exprs tops es /\
            MAP expr_type es = MAP (SND o FST) fields` by
    (gvs[supported_stmt_def, supported_log_def, AllCaseEqs()] >>
     Cases_on `supported_event_fields tops id` >> gvs[]) >>
  drule_all body_log_metadata >> strip_tac >>
  `SUM (MAP (type_memory_bytes cenv)
          (log_non_indexed_types (MAP SND fields) (MAP (SND o FST) fields))) < dimword(:256) /\
   abi_size_bound cenv.ce_struct_fields
     (TupleT (log_non_indexed_types (MAP SND fields) (MAP (SND o FST) fields))) < dimword(:256)` by
    (gvs[stmt_exprs_ok_def, alloc_limits_stmt_def, log_alloc_ok_def] >>
     conj_tac >> irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
     qexists_tac `2 ** 64` >> gvs[wordsTheory.dimword_def]) >>
  `well_typed_exprs env es /\
   !id t. FLOOKUP env.var_types id = SOME t ==>
     ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    gvs[type_stmt_def, expr_sim_inv_def, AllCaseEqs()] >>
  irule compile_log_ready_stmt_frag_ptr >>
  conj_tac
  >- (qexistsl_tac [`MAP SND fields`,`h`,`MAP (SND o FST) fields`] >> simp[] >>
      qpat_x_assum `MAP expr_type _ = _` (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  conj_tac >- (qexists_tac `env` >> simp[]) >>
  qexists_tac `\s. expr_sim_inv cenv cx env s` >> simp[] >>
  irule body_log_args_ready_ptr >>
  gvs[type_stmt_def, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
      int_calls_stmt_def, AllCaseEqs()] >> metis_tac[]
QED

(* ADMITTED: a piece of the body induction. *)
Theorem body_append_case_ptr:
  !cx t e.
    (!s'' p t'.
       eval_target_place cx t s'' = (INL p,t') ==> body_expr_ptr_ok cx e) /\
    body_base_target_ptr_ok cx t ==>
    body_stmt_ptr_ok cx (Append t e)
Proof
  rpt strip_tac >> Cases_on `?nid. t = TopLevelNameTarget nid`
  >- (gvs[] >> irule body_append_storage_other_ptr >> first_assum ACCEPT_TAC) >>
  Cases_on `t` >> gvs[] >>
  rw[body_stmt_ptr_ok_def, supported_stmt_def, supported_append_target_def]
QED

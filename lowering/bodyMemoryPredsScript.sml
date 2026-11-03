(* Reachability predicates for the additive memory body induction. *)
Theory bodyMemoryPreds
Ancestors
  bodyMemoryDefs bodyExprMemory stmtMemory stmtControlMemory stmtSim
  bodySim bodySimStmtCases exprSimHyps supportedExprTraverse supportedStmtTraverse
  supportedStmts vyperTypeCallGraph
  vyperInterpreter vyperTypeSystem vyperState vyperAST list

val _ = Parse.hide "body";

Definition body_expr_mem_ok_def:
  body_expr_mem_ok cx e <=>
    !tops ctx func cenv env ty es.
      body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e es ==>
      expr_sim_mem ctx func cenv cx ty e es /\
      expr_vv_sim_mem ctx func cenv cx ty e es
End

Definition body_stmt_mem_ok_def:
  body_stmt_mem_ok cx s <=>
    !d tops bindings ctx func cenv env env' ret_ty lctx RetQ es res es'.
      body_inv tops ctx cenv cx /\ supported_stmt tops bindings s /\
      expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
      locals_alloc_ok cenv env /\
      type_stmt env ret_ty s = SOME env' /\ stmt_exprs_ok cenv s /\
      call_evaluation_safe cx (int_calls_stmt s) /\
      frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
      eval_stmt cx s es = (res, es') ==>
      stmt_frag_mem d ctx func cx lctx RetQ cenv
        (stmt_env cenv lctx ret_ty s) es res es'
End

Definition body_stmts_mem_ok_def:
  body_stmts_mem_ok cx ss <=>
    !d tops bindings ctx func cenv env env' ret_ty lctx RetQ es res es'.
      body_inv tops ctx cenv cx /\ supported_stmts tops bindings ss /\
      expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
      locals_alloc_ok cenv env /\
      type_stmts env ret_ty ss = SOME env' /\
      EVERY (stmt_exprs_ok cenv) ss /\
      call_evaluation_safe cx (int_calls_stmts ss) /\
      frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
      eval_stmts cx ss es = (res, es') ==>
      stmt_frag_mem d ctx func cx lctx RetQ cenv
        (stmts_env cenv lctx ret_ty ss) es res es'
End

Definition body_exprs_mem_ok_def:
  body_exprs_mem_ok cx [] = T /\
  body_exprs_mem_ok cx (e::es) =
    (body_expr_mem_ok cx e /\
     ((?s tv t s1 v t1. eval_expr cx e s = (INL tv, t) /\
                        read_result cx tv s1 = (INL v, t1)) ==>
      body_exprs_mem_ok cx es))
End

Definition body_results_mem_ok_def:
  body_results_mem_ok cx [] = T /\
  body_results_mem_ok cx (e::es) =
    (body_expr_mem_ok cx e /\
     ((?s res t. eval_expr cx e s = (INL res, t)) ==>
      body_results_mem_ok cx es))
End

Definition body_iterator_mem_ok_def:
  body_iterator_mem_ok cx (Array e) = body_expr_mem_ok cx e /\
  body_iterator_mem_ok cx (Range e1 e2) =
    (body_expr_mem_ok cx e1 /\
     ((?s tv t s1 v t1. eval_expr cx e1 s = (INL tv, t) /\
                        read_result cx tv s1 = (INL v, t1)) ==>
      body_expr_mem_ok cx e2))
End

Definition body_for_mem_ok_def:
  body_for_mem_ok cx (tyv : type_value) (nm : identifier) body (vs : value list)
  <=> vs <> [] ==> body_stmts_mem_ok cx body
End

Definition body_base_target_mem_ok_def:
  body_base_target_mem_ok cx (NameTarget id) = T /\
  body_base_target_mem_ok cx (TopLevelNameTarget nid) = T /\
  body_base_target_mem_ok cx (AttributeTarget t id) = body_base_target_mem_ok cx t /\
  body_base_target_mem_ok cx (SubscriptTarget t e) =
    (body_base_target_mem_ok cx t /\
     ((?s pv s1. eval_base_place cx t s = (INL pv, s1)) ==>
      body_expr_mem_ok cx e))
End

Definition body_tuple_target_mem_ok_def:
  body_tuple_target_mem_ok cx (BaseTarget t) (v : value) =
    body_base_target_mem_ok cx t /\
  body_tuple_target_mem_ok cx (TupleTarget gs) v =
    (!vs. v = ArrayV (TupleV vs) ==> body_tuple_targets_mem_ok cx gs vs) /\
  body_tuple_targets_mem_ok cx [] vs = T /\
  body_tuple_targets_mem_ok cx (g::gs) [] = T /\
  body_tuple_targets_mem_ok cx (g::gs) (v::vs) =
    (body_tuple_target_mem_ok cx g v /\
     ((?s x t. assign_tuple_targets cx g v s = (INL x, t)) ==>
      body_tuple_targets_mem_ok cx gs vs))
Termination
  WF_REL_TAC `measure (\x. case x of
    INL (_,t,_) => assignment_target_size t
  | INR (_,ts,_) => list_size assignment_target_size ts)` >>
  simp[assignment_target_size_def, list_size_def]
End

Theorem body_bool_literal_mem_ok:
  !cx b. body_expr_mem_ok cx (Literal (BaseT BoolT) (BoolL b))
Proof
  simp[body_expr_mem_ok_def] >> metis_tac[body_bool_literal_mem]
QED

Theorem body_stmts_mem_projection:
  (!cx ss. body_stmts_mem_ok cx ss) ==>
  !d tops bindings ctx func cenv cx env env' ret_ty lctx RetQ ss es res es'.
    body_inv tops ctx cenv cx /\ supported_stmts tops bindings ss /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmts env ret_ty ss = SOME env' /\
    EVERY (stmt_exprs_ok cenv) ss /\
    call_evaluation_safe cx (int_calls_stmts ss) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
    eval_stmts cx ss es = (res, es') ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmts_env cenv lctx ret_ty ss) es res es'
Proof
  rw[body_stmts_mem_ok_def] >> metis_tac[]
QED

Theorem body_pass_mem_ok:
  !cx. body_stmt_mem_ok cx Pass
Proof
  rw[body_stmt_mem_ok_def] >>
  gvs[Once evaluate_def, return_def] >>
  irule compile_pass_frag_mem
QED

Theorem body_nil_mem_ok:
  !cx. body_stmts_mem_ok cx []
Proof
  rw[body_stmts_mem_ok_def] >>
  gvs[Once evaluate_def, return_def] >>
  irule stmt_frag_nil_mem
QED

Theorem body_break_mem_ok:
  !cx. body_stmt_mem_ok cx Break
Proof
  rw[body_stmt_mem_ok_def] >>
  gvs[Once evaluate_def, raise_def] >>
  Cases_on `lctx`
  >- simp[stmt_frag_mem_def, stmt_res_ok_def] >>
  irule compile_break_frag_mem
QED

Theorem body_continue_mem_ok:
  !cx. body_stmt_mem_ok cx Continue
Proof
  rw[body_stmt_mem_ok_def] >>
  gvs[Once evaluate_def, raise_def] >>
  Cases_on `lctx`
  >- simp[stmt_frag_mem_def, stmt_res_ok_def] >>
  irule compile_continue_frag_mem
QED

Theorem body_return_none_mem_ok:
  !cx. body_stmt_mem_ok cx (Return NONE)
Proof
  rw[body_stmt_mem_ok_def, frame_ret_ok_mem_def] >>
  first_x_assum irule >> simp[same_frame_refl] >>
  qexists_tac `env` >> simp[]
QED

Theorem body_return_mem_ok:
  !cx e. body_expr_mem_ok cx e ==> body_stmt_mem_ok cx (Return (SOME e))
Proof
  rw[body_stmt_mem_ok_def, frame_ret_ok_mem_def] >>
  `supported_expr tops e` by gvs[supported_stmt_def] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[type_stmt_def, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_expr_exists_def, int_calls_stmt_def, int_calls_expr_def] >>
     qexists_tac `[]` >> simp[]) >>
  first_x_assum irule >> fs[body_expr_mem_ok_def] >>
  conj_tac >- metis_tac[] >> qexists_tac `env` >> simp[]
QED

(* Do not mistake these base cases and projection for the mutual theorem:
   the recursive producer cases remain separate obligations. *)
val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_MEMORY_PREDICATE_AUDIT OK\n"
     else raise Fail "body memory predicate inherited admission"
  end) [body_bool_literal_mem_ok, body_stmts_mem_projection,
        body_pass_mem_ok, body_nil_mem_ok, body_break_mem_ok,
        body_continue_mem_ok, body_return_none_mem_ok, body_return_mem_ok];


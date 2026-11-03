Theory bodyStmtClosureMemory
Ancestors
  bodyMemoryPreds bodyLiteralMemory bodySimStmtCases bodySim
  bodyMemoryDefs stmtMemory stmtControlMemory exprSimHyps
  exprLoweringProps stmtLoweringProps supportedExprTraverse supportedStmtTraverse
  supportedStmts vyperTypeCallGraph vyperInterpreter vyperTypeSystem
  vyperState vyperAST allocLimits vyperTypeCallStackSoundness supportedExprs
  stmtLoweringMono exprOpenMain

val _ = Parse.hide "body";

Theorem frame_ret_ok_mem_same_frame:
  same_frame cenv c /\ frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty ==>
  frame_ret_ok_mem d ctx func cx RetQ c ret_ty
Proof
  rw[frame_ret_ok_mem_def] >> first_x_assum irule >>
  metis_tac[same_frame_trans]
QED

Theorem body_expr_stmt_mem_case:
  !cx e. body_expr_mem_ok cx e ==> body_stmt_mem_ok cx (Expr e)
Proof
  rpt gen_tac >> strip_tac >> simp[Once body_stmt_mem_ok_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[type_stmt_def, supported_stmt_def, int_calls_stmt_def,
      stmt_exprs_ok_def, supported_stmt_expr_exists_def] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >> simp[] >> qexists_tac `[]` >> simp[]) >>
  `expr_sim_mem ctx func cenv cx (expr_type e) e es /\
   expr_vv_sim_mem ctx func cenv cx (expr_type e) e es` by
    (qpat_x_assum `body_expr_mem_ok _ _`
       (mp_tac o REWRITE_RULE [body_expr_mem_ok_def]) >>
     disch_then irule >> metis_tac[]) >>
  irule compile_expr_stmt_frag_ok_mem >> simp[] >>
  rpt gen_tac >> strip_tac >> irule compile_expr_open >> metis_tac[]
QED

Theorem body_if_mem_case:
  !cx e ss1 ss2.
    (!s tv t s3 x t'.
       eval_expr cx e s = (INL tv,t) /\ push_scope s3 = (INL x,t') ==>
       body_stmts_mem_ok cx ss1) /\
    (!s tv t s3 x t'.
       eval_expr cx e s = (INL tv,t) /\ push_scope s3 = (INL x,t') ==>
       body_stmts_mem_ok cx ss2) /\ body_expr_mem_ok cx e ==>
    body_stmt_mem_ok cx (If e ss1 ss2)
Proof
  rpt gen_tac >> strip_tac >> simp[Once body_stmt_mem_ok_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[type_stmt_def, supported_stmt_def, int_calls_stmt_def,
      stmt_exprs_ok_def, supported_stmt_expr_exists_def, optionTheory.IS_SOME_EXISTS] >>
  `supported_expr tops e` by simp[supported_expr_def] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >> simp[] >>
     qexists_tac `int_calls_stmts ss1 ++ int_calls_stmts ss2` >> simp[]) >>
  `!ty. expr_sim_mem ctx func cenv cx ty e es /\
        expr_vv_sim_mem ctx func cenv cx ty e es` by
    (gen_tac >>
     qpat_x_assum `body_expr_mem_ok _ _` (mp_tac o REWRITE_RULE [body_expr_mem_ok_def]) >>
     disch_then irule >> metis_tac[]) >>
  irule compile_if_stmt_frag_mem >> simp[stmts_env_cs_mono] >>
  reverse conj_tac >- metis_tac[compile_expr_grows] >>
  rpt strip_tac >>
  rename1 `_ = (INL (BoolV b), es1)` >>
  `?tv s1. eval_expr cx e es = (INL tv, s1)` by
    (qpat_x_assum `_ = (INL (BoolV b), es1)` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  `body_stmts_mem_ok cx ss1 /\ body_stmts_mem_ok cx ss2` by
    (`push_scope es1 = (INL (), es1 with scopes updated_by CONS FEMPTY)` by
       simp[push_scope_def, return_def] >> metis_tac[]) >>
  `expr_sim_inv cenv cx env es1` by
    (drule_all expr_body_pre_eval >> simp[]) >>
  drule expr_sim_inv_push_scope >> strip_tac >>
  rpt (qpat_x_assum `body_stmts_mem_ok _ _`
         (strip_assume_tac o REWRITE_RULE [body_stmts_mem_ok_def])) >>
  Cases_on `b` >> fs[] >> first_x_assum irule >>
  gvs[stmts_exprs_ok_EVERY, stmt_exprs_ok_def, alloc_limits_stmt_def] >>
  metis_tac[call_evaluation_safe_append_left, call_evaluation_safe_append_right]
QED

Theorem body_stmts_cons_mem_case:
  !cx s ss.
    (!s0 x t. eval_stmt cx s s0 = (INL x,t) ==> body_stmts_mem_ok cx ss) /\
    body_stmt_mem_ok cx s ==> body_stmts_mem_ok cx (s::ss)
Proof
  rpt gen_tac >> strip_tac >> simp[Once body_stmts_mem_ok_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[supported_stmt_def, type_stmt_def, AllCaseEqs(), int_calls_stmt_def] >>
  rename1 `type_stmt env ret_ty s = SOME env1` >>
  irule stmt_frag_cons_env_mem >>
  simp[cj 1 compile_stmt_cs_mono, stmts_env_cs_mono] >> reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `body_stmt_mem_ok _ _` (irule o REWRITE_RULE [body_stmt_mem_ok_def]) >>
      metis_tac[call_evaluation_safe_append_left]) >>
  rpt strip_tac >>
  rename1 `stmt_env cenv lctx ret_ty s sa = (c, sm)` >>
  `same_frame cenv c` by metis_tac[cenv_top_ext_same_frame] >>
  `eval_stmts cx ss es1 = (res, es')` by
    (qpat_x_assum `eval_stmts _ (_::_) _ = _` mp_tac >>
     simp[Once evaluate_def, bind_def, ignore_bind_def]) >>
  `stmt_exprs_ok c = stmt_exprs_ok cenv` by
    metis_tac[stmt_exprs_ok_same_frame] >>
  `expr_sim_inv c cx env1 es1` by
    (irule expr_sim_inv_stmt >> fs[body_inv_def] >>
     metis_tac[call_evaluation_safe_append_left]) >>
  `ce_locals_declared c env1` by metis_tac[ce_locals_declared_stmt] >>
  `locals_alloc_ok c env1` by metis_tac[locals_alloc_ok_stmt] >>
  `body_inv tops ctx c cx` by metis_tac[body_inv_same_frame] >>
  `frame_ret_ok_mem d ctx func cx RetQ c ret_ty` by
    metis_tac[frame_ret_ok_mem_same_frame] >>
  qpat_x_assum `!s0 t. _ ==> body_stmts_mem_ok _ _` drule >>
  simp[body_stmts_mem_ok_def] >> disch_then irule >>
  metis_tac[call_evaluation_safe_append_right]
QED

Theorem body_word_literal_mem_ok:
  !cx ann l. is_word_type ann ==> body_expr_mem_ok cx (Literal ann l)
Proof
  rw[body_expr_mem_ok_def] >>
  `expr_sim_pre cenv cx env (Literal ann l) es` by
    gvs[expr_sim_pre_body, int_calls_expr_def] >>
  metis_tac[compile_literal_word_body_sim_mem, compile_literal_word_body_vv_sim_mem]
QED

Theorem body_word_literal_stmts_mem_ok:
  !cx ann l. is_word_type ann ==> body_stmts_mem_ok cx [Expr (Literal ann l)]
Proof
  rpt strip_tac >> irule body_stmts_cons_mem_case >>
  simp[body_nil_mem_ok] >> irule body_expr_stmt_mem_case >>
  simp[body_word_literal_mem_ok]
QED

(* Clean additive execution/transport outputs.  The general Expr closure is
   deliberately NOT classified as oracle-clean: its source-side openness
   proof uses the pre-existing functional admission supported_immutable_bound
   (exprOpenMain), through compile_expr_open_general and compile_expr_open.
   The singleton corollary inherits that same dependency.  No memory
   admission is used here.  The relative tag check below is an inventory,
   not a replacement for the source dependency audit. *)
val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_STMT_CLOSURE_MEMORY_CLEAN OK\n"
     else raise Fail "unexpected admission in clean statement closure"
  end) [frame_ret_ok_mem_same_frame, body_if_mem_case,
        body_stmts_cons_mem_case, body_word_literal_mem_ok,
        stmt_expr_body_pre, supported_expr_body_calls, expr_body_pre_eval,
        expr_sim_inv_push_scope, expr_sim_inv_stmt, ce_locals_declared_stmt,
        locals_alloc_ok_stmt, compile_expr_stmt_frag_ok_mem,
        compile_if_stmt_frag_mem, stmt_frag_cons_env_mem];

val () = List.app (fn (name, th) =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
      val (inherited, _) = Tag.dest_tag (Thm.tag compile_expr_open)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn tag => tag = "DISK_THM" orelse
                           List.exists (fn dep => dep = tag) inherited) oracles
     then print ("BODY_STMT_CLOSURE_INHERITED_FUNCTIONAL " ^ name ^
                 ": supported_immutable_bound -> compile_expr_open_general -> compile_expr_open\n")
     else raise Fail "unexpected dependency in inherited functional closure"
  end) [("body_expr_stmt_mem_case",body_expr_stmt_mem_case),
        ("body_word_literal_stmts_mem_ok",body_word_literal_stmts_mem_ok)];

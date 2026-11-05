Theory bodySeqMemory
Ancestors
  bodyExprPreFacts exprSimSource bodyMemoryPreds bodyMemoryDefs bodySim
  exprSimHypsDefs gasContext loweringPosts stmtSimDefs
  exprLoweringProps stmtLoweringProps stmtLoweringMono compileEnv
  supportedExprTraverse supportedStmtTraverse supportedStmts supportedExprs
  vyperTypeCallGraph vyperTypeCallStackSoundness vyperInterpreter
  vyperTypeSystem vyperState vyperAST list finite_map
  stmtSimSeqMem

val _ = Parse.hide "body";

Theorem frame_ret_ok_mem_same_frame:
  same_frame cenv c /\ frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty ==>
  frame_ret_ok_mem d ctx func cx RetQ c ret_ty
Proof
  rw[frame_ret_ok_mem_def] >> first_x_assum irule >>
  metis_tac[same_frame_trans]
QED

(* Historical successful proof, before counted source-action composition:
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
*)

Theorem body_stmts_cons_mem_case:
  !cx s ss.
    (!s0 x t. eval_stmt cx s s0 = (INL x,t) ==> body_stmts_mem_ok cx ss) /\
    body_stmt_mem_ok cx s ==> body_stmts_mem_ok cx (s::ss)
Proof
  rpt gen_tac >> strip_tac >> simp[Once body_stmts_mem_ok_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[supported_stmt_def, type_stmt_def, AllCaseEqs(), int_calls_stmt_def,
      supported_stmt_expr_exists_def] >>
  rename1 `type_stmt env ret_ty s = SOME env1` >>
  irule stmt_frag_cons_env_mem >>
  simp[cj 1 compile_stmt_cs_mono, stmts_env_cs_mono] >> reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `body_stmt_mem_ok _ _` (irule o REWRITE_RULE [body_stmt_mem_ok_def]) >>
      metis_tac[call_evaluation_safe_append_left]) >>
  rpt strip_tac >>
  rename1 `stmt_env cenv lctx ret_ty s sa = (c, sm)` >>
  `same_frame cenv c` by metis_tac[cenv_top_ext_same_frame] >>
  `stmt_exprs_ok c = stmt_exprs_ok cenv` by
    metis_tac[stmt_exprs_ok_same_frame] >>
  `expr_sim_inv c cx env1 es1` by
    (irule expr_sim_inv_stmt >> fs[body_inv_def] >>
     metis_tac[expr_sim_inv_gas_obs, call_evaluation_safe_append_left]) >>
  `ce_locals_declared c env1` by metis_tac[ce_locals_declared_stmt] >>
  `locals_alloc_ok c env1` by metis_tac[locals_alloc_ok_stmt] >>
  `body_inv tops ctx c cx` by metis_tac[body_inv_same_frame] >>
  `frame_ret_ok_mem d ctx func cx RetQ c ret_ty` by
    metis_tac[frame_ret_ok_mem_same_frame] >>
  qpat_x_assum `!s0 t. _ ==> body_stmts_mem_ok _ _` drule >>
  simp[body_stmts_mem_ok_def] >> disch_then irule >>
  metis_tac[call_evaluation_safe_append_right]
QED


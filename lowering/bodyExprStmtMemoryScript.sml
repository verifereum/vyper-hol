Theory bodyExprStmtMemory
Ancestors
  bodyExprPreFacts exprSimSource bodyMemoryPreds bodyMemoryDefs bodySim
  exprSimHypsDefs gasContext loweringPosts stmtSimDefs
  exprLoweringProps stmtLoweringProps stmtLoweringMono compileEnv
  supportedExprTraverse supportedStmtTraverse supportedStmts supportedExprs
  vyperTypeCallGraph vyperTypeCallStackSoundness vyperInterpreter
  vyperTypeSystem vyperState vyperAST list finite_map
  stmtMemory exprOpenMain

val _ = Parse.hide "body";

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
  rpt gen_tac >> strip_tac >> irule compile_expr_open_general >> metis_tac[]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_COMPOSITION_MEMORY_AUDIT OK\n"
     else raise Fail "body composition inherited admission"
  end) [body_expr_stmt_mem_case];

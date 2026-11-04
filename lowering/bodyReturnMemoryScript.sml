(* Return-value composition through the body expression precondition. *)
Theory bodyReturnMemory
Ancestors
  bodyMemoryPreds bodyMemoryDefs bodySim bodySimStmtCases exprSimHyps
  supportedExprTraverse supportedStmtTraverse supportedStmts
  vyperInterpreter vyperTypeSystem vyperState vyperAST vyperTypeCallGraph

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

val () =
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag body_return_mem_ok)
  in if null axioms andalso null (Thm.hyp body_return_mem_ok) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_RETURN_MEMORY_AUDIT OK\n"
     else raise Fail "body return memory inherited admission"
  end;

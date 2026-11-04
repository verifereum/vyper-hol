(* A source pass and an empty list compile to the same counted fragment. *)
Theory stmtSimPass
Ancestors
  stmtSimDefs stmtSimZero loweringPosts stmtLowering emitHelper
  compileEnv vyperInterpreter vyperState

Theorem compile_pass_frag:
  !ctx func cx lctx RetQ cenv ty es.
    stmt_frag ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty Pass)
      (eval_stmt cx Pass) es
Proof
  rpt gen_tac >>
  `eval_stmt cx Pass = eval_stmts cx []` by
    simp[FUN_EQ_THM, evaluate_def, return_def] >>
  `stmt_env cenv lctx ty Pass = stmts_env cenv lctx ty []` by
    simp[FUN_EQ_THM, stmt_env_def, stmts_env_def, declare_stmt_local_def,
         comp_bind_def, comp_ignore_bind_def, compile_stmt_def, comp_return_def] >>
  simp[stmt_frag_nil]
QED

Theorem compile_pass_frag_mem:
  !d ctx func cx lctx RetQ cenv ty es.
    stmt_frag_mem d ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty Pass)
      (eval_stmt cx Pass) es
Proof
  rpt gen_tac >>
  `eval_stmt cx Pass = eval_stmts cx []` by
    simp[FUN_EQ_THM, evaluate_def, return_def] >>
  `stmt_env cenv lctx ty Pass = stmts_env cenv lctx ty []` by
    simp[FUN_EQ_THM, stmt_env_def, stmts_env_def, declare_stmt_local_def,
         comp_bind_def, comp_ignore_bind_def, compile_stmt_def, comp_return_def] >>
  simp[stmt_frag_nil_mem]
QED

val () =
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag compile_pass_frag_mem)
  in
    if null axioms andalso null (Thm.hyp compile_pass_frag_mem) andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then
      print "STMT_PASS_MEM_AUDIT compile_pass_frag_mem OK\n"
    else raise Fail "compile_pass_frag_mem: admitted proof dependency"
  end;

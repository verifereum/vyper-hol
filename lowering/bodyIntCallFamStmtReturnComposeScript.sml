(* Counted composition of a forced expression and its terminal return. *)
Theory bodyIntCallFamStmtReturnCompose
Ancestors
  gasSummaryCompose gasSummary fragGasMode stmtSimReturn vyperInterpreter vyperState

Theorem forced_return_marked_exec:
  gas_marked_exec F (ctx,func)
    (bind (eval_expr cx e) (read_result cx)) (es,s) marks (INL v) mid (OK t) /\
  gas_path ctx func t k r ==>
  gas_marked_exec F (ctx,func) (eval_stmt cx (Return (SOME e))) (es,s)
    (marks ++ REPLICATE k F) (INR (ReturnException v)) mid r
Proof
  strip_tac >> rewrite_tac[REWRITE_RULE [GSYM FUN_EQ_THM] eval_return_forced] >>
  pure_rewrite_tac[ETA_THM] >> irule gas_marked_exec_bind_normal >>
  goal_assum (drule_at Any) >>
  irule gas_marked_exec_no_source_read >>
  simp[raise_def, gas_marked_path_def]
QED

(* Memory case of the body induction (bodyMemory's body_mem_mutual): append. *)
Theory bodyMemAppend
Ancestors
  bodyMemoryPreds bodyMemAppendAdapter supportedStmts supportedExprs

Theorem body_append_mem_case:
  !cx t e.
    (!s'' p t'. eval_target_place cx t s'' = (INL p,t') ==> body_expr_mem_ok cx e) /\
    body_base_target_mem_ok cx t ==>
    body_stmt_mem_ok cx (Append t e)
Proof
  rpt strip_tac >> Cases_on `?nid. t = TopLevelNameTarget nid`
  >- (gvs[] >> Cases_on `nid` >>
      rw[body_stmt_mem_ok_def, supported_stmt_def, supported_append_target_def] >>
      irule body_append_storage_fragment_mem >> metis_tac[supported_expr_def]) >>
  Cases_on `t` >> gvs[] >>
  rw[body_stmt_mem_ok_def, supported_stmt_def, supported_append_target_def]
QED

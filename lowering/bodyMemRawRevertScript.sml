(* Memory case of the body induction (bodyMemory's body_mem_mutual):
   raw_revert. *)
Theory bodyMemRawRevert
Ancestors
  bodyMemoryPreds bodyMemRawRevertCompose exprSimAbortMemory
  exprSimRawRevertCore exprSimHypsDefs exprSimDefs exprSimHyps
  vyperTypeSystem exprLoweringProps compileEnv vyperAST vyperState

Theorem body_raw_revert_mem_case:
  !cx v22 es v23.
    body_exprs_mem_ok cx es ==> body_expr_mem_ok cx (Call v22 RawRevert es v23)
Proof
  rpt gen_tac >> disch_tac >> rewrite_tac[body_expr_mem_ok_def] >>
  rpt gen_tac >> strip_tac >>
  drule raw_revert_pre_arg >> strip_tac >> gvs[] >>
  `expr_sim_mem ctx func cenv cx (expr_type e) e es'` by
    (gvs[body_exprs_mem_ok_def, body_expr_mem_ok_def] >> metis_tac[]) >>
  `expr_vv_sim_mem ctx func cenv cx ty (Call v22 RawRevert [e] v23) es'` by
    (irule raw_revert_vv_sim_mem >> simp[] >> metis_tac[]) >>
  simp[] >> irule expr_sim_mem_of_aborting_vv >> simp[] >>
  rpt gen_tac >> simp[eval_raw_revert_action, bind_def, raise_def, AllCaseEqs()]
QED

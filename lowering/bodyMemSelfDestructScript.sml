(* Memory case of the body induction (bodyMemory's body_mem_mutual):
   selfdestruct. *)
Theory bodyMemSelfDestruct
Ancestors
  bodyMemoryPreds exprSimSelfDestructMem exprSimSelfDestruct
  exprSimAbortMemory exprSimHypsDefs exprSimDefs exprSimMemDefs
  vyperAST vyperState

Theorem body_selfdestruct_mem_case:
  !cx v24 es v25.
    body_exprs_mem_ok cx es ==>
    body_expr_mem_ok cx (Call v24 SelfDestructTarget es v25)
Proof
  rpt gen_tac >> disch_tac >> (rpt gen_tac >> match_mp_tac body_expr_mem_ok_intro >>
   conj_tac >- (rpt strip_tac >> gvs[])) >>
  rpt gen_tac >> strip_tac >>
  drule selfdestruct_pre_arg >> strip_tac >> gvs[] >>
  `expr_sim_mem ctx func cenv cx (expr_type e) e es'` by
    (gvs[body_exprs_mem_ok_def, body_expr_mem_ok_def] >> metis_tac[]) >>
  `expr_vv_sim_mem ctx func cenv cx ty
     (Call v24 SelfDestructTarget [e] v25) es'` by
    (irule selfdestruct_vv_sim_mem >> gvs[]) >>
  simp[] >> irule expr_sim_mem_of_aborting_vv >>
  simp[eval_selfdestruct_raises]
QED

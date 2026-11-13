(* The forced memory judgment of a body expression from its value one:
   exprSimMemUnwrap's expr_sim_mem_of_vv_sim_mem with the typing premises
   discharged by expr_body_pre. *)
Theory bodyExprForceMemory
Ancestors
  exprSimMemUnwrap exprSimMemDefs exprSimHyps exprSimDefs exprLowering
  loweringPosts

Theorem body_expr_sim_mem_of_vv_sim_mem:
  !ctx func cenv cx env ty e es.
    post_value_type cenv e = expr_type e /\
    expr_body_pre cenv cx env e es /\
    expr_vv_sim_mem ctx func cenv cx ty e es /\
    (!sa t op sb. compile_expr cenv ty e sa = (StackValue t op, sb) ==>
                  is_word_type (expr_type e)) ==>
    expr_sim_mem ctx func cenv cx ty e es
Proof
  rpt strip_tac >> irule expr_sim_mem_of_vv_sim_mem >> simp[] >>
  drule expr_body_pre_type_evaluates >>
  simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >> drule_all expr_body_pre_copy_ok >> simp[]
QED

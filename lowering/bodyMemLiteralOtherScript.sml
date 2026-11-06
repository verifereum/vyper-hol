(* Memory case of the body induction (bodyMemory's body_mem_mutual): a literal
   of a non-word type (bodyLiteralForceMemory's body_literal_word_mem_case has
   the word case). *)
Theory bodyMemLiteralOther
Ancestors
  bodyMemoryPreds bodyLiteralBufferMemory exprSimHypsDefs vyperTypeCallGraph

Theorem body_literal_other_mem_case:
  !cx ann l. ~is_word_type ann ==> body_expr_mem_ok cx (Literal ann l)
Proof
  rpt gen_tac >> strip_tac >> pure_rewrite_tac[body_expr_mem_ok_def] >>
  rpt gen_tac >> strip_tac >>
  `expr_sim_pre cenv cx env (Literal ann l) es` by
    gvs[expr_sim_pre_def, expr_body_pre_def, int_calls_expr_def] >>
  drule_all literal_other_body_mem >> simp[]
QED

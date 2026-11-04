(* Compiler growth, independent of argument readiness and operand safety. *)
Theory stmtSimLogArgsGrowth
Ancestors
  stmtSimLogArgs exprLoweringProps loweringSlice compileEnv

Theorem compile_log_eval_all_grows:
  !args sa xs sb.
    compile_log_eval_all cenv args sa = (xs,sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id
Proof
  Induct
  >- simp[compile_log_eval_all_nil, cs_extends_refl] >>
  rpt gen_tac >> simp[compile_log_eval_all_cons] >> strip_tac >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  metis_tac[cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]
QED

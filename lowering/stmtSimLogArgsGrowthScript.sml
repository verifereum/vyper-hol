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
  cheat
QED

Theory bodyFullBopBytestringIntervals
Ancestors
  exprBopLowering exprBopSimProps exprLoweringProps bytestringHashProps fragExec
  exprLowering compileEnv
Libs pairLib

Theorem bop_bytestring_selected_code_intervals:
  (bop = Eq \/ bop = NotEq) /\ is_bytestring_type (expr_type e1) /\
  expr_type e2 = expr_type e1 /\
  lower_value compile_expr cenv ty (Builtin ann (Bop bop) [e1;e2]) sa = (op,sb) /\
  fn_has_code sa sb func /\
  (case bytestring_literal_hash e1 of
     NONE => compile_bytestring_hash (FST (lower_value compile_expr cenv (expr_type e1) e1 sa))
       (SND (lower_value compile_expr cenv (expr_type e1) e1 sa))
   | SOME digest => (Lit digest,sa)) = (h1,sh1) /\
  (case bytestring_literal_hash e2 of
     NONE => compile_bytestring_hash (FST (lower_value compile_expr cenv (expr_type e2) e2 sh1))
       (SND (lower_value compile_expr cenv (expr_type e2) e2 sh1))
   | SOME digest => (Lit digest,sh1)) = (h2,sh2) ==>
  cs_extends sa sh1 /\ sa.cs_next_var <= sh1.cs_next_var /\
  cs_extends sh1 sh2 /\ sh1.cs_next_var <= sh2.cs_next_var /\
  cs_extends sh2 sb /\ fn_has_code sa sh1 func /\
  fn_has_code sh1 sh2 func /\ fn_has_code sh2 sb func /\
  (!m cb. bytestring_literal_hash e1 = NONE /\
    lower_value compile_expr cenv (expr_type e1) e1 sa = (m,cb) ==>
    fn_has_code sa cb func) /\
  (!m cb. bytestring_literal_hash e2 = NONE /\
    lower_value compile_expr cenv (expr_type e2) e2 sh1 = (m,cb) ==>
    fn_has_code sh1 cb func)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  ` (if bop = Eq then emit_op EQ [h1;h2] sh2
     else let (q,sm) = emit_op EQ [h1;h2] sh2 in emit_op ISZERO [q] sm) = (op,sb)` by
    (gvs[lower_value_bytestring_compare, pairTheory.UNCURRY]) >>
  drule comparison_digest_shape >> strip_tac >>
  Cases_on `bytestring_literal_hash e1` >>
  Cases_on `bytestring_literal_hash e2` >>
  Cases_on `lower_value compile_expr cenv (expr_type e1) e1 sa` >>
  Cases_on `lower_value compile_expr cenv (expr_type e1) e2 sh1` >> gvs[] >>
  imp_res_tac (cj 2 compile_expr_grows) >>
  imp_res_tac compile_bytestring_hash_shape >>
  fs[ci_mono_def] >> rpt strip_tac >> gvs[] >>
  imp_res_tac cs_extends_trans >>
  imp_res_tac arithmeticTheory.LESS_EQ_TRANS >>
  imp_res_tac fn_has_code_split >> simp[cs_extends_refl]
QED

Theory bodyPtrTypeBuiltinsCastPost
Ancestors
  exprSimConvertBytes exprSimHash exprSimExtract32Post exprLoweringProps
  loweringPosts exprLowering compileEnv venomState vyperAST
  bodyFieldMemoryProps

Theorem cast_convert_parent_post:
  expr_post ctx fn cenv cx e es ca sa s0 ee v (Var src) s /\
  post_value_type cenv e = expr_type e /\
  is_bytestring_type (expr_type e) /\ is_bytestring_type dst /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  evaluate_type (get_tenv cx) dst = SOME tout /\ value_has_type tv v /\
  convert_result cx (expr_type e) dst v = INL vout /\
  (t with vs_vars := s.vs_vars) = s /\
  (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s) /\
  lookup_var src s = SOME w /\ not_fresh_at sa src /\
  local_ptrs_reserved cenv sa /\
  ca.cs_next_var <= sa.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id ==>
  expr_post ctx fn cenv cx (TypeBuiltin dst Convert dst [e]) es ca sb s0
    (ee with gas_obs := []) vout (Var src) (t with vs_inst_idx := j)
Proof
  strip_tac >>
  `stmt_state_rel ctx fn cenv cx ee s` by fs[expr_post_def] >>
  `stmt_state_rel ctx fn cenv cx ee t` by
    (irule hash_readonly_state_rel >> metis_tac[]) >>
  `t = s with vs_vars := t.vs_vars` by
    (qpat_x_assum `(t with vs_vars := _) = s` (fn eq => once_rewrite_tac[GSYM eq]) >> simp[]) >>
  `expr_post ctx fn cenv cx e es ca sb s0 ee v (Var src) t` by
    (irule convert_readonly_expr_post >>
     simp[] >> qexistsl_tac [`w`,`s`,`sa`,`Var src`] >>
     simp[eval_operand_def] >>
     qpat_x_assum `t = s with vs_vars := _` (fn eq => once_rewrite_tac[eq]) >> simp[]) >>
  simp[extract32_expr_post_end_gas_obs] >>
  irule convert_bytestring_expr_post >>
  simp[expr_type_def] >> qexistsl_tac [`e`,`tv`,`v`] >> simp[] >>
  simp[body_field_expr_post_inst_idx]
QED

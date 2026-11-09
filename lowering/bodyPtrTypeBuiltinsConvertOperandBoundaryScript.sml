Theory bodyPtrTypeBuiltinsConvertOperandBoundary
Ancestors
  bodyPtrPreds exprSimConvert loweringPosts exprLoweringProps
  bodyPtrTypeBuiltinsMarkedBind gasExemptCert

Theorem convert_operand_post_type:
  ~((?a f args drv. e = Call a (IntCall f) args drv) /\
    lowered_value_type cenv e <> expr_type e) ==>
  post_value_type cenv e = expr_type e
Proof
  strip_tac >> Cases_on `lowered_value_type cenv e = expr_type e`
  >- metis_tac[post_value_type_lowered] >>
  irule post_value_type_not_int_call >> metis_tac[]
QED

Theorem convert_operand_ptr_entry:
  body_exprs_ptr_ok cx [e] /\ body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (TypeBuiltin ann Convert typ [e]) es ==>
  ann = typ /\ valid_conversion (expr_type e) typ /\
  expr_body_pre cenv cx env e es /\
  expr_sim_ptr d ctx PG func cenv cx (expr_type e) e es /\
  expr_vv_sim_ptr d ctx PG func cenv cx (expr_type e) e es
Proof
  strip_tac >> drule expr_body_pre_convert >> strip_tac >> gvs[] >>
  fs[body_exprs_ptr_ok_def] >>
  qpat_x_assum `body_expr_ptr_ok _ _` mp_tac >>
  simp[body_expr_ptr_ok_def] >> metis_tac[]
QED

Theorem convert_operand_marked_bind:
  gas_outcome_ptr D tops (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\res ee G tn t. ?v. res = INL v /\ Q v ee G tn t)
    (\res ee gt r. ?exc. res = INR exc /\ R (INR exc) ee gt r) /\
  (!marks v mid G tn t.
    gas_marked_exec_ptr D (ctx,func) PG
      (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
      marks (INL v) mid G tn (OK t) /\
    Q v (mid with gas_obs := []) G tn t ==>
    gas_outcome_ptr D tops (ctx,func) PG
      (\ee. (convert_result cx (expr_type e) typ v,ee))
      (mid with gas_obs := [],t,G,tn) Q' R) ==>
  gas_outcome_ptr D tops (ctx,func) PG
    (bind (eval_expr cx (TypeBuiltin ann Convert typ [e])) (read_result cx))
    (es,s0,G0,tn0) Q' R
Proof
  strip_tac >> rewrite_tac[eval_expr_convert_action] >>
  irule gas_outcome_ptr_marked_bind >> simp[] >> conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
      goal_assum (drule_at Any) >> BETA_TAC >>
      qpat_x_assum `gas_exempt_cert _ _ _ _ _ _ _ _` (ACCEPT_TAC o BETA_RULE)) >>
  conj_tac
  >- simp[gas_exempt_cert_error_value] >>
  qexists_tac `Q` >> simp[] >> metis_tac[]
QED

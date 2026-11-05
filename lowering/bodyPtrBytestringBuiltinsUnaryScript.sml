Theory bodyPtrBytestringBuiltinsUnary
Ancestors
  bodyPtrBytestringBuiltinsInterfaces exprSimSource gasSummaryComposePtr
  gasExemptCert

Theorem unary_builtin_operand_sim_ptr:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Builtin ann bt [e]) es /\
  body_exprs_ptr_ok cx [e] /\
  expr_type e <> BaseT (BytesT (Dynamic 24576)) ==>
  expr_sim_ptr d ctx PG func cenv cx (expr_type e) e es
Proof
  strip_tac >>
  `expr_body_pre cenv cx env e es` by
    (irule expr_body_pre_builtin_typed_arg >>
     fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
     qexistsl_tac [`ann`, `[e]`, `bt`, `es`] >> simp[]) >>
  drule body_exprs_ptr_head >>
  simp[bodyPtrPredsTheory.body_expr_ptr_ok_def] >>
  metis_tac[]
QED

Theorem gas_outcome_ptr_value_bind:
  gas_outcome_ptr D tops (ctx, func) PG
    (source : evaluation_state -> value evaluation_result)
    (es, s0, G0, tn0) P E /\
  (!res ee G tn t. P res ee G tn t ==>
    ?v. res = INL v /\
      gas_outcome_ptr D tops (ctx, func) PG (next v) (ee, t, G, tn) Q R) /\
  (!res ee gt r. E res ee gt r ==>
    ?exc. res = INR exc /\ R (INR exc) ee gt r) ==>
  gas_outcome_ptr D tops (ctx, func) PG (bind source next)
    (es, s0, G0, tn0) Q R
Proof
  strip_tac >> irule gas_outcome_ptr_bind >> rpt conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
      goal_assum (drule_at Any) >> simp[])
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[])
  >> irule gas_outcome_ptr_conseq >>
  qexistsl_tac [`P`, `E`] >> simp[]
QED

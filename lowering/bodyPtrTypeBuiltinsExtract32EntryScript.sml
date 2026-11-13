Theory bodyPtrTypeBuiltinsExtract32Entry
Ancestors
  bodyPtrTypeBuiltinsIndexEntry bodyPtrTypeBuiltinsOperands
  exprSimExtract32Source gasSummaryComposePtr gasSummary exprSimHypsDefs
  bodyPtrPreds bodyPtrDefs vyperState

Theorem extract32_marked_offset_ptr_sim:
  body_inv tops ctx cenv cx /\ body_exprs_ptr_ok cx [src;off] /\
  expr_body_pre cenv cx env (TypeBuiltin ann Extract32 typ [src;off]) es /\
  expr_type src = BaseT (BytesT (Dynamic m)) /\
  gas_marked_exec_ptr D (ctx,func) PG
    (vyperState$bind (eval_expr cx src) (read_result cx)) (es,s0,G0,tn0)
    marks (INL v) mid G tn (OK t) ==>
  expr_sim_inv cenv cx env (mid with gas_obs := []) /\
  expr_body_pre cenv cx env off (mid with gas_obs := []) /\
  (?bs. v = BytesV bs /\ LENGTH bs <= m) /\
  expr_sim_ptr d ctx PG func cenv cx ty off (mid with gas_obs := [])
Proof
  strip_tac >> drule gas_marked_exec_ptr_exec >> strip_tac >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) extract32_marked_source_typed) >> strip_tac >> simp[] >>
  `vyperState$bind (eval_expr cx src) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
       (INL v,mid with gas_obs := [])` by
    (gvs[gas_marked_exec_def] >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `body_expr_ptr_ok cx off` by
    (irule body_exprs_ptr_ok_second >> goal_assum (drule_at Any) >> metis_tac[]) >>
  irule body_expr_ptr_ok_sim >> goal_assum (drule_at Any) >> metis_tac[]
QED

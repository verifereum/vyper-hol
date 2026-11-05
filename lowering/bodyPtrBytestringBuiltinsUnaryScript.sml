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

Theorem expr_sim_ptr_suffix:
  expr_sim_ptr d ctx PG func cenv cx ty e es /\
  lower_value compile_expr cenv ty e sa = (op, sm) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\
  ghost_inv d cenv cx es G0 tn0 s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!exc ee gt r. expr_exit (INR exc : value + exception) r ==>
    R (INR exc) ee gt r) /\
  (!v ee G tn t.
    expr_post ctx func cenv cx e es sa sm s0 ee v op t /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    ghost_inv d cenv cx ee G tn t /\
    ptr_val_ok cx (expr_type e) v op G tn t /\
    (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e op G t) /\
    ghost_kept cenv es sa G0 tn0 s0 G tn ==>
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx, func) PG
      (k v) (ee, t, G, tn) Q R) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx, func) PG
    (bind (bind (eval_expr cx e) (read_result cx)) k)
    (es, s0, G0, tn0) Q R
Proof
  strip_tac >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.expr_sim_ptr_def]) >>
  disch_then drule_all >> strip_tac >>
  irule gas_outcome_ptr_value_bind >>
  first_assum (irule_at (Pat `gas_outcome_ptr _ _ _ _ _ _ _ _`)) >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `res` >>
      gvs[exprSimDefsTheory.expr_exit_INL] >> metis_tac[]) >>
  rpt strip_tac >> Cases_on `res` >>
  gvs[exprSimDefsTheory.expr_exit_INL] >> metis_tac[]
QED

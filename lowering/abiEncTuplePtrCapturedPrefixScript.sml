(* Successful vv evaluation before owned tuple-argument materialization. *)
Theory abiEncTuplePtrCapturedPrefix
Ancestors
  abiEncodeArgsSim bodyPtrBytestringBuiltinsEval bodyPtrDefs
  gasSummaryComposePtr fragGasPathPtr gasExemptCert

Theorem abi_args_result_bind_ptr:
  gas_outcome_ptr D tops (ctx,func) PG
    (source : evaluation_state -> eval_result evaluation_result)
    (es,s0,G0,tn0) P E /\
  (!res ee G tn t. P res ee G tn t ==>
    ?v. res = INL v /\
      gas_outcome_ptr D tops (ctx,func) PG (next v) (ee,t,G,tn) Q R) /\
  (!res ee gt r. E res ee gt r ==>
    ?exc. res = INR exc /\ R (INR exc) ee gt r) ==>
  gas_outcome_ptr D tops (ctx,func) PG (bind source next)
    (es,s0,G0,tn0) Q R
Proof
  strip_tac >> irule gas_outcome_ptr_bind >> rpt conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_result >>
      goal_assum (drule_at Any) >> simp[])
  >- (rpt strip_tac >> irule gas_exempt_cert_error_result >> simp[]) >>
  irule gas_outcome_ptr_conseq >> qexistsl [`P`, `E`] >> simp[]
QED

Theorem abi_args_vv_eval_suffix_ptr:
  expr_vv_sim_ptr d ctx PG func ce cx (expr_type e) e es /\
  compile_expr ce (expr_type e) e sa = (vv,mid) /\
  fn_has_code sa mid func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
  stmt_state_rel ctx func ce cx es s0 /\ ghost_inv d ce cx es G0 tn0 s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!exc ee gt r. expr_exit (INR exc : type_value + exception) r ==>
    R (INR exc) ee gt r) /\
  (!tv v ee G tn t.
    vv_post ctx func ce cx e es sa mid s0 ee tv vv t /\
    read_result cx tv ee = (INL v,ee) /\
    t.vs_current_bb = mid.cs_current_bb /\
    t.vs_inst_idx = LENGTH mid.cs_current_insts /\ ~t.vs_halted /\
    ghost_inv d ce cx ee G tn t /\
    ptr_vv_ok cx (post_value_type ce e) tv vv ee G tn t /\
    (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type ce e) ==>
      ptr_buf_ok ce e op G t) /\
    (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok ce e p.ptr_operand G t) /\
    ghost_kept ce es sa G0 tn0 s0 G tn /\
    (?marks ee0. ee = ee0 with gas_obs := [] /\
      !tail. eval_expr cx e
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
        (INL tv,ee0 with gas_obs := tail)) ==>
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
      (k tv) (ee,t,G,tn) Q R) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (bind (eval_expr cx e) k) (es,s0,G0,tn0) Q R
Proof
  strip_tac >>
  qpat_x_assum `expr_vv_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_ptr_def]) >>
  disch_then drule_all >> strip_tac >>
  dxrule gas_outcome_ptr_eval_evidence >> strip_tac >>
  irule abi_args_result_bind_ptr >>
  first_assum (irule_at (Pat `gas_outcome_ptr _ _ _ _ _ _ _ _`)) >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `res` >>
      gvs[exprSimDefsTheory.expr_exit_INL] >>
      first_x_assum irule >> simp[] >> metis_tac[abi_args_vv_post_read]) >>
  rpt strip_tac >> Cases_on `res` >>
  gvs[exprSimDefsTheory.expr_exit_INL] >>
  first_x_assum irule >> simp[] >>
  fs[stmtSimPropsTheory.expr_exit_INR_type]
QED

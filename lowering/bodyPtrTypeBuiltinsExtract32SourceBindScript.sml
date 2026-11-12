Theory bodyPtrTypeBuiltinsExtract32SourceBind
Ancestors
  bodyPtrTypeBuiltinsExtract32Entry bodyPtrTypeBuiltinsMarkedBind
  bodyPtrTypeBuiltinsOperands exprSimExtract32Source
  bodyPtrDefs bodyPtrPreds exprSimHypsDefs vyperState

Theorem extract32_source_ptr_bind:
  body_inv tops ctx cenv cx /\ body_exprs_ptr_ok cx [src;off] /\
  expr_body_pre cenv cx env (TypeBuiltin ann Extract32 typ [src;off]) es /\
  expr_type src = BaseT (BytesT (Dynamic m)) /\
  lower_value compile_expr cenv (expr_type src) src sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (vyperState$bind (eval_expr cx src) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\ ghost_inv d cenv cx es G0 tn0 s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!marks bs mid G tn t.
    gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG
      (vyperState$bind (eval_expr cx src) (read_result cx))
      (es,s0,G0,tn0) marks (INL (BytesV bs)) mid G tn (OK t) /\
    LENGTH bs <= m /\ expr_sim_inv cenv cx env (mid with gas_obs := []) /\
    expr_body_pre cenv cx env off (mid with gas_obs := []) /\
    expr_sim_ptr d ctx PG func cenv cx ty off (mid with gas_obs := []) /\
    expr_post ctx func cenv cx src es sa sb s0
      (mid with gas_obs := []) (BytesV bs) op t /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ghost_inv d cenv cx (mid with gas_obs := []) G tn t /\
    ptr_val_ok cx (post_value_type cenv src) (BytesV bs) op G tn t /\
    (~is_word_type (post_value_type cenv src) ==> ptr_buf_ok cenv src op G t) /\
    ghost_kept cenv es sa G0 tn0 s0 G tn ==>
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
      (next (BytesV bs)) (mid with gas_obs := [],t,G,tn) Q
      (\res ee gt r. expr_exit res r)) /\
  (!marks err ee leaf fstate.
    gas_exempt_cert F (cx_tops cx) (ctx,func)
      (ignore_bind (vyperState$bind (eval_expr cx src) (read_result cx)) (return ()))
      (es,s0) marks (err,ee) (leaf,fstate) ==>
    gas_exempt_cert F (cx_tops cx) (ctx,func)
      (vyperState$bind (vyperState$bind (eval_expr cx src) (read_result cx))
        (\v. ignore_bind (next v) (return ())))
      (es,s0) marks (err,ee) (leaf,fstate)) /\
  (!left v mid t right err ee leaf fstate.
    gas_marked_exec F (ctx,func)
      (vyperState$bind (eval_expr cx src) (read_result cx))
      (es,s0) left (INL v) mid (OK t) /\
    gas_exempt_cert F (cx_tops cx) (ctx,func) (ignore_bind (next v) (return ()))
      (mid with gas_obs := [],t) right (err,ee) (leaf,fstate) ==>
    gas_exempt_cert F (cx_tops cx) (ctx,func)
      (vyperState$bind (vyperState$bind (eval_expr cx src) (read_result cx))
        (\v. ignore_bind (next v) (return ())))
      (es,s0) (left ++ right) (err,ee) (leaf,fstate)) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (vyperState$bind (vyperState$bind (eval_expr cx src) (read_result cx)) next)
    (es,s0,G0,tn0) Q (\res ee gt r. expr_exit res r)
Proof
  strip_tac >>
  `expr_body_pre cenv cx env src es` by
    (irule expr_body_pre_type_builtin_arg >>
     conj_tac >- gvs[expr_body_pre_def] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `body_expr_ptr_ok cx src` by gvs[body_exprs_ptr_ok_def] >>
  `expr_sim_ptr d ctx PG func cenv cx (expr_type src) src es` by
    (irule body_expr_ptr_ok_sim >> goal_assum (drule_at Any) >> metis_tac[]) >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ src _`
    (mp_tac o REWRITE_RULE [expr_sim_ptr_def]) >>
  disch_then drule_all >> strip_tac >>
  irule gas_outcome_ptr_marked_bind >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `\v ee G tn t.
    expr_post ctx func cenv cx src es sa sb s0 ee v op t /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ghost_inv d cenv cx ee G tn t /\
    ptr_val_ok cx (post_value_type cenv src) v op G tn t /\
    (~is_word_type (post_value_type cenv src) ==> ptr_buf_ok cenv src op G t) /\
    ghost_kept cenv es sa G0 tn0 s0 G tn` >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      `expr_sim_inv cenv cx env (mid with gas_obs := []) /\
       expr_body_pre cenv cx env off (mid with gas_obs := []) /\
       (?bs. v = BytesV bs /\ LENGTH bs <= m) /\
       expr_sim_ptr d ctx PG func cenv cx ty off (mid with gas_obs := [])` by
        (irule extract32_marked_offset_ptr_sim >> metis_tac[]) >>
      gvs[] >> first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
      metis_tac[]) >>
  irule gasSummaryComposePtrTheory.gas_outcome_ptr_conseq >>
  goal_assum (drule_at Any) >> simp[] >> rpt strip_tac >>
  Cases_on `res` >> gvs[exprSimDefsTheory.expr_exit_INL] >>
  metis_tac[stmtSimPropsTheory.expr_exit_INR_type]
QED

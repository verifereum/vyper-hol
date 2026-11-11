Theory bodyPtrTypeBuiltinsExtract32OffsetBind
Ancestors
  bodyPtrTypeBuiltinsExtract32Saved bodyPtrTypeBuiltinsMarkedBind
  exprSimExtract32Source exprSimSource gasSummaryComposePtr gasSummary
  bodyPtrDefs stmtSimProps vyperState

Theorem extract32_marked_offset_value:
  expr_body_pre cenv cx env off es /\ is_uint_type (expr_type off) /\
  gas_marked_exec_ptr D (ctx,func) PG
    (vyperState$bind (eval_expr cx off) (read_result cx))
    (es,s,G,tn) marks (INL v) mid H th (OK t) ==>
  ?i. v = IntV i /\ 0 <= i
Proof
  strip_tac >> drule gas_marked_exec_ptr_exec >> strip_tac >>
  `vyperState$bind (eval_expr cx off) (read_result cx)
    (es with gas_obs := gas_explicit marks s.vs_gas_readings) =
      (INL v,mid with gas_obs := [])` by
    (gvs[gas_marked_exec_def] >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  irule (CONV_RULE (DEPTH_CONV ETA_CONV) extract32_offset_value) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem extract32_offset_ptr_bind:
  expr_sim_ptr d ctx PG func cenv cx ty off es /\
  expr_body_pre cenv cx env off es /\ is_uint_type (expr_type off) /\
  lower_value compile_expr cenv ty off sb = (offop,sc') /\
  fn_has_code sb sc' func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sb /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x) /\
  gas_admissible (vyperState$bind (eval_expr cx off) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  expr_type src = BaseT (BytesT (Dynamic m)) /\
  expr_post ctx func cenv cx src es0 sa sb s0 es (BytesV bs) (Var sv) s /\
  ptr_mem_ok cx (expr_type src) (BytesV bs) (Var sv) G tn s /\
  expr_sim_inv cenv cx env es /\
  not_fresh_at sb sv /\ not_fresh_at sb len /\ not_fresh_at sb data /\
  eval_operand (Var sv) s = SOME (n2w p) /\
  eval_operand (Var len) s = SOME (n2w (LENGTH bs)) /\
  eval_operand (Var data) s = SOME (n2w (p+32)) /\
  op_taint tn (Var sv) = {} /\ op_taint tn (Var len) = {} /\
  op_prov G (Var len) = NONE /\
  (!n. 0 < LENGTH bs /\ n <= LENGTH bs ==> ptr_covers G tn data s n) /\
  (!marks i mid H th t.
    gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG
      (vyperState$bind (eval_expr cx off) (read_result cx))
      (es,s,G,tn) marks (INL (IntV i)) mid H th (OK t) /\ 0 <= i /\
    expr_post ctx func cenv cx off es sb sc' s
      (mid with gas_obs := []) (IntV i) offop t /\
    t.vs_current_bb = sc'.cs_current_bb /\ t.vs_inst_idx = LENGTH sc'.cs_current_insts /\
    ghost_inv d cenv cx (mid with gas_obs := []) H th t /\
    ptr_val_ok cx (post_value_type cenv off) (IntV i) offop H th t /\
    (~is_word_type (post_value_type cenv off) ==> ptr_buf_ok cenv off offop H t) /\
    ghost_kept cenv es sb G tn s H th /\
    ptr_mem_ok cx (expr_type src) (BytesV bs) (Var sv) H th t /\
    eval_operand (Var sv) t = SOME (n2w p) /\
    eval_operand (Var len) t = SOME (n2w (LENGTH bs)) /\
    eval_operand (Var data) t = SOME (n2w (p+32)) /\
    op_taint th (Var sv) = {} /\ op_taint th (Var len) = {} /\
    op_prov H (Var len) = NONE /\
    (!n. 0 < LENGTH bs /\ n <= LENGTH bs ==> ptr_covers H th data t n) ==>
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
      (next (IntV i)) (mid with gas_obs := [],t,H,th) Q
      (\res ee gt r. expr_exit res r)) /\
  (!marks err ee leaf fstate.
    gas_exempt_cert F (cx_tops cx) (ctx,func)
      (ignore_bind (vyperState$bind (eval_expr cx off) (read_result cx)) (return ()))
      (es,s) marks (err,ee) (leaf,fstate) ==>
    gas_exempt_cert F (cx_tops cx) (ctx,func)
      (vyperState$bind (vyperState$bind (eval_expr cx off) (read_result cx))
        (\v. ignore_bind (next v) (return ())))
      (es,s) marks (err,ee) (leaf,fstate)) /\
  (!left v mid t right err ee leaf fstate.
    gas_marked_exec F (ctx,func)
      (vyperState$bind (eval_expr cx off) (read_result cx))
      (es,s) left (INL v) mid (OK t) /\
    gas_exempt_cert F (cx_tops cx) (ctx,func) (ignore_bind (next v) (return ()))
      (mid with gas_obs := [],t) right (err,ee) (leaf,fstate) ==>
    gas_exempt_cert F (cx_tops cx) (ctx,func)
      (vyperState$bind (vyperState$bind (eval_expr cx off) (read_result cx))
        (\v. ignore_bind (next v) (return ())))
      (es,s) (left ++ right) (err,ee) (leaf,fstate)) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (vyperState$bind (vyperState$bind (eval_expr cx off) (read_result cx)) next)
    (es,s,G,tn) Q (\res ee gt r. expr_exit res r)
Proof
  strip_tac >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_ptr_def]) >>
  disch_then drule_all >> strip_tac >>
  irule gas_outcome_ptr_marked_bind >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `\v ee H th t.
    expr_post ctx func cenv cx off es sb sc' s ee v offop t /\
    t.vs_current_bb = sc'.cs_current_bb /\ t.vs_inst_idx = LENGTH sc'.cs_current_insts /\
    ghost_inv d cenv cx ee H th t /\
    ptr_val_ok cx (post_value_type cenv off) v offop H th t /\
    (~is_word_type (post_value_type cenv off) ==> ptr_buf_ok cenv off offop H t) /\
    ghost_kept cenv es sb G tn s H th` >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      `?i. v = IntV i /\ 0 <= i` by
        (irule extract32_marked_offset_value >> metis_tac[]) >>
      gvs[] >>
      `ptr_mem_ok cx (expr_type src) (BytesV bs) (Var sv) G' tn' t /\
       eval_operand (Var sv) t = SOME (n2w p) /\
       eval_operand (Var len) t = SOME (n2w (LENGTH bs)) /\
       eval_operand (Var data) t = SOME (n2w (p+32)) /\
       op_taint tn' (Var sv) = {} /\ op_taint tn' (Var len) = {} /\
       op_prov G' (Var len) = NONE /\
       (!n. 0 < LENGTH bs /\ n <= LENGTH bs ==> ptr_covers G' tn' data t n)` by
        (irule extract32_saved_source_after_offset >> metis_tac[]) >>
      first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  irule gasSummaryComposePtrTheory.gas_outcome_ptr_conseq >>
  goal_assum (drule_at Any) >> simp[] >> rpt strip_tac >>
  Cases_on `res` >> gvs[exprSimDefsTheory.expr_exit_INL] >>
  metis_tac[expr_exit_INR_type]
QED

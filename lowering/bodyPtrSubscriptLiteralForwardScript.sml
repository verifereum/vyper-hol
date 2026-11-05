(* Stack forcing retains the actual prefix endpoint and ghost. *)
Theory bodyPtrSubscriptLiteralForward
Ancestors
  bodyPtrDefs loweringPosts gasSummaryComposePtr exprSimMemorySource
  vyperState ptrDiscipline

Theorem stack_read_post_ptr:
  vv_post ctx func cenv cx e es sa sb s0 ee tv (StackValue t op) s /\
  ptr_vv_ok cx (expr_type e) tv (StackValue t op) ee G tn s /\
  read_result cx tv ee = (INL v,ee) ==>
  expr_post ctx func cenv cx e es sa sb s0 ee v op s /\
  ptr_val_ok cx (expr_type e) v op G tn s
Proof
  strip_tac >>
  gvs[vv_post_def, vv_holds_def, vv_at_def, expr_post_def,
      ptr_vv_ok_def] >> first_assum ACCEPT_TAC
QED

Theorem unwrap_literal_word_prefix_ptr:
  gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG source
    (ei,si,Gi,tni) left (INL tv) ee G tn (OK s) /\
  vv_post ctx func cenv cx e es sa sb s0 ee tv (StackValue t (Lit w)) s /\
  ptr_vv_ok cx (expr_type e) tv (StackValue t (Lit w)) ee G tn s /\
  read_result cx tv ee = (INL v,ee) /\ ee.gas_obs = [] /\
  is_word_type (expr_type e) ==>
  gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG
    (vyperState$bind source (read_result cx))
    (ei,si,Gi,tni) left (INL v) ee G tn (OK s) /\
  expr_post ctx func cenv cx e es sa sb s0 ee v (Lit w) s /\
  ptr_val_ok cx (expr_type e) v (Lit w) G tn s /\
  op_prov G (Lit w) = NONE
Proof
  strip_tac >> drule_all stack_read_post_ptr >> strip_tac >>
  simp[op_prov_def] >>
  qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_marked_exec_ptr_def] >> strip_tac >>
  simp[gas_marked_exec_ptr_def] >> gen_tac >>
  simp[bind_def] >> metis_tac[read_result_gas_obs]
QED

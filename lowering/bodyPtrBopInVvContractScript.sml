Theory bodyPtrBopInVvContract
Ancestors bodyPtrBopInVvOutcome bodyPtrBopOperandContract

(* Transparent entry/post bundles are reused by the raw-vv adapter and the
   mixed operand consumer. They avoid duplicating the two buffer alternatives
   and the cursor/ghost interface in every nested continuation. *)
Definition membership_vv_entry_def:
  membership_vv_entry d ctx func cenv cx e es sa sb s G tn <=>
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sa x) /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
  stmt_state_rel ctx func cenv cx es s /\
  ghost_inv d cenv cx es G tn s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts
End

Definition membership_vv_post_def:
  membership_vv_post d ctx func cenv cx e es sa sb vv s G tn tv ee t H un <=>
  vv_post ctx func cenv cx e es sa sb s ee tv vv t /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ghost_inv d cenv cx ee H un t /\
  ptr_vv_ok cx (expr_type e) tv vv ee H un t /\
  (!t' op. vv = StackValue t' op /\ ~is_word_type (expr_type e) ==>
    ptr_buf_ok cenv e op H t) /\
  (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv e p.ptr_operand H t) /\
  ghost_kept cenv es sa G tn s H un
End

Theorem membership_vv_contract_ptr:
  expr_vv_sim_ptr d ctx PG func cenv cx ty e es /\
  compile_expr cenv ty e sa = (vv,sb) /\
  membership_vv_entry d ctx func cenv cx e es sa sb s0 G0 tn0 /\
  (!gs rr ee. eval_expr cx e (es with gas_obs := gs) = (rr,ee) ==> P rr ee) /\
  (!tv ee H un t.
    membership_vv_post d ctx func cenv cx e es sa sb vv s0 G0 tn0 tv ee t H un /\
    P (INL tv) ee /\ ee.gas_obs = [] /\ ~t.vs_halted ==>
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
      (next tv) (ee,t,H,un) Q (\res ee gt r. expr_exit res r)) /\
  (!marks err ee leaf fstate.
    gas_exempt_cert F (cx_tops cx) (ctx,func)
      (ignore_bind (eval_expr cx e) (return ()))
      (es,s0) marks (err,ee) (leaf,fstate) ==>
    gas_exempt_cert F (cx_tops cx) (ctx,func)
      (bind (eval_expr cx e) (\tv. ignore_bind (next tv) (return ())))
      (es,s0) marks (err,ee) (leaf,fstate)) /\
  (!left tv mid t right err ee leaf fstate.
    gas_marked_exec F (ctx,func) (eval_expr cx e)
      (es,s0) left (INL tv) mid (OK t) /\
    gas_exempt_cert F (cx_tops cx) (ctx,func)
      (ignore_bind (next tv) (return ()))
      (mid with gas_obs := [],t) right (err,ee) (leaf,fstate) ==>
    gas_exempt_cert F (cx_tops cx) (ctx,func)
      (bind (eval_expr cx e) (\tv. ignore_bind (next tv) (return ())))
      (es,s0) (left ++ right) (err,ee) (leaf,fstate)) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (bind (eval_expr cx e) next) (es,s0,G0,tn0)
    Q (\res ee gt r. expr_exit res r)
Proof
  rewrite_tac[membership_vv_entry_def, membership_vv_post_def, GSYM CONJ_ASSOC] >>
  MATCH_ACCEPT_TAC membership_vv_operand_outcome_ptr
QED

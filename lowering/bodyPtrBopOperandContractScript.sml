Theory bodyPtrBopOperandContract
Ancestors
  bodyPtrBopPairOutcome bodyPtrDefs gasSummaryComposePtr

(* Transparent bundles prevent duplicated entry/post contracts in nested CPS
   proofs. Neither bundle asserts a simulation or an execution outcome. *)
Definition bop_operand_entry_def:
  bop_operand_entry d ctx func cenv cx e es sa sb op s G tn <=>
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func cenv cx es s /\
  ghost_inv d cenv cx es G tn s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts
End

Definition bop_operand_post_def:
  bop_operand_post d ctx func cenv cx e es sa sb op s G tn v ee t H un <=>
  expr_post ctx func cenv cx e es sa sb s ee v op t /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  ghost_inv d cenv cx ee H un t /\
  ptr_val_ok cx (expr_type e) v op H un t /\
  (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e op H t) /\
  ghost_kept cenv es sa G tn s H un
End

Theorem bop_operand_contract_ptr:
  expr_sim_ptr d ctx PG func cenv cx ty e es /\
  lower_value compile_expr cenv ty e sa = (op,sb) /\
  bop_operand_entry d ctx func cenv cx e es sa sb op s0 G0 tn0 /\
  (!gs rr ee.
    bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (rr,ee)
    ==> P rr ee) /\
  (!v ee H un t.
    bop_operand_post d ctx func cenv cx e es sa sb op s0 G0 tn0 v ee t H un /\
    P (INL v) ee /\ ee.gas_obs = [] /\ ~t.vs_halted ==>
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
      (next v) (ee,t,H,un) Q (\res ee gt r. expr_exit res r)) /\
  (!marks err ee leaf fstate.
    gas_exempt_cert F (cx_tops cx) (ctx,func)
      (ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()))
      (es,s0) marks (err,ee) (leaf,fstate) ==>
    gas_exempt_cert F (cx_tops cx) (ctx,func)
      (bind (bind (eval_expr cx e) (read_result cx))
        (\v. ignore_bind (next v) (return ())))
      (es,s0) marks (err,ee) (leaf,fstate)) /\
  (!left v mid t right err ee leaf fstate.
    gas_marked_exec F (ctx,func) (bind (eval_expr cx e) (read_result cx))
      (es,s0) left (INL v) mid (OK t) /\
    gas_exempt_cert F (cx_tops cx) (ctx,func)
      (ignore_bind (next v) (return ()))
      (mid with gas_obs := [],t) right (err,ee) (leaf,fstate) ==>
    gas_exempt_cert F (cx_tops cx) (ctx,func)
      (bind (bind (eval_expr cx e) (read_result cx))
        (\v. ignore_bind (next v) (return ())))
      (es,s0) (left ++ right) (err,ee) (leaf,fstate)) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (bind (bind (eval_expr cx e) (read_result cx)) next)
    (es,s0,G0,tn0) Q (\res ee gt r. expr_exit res r)
Proof
  rewrite_tac[bop_operand_entry_def, bop_operand_post_def, GSYM CONJ_ASSOC] >>
  MATCH_ACCEPT_TAC bop_operand_outcome_ptr
QED

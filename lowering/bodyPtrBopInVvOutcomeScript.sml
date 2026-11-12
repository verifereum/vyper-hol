Theory bodyPtrBopInVvOutcome
Ancestors bodyPtrBopPairOutcome bodyPtrDefs gasSummaryComposePtr
  stmtSimProps exprSimDefs typedWordArgsFactsPtr

(* Raw value/place evaluation: unlike bop_operand_outcome_ptr this does not
   insert read_result into the compiled haystack evaluation. *)
Theorem membership_vv_operand_outcome_ptr:
  post_value_type cenv e = expr_type e ==>
  expr_vv_sim_ptr d ctx PG func cenv cx ty e es /\
  compile_expr cenv ty e sa = (vv,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\
  ghost_inv d cenv cx es G0 tn0 s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!gs rr ee. eval_expr cx e (es with gas_obs := gs) = (rr,ee) ==>
    P rr ee) /\
  (!tv ee G tn t.
    vv_post ctx func cenv cx e es sa sb s0 ee tv vv t /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ghost_inv d cenv cx ee G tn t /\
    ptr_vv_ok cx (expr_type e) tv vv ee G tn t /\
    (!t' op. vv = StackValue t' op /\ ~is_word_type (expr_type e) ==>
      ptr_buf_ok cenv e op G t) /\
    (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok cenv e p.ptr_operand G t) /\
    ghost_kept cenv es sa G0 tn0 s0 G tn /\
    P (INL tv) ee /\ ee.gas_obs = [] /\ ~t.vs_halted ==>
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
      (next tv) (ee,t,G,tn) Q (\res ee gt r. expr_exit res r)) /\
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
  strip_tac >> strip_tac >>
  irule gas_outcome_ptr_bind >> simp[] >>
  conj_tac >- metis_tac[] >>
  irule gas_outcome_ptr_conseq >>
  qexistsl_tac
    [`\res ee G tn t. (?tv. res = INL tv /\
       vv_post ctx func cenv cx e es sa sb s0 ee tv vv t /\
       t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts /\
       ghost_inv d cenv cx ee G tn t /\
       ptr_vv_ok cx (expr_type e) tv vv ee G tn t /\
       (!t' op. vv = StackValue t' op /\ ~is_word_type (expr_type e) ==>
         ptr_buf_ok cenv e op G t) /\
       (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
         ptr_buf_ok cenv e p.ptr_operand G t) /\
       ghost_kept cenv es sa G0 tn0 s0 G tn) /\
       P res ee /\ ee.gas_obs = [] /\ ~t.vs_halted`,
     `\res ee gt r. expr_exit res r`] >>
  conj_tac >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `res`
      >- (Cases_on `r` >> gvs[expr_exit_def]) >>
      fs[] >> metis_tac[expr_exit_INR_type]) >>
  ho_match_mp_tac gas_outcome_ptr_source_facts >>
  conj_tac
  >- (fs[expr_vv_sim_ptr_def] >> metis_tac[]) >>
  metis_tac[]
QED

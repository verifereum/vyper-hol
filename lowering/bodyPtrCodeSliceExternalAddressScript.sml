Theory bodyPtrCodeSliceExternalAddress
Ancestors
  bodyPtrDefs bodyPtrCodeSliceSelfOperands exprSimSliceExtcodeContinue
  exprSimSliceExtcodeEntry loweringPosts ptrDiscipline gasSummaryComposePtr
  gasOutcomeMarkedPtr compileEnv wordArgsPtr exprSimWordArgs venomState

Theorem code_slice_address_read_ptr_post:
  expr_body_pre cenv cx env e es /\ expr_type e = BaseT AddressT /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee) /\
  expr_post ctx func cenv cx e es sa sb s ee v op t /\
  ptr_val_ok cx (expr_type e) v op G tn t ==>
  expr_sim_inv cenv cx env ee /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  op_taint tn op = {} /\ op_prov G op = NONE /\
  ?bs. v = BytesV bs /\ LENGTH bs = 20 /\
    eval_operand op t = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs))
Proof
  strip_tac >> drule_all slice_address_read_post >>
  gvs[ptr_val_ok_def, is_word_type_def]
QED

Theorem code_slice_address_marked_ptr_post:
  expr_body_pre cenv cx env e es /\ expr_type e = BaseT AddressT /\
  gas_marked_exec_ptr D (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    marks (INL v) mid G tn (OK t) /\
  expr_post ctx func cenv cx e es sa sb s0 (mid with gas_obs := []) v op t /\
  ptr_val_ok cx (expr_type e) v op G tn t ==>
  expr_sim_inv cenv cx env (mid with gas_obs := []) /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  op_taint tn op = {} /\ op_prov G op = NONE /\
  ?bs. v = BytesV bs /\ LENGTH bs = 20 /\
    eval_operand op t = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs))
Proof
  strip_tac >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v,mid with gas_obs := [])` by
    (fs[gas_marked_exec_ptr_def] >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  drule_all code_slice_address_read_ptr_post >> simp[]
QED

Theorem code_slice_address_outcome_ptr:
  expr_body_pre cenv cx env e es /\ expr_type e = BaseT AddressT /\
  gas_outcome_ptr D tops (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\rr ee G tn t. ?v. rr = INL v /\
      expr_post ctx func cenv cx e es sa sb s0 ee v op t /\
      ptr_val_ok cx (expr_type e) v op G tn t /\ H v ee G tn t) R ==>
  gas_outcome_ptr D tops (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\rr ee G tn t. ?bs. rr = INL (BytesV bs) /\ LENGTH bs = 20 /\
      expr_post ctx func cenv cx e es sa sb s0 ee (BytesV bs) op t /\
      ptr_val_ok cx (expr_type e) (BytesV bs) op G tn t /\
      H (BytesV bs) ee G tn t /\
      expr_sim_inv cenv cx env ee /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
      eval_operand op t = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)) /\
      op_taint tn op = {} /\ op_prov G op = NONE /\ ee.gas_obs = []) R
Proof
  strip_tac >> irule gas_outcome_ptr_marked_conseq >>
  goal_assum (drule_at Any) >> rpt strip_tac >> BETA_TAC >>
  qpat_x_assum `(\rr ee G tn t. _) _ _ _ _ _`
    (strip_assume_tac o BETA_RULE) >>
  qpat_x_assum `rr = INL v` SUBST_ALL_TAC >>
  drule_all code_slice_address_marked_ptr_post >> strip_tac >>
  qexists_tac `bs` >> gvs[]
QED

Theorem code_slice_address_bind_ptr:
  expr_body_pre cenv cx env e es /\ expr_type e = BaseT AddressT /\
  gas_outcome_ptr D tops (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\rr ee G tn t. ?v. rr = INL v /\
      expr_post ctx func cenv cx e es sa sb s0 ee v op t /\
      ptr_val_ok cx (expr_type e) v op G tn t /\ H v ee G tn t) R /\
  (!marks err ee leaf fstate.
     gas_exempt_cert F tops (ctx,func)
       (ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()))
       (es,s0) marks (err,ee) (leaf,fstate) ==>
     gas_exempt_cert F tops (ctx,func)
       (bind (bind (eval_expr cx e) (read_result cx))
         (\v. ignore_bind (next v) (return ())))
       (es,s0) marks (err,ee) (leaf,fstate)) /\
  (!left v mid t right err ee leaf fstate.
     gas_marked_exec F (ctx,func) (bind (eval_expr cx e) (read_result cx))
       (es,s0) left (INL v) mid (OK t) /\
     gas_exempt_cert F tops (ctx,func) (ignore_bind (next v) (return ()))
       (mid with gas_obs := [],t) right (err,ee) (leaf,fstate) ==>
     gas_exempt_cert F tops (ctx,func)
       (bind (bind (eval_expr cx e) (read_result cx))
         (\v. ignore_bind (next v) (return ())))
       (es,s0) (left ++ right) (err,ee) (leaf,fstate)) /\
  (!res ee gt r. R res ee gt r ==> ?exc. res = INR exc /\ R' (INR exc) ee gt r) /\
  (!bs ee G tn t.
     LENGTH bs = 20 /\
     expr_post ctx func cenv cx e es sa sb s0 ee (BytesV bs) op t /\
     ptr_val_ok cx (expr_type e) (BytesV bs) op G tn t /\ H (BytesV bs) ee G tn t /\
     expr_sim_inv cenv cx env ee /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
     eval_operand op t = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)) /\
     op_taint tn op = {} /\ op_prov G op = NONE /\ ee.gas_obs = [] ==>
     gas_outcome_ptr D tops (ctx,func) PG (next (BytesV bs)) (ee,t,G,tn) Q R') ==>
  gas_outcome_ptr D tops (ctx,func) PG
    (bind (bind (eval_expr cx e) (read_result cx)) next) (es,s0,G0,tn0) Q R'
Proof
  strip_tac >> drule_all code_slice_address_outcome_ptr >>
  qhdtm_x_assum `gas_outcome_ptr` kall_tac >> disch_tac >>
  irule gas_outcome_ptr_bind >> simp[] >>
  conj_tac >- metis_tac[] >>
  irule gas_outcome_ptr_conseq >> goal_assum (drule_at Any) >>
  conj_tac >- (rpt strip_tac >> fs[] >> metis_tac[]) >>
  rpt strip_tac >> metis_tac[]
QED

(* Reuse concat_operand_eval_suffix for the normal/exceptional counted bind.
   This leaf supplies the previously implicit successful-source tail witness. *)
Theory bodyPtrBytestringBuiltinsConcatContinuation
Ancestors
  bodyPtrBytestringBuiltinsConcatHead bodyPtrBytestringBuiltinsInterfaces
  bodyPtrBytestringBuiltinsConcatDispatch bodyPtrBytestringBuiltinsConcatFrame
  vyperState

Theorem operand_read_success_exists:
  vyperState$bind (eval_expr cx e) (read_result cx) s = (INL v,t) ==>
  ?s0 tv t0 s1 v1 t1.
    eval_expr cx e s0 = (INL tv,t0) /\
    read_result cx tv s1 = (INL v1,t1)
Proof
  simp[vyperStateTheory.bind_def] >>
  Cases_on `eval_expr cx e s` >> Cases_on `q` >> simp[] >>
  strip_tac >> metis_tac[]
QED

Theorem operand_evidence_ptr_tail:
  body_exprs_ptr_ok cx (e::rest) /\
  (?marks ee0. ee = ee0 with gas_obs := [] /\
    !tail. vyperState$bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks readings ++ tail) =
      (INL v,ee0 with gas_obs := tail)) ==>
  body_exprs_ptr_ok cx rest
Proof
  strip_tac >> irule body_exprs_ptr_tail >>
  first_assum (irule_at Any) >>
  first_x_assum (qspec_then `[]` mp_tac) >>
  metis_tac[operand_read_success_exists]
QED

(* The offset-cell inputs of concat_fixed_arm_endpoint/concat_bytes_arm_endpoint
   survive the operand. Root capacity and payload use the same two frame rules.
   Separation and allocation age are real caller obligations, not freshness. *)
Theorem concat_offset_continuation_inputs:
  body_exprs_ptr_ok cx (e::rest) /\
  (?marks ee0. ee = ee0 with gas_obs := [] /\
    !tail. vyperState$bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks readings ++ tail) =
      (INL v,ee0 with gas_obs := tail)) /\
  expr_post ctx func cenv cx e es sa sm s0 ee v op t /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  not_fresh_at sa off /\ lookup_var off s0 = SOME w /\
  ptr_covers G0 tn0 off s0 32 /\
  FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\ aid < sa.cs_next_id /\
  (!name lb lsz. local_region cenv es.scopes s0 name lb lsz ==>
    b+sz <= lb \/ lb+lsz <= b) /\
  b <= w2n w /\ w2n w+32 <= b+sz /\
  (!i. w2n w <= i /\ i < w2n w+32 ==> i NOTIN tn0.t_mem) ==>
  body_exprs_ptr_ok cx rest /\
  lookup_var off t = SOME w /\ ptr_covers G tn off t 32 /\
  mload (w2n w) t = mload (w2n w) s0 /\
  (!i. w2n w <= i /\ i < w2n w+32 ==> i NOTIN tn.t_mem)
Proof
  strip_tac >>
  `body_exprs_ptr_ok cx rest` by
    (irule operand_evidence_ptr_tail >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[]) >>
  drule_all expr_operand_old_pointer_frame >> strip_tac >>
  drule_all expr_operand_old_offset_frame >> simp[]
QED

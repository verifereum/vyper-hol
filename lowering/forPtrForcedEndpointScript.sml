Theory forPtrForcedEndpoint
Ancestors
  bodyPtrDefs fragGasPathPtr gasSummaryComposePtr gasSummaryCompose gasOutcome gasExemptCert
  gasContext exprSimDefs loweringPosts stmtSimForced stmtSimForRounds stmtSimProps vyperInterpreter vyperState


Theorem for_forced_endpoint_error_cert:
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()))
    (es,s0) marks (err,ee) (leaf,fstate) ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (bind (bind (eval_expr cx e) (read_result cx)) next)
      (return ())) (es,s0) marks (err,ee) (leaf,fstate)
Proof
  strip_tac >> pure_once_rewrite_tac[ignore_bind_def] >>
  pure_once_rewrite_tac[bind_assoc] >>
  irule gas_exempt_cert_error_value >> simp[]
QED

Theorem for_forced_endpoint_tail_cert:
  gas_marked_exec memory (ctx,func)
    (bind (eval_expr cx e) (read_result cx))
    (es,s0) left (INL v) mid (OK t) /\
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (next v) (return ()))
    (mid with gas_obs := [],t) right (err,ee) (leaf,fstate) ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (bind (bind (eval_expr cx e) (read_result cx)) next)
      (return ())) (es,s0) (left ++ right) (err,ee) (leaf,fstate)
Proof
  strip_tac >> pure_once_rewrite_tac[ignore_bind_def] >>
  pure_once_rewrite_tac[bind_assoc] >>
  drule gas_exempt_cert_bind_value >> disch_then irule >>
  simp[GSYM ignore_bind_def]
QED

(* A forced endpoint is an expression fragment, not an unchecked S1 prefix.
   The continuation receives the exact updated provenance and taint. *)
Theorem forced_endpoint_bind_outcome_ptr:
  expr_sim_ptr d ctx PG func cenv cx fty e es /\
  lower_value compile_expr cenv fty e sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  stmt_state_rel ctx func cenv cx es s0 /\
  ghost_inv d cenv cx es G0 tn0 s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  gas_admissible (bind (bind (eval_expr cx e) (read_result cx)) next)
    (stmt_res_ok lctx) es /\
  (!marks v mid G tn t.
    gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG
      (bind (eval_expr cx e) (read_result cx))
      (es,s0,G0,tn0) marks (INL v) mid G tn (OK t) /\
    expr_post ctx func cenv cx e es sa sb s0 mid v op t /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ghost_inv d cenv cx mid G tn t /\
    ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G t) /\
    ghost_kept cenv es sa G0 tn0 s0 G tn /\
    gas_admissible (next v) (stmt_res_ok lctx) (mid with gas_obs := []) ==>
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG (next v)
      (mid with gas_obs := [],t,G,tn) Post
      (\res ee gt r. !tail. stmt_exit_ptr RetQ (ee with gas_obs := tail) res gt r)) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (bind (bind (eval_expr cx e) (read_result cx)) next)
    (es,s0,G0,tn0) Post
    (\res ee gt r. !tail. stmt_exit_ptr RetQ (ee with gas_obs := tail) res gt r)
Proof
  strip_tac >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule forced_then_admissible >> goal_assum (drule_at Any)) >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_ptr_def] >> disch_then drule_all >>
  rewrite_tac[gas_outcome_ptr_def, gas_summary_ptr_at_marked] >> strip_tac
  >- suspend "normal"
  >- suspend "exception" >>
  qexists_tac `marks` >> disj2_tac >>
  irule_at Any for_forced_endpoint_error_cert >> goal_assum (drule_at Any)
QED

Resume forced_endpoint_bind_outcome_ptr[normal]:
  gvs[] >>
  `gas_admissible (next v) (stmt_res_ok lctx) (es_end with gas_obs := [])` by
    (irule gas_admissible_bind_tail >> goal_assum (drule_at Any) >>
     qexists_tac `gas_explicit marks s0.vs_gas_readings` >>
     fs[gas_marked_exec_ptr_def]) >>
  `gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG
     (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
     marks (INL v) (es_end with gas_obs := []) G tn (OK t)` by
    fs[gas_marked_exec_ptr_def] >>
  qpat_x_assum `!marks v mid G tn t. _` drule_all >> disch_tac >>
  gvs[gas_outcome_ptr_def, gas_summary_ptr_at_marked]
  >- suspend "bind_normal"
  >- suspend "bind_exit" >>
  qexists_tac `marks ++ marks'` >> disj2_tac >>
  irule_at Any for_forced_endpoint_tail_cert >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[gas_marked_exec_ptr_exec]
QED

Resume forced_endpoint_bind_outcome_ptr[bind_normal]:
  qexists_tac `marks ++ marks'` >> disj1_tac >>
  qexistsl_tac [`res`, `es_end'`, `G'`, `tn'`, `OK t'`] >>
  conj_tac
  >- (irule gas_marked_exec_ptr_bind_normal >>
      goal_assum (drule_at Any) >> simp[]) >>
  gvs[]
QED

Resume forced_endpoint_bind_outcome_ptr[bind_exit]:
  qexists_tac `marks ++ marks'` >> disj1_tac >>
  qexistsl_tac [`res`, `es_end'`, `G'`, `tn'`, `r`] >>
  conj_tac
  >- (irule gas_marked_exec_ptr_bind_normal >>
      goal_assum (drule_at Any) >> simp[]) >>
  gvs[]
QED

Resume forced_endpoint_bind_outcome_ptr[exception]:
  gvs[] >> Cases_on `res` >- fs[] >>
  rename1 `INR ex` >> qexists_tac `marks` >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_marked] >>
  qexistsl_tac [`INR ex`, `es_end`, `G`, `tn`, `r`] >>
  conj_tac
  >- (irule gas_marked_exec_ptr_bind_exception >> simp[]) >>
  disj2_tac >> simp[stmt_exit_ptr_def] >>
  gen_tac >> disj1_tac >>
  once_rewrite_tac[INST_TYPE [beta |-> ``:value``] expr_exit_INR_type] >>
  first_assum ACCEPT_TAC
QED

Finalise forced_endpoint_bind_outcome_ptr

Theory forPtrForcedEndpoint
Ancestors
  bodyPtrDefs gasSummary fragGasPathPtr gasSummaryComposePtrAll gasSummaryComposePtr gasSummaryCompose gasOutcome gasExemptCert
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
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv H d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  gas_admissible (bind (bind (eval_expr cx e) (read_result cx)) next)
    (stmt_res_ok lctx) es /\
  (!v. storage_trace_frame (next v)) /\
  (!marks v mid G tn t.
    (?H. valid_horizon cx st0 H mid.storage_trace) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_marked_exec_ptr (cx_dead H cx) (ctx,func) PG
      (bind (eval_expr cx e) (read_result cx))
      (es,s0,G0,tn0) marks (INL v) mid G tn (OK t) /\
    expr_post H ctx func cenv cx e es sa sb s0 mid v op t /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ghost_inv H d cenv cx mid G tn t /\
    ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G t) /\
    ghost_kept cenv es sa G0 tn0 s0 G tn) /\
    gas_admissible (next v) (stmt_res_ok lctx) (mid with gas_obs := []) ==>
    gas_outcome_ptr (\H. cx_dead H cx) (cx_tops cx) (ctx,func) PG cx st0 (next v)
      (mid with gas_obs := [],t,G,tn) Post
      (\H res ee gt r. !tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r)) ==>
  gas_outcome_ptr (\H. cx_dead H cx) (cx_tops cx) (ctx,func) PG cx st0
    (bind (bind (eval_expr cx e) (read_result cx)) next)
    (es,s0,G0,tn0) Post
    (\H res ee gt r. !tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r)
Proof
  strip_tac >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule forced_then_admissible >> goal_assum (drule_at Any)) >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_ptr_def] >> disch_then drule_all >> strip_tac >>
  mp_tac (Q.INST
    [`D` |-> `\H. cx_dead H cx`, `tops` |-> `cx_tops cx`,
     `source` |-> `bind (eval_expr cx e) (read_result cx)`,
     `P` |-> `\H res ee G tn t. ?v. res = INL v /\
       expr_post H ctx func cenv cx e es sa sb s0 ee v op t /\
       t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts /\
       ghost_inv H d cenv cx ee G tn t /\
       ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
       (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G t) /\
       ghost_kept cenv es sa G0 tn0 s0 G tn`,
     `E` |-> `\H res ee gt r. expr_exit res r`,
     `Q` |-> `Post`,
     `R` |-> `\H res ee gt r. !tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r`]
    (INST_TYPE [alpha |-> ``:value``, beta |-> ``:unit``] gas_outcome_ptr_bind_all)) >>
  impl_tac
  >- (rpt conj_tac
      >- first_assum ACCEPT_TAC
      >- (rpt strip_tac >> gvs[])
      >- (rpt strip_tac >> Cases_on `res` >> gvs[expr_exit_def] >>
          simp[stmt_exit_ptr_def] >> metis_tac[expr_exit_INR_type])
      >- first_assum ACCEPT_TAC
      >- (rpt gen_tac >> strip_tac >>
          `gas_admissible (next v) (stmt_res_ok lctx) (mid with gas_obs := [])` by
            (irule gas_admissible_bind_tail >> goal_assum (drule_at Any) >>
             qexists_tac `gas_explicit left s0.vs_gas_readings` >>
             fs[gas_marked_exec_def]) >>
          qpat_x_assum `!marks v mid G tn t. _`
            (qspecl_then [`left`, `v`, `mid with gas_obs := []`, `G`, `tn`, `t`] mp_tac) >>
          impl_tac
          >- (simp[] >> conj_tac >- metis_tac[] >>
              rpt strip_tac >> first_x_assum drule >> strip_tac >>
              gvs[gas_marked_exec_ptr_def, gas_marked_exec_def,
                  fragGasModeTheory.gas_marked_path_def]) >>
          simp[])
      >- (rpt strip_tac >>
          irule for_forced_endpoint_error_cert >> goal_assum (drule_at Any)) >>
      rpt strip_tac >> irule for_forced_endpoint_tail_cert >>
      goal_assum (drule_at Any)) >>
  simp[]
QED

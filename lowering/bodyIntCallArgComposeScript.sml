(* Counted source-result sequencing keeps the very endpoint on which its
   continuation is invoked.  Exempt certificates remain a separate branch. *)
Theory bodyIntCallArgCompose
Ancestors
  gasOutcome gasSummary gasSummaryCompose gasExemptCert vyperState vyperInterpreter
  exprSimDefs loweringPosts

Theorem marked_result_then_outcome:
  gas_marked_exec memory (ctx,func)
    (a : evaluation_state -> eval_result evaluation_result)
    (es,s0) left (INL v) mid (OK t) /\
  gas_outcome memory tops (ctx,func)
    (k v : evaluation_state -> 'b evaluation_result)
    (mid with gas_obs := [],t) Q R ==>
  gas_outcome memory tops (ctx,func) (bind a k) (es,s0) Q R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qexists `left ++ marks` >> disj1_tac >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
      rewrite_tac[gas_summary_at_def] >>
      metis_tac[gas_marked_exec_bind_normal]) >>
  qexists `left ++ marks` >> disj2_tac >>
  qexistsl [`err`, `ee`, `leaf`, `finish'`] >>
  rewrite_tac[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_bind_result >>
  simp[GSYM ignore_bind_def] >> metis_tac[]
QED

Theorem gas_outcome_bind_result_marked:
  gas_outcome memory tops (ctx,func)
    (a : evaluation_state -> eval_result evaluation_result) (es,s0) P
    (\res ee r. ?exc. res = INR exc /\ E exc ee r) /\
  (!left v mid t.
    gas_marked_exec memory (ctx,func) a (es,s0) left (INL v) mid (OK t) /\
    P (INL v) (mid with gas_obs := []) t ==>
    gas_outcome memory tops (ctx,func)
      (k v : evaluation_state -> 'b evaluation_result)
      (mid with gas_obs := [],t) Q
      (\res ee r. ?exc. res = INR exc /\ E exc ee r)) /\
  (!res ee t. P res ee t ==> ?v. res = INL v) ==>
  gas_outcome memory tops (ctx,func) (bind a k) (es,s0) Q
    (\res ee r. ?exc. res = INR exc /\ E exc ee r)
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  disch_then (strip_assume_tac o
    REWRITE_RULE[gas_outcome_def, gas_summary_at_def])
  >- (gvs[] >>
      `?v. res = INL v` by metis_tac[] >> gvs[] >>
      irule marked_result_then_outcome >>
      goal_assum (drule_at Any) >>
      first_x_assum irule >> metis_tac[])
  >- (gvs[] >> rewrite_tac[gas_outcome_def] >>
      qexists `marks` >> disj1_tac >>
      rewrite_tac[gas_summary_at_def] >>
      qexistsl [`INR exc`, `es_end`, `r`] >>
      conj_tac >- (irule gas_marked_exec_bind_exception >> simp[]) >>
      metis_tac[]) >>
  rewrite_tac[gas_outcome_def] >>
  qexists `marks` >> disj2_tac >>
  qexistsl [`err`, `ee`, `leaf`, `finish'`] >>
  rewrite_tac[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_error_result >>
  simp[GSYM ignore_bind_def]
QED

(* Keep the exception result polymorphism out of the sequencing interface. *)
Theorem expr_exit_errors[local]:
  (\res ee r. expr_exit (res : eval_result + exception) r) =
  (\res (ee:evaluation_state) r.
    ?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) r)
Proof
  simp[FUN_EQ_THM] >> Cases >> simp[]
QED

Theorem expr_vv_then_outcome:
  expr_vv_sim ctx func cenv cx ty e es /\
  compile_expr cenv ty e sa = (vv,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!raw ee t.
    vv_post ctx func cenv cx e es sa sb s0 ee raw vv t /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (ctx,func) (k raw) (ee,t) Q
      (\res ee r. ?exc. res = INR exc /\
        expr_exit (INR exc : eval_result + exception) r)) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (eval_expr cx e) k) (es,s0) Q
    (\res ee r. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) r)
Proof
  strip_tac >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_vv_sim_def] >>
  disch_then (qspecl_then [`sa`, `sb`, `vv`, `s0`] mp_tac) >>
  simp[expr_exit_errors] >> disch_tac >>
  ho_match_mp_tac (Q.INST
    [`P` |-> `\res ee t. ?tv. res = INL tv /\
      vv_post ctx func cenv cx e es sa sb s0 ee tv vv t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts`]
    gas_outcome_bind_result_marked) >>
  simp[] >> metis_tac[]
QED

(* The empty argument prefix has no endpoint to choose: it is the caller's
   very state, whether the continuation is counted or exempt. *)
Theorem empty_args_then_outcome[local]:
  gas_outcome memory tops p (k []) (es,s0) Q R ==>
  gas_outcome memory tops p
    (bind (eval_expr_results cx []) k) (es,s0) Q R
Proof
  simp[evaluate_def, bind_return]
QED

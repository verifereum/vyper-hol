Theory stmtForRangeEndpointsMemory
Ancestors
  stmtSimForced gasOutcome gasSummary gasSummaryCompose gasExemptCert fragGasMode
  fragGasPath fragGasPathMem fragExec vyperState exprSimMemDefs

Theorem for_endpoint_bind_outcome_mem:
  !tops ctx func (a : evaluation_state -> value evaluation_result)
   (k : value -> evaluation_state -> unit evaluation_result) es s0 A Q R.
    gas_outcome T tops (ctx,func) a (es,s0)
      (\res ee t. ?v. res = INL v /\ A v ee t)
      (\res ee r. expr_exit res r) /\
    (!v ee t. A v ee t /\ ee.gas_obs = [] /\ ~t.vs_halted /\
       (!tail. ?gs. a (es with gas_obs := gs) = (INL v,ee with gas_obs := tail)) ==>
       gas_outcome T tops (ctx,func) (k v) (ee,t) Q R) /\
    (!ex ee r. expr_exit (INR ex : value + exception) r ==>
       R (INR ex) ee r) ==>
    gas_outcome T tops (ctx,func) (bind a k) (es,s0) Q R
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  simp[gas_outcome_def] >> strip_tac
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
      simp[gas_summary_at_def] >> strip_tac
      >- (gvs[] >>
          `!tail. ?gs. a (es with gas_obs := gs) =
              (INL v,es_end with gas_obs := tail)` by
            (fs[gas_marked_exec_def] >> metis_tac[]) >>
          `~t.vs_halted` by
            (fs[gas_marked_exec_def, gas_marked_path_def] >>
             drule gas_path_mem_exec >> simp[exit_result_def]) >>
          first_x_assum (qspecl_then [`v`, `es_end with gas_obs := []`, `t`] mp_tac) >>
          impl_tac >- (simp[] >> metis_tac[]) >>
          simp[gas_outcome_def] >> strip_tac
          >- (qexists_tac `marks ++ marks'` >> disj1_tac >>
              fs[gas_summary_at_def] >>
              qexistsl_tac [`res`, `es_end'`, `r`] >> simp[] >>
              irule gas_marked_exec_bind_normal >> metis_tac[]) >>
          qexists_tac `marks ++ marks'` >> disj2_tac >>
          qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
          simp[ignore_bind_def, bind_assoc] >>
          irule gas_exempt_cert_bind_value >> simp[GSYM ignore_bind_def] >>
          metis_tac[]) >>
      `?ex. res = INR ex` by (Cases_on `res` >> gvs[exprSimDefsTheory.expr_exit_def]) >>
      gvs[] >> qexists_tac `marks` >> disj1_tac >>
      qexistsl_tac [`INR ex`, `es_end`, `r`] >> conj_tac
      >- (irule gas_marked_exec_bind_exception >> simp[]) >>
      disj2_tac >> simp[]) >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  simp[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_error_value >> simp[GSYM ignore_bind_def]
QED

(* Consumer boundary for a forced endpoint.  The continuation receives both
   the memory expression post and the source reachability fact needed by
   dependent endpoint hypotheses. *)
Theorem for_expr_endpoint_outcome_mem:
  expr_sim_mem ctx func cenv cx ty e es /\
  lower_value compile_expr cenv ty e sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!v ee t.
     expr_post ctx func cenv cx e es sa sb s0 ee v op t /\
     expr_store_bound cx (expr_type e) v op t /\
     t.vs_current_bb = sb.cs_current_bb /\
     t.vs_inst_idx = LENGTH sb.cs_current_insts /\
     alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
     ee.gas_obs = [] /\ ~t.vs_halted /\
     (!tail. ?gs. bind (eval_expr cx e) (read_result cx)
        (es with gas_obs := gs) = (INL v,ee with gas_obs := tail)) ==>
     gas_outcome T (cx_tops cx) (ctx,func) (k v) (ee,t) Q R) /\
  (!ex ee r. expr_exit (INR ex : value + exception) r ==> R (INR ex) ee r) ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (bind (bind (eval_expr cx e) (read_result cx))
      (k : value -> evaluation_state -> unit evaluation_result)) (es,s0) Q R
Proof
  strip_tac >> irule for_endpoint_bind_outcome_mem >>
  conj_tac >- simp[] >> qexists_tac `\v ee t.
    expr_post ctx func cenv cx e es sa sb s0 ee v op t /\
    expr_store_bound cx (expr_type e) v op t /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next` >>
  simp[] >>
  qhdtm_x_assum `expr_sim_mem` mp_tac >>
  simp[expr_sim_mem_def] >> disch_then irule >> simp[]
QED

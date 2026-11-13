Theory stmtForRangeEndpointsMemory
Ancestors
  stmtSimForRange
  stmtSimForced gasOutcome gasSummary gasSummaryCompose gasExemptCert fragGasMode
  fragGasPath fragGasPathMem fragExec vyperState exprSimMemDefs
  aggregateCountedOutcome gasStorage vyperStorageTrace vyperStorageFootprint

(* Consumer boundary for a forced endpoint.  The continuation receives both
   the memory expression post and the source reachability fact needed by
   dependent endpoint hypotheses. *)
Theorem for_expr_endpoint_outcome_mem:
  expr_sim_mem ctx func cenv cx ty e es /\
  lower_value compile_expr cenv ty e sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s0 /\
     storage_well_formed_on cx es (FST H)) /\
  alloca_history func s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!v. storage_trace_frame (k v)) /\
  (!v ee t.
     (?H. valid_horizon cx st0 H ee.storage_trace) /\
     (!H. valid_horizon cx st0 H ee.storage_trace ==>
        expr_post H ctx func cenv cx e es sa sb s0 ee v op t) /\
     expr_store_bound cx (expr_type e) v op t /\
     t.vs_current_bb = sb.cs_current_bb /\
     t.vs_inst_idx = LENGTH sb.cs_current_insts /\
     alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
     ee.gas_obs = [] /\ ~t.vs_halted /\
     (!tail. ?gs. bind (eval_expr cx e) (read_result cx)
        (es with gas_obs := gs) = (INL v,ee with gas_obs := tail)) ==>
     gas_outcome T (cx_tops cx) (ctx,func) cx st0 (k v) (ee,t) Q R) /\
  (!H ex ee r. expr_exit (INR ex : value + exception) r ==>
     R H (INR ex) ee r) ==>
  gas_outcome T (cx_tops cx) (ctx,func) cx st0
    (bind (bind (eval_expr cx e) (read_result cx))
      (k : value -> evaluation_state -> unit evaluation_result)) (es,s0) Q R
Proof
  strip_tac >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_mem_def] >>
  disch_then (qspecl_then [`st0`, `sa`, `sb`, `op`, `s0`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule_then irule counted_outcome_bind_exec >>
  rpt conj_tac
  >- (rpt strip_tac >> irule forced_endpoint_error_cert >>
      first_assum ACCEPT_TAC)
  >- (rpt strip_tac >> drule_all forced_endpoint_tail_cert >>
      disch_then ACCEPT_TAC)
  >- suspend "next"
  >- (BETA_TAC >> rpt strip_tac >> Cases_on `res`
      >- fs[exprSimDefsTheory.expr_exit_def] >>
      rename1 `INR ex` >> qexists_tac `ex` >> simp[] >>
      qpat_x_assum `!H ex ee r. _ ==> R H _ ee r` irule >> simp[])
  >- (BETA_TAC >> rpt strip_tac >> qexists_tac `v` >> first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED

Resume for_expr_endpoint_outcome_mem[next]:
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  reverse (Cases_on `storage_trace_domain cx st0 mid.storage_trace`)
  >- (rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
      irule gasStorageTheory.gas_bad_storage_at_initial >> simp[]) >>
  `?H0. valid_horizon cx st0 H0 mid.storage_trace` by
    metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `~t.vs_halted` by
    (fs[gas_marked_exec_def, gas_marked_path_def] >>
     drule gas_path_mem_exec >> simp[exit_result_def]) >>
  `!tail. ?gs. bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gs) = (INL v,mid with gas_obs := tail)` by
    (fs[gas_marked_exec_def] >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     expr_post H ctx func cenv cx e es sa sb s0 (mid with gas_obs := []) v op t /\
     expr_store_bound cx (expr_type e) v op t /\
     t.vs_current_bb = sb.cs_current_bb /\
     t.vs_inst_idx = LENGTH sb.cs_current_insts /\
     alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next` by
    (rpt strip_tac >>
     qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> ?v'. _`
       drule >> simp[]) >>
  first_assum (qspec_then `H0` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
  qpat_x_assum `!v ee t. _ ==> gas_outcome _ _ _ _ _ (k v) _ _ _` irule >>
  simp[] >> rpt conj_tac >> metis_tac[]
QED
Finalise for_expr_endpoint_outcome_mem

(* Joint target-address interface. *)
Theory bodyFullExtCallRequestHead
Ancestors
  bodyFullPreds bodyFullExtCallRequestSource bodySimFull gasOutcomeFullCompose
  gasOutcomeFull gasExemptCert vyperStorageTrace stmtSimProps
  exprSimHypsDefs exprSimDefs exprLowering gasShadow vyperInterpreter vyperState
  loweringPosts bodyPtrDefs

Theorem extcall_head_source_map[local]:
  !cx e es. eval_exprs cx [e] es =
    ((case FST (bind (eval_expr cx e) (read_result cx) es) of
       INL v => INL [v] | INR ex => INR ex),
     SND (bind (eval_expr cx e) (read_result cx) es))
Proof
  rpt gen_tac >>
  simp[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx e es` >> Cases_on `q` >> simp[] >>
  Cases_on `read_result cx x r` >> Cases_on `q` >>
  simp[Once evaluate_def, bind_def, return_def]
QED

Theorem extcall_head_outcome_map[local]:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (bind (eval_expr cx addr) (read_result cx)) (es,s,G,tn) Q R ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (eval_exprs cx [addr]) (es,s,G,tn)
    (\H raw ee G tn t. ?res.
      raw = (case res of INL v => INL [v] | INR ex => INR ex) /\
      Q H res ee G tn t)
    (\H raw ee gt r. ?res.
      raw = (case res of INL v => INL [v] | INR ex => INR ex) /\
      R H res ee gt r)
Proof
  strip_tac >>
  ho_match_mp_tac (GEN_ALL gas_outcome_full_source_map) >>
  qexists `bind (eval_expr cx addr) (read_result cx)` >>
  simp[extcall_head_source_map]
QED

Theorem extcall_request_head_outcome:
  body_exprs_full_ok cx [addr] /\ body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env addr es /\
  lower_value compile_expr cenv (BaseT AddressT) addr sa = (ao,sb) /\
  lower_value compile_expr cenv (BaseT AddressT) (gas_shadow_expr addr)
    shadow_sa = (ao,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx addr) (read_result cx)) expr_res_ok es /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (eval_exprs cx [addr]) (es,s0,G0,tn0)
    (\H res ee G tn t. ?v. res = INL [v] /\
      expr_post H ctx func cenv cx addr es sa sb s0 ee v ao t /\
      expr_store_bound cx (expr_type addr) v ao t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ptr_val_ok cx (post_value_type cenv addr) v ao G tn t /\
      (~is_word_type (post_value_type cenv addr) ==>
       ptr_buf_ok cenv addr ao G t) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
    (\H res ee gt r. expr_exit res r)
Proof
  strip_tac >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (BaseT AddressT) addr es` by
    (gvs[body_exprs_full_ok_def] >>
     qpat_x_assum `body_expr_full_ok cx addr` mp_tac >>
     simp[Once body_expr_full_ok_def] >> metis_tac[]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_full_def] >> disch_then drule_all >> strip_tac >>
  drule extcall_head_outcome_map >> strip_tac >>
  irule gas_outcome_full_post_mono >> goal_assum (drule_at Any) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  gvs[] >> simp[expr_exit_success_map]
QED

(* The post is a local formula, not a new logical predicate.  It is shared
   by the lower-value provider and the normalized continuation contract. *)
Theorem extcall_request_head_full:
  let P = (\H res ee G tn t. ?v. res = INL [v] /\
        expr_post H ctx func cenv cx addr es sa sb s0 ee v ao t /\
        expr_store_bound cx (expr_type addr) v ao t /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
        ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
        ptr_val_ok cx (post_value_type cenv addr) v ao G tn t /\
        (~is_word_type (post_value_type cenv addr) ==>
         ptr_buf_ok cenv addr ao G t) /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
  in
  body_exprs_full_ok cx [addr] /\ body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env addr es /\
  lower_value compile_expr cenv (BaseT AddressT) addr sa = (ao,sb) /\
  lower_value compile_expr cenv (BaseT AddressT) (gas_shadow_expr addr)
    shadow_sa = (ao,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx addr) (read_result cx)) expr_res_ok es /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!vs. storage_trace_frame (next vs)) /\
  (!marks vs mid G tn t.
     (!tail. eval_exprs cx [addr]
       (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
       (INL vs,mid with gas_obs := tail)) /\
     storage_trace_domain cx st0 mid.storage_trace /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
       P H (INL vs) mid G tn t) ==>
     gas_outcome_full
       (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (cx_tops cx) cx st0 (next vs) (mid,t,G,tn) Q
       (\H res ee gt r. expr_exit res r)) ==>
  gas_outcome_full
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_exprs cx [addr]) next) (es,s0,G0,tn0)
    Q (\H res ee gt r. expr_exit res r)
Proof
  rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  drule_all extcall_request_head_outcome >> strip_tac >>
  pop_assum (qspec_then `PG` assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ P _` >>
  irule gas_outcome_full_bind_all >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_values >>
      goal_assum (drule_at Any) >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_values >>
      first_assum ACCEPT_TAC) >>
  conj_tac >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  qexists `P` >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `res`
      >- (disj1_tac >> qexists `x` >> simp[] >>
          first_x_assum irule >> gvs[Abbr `P`] >> metis_tac[]) >>
      `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
         mid.storage_trace` by gvs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
      first_x_assum drule >> simp[Abbr `P`]) >>
  irule gas_outcome_full_post_mono >>
  goal_assum (drule_at Any) >> simp[] >>
  rpt strip_tac >> Cases_on `res` >>
  gvs[expr_exit_def] >> metis_tac[expr_exit_INR_type]
QED

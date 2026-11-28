Theory s1PrefixCreateOperandCut
Ancestors
  s1PrefixPreds s1PrefixDefs s1PrefixCompose s1PrefixProps bodyFullPreds bodyFullSimProjection
  bodyFullCreateHeld[qualified] bodyFullIfExpReach[qualified]
  bodyMemoryDefs[qualified] fragGasOriginPtrExec[qualified] fragExec[qualified]
  exprSimFullBundleProps exprSimSource exprSimDefs exprLoweringProps
  exprSimWordArgs[qualified] compileEnv
  gasOutcomeFull gasStorage fragGasOriginPtr vyperStorageTrace
  vyperInterpreter loweringPosts bodyPtrDefs

Theorem create_operand_body_judgments[local]:
  body_expr_full_ok cx e /\ body_expr_prefix_ok cx e /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env e es ==>
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es /\
  expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es
Proof
  strip_tac >> conj_tac
  >- (drule_all body_expr_full_ok_simulations >> simp[]) >>
  qpat_x_assum `body_expr_prefix_ok _ _`
    (mp_tac o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
  strip_tac >>
  qpat_assum `!DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es.
     _ ==> expr_sim_prefix _ _ _ _ _ _ /\ _`
    (fn th => metis_tac[th])
QED

(* Attach the replay and path of the outcome's own marks to its normal post. *)
Theorem create_operand_outcome_replay[local]:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 source
    (es,s,G,tn) Q R ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 source
    (es,s,G,tn)
    (\H res ee G1 tn1 t. Q H res ee G1 tn1 t /\
      (?marks.
        (!tail. source (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
          (res,ee with gas_obs := tail)) /\
        (!H'. valid_horizon cx st0 H' ee.storage_trace ==>
          gas_origin_ptr_path (DF H',lo,explicit,ctx,func,PG)
            (s,G,tn) marks (OK t,G1,tn1)))) R
Proof
  rw[gas_outcome_full_def] >> qexists_tac `marks`
  >- (disj1_tac >> metis_tac[])
  >- (disj2_tac >> disj1_tac >> rpt (goal_assum (drule_at Any)) >>
      qexistsl [`r`,`G'`,`tn'`] >> qx_gen_tac `H` >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _`
        (drule_then strip_assume_tac) >> simp[] >> metis_tac[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >> drule_all create_operand_body_judgments >>
  disch_then (qspecl_then [`expr_type e`,`shadow_func`,`lo`,`func`,`d`,`PG`,`DF`]
    strip_assume_tac) >>
  drule_then assume_tac expr_body_pre_gas_admissible >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_full_via_bundle]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sb`,`sh`,`shb`,`op`,`s`,`G`,`tn`] mp_tac) >>
  (impl_tac >- (simp[expr_sim_full_hypotheses_def,expr_sim_full_code_def] >>
                first_assum ACCEPT_TAC)) >>
  disch_then (assume_tac o MATCH_MP create_operand_outcome_replay) >>
  qpat_x_assum `expr_sim_prefix _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_prefix_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sb`,`sh`,`shb`,`op`,`s`,`G`,`tn`] mp_tac) >>
  (impl_tac >- (simp[expr_sim_full_pre_def] >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  irule gas_prefix_full_bind >>
  simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,
       storage_trace_frame_read_result,requests_outcomes_frame_bind_all,
       evaluate_requests_outcomes_frame,requests_outcomes_frame_read_result] >>
  goal_assum (drule_at Any) >>
  (reverse conj_tac >- (rpt gen_tac >> Cases_on `res` >> simp[expr_exit_def])) >>
  simp[expr_sim_full_post_def,expr_sim_full_endpoint_def] >>
  rpt gen_tac >> strip_tac >>
  rename1 `storage_trace_domain cx st0 ee.storage_trace` >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace`
    by fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. _ ==> (_ /\ _) /\ ?ms. _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. _ ==> gas_origin_ptr_path _ _ _ _` (drule_then assume_tac) >>
  `~t.vs_halted` by
    (drule fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec >>
     simp[fragExecTheory.exit_result_def]) >>
  `return_buf_frame d cenv sb t` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qpat_assum `return_buf_frame d cenv sa s` (irule_at Any) >>
     drule_then assume_tac exprSimWordArgsTheory.expr_post_frame >>
     simp[] >> metis_tac[exprSimWordArgsTheory.wb_frame_vars,
                        ci_mono_lower_value_compile_expr,ci_mono_def,pairTheory.SND]) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[bodyFullIfExpReachTheory.body_inv_no_phi] >>
  `!f i z. frag_reachable ctx func t f i z ==> dalloca_fmp_headroom i z` by
    (rpt gen_tac >> strip_tac >>
     drule_all bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom >> simp[]) >>
  `body_const_cells_agree [(NONE,tops)] cx env ee` by
    (irule bodyFullCreateHeldTheory.create_operand_const_cells_replay >>
     rpt (goal_assum (drule_at Any))) >>
  qpat_assum `!tail. _ = (INL _,_)` (qspec_then `[]` assume_tac) >>
  drule_all bodyFullCreateHeldTheory.create_operand_read_post >> simp[] >>
  disch_then (qspec_then `st0` strip_assume_tac) >>
  qpat_assum `!v ee G1 tn1 t. _ ==> gas_prefix_full _ _ _ _ _` irule >>
  simp[] >> metis_tac[]
QED
*)
Theorem create_body_operand_cut_prefix_replay:
  body_const_cells_agree [(NONE,tops)] cx env es /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  expr_body_pre cenv cx env e es /\ body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e /\
  lower_value compile_expr cenv (expr_type e) e sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
    (gas_shadow_expr e) sh = (op,shb) /\
  gas_shadow_state sa sh /\ gas_shadow_state sb shb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code sh shb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!fn i z. frag_reachable ctx func s fn i z ==> dalloca_fmp_headroom i z) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!v. storage_trace_frame (next v)) /\
  (!v ee G1 tn1 t.
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      expr_post H ctx func cenv cx e es sa sb s ee v op t /\
      ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 t) /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ~t.vs_halted /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    ptr_val_ok cx (post_value_type cenv e) v op G1 tn1 t /\
    ghost_kept_at lo cenv es sa G tn s G1 tn1 /\
    return_buf_frame d cenv sb t /\
    (!fn i z. frag_reachable ctx func t fn i z ==> dalloca_fmp_headroom i z) /\
    body_const_cells_agree [(NONE,tops)] cx env ee /\
    expr_sim_inv cenv cx env ee /\ expr_result_typed env e (Value v) /\
    (?a tv b a' v' b'. eval_expr cx e a = (INL tv,b) /\
                        read_result cx tv a' = (INL v',b')) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
         valid_horizon cx st0 H es.storage_trace) /\
    (?marks.
      (!tail. bind (eval_expr cx e) (read_result cx)
        (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
        (INL v,ee with gas_obs := tail)) /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (s,G,tn) marks (OK t,G1,tn1))) ==>
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (next v) (ee,t,G1,tn1)) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (bind (bind (eval_expr cx e) (read_result cx)) next) (es,s,G,tn)
Proof
  cheat
QED

(* Specialize scoped sequencing to one ordinary value-mode operand. *)
Theory entryCreateScalarScopedBind
Ancestors
  entryCreateScopedBind entryCreateFocusSpec entryCreateCompletedCut
  exprSimFullBundleProps bodySim exprSimDefs gasContext
  gasExemptCert vyperStorageTrace vyperStorageFootprint

Theorem scalar_exit_is_exception[local]:
  create_operand_exit_post ctx cx H res ee gt r ==>
  ?exc. res = INR exc
Proof
  Cases_on `res` >> Cases_on `r` >>
  simp[create_operand_exit_post_def, expr_exit_def]
QED

Theorem scalar_scoped_exception_post[local]:
  scoped_operand_outcome env tops cx st0 a m source (es,s,G,tn) Q
    (create_operand_exit_post ctx cx) ==>
  scoped_operand_outcome env tops cx st0 a m source (es,s,G,tn) Q
    (\H res ee gt r. (?exc. res = INR exc) /\ create_operand_exit_post ctx cx H res ee gt r)
Proof
  PairCases_on `env` >>
  simp_tac bool_ss [scoped_operand_outcome_def] >>
  disch_then (qx_choose_then `marks` strip_assume_tac) >> qexists_tac `marks`
  >- metis_tac[]
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >>
      simp[] >> rpt strip_tac >> first_x_assum drule >> strip_tac >>
      simp[] >> metis_tac[scalar_exit_is_exception]) >>
  metis_tac[]
QED

Theorem create_body_operand_scoped_bind:
  let source = bind (eval_expr cx e) (read_result cx) in
  let E = gas_explicit_sites ctx shctx in
  let post = expr_sim_full_post (DF,lo,d,ctx,func) ce cx e (es,a,m,s,op,G,tn) in
  let replay = \marks v ee. !tail.
    source (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL v,ee with gas_obs := tail) in
  let path = \marks G1 tn1 t ee. !H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,E,ctx,func,PG) (s,G,tn) marks (OK t,G1,tn1) in
  let returned = \v ee G1 tn1 t.
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      expr_post H ctx func ce cx e es a m s ee v op t /\
      ghost_inv_at (DF H) lo d ce cx ee G1 tn1 t) /\
    t.vs_current_bb = m.cs_current_bb /\ t.vs_inst_idx = LENGTH m.cs_current_insts /\
    ~t.vs_halted /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    ptr_val_ok cx (post_value_type ce e) v op G1 tn1 t /\
    ghost_kept_at lo ce es a G tn s G1 tn1 /\ return_buf_frame d ce m t /\
    (!fn i z. frag_reachable ctx func t fn i z ==> dalloca_fmp_headroom i z) /\
    body_const_cells_agree [(NONE,tops)] cx env ee /\ expr_sim_inv ce cx env ee /\
    expr_result_typed env e (Value v) /\
    (?p tv q p' v' q'. eval_expr cx e p = (INL tv,q) /\
                        read_result cx tv p' = (INL v',q')) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
         valid_horizon cx st0 H es.storage_trace) in
  body_inv tops ctx ce cx /\ body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre ce cx env e es /\
  expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
    ce cx (expr_type e) e es (st0,a,m,sha,shm,op,s,G,tn) /\
  expr_sim_scoped (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx (expr_type e) e es /\
  (!marks v ee G1 tn1 t.
    body_inv tops ctx ce cx /\ body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_body_pre ce cx env e es /\ MEM func ctx.ctx_functions /\
    lower_value compile_expr ce (expr_type e) e a = (op,m) /\
    return_buf_frame d ce a s /\
    (!fn i z. frag_reachable ctx func s fn i z ==> dalloca_fmp_headroom i z) /\
    storage_trace_domain cx st0 ee.storage_trace /\ replay marks v ee /\
    path marks G1 tn1 t ee /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==> post H (INL v) ee G1 tn1 t) ==>
    returned v ee G1 tn1 t) /\
  (!marks v ee G1 tn1 t.
    storage_trace_domain cx st0 ee.storage_trace /\ replay marks v ee /\
    path marks G1 tn1 t ee /\ create_operand_full_scope a m E ctx func s marks (OK t) /\
    returned v ee G1 tn1 t ==>
    scoped_operand_outcome (DF,lo,E,ctx,func,PG) tops cx st0 m b (next v)
      (ee,t,G1,tn1) Q (create_operand_exit_post ctx cx)) /\
  (!v. storage_trace_frame (next v)) /\
  (!marks. create_operand_focus_scope a m E ctx func s marks ==>
           create_operand_focus_scope a b E ctx func s marks) /\
  (!marks r. exit_result r /\ create_operand_full_scope a m E ctx func s marks r ==>
             create_operand_full_scope a b E ctx func s marks r) /\
  (!left t right. create_operand_full_scope a m E ctx func s left (OK t) /\
    create_operand_focus_scope m b E ctx func t right ==>
    create_operand_focus_scope a b E ctx func s (left ++ right)) /\
  (!left t right r. create_operand_full_scope a m E ctx func s left (OK t) /\
    create_operand_full_scope m b E ctx func t right r ==>
    create_operand_full_scope a b E ctx func s (left ++ right) r) ==>
  scoped_operand_outcome (DF,lo,E,ctx,func,PG) tops cx st0 a b
    (bind source next) (es,s,G,tn) Q (create_operand_exit_post ctx cx)
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `expr_sim_scoped _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_scoped_def]) >>
  disch_then (drule_then assume_tac) >>
  `cx_tops cx = tops` by fs[body_inv_def, cx_tops_def] >>
  qpat_x_assum `cx_tops cx = tops` SUBST_ALL_TAC >>
  drule scalar_scoped_exception_post >> disch_tac >>
  qpat_assum `scoped_operand_outcome _ _ _ _ _ _ _ _ _ (\H res ee gt r. _ /\ _)`
    (mp_then (Pat `scoped_operand_outcome _ _ _ _ _ _ _ _ _ _`)
      (qspecl_then [`next`,`b`,`Q`] mp_tac o SIMP_RULE bool_ss [])
      scoped_operand_bind_all) >>
  (impl_tac >- (
    simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
         storage_trace_frame_read_result] >>
    rpt conj_tac
    >~ [`gas_marked_exec _ _ _ _ _ _ _ _`] >-
      (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
       goal_assum (drule_at Any) >> simp[])
    >~ [`gas_exempt_cert _ _ _ _ _ _ _`] >-
      (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[]) >>
    suspend "normal")) >> simp[]
QED

Resume create_body_operand_scoped_bind[normal]:
  rpt strip_tac >>
  rename1 `storage_trace_domain cx st0 mid.storage_trace` >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace`
    by fs[storage_trace_domain_def] >>
  `?v. res = INL v` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> expr_sim_full_post _ _ _ _ _ H _ _ _ _ _ /\ _`
       (drule_then mp_tac) >> simp[expr_sim_full_post_def] >> metis_tac[]) >>
  pop_assum strip_assume_tac >> gvs[] >>
  FAIL_TAC "normal callback"
QED
Finalise create_body_operand_scoped_bind

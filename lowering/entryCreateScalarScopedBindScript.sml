(* Specialize scoped sequencing to one ordinary value-mode operand. *)
Theory entryCreateScalarScopedBind
Ancestors
  entryCreateScopedBind entryCreateFocusSpec entryCreateCompletedCut
  exprSimFullBundleProps bodySim exprSimDefs gasContext
  gasExemptCert vyperStorageTrace vyperStorageFootprint vyperState

Theorem scalar_scoped_exception_post[local]:
  (\H (res : 'a + exception) ee gt r. ?exc. res = INR exc /\
    create_operand_exit_post ctx cx H (INR exc : 'b + exception) ee gt r) =
  create_operand_exit_post ctx cx
Proof
  simp[FUN_EQ_THM] >> rpt gen_tac >>
  Cases_on `res` >- simp[create_operand_exit_post_def] >>
  rename1 `INR ex` >> Cases_on `ex` >> Cases_on `r` >>
  simp[create_operand_exit_post_def, halt_exit_def, expr_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >> simp[expr_exit_def]
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
  irule scoped_operand_bind_all_mixed >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result] >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`] >-
    (rpt strip_tac >> pure_rewrite_tac[ignore_bind_def] >>
     pure_once_rewrite_tac[bind_assoc] >> irule gas_exempt_cert_bind_value >>
     qexistsl_tac [`mid`,`t`,`v`] >> fs[ignore_bind_def])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`] >-
    (rpt strip_tac >> pure_rewrite_tac[ignore_bind_def] >>
     pure_once_rewrite_tac[bind_assoc] >> irule gas_exempt_cert_error_value >>
     simp[ignore_bind_def]) >>
  qexistsl_tac [`expr_sim_full_post (DF,lo,d,ctx,func) ce cx e (es,a,m,s,op,G,tn)`, `m`] >>
  (rpt conj_tac >> TRY (first_assum ACCEPT_TAC))
  >- suspend "normal" >>
  pure_rewrite_tac[scalar_scoped_exception_post] >> first_assum ACCEPT_TAC
QED

Resume create_body_operand_scoped_bind[normal]:
  rpt strip_tac >>
  rename1 `storage_trace_domain cx st0 mid.storage_trace` >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace`
    by fs[storage_trace_domain_def] >>
  `?v. res = INL v` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> expr_sim_full_post _ _ _ _ _ H _ _ _ _ _ /\ _`
       (drule_then (strip_assume_tac o SIMP_RULE bool_ss [expr_sim_full_post_def])) >>
     goal_assum (drule_at Any)) >>
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >>
  qexists_tac `v` >> simp_tac bool_ss [] >>
  qpat_x_assum `expr_sim_full_pre _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [s1PrefixDefsTheory.expr_sim_full_pre_def]) >>
  qpat_x_assum `!marks v ee G1 tn1 t. body_inv _ _ _ _ /\ _ ==> _`
    (qspecl_then [`marks`,`v`,`mid`,`G1`,`tn1`,`t`] mp_tac) >>
  (impl_tac >- (rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >>
    qx_gen_tac `H` >> disch_tac >>
    qpat_assum `!H. valid_horizon _ _ H _ ==> expr_sim_full_post _ _ _ _ _ H _ _ _ _ _ /\ _`
      (qspec_then `H` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    rpt (pop_assum kall_tac) >>
    simp_tac bool_ss [expr_sim_full_post_def, sumTheory.INL_11] >> metis_tac[])) >>
  disch_tac >>
  qpat_x_assum `!marks v ee G1 tn1 t. _ ==> scoped_operand_outcome _ _ _ _ _ _ _ _ _ _`
    (qspecl_then [`marks`,`v`,`mid`,`G1`,`tn1`,`t`] mp_tac) >>
  (impl_tac >- (rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >>
    qx_gen_tac `H` >> disch_tac >>
    qpat_assum `!H. valid_horizon _ _ H _ ==> expr_sim_full_post _ _ _ _ _ H _ _ _ _ _ /\ _`
      (qspec_then `H` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    rpt (pop_assum kall_tac) >> metis_tac[])) >>
  disch_then ACCEPT_TAC
QED
Finalise create_body_operand_scoped_bind

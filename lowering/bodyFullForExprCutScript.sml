(* Common expression cut of an array For. *)
Theory bodyFullForExprCut
Ancestors
  bodyFullForArray bodyFullIfExpReach bodyFullShared bodyFullForFacts
  stmtLoweringMono gasShadowCompileStmtHelpers gasOutcomeFullCompose gasExemptCert
  exprSimSource loweringPosts vyperEvalExprPreservesScopesDom vyperStorageTrace
  vyperStorageFootprint stmtSimForRounds vyperInterpreter vyperState
  stmtSimDefs stmtSimProps exprSimDefs bodyPtrDefs haltExitProj

Definition for_array_loop_post_def:
  for_array_loop_post (DF,lo,d,ctx,func) c cx lctx
    (es,sa,s0,G0,tn0) sb H res ee G tn t <=>
    stmt_lands lctx sb res t /\ ~t.vs_halted /\
    (res = INL () ==> ~block_is_terminated sb) /\
    cenv_top_ext c c ee.scopes /\
    stmt_state_rel H ctx func c cx ee t /\
    storage_well_formed_on cx ee (FST H) /\
    return_buf_frame d c sb t /\ alloca_history func t /\
    return_buf_sep d c ee t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at (DF H) lo d c cx ee G tn t /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
           lookup_var x t = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
             FLOOKUP t.vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sa x ==>
         FLOOKUP G x = FLOOKUP G0 x /\
         op_taint tn (Var x) = op_taint tn0 (Var x)) /\
    alloca_frame c es sa s0 c ee t /\
    (!aid off sz i.
       FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
       (!n b sz'. local_region c es.scopes s0 n b sz' ==>
                  off + sz <= b \/ b + sz' <= off) /\
       off <= i /\ i < off + sz /\ i IN tn.t_mem ==>
       i IN tn0.t_mem)
End

Definition for_array_loop_exit_def:
  for_array_loop_exit ctx cx RetQ H res ee gt r <=>
    (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
    halt_exit H cx ee res r /\
    (ctx_has_dalloca ctx ==>
     !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s)
End

Theorem for_array_loop_post_witness:
  for_array_loop_post (DF,lo,d,ctx,func) c cx lctx (es,sa,s0,G0,tn0)
    sb H res ee G tn t ==>
  ?c'. stmt_lands lctx sb res t /\ ~t.vs_halted /\
    (res = INL () ==> ~block_is_terminated sb /\ c' = c) /\
    cenv_top_ext c c' ee.scopes /\
    stmt_state_rel H ctx func c' cx ee t /\
    storage_well_formed_on cx ee (FST H) /\
    return_buf_frame d c' sb t /\ alloca_history func t /\
    return_buf_sep d c' ee t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at (DF H) lo d c' cx ee G tn t /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
           lookup_var x t = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
             FLOOKUP t.vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sa x ==>
         FLOOKUP G x = FLOOKUP G0 x /\
         op_taint tn (Var x) = op_taint tn0 (Var x)) /\
    alloca_frame c es sa s0 c' ee t /\
    (!aid off sz i.
       FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
       (!n b sz'. local_region c es.scopes s0 n b sz' ==>
                  off + sz <= b \/ b + sz' <= off) /\
       off <= i /\ i < off + sz /\ i IN tn.t_mem ==>
       i IN tn0.t_mem)
Proof
  simp[for_array_loop_post_def] >> strip_tac >> qexists_tac `c` >>
  simp[] >> first_assum ACCEPT_TAC
QED

Definition for_array_expr_endpoint_def:
  for_array_expr_endpoint (DF,lo,d,ctx,func) c cx e (es,sa,s0,G0,tn0)
    (vv,se) H rv em G tn u <=>
    ~u.vs_halted /\ em.gas_obs = [] /\
    vv_post H ctx func c cx e es sa se s0 em rv vv u /\
    vv_store_bound cx (post_value_type c e) (lowered_value_type c e) em rv vv u /\
    u.vs_current_bb = se.cs_current_bb /\ u.vs_inst_idx = LENGTH se.cs_current_insts /\
    alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    s0.vs_alloca_next <= u.vs_alloca_next /\
    ghost_inv_at (DF H) lo d c cx em G tn u /\
    ptr_vv_ok cx (post_value_type c e) rv vv em G tn u /\
    (!v. rv = Value v /\ ~is_word_type (post_value_type c e) /\
      ~is_bytestring_type (post_value_type c e) ==>
      vv_own c cx (post_value_type c e) sa se em rv vv u /\
      (!ty p. vv = LocatedValue ty p ==> p.ptr_location = LocMemory)) /\
    (c.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
      ?v. read_result cx rv em = (INL v,em) /\
        !rt w. evaluate_type (get_tenv cx) (post_value_type c e) = SOME rt /\
          eval_operand (vv_operand vv) u = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn.t_mem u.vs_memory mem ==>
             val_in_memory rt v (w2n w) mem)) /\
    (!ty op. vv = StackValue ty op /\ ~is_word_type (post_value_type c e) ==>
      ptr_buf_ok c e op G u) /\
    (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok c e p.ptr_operand G u) /\
    ghost_kept_at lo c es sa G0 tn0 s0 G tn
End

Theorem for_array_expr_compile_code[local]:
  compile_stmt c lctx ret_ty (For id typ (Array e) n loop_body) sa = ((),sb) /\
  compile_expr c (expr_type e) e sa = (vv,se) /\ fn_has_code sa sb func ==>
  fn_has_code sa se func /\ ci_mono sa se /\ ci_mono se sb
Proof
  strip_tac >> drule_all compile_for_array_expr_prefix_mono >> strip_tac >>
  `ci_mono sa se` by
    (qpat_assum `compile_expr _ _ _ _ = _` (fn th =>
       qspecl_then [`c`,`expr_type e`,`e`,`sa`] mp_tac
         (cj 1 ci_mono_compile_expr_sa) >> simp[th])) >>
  simp[] >> irule fragExecTheory.fn_has_code_mid >>
  conj_tac >- fs[exprLoweringPropsTheory.ci_mono_def] >>
  qexistsl [`sb`,`sa`] >> fs[exprLoweringPropsTheory.ci_mono_def, compileEnvTheory.cs_extends_refl]
QED

Theorem for_array_expr_compile_cuts:
  compile_stmt c lctx ret_ty (For id typ (Array e) n loop_body) sa = ((),sb) /\
  compile_stmt c lctx ret_ty (gas_shadow_stmt (For id typ (Array e) n loop_body)) sha = ((),shb) /\
  fn_has_code sa sb func /\ fn_has_code sha shb shfunc /\
  gas_shadow_state sa sha ==>
  ?vv se she. compile_expr c (expr_type e) e sa = (vv,se) /\
    compile_expr c (expr_type e) (gas_shadow_expr e) sha = (vv,she) /\
    gas_shadow_state se she /\ fn_has_code sa se func /\
    fn_has_code sha she shfunc /\ ci_mono sa se /\ ci_mono se sb
Proof
  strip_tac >>
  Cases_on `compile_expr c (expr_type e) e sa` >>
  Cases_on `compile_expr c (expr_type e) (gas_shadow_expr e) sha` >>
  `gas_shadow_compiles (compile_expr c (expr_type e) e)
    (compile_expr c (expr_type e) (gas_shadow_expr e))` by
    irule gas_shadow_stmt_compile_expr >>
  drule_all gas_shadow_step >> strip_tac >> gvs[] >>
  drule_all for_array_expr_compile_code >> strip_tac >>
  fs[gasShadowTheory.gas_shadow_stmt_def,gasShadowTheory.gas_shadow_iterator_def] >>
  drule_all (Q.INST [`e` |-> `gas_shadow_expr e`]
      for_array_expr_compile_code |> SRULE []) >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem for_array_expr_source_cut[local]:
  evaluate_type (get_tenv cx) typ = SOME tyv ==>
  eval_stmt cx (For id typ (Array e) n loop_body) =
    bind (eval_expr cx e)
      (\rv. bind (array_iterator_results cx (expr_type e) rv)
        (\vs. ignore_bind (check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long")
                       (eval_for cx tyv id loop_body vs)))
Proof
  strip_tac >> simp[Once evaluate_def, lift_option_type_def, bind_return] >>
  simp[Once evaluate_def, bind_assoc]
QED

(* Binding the source at the expression cut requires no array-kind facts. *)
Theorem for_array_expr_finish:
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (eval_expr cx e) (es,s0,G0,tn0)
    (\H res em G tn u. ?rv. res = INL rv /\
       for_array_expr_endpoint (DF,lo,d,ctx,func) c cx e (es,sa,s0,G0,tn0)
         (vv,se) H rv em G tn u)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !t. r = Halt t ==> allocas_below_fmp t)) /\
  gas_admissible (eval_stmt cx (For id typ (Array e) n loop_body)) (stmt_res_ok lctx) es /\
  (!marks rv em G tn u.
    (!tail. eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
                            (INL rv,em with gas_obs := tail)) /\
    storage_trace_domain cx st0 em.storage_trace /\
    (!H. valid_horizon cx st0 H em.storage_trace ==>
       for_array_expr_endpoint (DF,lo,d,ctx,func) c cx e (es,sa,s0,G0,tn0)
         (vv,se) H rv em G tn u) /\
    (!H. valid_horizon cx st0 H em.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (s0,G0,tn0) marks (OK u,G,tn)) /\
    gas_admissible
      (bind (array_iterator_results cx (expr_type e) rv)
        (\vs. ignore_bind (check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long")
                         (eval_for cx tyv id loop_body vs))) (stmt_res_ok lctx) em ==>
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0
      (bind (array_iterator_results cx (expr_type e) rv)
        (\vs. ignore_bind (check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long")
                         (eval_for cx tyv id loop_body vs)))
      (em,u,G,tn) Q (for_array_loop_exit ctx cx RetQ)) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (eval_stmt cx (For id typ (Array e) n loop_body))
    (es,s0,G0,tn0) Q (for_array_loop_exit ctx cx RetQ)
Proof
  strip_tac >> drule for_array_expr_source_cut >>
  disch_then (qspec_then `n` (qspec_then `loop_body` (qspec_then `id`
    (qspec_then `e` SUBST_ALL_TAC)))) >>
  irule gas_outcome_full_bind_all_path >> BETA_TAC >>
  conj_tac >-
    (gen_tac >> irule storage_trace_frame_bind >>
     simp[storage_trace_frame_array_iterator_results,storage_trace_frame_ignore_bind,
          storage_trace_frame_checks,cj 4 evaluate_storage_trace_frame]) >>
  conj_tac >-
    (rpt strip_tac >> irule gas_exempt_cert_bind_result >>
     goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >-
    (rpt strip_tac >> irule gas_exempt_cert_error_result >> first_assum ACCEPT_TAC) >>
  conj_tac >- simp[cj 5 evaluate_storage_trace_frame] >>
  qexists_tac `\H res em G tn u. ?rv. res = INL rv /\
      for_array_expr_endpoint (DF,lo,d,ctx,func) c cx e (es,sa,s0,G0,tn0)
        (vv,se) H rv em G tn u` >> BETA_TAC >>
  reverse conj_tac >-
    (irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
     qpat_assum `gas_outcome_full _ _ _ _ (eval_expr _ _) _ _ _` (irule_at Any) >>
     simp[NoAsms] >> rpt gen_tac >> Cases_on `res` >>
     simp[for_array_loop_exit_def,expr_exit_INL] >> strip_tac >> conj_tac
     >- (simp[stmt_exit_ptr_def] >> metis_tac[stmtSimPropsTheory.expr_exit_INR_type]) >>
     conj_tac >- metis_tac[halt_exit_INR_type] >>
     rpt strip_tac >> gvs[expr_exit_def]) >>
  rpt gen_tac >> strip_tac >>
  rename1 `storage_trace_domain cx st0 em.storage_trace` >>
  `valid_horizon cx st0 (storage_trace_horizon em.storage_trace) em.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H em.storage_trace ==> ?rv. _`
    (qspec_then `storage_trace_horizon em.storage_trace` (drule_then strip_assume_tac)) >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  disj1_tac >> qexists_tac `rv` >> simp[] >>
  qpat_assum `!marks rv em G tn u. _ ==> gas_outcome_full _ _ _ _ _ _ _ _` irule >>
  conj_tac >- (qexists_tac `marks` >> simp[]) >>
  conj_tac >-
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> ?rv'. _` mp_tac >>
     simp[NoAsms] >> disch_then (qspec_then `H` mp_tac) >>
     simp[] >> first_assum ACCEPT_TAC) >>
  drule_all gas_admissible_bind_tail >> simp[gasContextTheory.gas_admissible_gas_obs]
QED

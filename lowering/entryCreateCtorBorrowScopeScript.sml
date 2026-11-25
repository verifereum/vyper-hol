(* Reading the borrowed constructor row preserves the supplied VV scope. *)
Theory entryCreateCtorBorrowScope
Ancestors
  entryCreateFocusSpec bodyFullCreateHeld bodyFullAttribute s1PrefixDefs
  gasShadowCompileBase gasSummaryCompose gasStorage gasExemptCert
  exprSimMemorySource exprSimUnwrap fragGasPath stmtSimProps
  entryCreateCompletedCut exprLowering compileEnv vyperState vyperStorageTrace
  fragGasOriginPtr bodyFullIfExpReach vyperStorageFootprint fragExec exprSimDefs

Theorem borrowed_vv_field_post[local]:
  create_operand_vv_post (DF,lo,d,ctx,func) ce cx e (es,sa,sb,s0,vv,G0,tn0)
    H res ee G tn t /\ create_operand_at sb t ==>
  field_vv_post (DF,lo,d,ctx,func) ce cx e (es,sa,sb,s0,vv,G0,tn0)
    H res ee G tn t
Proof
  rewrite_tac[create_operand_vv_post_def, create_operand_at_def, field_vv_post_def] >>
  strip_tac >> qexists_tac `tv` >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem borrowed_vv_read[local]:
  field_vv_post (DF,lo,d,ctx,func) ce cx e (es,sa,sb,s0,vv,G0,tn0)
    H res ee G tn t ==>
  ?tv v. res = INL tv /\ read_result cx tv ee = (INL v,ee)
Proof
  rewrite_tac[field_vv_post_def] >> strip_tac >> qexists_tac `tv` >> simp[] >>
  Cases_on `read_result cx tv ee` >> drule_then SUBST_ALL_TAC read_result_state >>
  Cases_on `q` >> gvs[] >> metis_tac[vv_post_failed_read]
QED

Theorem create_ctor_borrowed_head_scoped:
  expr_body_pre ce cx env e es /\ body_inv tops ctx ce cx /\
  expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx (expr_type e) e es
    (st0,sa,sb,sha,shb,vv,s0,G0,tn0) /\
  expr_vv_sim_scoped (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx (expr_type e) e es /\
  sv = ext_call_arg_value (lowered_value_type ce e) vv /\
  ~is_word_type (vv_type sv) /\ ~is_word_type (lowered_value_type ce e) ==>
  compile_snapshot_vv ce F sv sb = (sv,sb) /\
  compile_snapshot_vv (gas_shadow_env sd ce) F sv shb = (sv,shb) /\
  scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
    (cx_tops cx) cx st0 sa sb (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (create_ctor_borrowed_head_post (DF,lo,d,ctx,func) ce cx e (es,sa,sb,s0,vv,sv,G0,tn0))
    (create_operand_exit_post ctx cx)
Proof
  strip_tac >>
  conj_tac >- simp[compile_snapshot_vv_def, comp_return_def] >>
  conj_tac >- simp[compile_snapshot_vv_gas_shadow_env, compile_snapshot_vv_def, comp_return_def] >>
  qpat_x_assum `expr_vv_sim_scoped _ _ _ _ _ _`
    (drule_then strip_assume_tac o REWRITE_RULE[expr_vv_sim_scoped_def]) >>
  qpat_x_assum `scoped_operand_outcome _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o BETA_RULE o REWRITE_RULE[scoped_operand_outcome_def])
  >~ [`gas_bad_storage_at _ _ _ _ _ _`]
  >- (rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `marks` >> disj1_tac >>
      conj_tac
      >- (irule gas_bad_storage_at_bind_left >> simp[storage_trace_frame_read_result]) >>
      metis_tac[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rename1 `gas_origin_ptr_focus _ _ _ (_,_,_,_,stop)` >>
      rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `marks` >> disj2_tac >> disj2_tac >>
      qexistsl_tac [`err`,`ee`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`stop`] >>
      simp[] >> conj_tac
      >- (simp[ignore_bind_def,bind_assoc] >> irule gas_exempt_cert_error_result >>
          first_assum ACCEPT_TAC) >>
      qexists_tac `H` >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  Cases_on `exit_result r`
  >- suspend "terminal" >>
  suspend "normal"
QED

Resume create_ctor_borrowed_head_scoped[terminal]:
  rename1 `create_operand_full_scope _ _ _ _ _ _ ms r` >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
        (s0,G0,tn0) ms (r,G',tn') /\
      create_operand_exit_post ctx cx H res (ee with gas_obs := []) (G',tn') r` by
    (rpt strip_tac >> res_tac >> fs[exit_result_def]) >>
  `expr_exit res r` by
    (qpat_assum `!H. _ ==> _ /\ create_operand_exit_post _ _ _ _ _ _ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1 o
         REWRITE_RULE[create_operand_exit_post_def] o CONJUNCT2))) >>
  `?exc. res = INR exc` by (Cases_on `res` >> fs[expr_exit_INL]) >>
  gvs[] >> rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `ms` >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`INR exc`,`ee`,`r`,`G'`,`tn'`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (irule gas_source_bind_exception >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >> qx_gen_tac `hz` >> disch_tac >>
  qpat_x_assum `!H. _ ==> _ /\ create_operand_exit_post _ _ _ _ _ _ _`
    (qspec_then `hz` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  conj_tac >- first_assum ACCEPT_TAC >> disj2_tac >> conj_tac >- first_assum ACCEPT_TAC >>
  qhdtm_assum `create_operand_exit_post` mp_tac >>
  SIMP_TAC bool_ss [create_operand_exit_post_def, expr_exit_INR_type, halt_exit_def,
    sumTheory.INR_11] >> rpt strip_tac >>
  qpat_assum `_ ==> ?s. r = Halt s /\ _` (drule_then ACCEPT_TAC)
QED

(* No target instruction or ghost update separates the VV exit from the read. *)
Resume create_ctor_borrowed_head_scoped[normal]:
  `?t. r = OK t` by metis_tac[storage_trace_domain_def] >> gvs[] >>
  qabbrev_tac `mid = ee with gas_obs := []` >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
        (s0,G0,tn0) marks (OK t,G',tn') /\
      field_vv_post (DF,lo,d,ctx,func) ce cx e (es,sa,sb,s0,vv,G0,tn0)
        H res mid G' tn' t` by
    (rpt strip_tac >> res_tac >> TRY (first_assum ACCEPT_TAC) >>
     irule borrowed_vv_field_post >> simp[create_operand_at_def]) >>
  qpat_assum `!H. _ ==> _ /\ field_vv_post _ _ _ _ _ _ _ _ _ _ _`
    (drule_then strip_assume_tac) >>
  drule_then strip_assume_tac borrowed_vv_read >> gvs[] >>
  `~t.vs_halted` by metis_tac[gas_origin_ptr_path_erase,gas_path_normal] >>
  qpat_x_assum `expr_vv_sim_full_pre _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[expr_vv_sim_full_pre_def]) >>
  rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `marks` >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`INL v`,`ee`,`OK t`,`G'`,`tn'`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qx_gen_tac `tail` >>
      qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `tail` assume_tac) >>
      drule read_result_gas_obs >> disch_then (qspec_then `tail` assume_tac) >>
      fs[Abbr `mid`,vyperStateTheory.bind_def]) >>
  conj_tac >- first_assum ACCEPT_TAC >> qx_gen_tac `hz` >> disch_tac >>
  qpat_assum `!H. _ ==> _ /\ field_vv_post _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `hz` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  conj_tac >- first_assum ACCEPT_TAC >> disj1_tac >> qexists_tac `t` >> simp[] >>
  irule create_ctor_borrowed_head_endpoint >>
  simp[] >> rpt conj_tac
  >- (qexists_tac `tops` >> first_assum ACCEPT_TAC)
  >- (qexists_tac `st0` >> reverse conj_tac >- simp[Abbr `mid`] >>
      rpt strip_tac >> qpat_assum `!H. _ ==> stmt_state_rel H _ _ _ _ _ _ /\ _`
        (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC)
  >- (qexists_tac `env` >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`gas_explicit marks s0.vs_gas_readings`,`tv`] >> simp[] >>
  qunabbrev_tac `mid` >>
  qpat_assum `!tail. eval_expr _ _ _ = _`
    (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE[listTheory.APPEND_NIL]))
QED

Finalise create_ctor_borrowed_head_scoped

(* Counted composition at the exact base and key cuts of a mapping subscript. *)
Theory bodyWriteMapBindCutsMods
Ancestors
  bodyWriteTargetStageMods bodyFullPostsMods bodyFullTargetSubscript
  bodyFullIfExpReach gasOutcomeFullMods gasOutcomeFullBindMods gasOutcomeFullPostMods
  vyperStorageFootprint targetPlaceSimDefs bodyFullTargetDefs fragExec exprSimDefs
  stmtSimForRounds haltExitProj targetSubscriptSplit targetSubscriptContinuation
  exprSimWordArgs exprLoweringProps gasContext gasShadow freshWrites
  bodyMemoryDefs vyperStorageTrace vyperInterpreter vyperState
  fragGasOriginPtr gasExemptCertMods venomExecSemantics unitTransformDefs
  contextRawReachable venomInst venomState list

(* Retain the path for transferring reachable headroom to the key cut. *)
Theorem map_bind_keep_base_path[local]:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source
    (es,s,G,tn) Q R ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source
    (es,s,G,tn)
    (\H res ee G' tn' t. Q H res ee G' tn' t /\
      ?marks. gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (s,G,tn) marks (OK t,G',tn')) R
Proof
  rewrite_tac[gas_outcome_full_mods_def] >> strip_tac >> qexists_tac `marks`
  >- (disj1_tac >> simp[] >> goal_assum (drule_at Any) >>
      rpt (goal_assum (drule_at Any)) >> simp[])
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >>
      simp[] >> rpt strip_tac >> first_x_assum drule >> strip_tac >> gvs[] >>
      disj1_tac >> simp[] >> qexists_tac `marks` >> simp[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Theorem map_key_admissible[local]:
  gas_admissible (bind k next) target_res_ok mid ==>
  gas_admissible k expr_res_ok mid
Proof
  simp[gas_admissible_def] >> rpt strip_tac >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  first_x_assum (qspec_then `gs` mp_tac) >>
  simp[bind_def,target_res_ok_def,expr_res_ok_def]
QED

Theorem map_key_horizon[local]:
  bind (eval_expr cx e) (read_result cx) (mid with gas_obs := obs) = (res,ee) /\
  valid_horizon cx st0 H ee.storage_trace ==>
  valid_horizon cx st0 H mid.storage_trace
Proof
  strip_tac >>
  qpat_assum `bind _ _ _ = _`
    (mp_then (Pat `_ = _`) mp_tac valid_horizon_frame) >>
  simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,
       storage_trace_frame_read_result]
QED

Theorem write_map_bind_cuts_mods:
  type_place_target env bt = SOME (HashMapT kt vt) /\
  type_place_target env (SubscriptTarget bt e) = SOME vt /\
  write_target_entry_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (SubscriptTarget bt e) es st0 sa sb shadow_sa shadow_sb r s0 G0 tn0 /\
  gas_admissible (eval_base_place cx (SubscriptTarget bt e)) target_res_ok es /\
  write_target_entry_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx bt es st0 sa sm shadow_sa shadow_sm rb s0 G0 tn0 /\
  lower_value compile_expr cenv (expr_type e) e sm = (iop,sn) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
    (gas_shadow_expr e) shadow_sm = (iop,shadow_sn) /\
  gas_shadow_state sm shadow_sm /\ gas_shadow_state sn shadow_sn /\
  ci_mono sa sm /\ fn_has_code sm sn func /\ fn_has_code shadow_sm shadow_sn shadow_func /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  write_base_sim_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx env bt es /\
  (!base_gas pv mid1. eval_base_place cx bt (es with gas_obs := base_gas) = (INL pv,mid1) ==>
    expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e mid1) /\
  (!base_gas pv mid1 t1 G1 tn1 key_gas v mid2 t2 G2 tn2.
    (!tail. eval_base_place cx bt (es with gas_obs := base_gas ++ tail) =
                 (INL pv,mid1 with gas_obs := tail)) /\
    (!tail. bind (eval_expr cx e) (read_result cx)
                 (mid1 with gas_obs := key_gas ++ tail) = (INL v,mid2 with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid1.storage_trace /\
    storage_trace_domain cx st0 mid2.storage_trace /\
    mid1.gas_obs = [] /\ mid2.gas_obs = [] /\ ~t1.vs_halted /\ ~t2.vs_halted /\
    gas_admissible (extend_place cx pv (ValueSubscript v)) target_res_ok mid2 /\
    (!H. valid_horizon cx st0 H mid2.storage_trace ==>
      write_target_post_mods H (DF H) lo d ctx func cenv cx bt es sa sm s0 mid1 pv
        (HashMapT kt vt) rb G0 tn0 G1 tn1 t1 /\
      expr_post_mods H ctx func cenv cx e mid1 sm sn t1 mid2 v iop t2 /\
      expr_store_bound cx (post_value_type cenv e) v iop t2 /\
      t2.vs_current_bb = sn.cs_current_bb /\ t2.vs_inst_idx = LENGTH sn.cs_current_insts /\
      alloca_history func t2 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t2) /\
      t1.vs_alloca_next <= t2.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx mid2 G2 tn2 t2 /\
      ptr_val_ok cx (post_value_type cenv e) v iop G2 tn2 t2 /\
      (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e iop G2 t2) /\
      ghost_kept_at lo cenv mid1 sm G1 tn1 t1 G2 tn2) ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0 (extend_place cx pv (ValueSubscript v)) (mid2,t2,G2,tn2)
      (\H res ee G tn t. ?p. res = INL p /\
        write_target_post_mods H (DF H) lo d ctx func cenv cx (SubscriptTarget bt e)
          es sa sb s0 ee p vt r G0 tn0 G tn t)
      (\H res ee gt q. expr_exit res q /\ halt_exit H cx ee res q /\
        (ctx_has_dalloca ctx ==> !s. q = Halt s ==> allocas_below_fmp s))) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (eval_base_place cx (SubscriptTarget bt e)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?p. res = INL p /\
      write_target_post_mods H (DF H) lo d ctx func cenv cx (SubscriptTarget bt e)
        es sa sb s0 ee p vt r G0 tn0 G tn t)
    (\H res ee gt q. expr_exit res q /\ halt_exit H cx ee res q /\
      (ctx_has_dalloca ctx ==> !s. q = Halt s ==> allocas_below_fmp s))
Proof
  strip_tac >>
  qpat_assum `write_target_entry_mods _ _ _ (SubscriptTarget bt e) _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [write_target_entry_mods_def]) >>
  `gas_admissible (eval_base_place cx bt) target_res_ok es` by
    (irule target_subscript_base_admissible >> qexists_tac `e` >> simp[]) >>
  `eval_base_place cx (SubscriptTarget bt e) =
     bind (eval_base_place cx bt)
       (\pv. bind (bind (eval_expr cx e) (read_result cx))
                 (\v. extend_place cx pv (ValueSubscript v)))` by
    simp[FUN_EQ_THM,Once evaluate_def,bind_assoc] >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> REWRITE_TAC [th]) >>
  qhdtm_x_assum `write_base_sim_mods` (mp_tac o REWRITE_RULE [write_base_sim_mods_def]) >>
  disch_then (qspecl_then [`st0`,`HashMapT kt vt`,`sa`,`sm`,`shadow_sa`,
                           `shadow_sm`,`rb`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (assume_tac o MATCH_MP map_bind_keep_base_path) >>
  suspend "base_bind"
QED

Resume write_map_bind_cuts_mods[base_bind]:
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ (eval_base_place cx bt) _ baseQ baseR` >>
  irule gas_outcome_full_mods_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> RULE_ASSUM_TAC BETA_RULE >>
      irule gas_exempt_cert_mods_bind_result >> goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_result >> simp[])
  >~ [`storage_trace_frame (eval_base_place _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_extend_place] >> irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame,storage_trace_frame_read_result]) >>
  qexists_tac `\H res ee G tn t. baseQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac >- suspend "key_entry" >>
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ (eval_base_place _ _) _ baseQ baseR` (irule_at Any) >>
  conj_tac >- simp[] >>
  simp[Abbr `baseR`] >> rpt strip_tac >> Cases_on `res` >> fs[expr_exit_def]
QED

Resume write_map_bind_cuts_mods[key_entry]:
  qx_genl_tac [`marks`,`res`,`mid1`,`G1`,`tn1`,`t1`] >> BETA_TAC >> strip_tac >>
  qunabbrev_tac `baseQ` >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon mid1.storage_trace) mid1.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid1.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid1.storage_trace` (drule_then strip_assume_tac)) >>
  gvs[] >> qabbrev_tac `base_gas = gas_explicit marks s0.vs_gas_readings` >>
  `mid1 with gas_obs := [] = mid1` by simp[evaluation_state_component_equality] >>
  `eval_base_place cx bt (es with gas_obs := base_gas) = (INL pv,mid1)` by
    (qpat_assum `!tail. eval_base_place _ _ _ = _` (qspec_then `[]` mp_tac) >>
     rewrite_tac[APPEND_NIL] >>
     qpat_assum `mid1 with gas_obs := [] = mid1` (fn th => rewrite_tac[th])) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e mid1` by
    (qpat_assum `!base_gas pv mid1. _ ==> expr_sim_full_mods _ _ _ _ _ _` drule >> simp[]) >>
  `gas_admissible (bind (bind (eval_expr cx e) (read_result cx))
       (\v. extend_place cx pv (ValueSubscript v))) target_res_ok mid1` by
    (qpat_assum `gas_admissible (bind (eval_base_place _ _) _) _ _`
       (mp_then (Pat `gas_admissible _ _ _`) mp_tac gas_admissible_bind_tail) >>
     BETA_TAC >> disch_then (drule_then mp_tac) >> simp[]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok mid1` by
    (irule map_key_admissible >> qexists_tac `\v. extend_place cx pv (ValueSubscript v)` >> simp[]) >>
  suspend "key_run"
QED

Resume write_map_bind_cuts_mods[key_run]:
  qpat_assum `!H. valid_horizon _ _ H mid1.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid1.storage_trace` (drule_then strip_assume_tac)) >>
  drule_then strip_assume_tac write_target_post_view_mods >>
  `sa.cs_next_var <= sm.cs_next_var` by fs[ci_mono_def] >>
  `!fn inst s. frag_reachable ctx func t1 fn inst s ==> dalloca_fmp_headroom inst s` by
    (match_mp_tac (GEN_ALL gas_origin_ptr_path_dalloca_fmp_headroom) >>
     qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) _ (OK t1,G1,tn1)` (irule_at Any) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `return_buf_frame d cenv sm t1` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >>
     simp[] >> rpt strip_tac >> drule_all wb_frame_vars >> simp[]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  qhdtm_x_assum `expr_sim_full_mods` (mp_tac o REWRITE_RULE [expr_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`sm`,`sn`,`shadow_sm`,`shadow_sn`,`iop`,`t1`,`G1`,`tn1`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid1.storage_trace ==> _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     drule_then strip_assume_tac write_target_post_view_mods >> simp[])) >> strip_tac >>
  suspend "key_bind"
QED

Resume write_map_bind_cuts_mods[key_bind]:
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ (bind (eval_expr cx e) _) _ keyQ keyR` >>
  irule gas_outcome_full_mods_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> RULE_ASSUM_TAC BETA_RULE >>
      irule gas_exempt_cert_mods_bind_value >> goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame (bind _ _)`]
  >- simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,storage_trace_frame_read_result]
  >~ [`storage_trace_frame _`]
  >- simp[storage_trace_frame_extend_place] >>
  qexists_tac `\H res ee G tn t. keyQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac >- suspend "suffix" >>
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ (bind (eval_expr _ _) _) _ keyQ keyR` (irule_at Any) >>
  conj_tac >- simp[] >>
  simp[Abbr `keyR`,Abbr `baseR`] >> rpt strip_tac >>
  Cases_on `res` >> fs[expr_exit_def] >> metis_tac[expr_exit_INR_retype,halt_exit_INR_type]
QED

Resume write_map_bind_cuts_mods[suffix]:
  qx_genl_tac [`marks2`,`res`,`mid2`,`G2`,`tn2`,`t2`] >> BETA_TAC >> strip_tac >>
  qunabbrev_tac `keyQ` >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon mid2.storage_trace) mid2.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid2.storage_trace` (drule_then strip_assume_tac)) >>
  gvs[] >> qabbrev_tac `key_gas = gas_explicit marks2 t1.vs_gas_readings` >>
  `mid2 with gas_obs := [] = mid2` by simp[evaluation_state_component_equality] >>
  `bind (eval_expr cx e) (read_result cx) (mid1 with gas_obs := key_gas) = (INL v,mid2)` by
    (qpat_assum `!tail. bind (eval_expr _ _) _ _ = _` (qspec_then `[]` mp_tac) >>
     rewrite_tac[APPEND_NIL] >>
     qpat_assum `mid2 with gas_obs := [] = mid2` (fn th => rewrite_tac[th])) >>
  `gas_admissible (extend_place cx pv (ValueSubscript v)) target_res_ok mid2` by
    (qpat_assum `gas_admissible (bind (bind (eval_expr _ _) _) _) _ _`
       (mp_then (Pat `gas_admissible _ _ _`) mp_tac gas_admissible_bind_tail) >>
     BETA_TAC >> disch_then (drule_then mp_tac) >> simp[]) >>
  `!H. valid_horizon cx st0 H mid2.storage_trace ==> valid_horizon cx st0 H mid1.storage_trace` by
    (rpt strip_tac >> drule_all map_key_horizon >> simp[]) >>
  qunabbrev_tac `baseR` >>
  qpat_assum `!base_gas pv mid1 t1 G1 tn1 key_gas v mid2 t2 G2 tn2. _ ==> _` irule >>
  asm_rewrite_tac[] >>
  qexistsl_tac [`G1`,`base_gas`,`key_gas`,`mid1`,`t1`,`tn1`] >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_assum `!H. valid_horizon _ _ H mid1.storage_trace ==> _ /\ _`
    (qspec_then `H` mp_tac) >> simp[]
QED

Finalise write_map_bind_cuts_mods

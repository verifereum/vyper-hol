(* Linked array target: compose the base and index before entering the suffix. *)
Theory bodyWriteArrayBindMods
Ancestors
  bodyWriteArrayPacketMods bodyFullPredsMods bodyFullTargetSubscript
  bodyFullIfExpReach bodyBranchCellFrameMods bodyWriteSubscriptSourceMods
  gasOutcomeFullBindMods gasOutcomeFullPostMods stmtSimForRounds
  haltExitProj targetSubscriptSplit exprSimWordArgs
  exprLoweringProps gasContext vyperStorageTrace supportedExprs
  gasOutcomeFullMods exprSimDefs targetPlaceSimDefs vyperStorageFootprint
  bodyWriteTargetStageMods vyperState vyperInterpreter gasExemptCertMods
  fragGasOriginPtr gasShadow bodyFullPostsMods bodyMemoryDefs freshWrites list
  venomExecSemantics unitTransformDefs contextRawReachable venomInst venomState

Theorem array_base_path[local]:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source
    (es,s,G,tn) Q R /\
  (!marks H res ee G' tn' t.
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (s,G,tn) marks (OK t,G',tn') /\ Q H res ee G' tn' t ==>
    Q' H res ee G' tn' t) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source
    (es,s,G,tn) Q' R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_mods_def]) >>
  rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks`
  >- (disj1_tac >> metis_tac[])
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >>
      rpt conj_tac >- simp[] >- simp[] >>
      rpt strip_tac >> first_x_assum drule >> strip_tac >> gvs[]
      >- (disj1_tac >> first_x_assum irule >> simp[] >>
          qexists_tac `marks` >> simp[]) >>
      disj2_tac >> simp[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Theorem array_index_admissible[local]:
  gas_admissible (bind index next) target_res_ok mid ==>
  gas_admissible index expr_res_ok mid
Proof
  simp[gas_admissible_def] >> rpt strip_tac >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  first_x_assum (qspec_then `gs` mp_tac) >>
  simp[bind_def,target_res_ok_def,expr_res_ok_def]
QED

Theorem array_index_horizon[local]:
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

Theorem write_array_index_bind_mods:
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  expr_sim_inv_mods mods cenv cx env es /\
  body_const_cells_agree_mods mods cx env es /\
  type_place_target env bt = SOME (Type (ArrayT et bd)) /\
  alloc_limits_target cenv (SubscriptTarget bt e) /\
  (!i s. MEM i (target_indices (SubscriptTarget bt e)) /\
         expr_sim_inv_mods mods cenv cx env s ==>
         expr_body_pre_mods mods cenv cx env i s) /\
  body_base_target_full_ok_mods mods exps cx (SubscriptTarget bt e) /\
  write_base_sim_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx env bt es /\
  (!sa sb shadow_sa shadow_sb r.
    compile_get_target_ptr compile_expr cenv (SubscriptTarget bt e) sa = (r,sb) /\
    compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
      (gas_shadow_target (SubscriptTarget bt e)) shadow_sa = (r,shadow_sb) /\
    gas_shadow_state sa shadow_sa /\
    fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func ==>
    ?rb sm iop sn shadow_sm shadow_sn.
      compile_get_target_ptr compile_expr cenv bt sa = (rb,sm) /\
      lower_value compile_expr cenv (expr_type e) e sm = (iop,sn) /\
      target_subscript_suffix cenv e rb iop sn = (r,sb) /\
      compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
        (gas_shadow_target bt) shadow_sa = (rb,shadow_sm) /\
      lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
        (gas_shadow_expr e) shadow_sm = (iop,shadow_sn) /\
      gas_shadow_state sm shadow_sm /\ gas_shadow_state sn shadow_sn /\
      ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn sb /\
      fn_has_code sa sm func /\ fn_has_code sm sn func /\ fn_has_code sn sb func /\
      fn_has_code shadow_sa shadow_sm shadow_func /\
      fn_has_code shadow_sm shadow_sn shadow_func) /\
  (!st pv mid. expr_sim_inv_mods mods cenv cx env st /\
      body_const_cells_agree_mods mods cx env st /\
      (!i s. MEM i (target_indices bt) /\ expr_sim_inv_mods mods cenv cx env s ==>
             expr_body_pre_mods mods cenv cx env i s) /\
      eval_base_place cx bt st = (INL pv,mid) ==>
      expr_sim_inv_mods mods cenv cx env mid /\
      body_const_cells_agree_mods mods cx env mid) /\
  (!st v mid. expr_body_pre_mods mods cenv cx env e st /\
      body_const_cells_agree_mods mods cx env st /\
      bind (eval_expr cx e) (read_result cx) st = (INL v,mid) ==>
      expr_sim_inv_mods mods cenv cx env mid /\
      value_runtime_typed env (expr_type e) v) /\
  (!st0 vt sa s0 G0 tn0 sm sn sb shadow_sa shadow_sb rb iop r
     base_gas mid1 pv t1 G1 tn1 index_gas mid2 v t2 G2 tn2.
    write_array_reached_mods
      ((DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func),
       (mods,exps,cenv,cx,env,bt,e,et,bd,vt),
       (st0,es,sa,s0,G0,tn0),
       (sm,sn,sb,shadow_sa,shadow_sb,rb,iop,r),
       (base_gas,mid1,pv,t1,G1,tn1),(index_gas,mid2,v,t2,G2,tn2)) ==>
    write_array_suffix_mods
      ((DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func),
       (mods,exps,cenv,cx,env,bt,e,et,bd,vt),
       (st0,es,sa,s0,G0,tn0),
       (sm,sn,sb,shadow_sa,shadow_sb,rb,iop,r),
       (base_gas,mid1,pv,t1,G1,tn1),(index_gas,mid2,v,t2,G2,tn2))) ==>
  write_base_sim_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx env (SubscriptTarget bt e) es
Proof
  strip_tac >> simp[write_base_sim_mods_def] >> rpt gen_tac >> strip_tac >>
  qpat_assum `write_target_entry_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [write_target_entry_mods_def]) >>
  qpat_x_assum `!sa sb shadow_sa shadow_sb r. _`
    (qspecl_then [`sa`,`sb`,`shadow_sa`,`shadow_sb`,`r`] mp_tac) >>
  simp[] >> strip_tac >>
  `eval_base_place cx (SubscriptTarget bt e) =
     bind (eval_base_place cx bt)
       (\pv. bind (bind (eval_expr cx e) (read_result cx))
                 (\v. extend_place cx pv (ValueSubscript v)))` by
    simp[FUN_EQ_THM,Once evaluate_def,bind_assoc] >>
  `gas_admissible (eval_base_place cx bt) target_res_ok es` by
    (irule target_subscript_base_admissible >> qexists_tac `e` >> simp[]) >>
  suspend "base"
QED

Resume write_array_index_bind_mods[base]:
  qpat_x_assum `eval_base_place cx (SubscriptTarget bt e) = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> REWRITE_TAC [th]) >>
  qpat_x_assum `write_base_sim_mods _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [write_base_sim_mods_def]) >>
  disch_then (qspecl_then [`st0`,`Type (ArrayT et bd)`,`sa`,`sm`,`shadow_sa`,
                           `shadow_sm`,`rb`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[write_target_entry_mods_def] >>
               rpt strip_tac >> first_x_assum drule >> simp[])) >> strip_tac >>
  qmatch_asmsub_abbrev_tac
    `gas_outcome_full_mods _ _ _ _ (eval_base_place cx bt) _ baseQ baseR` >>
  `gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cenv.ce_modules cx st0 (eval_base_place cx bt) (es,s0,G0,tn0)
     (\H res ee G tn t. baseQ H res ee G tn t /\
       ?cm. gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
                (s0,G0,tn0) cm (OK t,G,tn)) baseR` by
    (irule array_base_path >>
     qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ baseQ baseR` (irule_at Any) >>
     rpt strip_tac >> simp[] >> goal_assum (drule_at Any)) >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ pathQ baseR` >>
  irule gas_outcome_full_mods_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> RULE_ASSUM_TAC BETA_RULE >>
      irule gas_exempt_cert_mods_bind_result >>
      goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_result >> simp[])
  >~ [`storage_trace_frame (eval_base_place _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_extend_place] >>
      irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  qexists_tac `\H res ee G tn t. pathQ H res ee G tn t /\ ee.gas_obs = []` >>
  conj_tac >- suspend "index" >>
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ (eval_base_place _ _) _ pathQ baseR`
    (irule_at Any) >>
  conj_tac >- simp[] >>
  simp[Abbr `baseR`] >> rpt strip_tac >> Cases_on `res` >> fs[expr_exit_def]
QED

Resume write_array_index_bind_mods[index]:
  qx_genl_tac [`marks`,`res`,`mid1`,`G1`,`tn1`,`t1`] >> BETA_TAC >> strip_tac >>
  qunabbrev_tac `pathQ` >> qunabbrev_tac `baseQ` >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon mid1.storage_trace)
     mid1.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid1.storage_trace ==> _`
    (drule_then strip_assume_tac) >> gvs[] >>
  qabbrev_tac `base_gas = gas_explicit marks s0.vs_gas_readings` >>
  `mid1 with gas_obs := [] = mid1` by simp[evaluation_state_component_equality] >>
  `eval_base_place cx bt (es with gas_obs := base_gas) = (INL pv,mid1)` by
    (qpat_assum `!tail. eval_base_place _ _ _ = _` (qspec_then `[]` mp_tac) >>
     rewrite_tac[APPEND_NIL] >>
     qpat_assum `mid1 with gas_obs := [] = mid1` (fn th => rewrite_tac[th])) >>
  `expr_sim_inv_mods mods cenv cx env mid1 /\
   body_const_cells_agree_mods mods cx env mid1` by
    (qpat_assum `!st pv mid. expr_sim_inv_mods _ _ _ _ st /\ _ ==> _`
       (qspecl_then [`es with gas_obs := base_gas`,`pv`,`mid1`] mp_tac) >>
     simp[] >> (impl_tac >- (rpt strip_tac >>
       qpat_assum `!i s. MEM i (target_indices (SubscriptTarget _ _)) /\ _ ==> _` irule >>
       simp[target_indices_def])) >> simp[]) >>
  `expr_body_pre_mods mods cenv cx env e mid1` by
    (qpat_assum `!i s. MEM i (target_indices (SubscriptTarget _ _)) /\ _ ==> _` irule >>
     simp[target_indices_def]) >>
  `body_expr_full_ok_mods mods exps cx e` by
    (qpat_x_assum `body_base_target_full_ok_mods _ _ _ (SubscriptTarget _ _)` mp_tac >>
     simp[body_base_target_full_ok_mods_def] >> strip_tac >> first_x_assum irule >>
     qexistsl_tac [`es with gas_obs := base_gas`,`pv`,`mid1`] >> simp[]) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e mid1` by
    (qpat_x_assum `body_expr_full_ok_mods _ _ _ e` mp_tac >>
     simp[Once body_expr_full_ok_mods_def] >>
     disch_then (mp_tac o CONJUNCT1) >>
     disch_then (qspecl_then [`DF`,`lo`,`d`,`PG`,`src`,`tops`,`ctx`,`shadow_ctx`,
                              `func`,`shadow_func`,`cenv`,`env`,`expr_type e`,`mid1`] mp_tac) >>
     simp[]) >>
  `gas_admissible (bind (bind (eval_expr cx e) (read_result cx))
       (\v. extend_place cx pv (ValueSubscript v))) target_res_ok mid1` by
    (qpat_assum `gas_admissible (bind (eval_base_place _ _) _) _ _`
       (mp_then (Pat `gas_admissible _ _ _`) mp_tac gas_admissible_bind_tail) >>
     BETA_TAC >> disch_then (drule_then mp_tac) >>
     qpat_assum `mid1 with gas_obs := [] = mid1` (fn th => rewrite_tac[th])) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok mid1` by
    (irule array_index_admissible >> qexists_tac `\v. extend_place cx pv (ValueSubscript v)` >> simp[]) >>
  suspend "index_entry"
QED

Resume write_array_index_bind_mods[index_entry]:
  qpat_assum `!H. valid_horizon _ _ H mid1.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  drule_then strip_assume_tac write_target_post_view_mods >>
  `sa.cs_next_var <= sm.cs_next_var` by fs[ci_mono_def] >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> drule_all body_inv_no_phi_mods >> simp[]) >>
  `!fn inst s. frag_reachable ctx func t1 fn inst s ==>
    dalloca_fmp_headroom inst s` by
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
  qpat_x_assum `expr_sim_full_mods _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`sm`,`sn`,`shadow_sm`,`shadow_sn`,
                           `iop`,`t1`,`G1`,`tn1`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid1.storage_trace ==> _`
       (drule_then strip_assume_tac) >>
     drule_then strip_assume_tac write_target_post_view_mods >> simp[])) >> strip_tac >>
  suspend "index_bind"
QED

Resume write_array_index_bind_mods[index_bind]:
  qmatch_asmsub_abbrev_tac
    `gas_outcome_full_mods _ _ _ _ (bind (eval_expr cx e) _) _ idxQ idxR` >>
  irule gas_outcome_full_mods_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> RULE_ASSUM_TAC BETA_RULE >>
      irule gas_exempt_cert_mods_bind_value >> goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame (bind _ _)`]
  >- simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,
          storage_trace_frame_read_result]
  >~ [`storage_trace_frame _`]
  >- simp[storage_trace_frame_extend_place] >>
  qexists_tac `\H res ee G tn t. idxQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac >- suspend "suffix" >>
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ (bind (eval_expr _ _) _) _ idxQ idxR`
    (irule_at Any) >>
  conj_tac >- simp[] >>
  simp[Abbr `idxR`,Abbr `baseR`] >> rpt strip_tac >>
  Cases_on `res` >> fs[expr_exit_def] >>
  metis_tac[expr_exit_INR_retype,halt_exit_INR_type]
QED

Resume write_array_index_bind_mods[suffix]:
  qx_genl_tac [`marks2`,`res`,`mid2`,`G2`,`tn2`,`t2`] >> BETA_TAC >> strip_tac >>
  qunabbrev_tac `idxQ` >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon mid2.storage_trace)
     mid2.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> _`
    (drule_then strip_assume_tac) >> gvs[] >>
  qabbrev_tac `index_gas = gas_explicit marks2 t1.vs_gas_readings` >>
  `mid2 with gas_obs := [] = mid2` by simp[evaluation_state_component_equality] >>
  `bind (eval_expr cx e) (read_result cx) (mid1 with gas_obs := index_gas) =
     (INL v,mid2)` by
    (qpat_assum `!tail. bind (eval_expr _ _) _ _ = _` (qspec_then `[]` mp_tac) >>
     rewrite_tac[APPEND_NIL] >>
     qpat_assum `mid2 with gas_obs := [] = mid2` (fn th => rewrite_tac[th])) >>
  `expr_body_pre_mods mods cenv cx env e (mid1 with gas_obs := index_gas)` by simp[] >>
  `expr_sim_inv_mods mods cenv cx env mid2 /\ value_runtime_typed env (expr_type e) v` by
    (qpat_assum `!st v mid. expr_body_pre_mods _ _ _ _ _ st /\ _ ==> _`
       (qspecl_then [`mid1 with gas_obs := index_gas`,`v`,`mid2`] mp_tac) >> simp[]) >>
  `gas_admissible (extend_place cx pv (ValueSubscript v)) target_res_ok mid2` by
    (qpat_assum `gas_admissible (bind (bind (eval_expr _ _) _) _) _ _`
       (mp_then (Pat `gas_admissible _ _ _`) mp_tac gas_admissible_bind_tail) >>
     BETA_TAC >> disch_then (drule_then mp_tac) >>
     qpat_assum `mid2 with gas_obs := [] = mid2` (fn th => rewrite_tac[th])) >>
  `!H. valid_horizon cx st0 H mid2.storage_trace ==>
       valid_horizon cx st0 H mid1.storage_trace` by
    (rpt strip_tac >> drule_all array_index_horizon >> simp[]) >>
  `write_array_reached_mods
     ((DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func),
      (mods,exps,cenv,cx,env,bt,e,et,bd,vt),
      (st0,es,sa,s0,G0,tn0),(sm,sn,sb,shadow_sa,shadow_sb,rb,iop,r),
      (base_gas,mid1,pv,t1,G1,tn1),(index_gas,mid2,v,t2,G2,tn2))` by
    (rewrite_tac[write_array_reached_mods_def] >> asm_rewrite_tac[] >>
     rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid1.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> _`
       (qspec_then `H` mp_tac) >> simp[]) >>
  qunabbrev_tac `baseR` >>
  qpat_x_assum `!st0 vt sa s0 G0 tn0 sm sn sb shadow_sa shadow_sb rb iop r
                 base_gas mid1 pv t1 G1 tn1 index_gas mid2 v t2 G2 tn2.
                 write_array_reached_mods _ ==> _`
    (drule_then (ACCEPT_TAC o REWRITE_RULE [write_array_suffix_mods_def]))
QED

Finalise write_array_index_bind_mods

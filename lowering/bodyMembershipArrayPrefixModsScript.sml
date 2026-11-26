(* Count the forced needle and raw array operand at their actual landings.
   Reading the array result is the continuation, not part of its evaluation. *)
Theory bodyMembershipArrayPrefixMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyForcedStorageFrameMods
  exprBodyPreProps exprBodyPreTypingProps exprSimFullBundleProps exprBopSimProps exprBopSimDefs
  exprBodyPreCallSafetyProps vyperTypeExprSoundness vyperTypeEvalSoundness
  bodyFullIfExpReach bodyMemoryDefs haltExitProj stmtSimProps stmtSimForRounds
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasOutcomeFullPostPathMods
  gasExemptCertMods gasContext gasShadowState gasShadow
  vyperTypeCallStackSoundness vyperTypeInvariants
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState
  exprLoweringProps loweringPosts exprSimDefs fragExec contextRawReachable
  ptrDiscipline bodyPtrDefs compileEnv list bodyWriteSubscriptSourceMods
Libs monadsyntax

val suffix = ``bind (read_result cx tv)
  (\arr. \ee. (bop_result cx ann bop [expr_type e1; expr_type e2] needle arr ee,ee))``;

val needle_post = ``
  expr_post_mods (H : (bool # 256 word # type_value) list # num list)
    ctx func cenv cx e1 es sa s1 s0 mid needle op t /\
  expr_store_bound cx (post_value_type cenv e1) needle op t /\
  t.vs_current_bb = s1.cs_current_bb /\ t.vs_inst_idx = LENGTH s1.cs_current_insts /\
  alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx mid G1 tn1 t /\
  ptr_val_ok cx (post_value_type cenv e1) needle op G1 tn1 t /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\ ~t.vs_halted /\ mid.gas_obs = [] /\
  (!fn inst z. frag_reachable ctx func t fn inst z ==> dalloca_fmp_headroom inst z)``;

val array_post = ``
  vv_post_mods (H : (bool # 256 word # type_value) list # num list)
    ctx func cenv cx e2 mid s1 sm t fin tv vv u /\
  vv_store_bound cx (post_value_type cenv e2) (lowered_value_type cenv e2) fin tv vv u /\
  u.vs_current_bb = sm.cs_current_bb /\ u.vs_inst_idx = LENGTH sm.cs_current_insts /\
  alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  t.vs_alloca_next <= u.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx fin G2 tn2 u /\
  ptr_vv_ok cx (post_value_type cenv e2) tv vv fin G2 tn2 u /\
  (!v. tv = Value v /\ ~is_word_type (post_value_type cenv e2) /\
       ~is_bytestring_type (post_value_type cenv e2) ==>
       vv_own cenv cx (post_value_type cenv e2) s1 sm fin tv vv u /\
       (!ty p. vv = LocatedValue ty p ==> p.ptr_location = LocMemory)) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
   ?v. read_result cx tv fin = (INL v,fin) /\
       !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e2) = SOME rt /\
              eval_operand (vv_operand vv) u = SOME w ==>
              w2n w + type_memory_size rt <= lo /\
              (!mem. mem_agree_outside tn2.t_mem u.vs_memory mem ==>
                     val_in_memory rt v (w2n w) mem)) /\
  (!ty x. vv = StackValue ty x /\ ~is_word_type (post_value_type cenv e2) ==>
           ptr_buf_ok cenv e2 x G2 u) /\
  (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
           ptr_buf_ok cenv e2 p.ptr_operand G2 u) /\
  ghost_kept_at lo cenv mid s1 G1 tn1 t G2 tn2 /\ ~u.vs_halted /\ fin.gas_obs = []``;

val exit_post = ``\(H : (bool # 256 word # type_value) list # num list)
  (res : value + vyperState$exception) ee (gt : (string |-> num # num) # taint) r.
  expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)``;

Theorem membership_array_prefix_mods:
  is_word_type (expr_type e1) /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\
  body_expr_full_ok_mods mods exps cx e1 /\ expr_body_pre_mods mods cenv cx env e1 es /\
  (!obs needle mid.
     mid.gas_obs = [] /\
     (!tail. bind (eval_expr cx e1) (read_result cx)
        (es with gas_obs := obs ++ tail) = (INL needle,mid with gas_obs := tail)) ==>
     body_expr_full_ok_mods mods exps cx e2 /\
     expr_body_pre_mods mods cenv cx env e2 mid /\
     body_const_cells_agree_mods mods cx env mid /\
     value_runtime_typed env (expr_type e1) needle /\
     MAP FDOM es.scopes = MAP FDOM mid.scopes /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
          valid_horizon cx st0 H es.storage_trace)) /\
  lower_value compile_expr cenv (expr_type e1) e1 sa = (op,s1) /\
  compile_expr cenv (expr_type e2) e2 s1 = (vv,sm) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type e1)
    (gas_shadow_expr e1) sha = (op,sh1) /\
  compile_expr (gas_shadow_env T cenv) (expr_type e2) (gas_shadow_expr e2) sh1 = (vv,shm) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,s1,sha,sh1) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (s1,sm,sh1,shm) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv s1 /\
  sa.cs_next_var <= s1.cs_next_var /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s1 x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s1 x) /\
  gas_admissible (bind (eval_expr cx (Builtin ann (Bop bop) [e1;e2])) (read_result cx)) expr_res_ok es /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst z. frag_reachable ctx func s0 fn inst z ==> dalloca_fmp_headroom inst z) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!left needle mid G1 tn1 t right tv fin G2 tn2 u.
    (!tail. bind (eval_expr cx e1) (read_result cx)
      (es with gas_obs := gas_explicit left s0.vs_gas_readings ++ tail) =
      (INL needle,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==> ^needle_post) /\
    (!tail. eval_expr cx e2 (mid with gas_obs := gas_explicit right t.vs_gas_readings ++ tail) =
      (INL tv,fin with gas_obs := tail)) /\
    storage_trace_domain cx st0 fin.storage_trace /\
    (!H. valid_horizon cx st0 H fin.storage_trace ==> ^array_post) ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0 (^suffix) (fin,u,G2,tn2) Q (^exit_post)) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0
    (bind (eval_expr cx (Builtin ann (Bop bop) [e1;e2])) (read_result cx))
    (es,s0,G0,tn0) Q (^exit_post)
Proof
  strip_tac >> fs[expr_sim_full_code_def] >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e1) e1 es` by
    (qpat_assum `body_expr_full_ok_mods _ _ _ e1`
       (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
     `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
        cenv cx (expr_type e1) e1 es /\
      expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
        cenv cx (expr_type e1) e1 es` by
       (qpat_assum `!DF lo d PG src tops ctx shctx func shfunc cenv env ty es.
                     _ ==> expr_sim_full_mods _ _ _ _ _ _ /\ expr_vv_sim_full_mods _ _ _ _ _ _`
          irule >> simp[] >> conj_tac
        >- (qexistsl_tac [`src`,`tops`] >> simp[]) >> qexists_tac `env` >> simp[]) >>
     first_assum ACCEPT_TAC) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> irule body_inv_no_phi_mods >>
     qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
     qexists_tac `func` >> simp[]) >>
  qpat_x_assum `gas_admissible _ _ _`
    (assume_tac o PURE_REWRITE_RULE [REWRITE_RULE [ETA_AX] eval_expr_bop_bind]) >>
  pure_rewrite_tac[REWRITE_RULE [ETA_AX] eval_expr_bop_bind] >>
  `gas_admissible (bind (eval_expr cx e1) (read_result cx)) expr_res_ok es` by
    (qpat_assum `gas_admissible _ _ _` mp_tac >>
     rewrite_tac[gas_admissible_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
     Cases_on `res` >- simp[expr_res_ok_def] >>
     first_x_assum (qspec_then `gs` mp_tac) >> simp[bind_def]) >>
  qhdtm_x_assum `expr_sim_full_mods` (mp_tac o REWRITE_RULE [expr_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`s1`,`sha`,`sh1`,`op`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ leftQ leftR` >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      goal_assum (drule_at Any) >> BETA_TAC >> first_assum ACCEPT_TAC)
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> BETA_TAC >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ e1) _)`]
  >- simp[bodyForcedStorageFrameModsTheory.bop_forced_storage_frame]
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> irule storage_trace_frame_bind_all >>
      conj_tac >- simp[storage_trace_frame_def,bop_result_def] >>
      simp[bodyForcedStorageFrameModsTheory.bop_forced_storage_frame]) >>
  qexists_tac `\H res mid G1 tn1 t. ?needle. res = INL needle /\ ^needle_post` >>
  conj_tac >- suspend "array_entry" >>
  suspend "needle_post"
QED

Resume membership_array_prefix_mods[needle_post]:
  irule gas_outcome_full_mods_post_source >>
  qexistsl_tac [`\H res ee G tn t. leftQ H res ee G tn t /\
      (!fn inst z. frag_reachable ctx func t fn inst z ==> dalloca_fmp_headroom inst z)`, `leftR`] >>
  reverse (rpt conj_tac)
  >- (irule gas_outcome_full_mods_post_path >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ leftQ leftR` (irule_at Any) >>
      BETA_TAC >> rpt gen_tac >> strip_tac >> asm_rewrite_tac[] >>
      match_mp_tac (GEN_ALL gas_origin_ptr_path_dalloca_fmp_headroom) >>
      qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) _ (OK t,_,_)` (irule_at Any) >>
      conj_tac >> first_assum ACCEPT_TAC)
  >- (simp[Abbr `leftR`] >> gen_tac >> Cases >> simp[expr_exit_def]) >>
  simp[Abbr `leftQ`] >> rpt strip_tac >> qexists_tac `v` >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> goal_assum (drule_at Any)
QED

Resume membership_array_prefix_mods[array_entry]:
  qx_genl_tac [`left`,`res`,`mid`,`G1`,`tn1`,`t`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then strip_assume_tac)) >>
  qpat_x_assum `res = INL needle` SUBST_ALL_TAC >>
  disj1_tac >> qexists_tac `needle` >> conj_tac >- REFL_TAC >>
  qpat_assum `!obs needle mid. _ ==> body_expr_full_ok_mods _ _ _ _ /\ _`
    (qspecl_then [`gas_explicit left s0.vs_gas_readings`,`needle`,`mid`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  `expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e2) e2 mid` by
    (qpat_assum `body_expr_full_ok_mods _ _ _ e2`
       (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
     `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
        cenv cx (expr_type e2) e2 mid /\
      expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
        cenv cx (expr_type e2) e2 mid` by
       (qpat_assum `!DF lo d PG src tops ctx shctx func shfunc cenv env ty es.
                     _ ==> expr_sim_full_mods _ _ _ _ e2 _ /\ expr_vv_sim_full_mods _ _ _ _ e2 _`
          irule >> simp[] >> conj_tac
        >- (qexistsl_tac [`src`,`tops`] >> simp[]) >> qexists_tac `env` >> simp[]) >>
     first_assum ACCEPT_TAC) >>
  suspend "array_run"
QED

Resume membership_array_prefix_mods[array_run]:
  `gas_admissible (eval_expr cx e2) expr_vv_res_ok mid` by suspend "array_admissible" >>
  qpat_assum `expr_post_mods _ _ _ _ _ _ _ _ _ _ mid needle op t`
    (strip_assume_tac o REWRITE_RULE [expr_post_mods_def,expr_post_def]) >>
  `return_buf_frame d cenv s1 t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[]) >>
  qhdtm_x_assum `expr_vv_sim_full_mods` (mp_tac o REWRITE_RULE [expr_vv_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`s1`,`sm`,`sh1`,`shm`,`vv`,`t`,`G1`,`tn1`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> ?v. _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     fs[expr_post_mods_def,expr_post_def])) >> strip_tac >>
  suspend "array_bind"
QED

Resume membership_array_prefix_mods[array_admissible]:
  `gas_admissible
     (bind (bind (eval_expr cx e2) (read_result cx))
       (\v ee. (bop_result cx ann bop [expr_type e1;expr_type e2] needle v ee,ee)))
     expr_res_ok mid` by
    (qpat_assum `gas_admissible (bind (bind (eval_expr _ e1) _) _) _ _`
       (mp_then (Pat `gas_admissible _ _ _`) mp_tac gas_admissible_bind_tail) >>
     BETA_TAC >> disch_then (drule_then mp_tac) >>
     `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
     asm_rewrite_tac[]) >>
  qpat_x_assum `gas_admissible (bind (bind (eval_expr _ e2) _) _) _ _` mp_tac >>
  pure_rewrite_tac[bind_assoc,gas_admissible_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >> Cases_on `res`
  >- (rename1 `eval_expr cx e2 (mid with gas_obs := gs) = (INL raw,ee)` >>
      `expr_body_pre_mods mods cenv cx env e2 (mid with gas_obs := gs)` by
        simp[write_subscript_source_gas_obs_mods] >>
      drule_then strip_assume_tac expr_body_pre_mods_runtime_typing >>
      drule_then assume_tac expr_body_pre_mods_call_evaluation_safe >>
      qspecl_then [`cx`,`e2`] (mp_tac o cj 1) (cj 5 eval_scc_type_sound_mutual) >>
      disch_then (qspecl_then [`env`,`mid with gas_obs := gs`,`INL raw`,`ee`] mp_tac) >>
      Cases_on `raw` >> fs[runtime_consistent_def,expr_vv_res_ok_def,eval_result_typed_def]) >>
  qpat_assum `!gs res ee. _ ==> expr_res_ok res` (qspec_then `gs` mp_tac) >>
  simp[bind_def,expr_res_ok_def,expr_vv_res_ok_def]
QED

Resume membership_array_prefix_mods[array_bind]:
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ (eval_expr cx e2) _ rightQ rightR` >>
  once_rewrite_tac[bind_assoc] >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_result >>
      goal_assum (drule_at Any) >> BETA_TAC >> first_assum ACCEPT_TAC)
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_result >> BETA_TAC >> simp[])
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> irule storage_trace_frame_bind_all >>
      conj_tac >- simp[storage_trace_frame_def,bop_result_def] >>
      simp[storage_trace_frame_read_result]) >>
  qexists_tac `\H res fin G2 tn2 u. ?tv. res = INL tv /\ ^array_post` >>
  conj_tac >- suspend "array_continue" >>
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ (eval_expr cx e2) _ rightQ rightR` (irule_at Any) >>
  conj_tac
  >- (simp[Abbr `rightQ`] >> rpt strip_tac >> qexists_tac `tv` >> asm_rewrite_tac[]) >>
  simp[Abbr `rightR`,Abbr `leftR`] >> gen_tac >> Cases >> simp[expr_exit_def] >>
  metis_tac[expr_exit_INR_type,halt_exit_INR_type]
QED

Resume membership_array_prefix_mods[array_continue]:
  qx_genl_tac [`right`,`res`,`fin`,`G2`,`tn2`,`u`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> _`
    (qspec_then `storage_trace_horizon fin.storage_trace` (drule_then strip_assume_tac)) >>
  qpat_x_assum `res = INL tv` SUBST_ALL_TAC >>
  disj1_tac >> qexists_tac `tv` >> conj_tac >- REFL_TAC >>
  qpat_assum `!left needle mid G1 tn1 t right tv fin G2 tn2 u. _ ==> gas_outcome_full_mods _ _ _ _ _ _ _ _` irule >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`G1`,`left`,`mid`,`right`,`t`,`tn1`] >>
  fs[] >> gen_tac >> disch_tac >> first_assum ACCEPT_TAC
QED

Finalise membership_array_prefix_mods

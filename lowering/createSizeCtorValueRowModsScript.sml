Theory createSizeCtorValueRowMods
Ancestors
  createSizeCtorValueRow createExprSizeExitDefsMods
  gasShadowCompileBase
  abiEncoderProps e2eDefs exprSimFullBundleProps fragExec fragGasOrigin fragGasOriginPtr
  gasExplicitSites gasSummary s1PrefixDefs venomExecSemantics venomState vyperState relation
  list words createMarkedPath pair bodyFullIfExpReach arithmetic exprLowering
  stmtLoweringMono vfmConstants compileEnv exprLoweringProps exprSimSource vyperStorageTrace
  fragGasOriginPtrExec bodyMemoryDefs rich_list exprSimHypsDefs vyperTypeSystem exprSimHyps
  bodyPtrDefs loweringPosts context vyperAST vyperStorageFootprint vyperTyping vyperValue
  integer_word valueEncoding createCtorPrivateSnapshotMods createCtorSegmentArrival
  bodyFullExtCallPosList bodyFullExtCallPosAggregate abiEncodeArgsSim abiEncodeArgsCase
  exprSimMemorySource bodyFullHashKeccakFixed aggregateEvaluatedLayout
  exprSimIfExpWidenedPhysicalType exprSimSubscriptArrayCompose loweringStateRelDefs
  exprSimMemDefs ptrDiscipline bodySim createExprSizeExitDefs createSizePrefixReplayMods
  createSizeCopyReplayMods createSizeBlueprintKeywordReplayMods createSizeRawReplayMods
  createSizeRawGasAdmissibleMods createCtorSourceReadinessMods
  exprSimIfExpCompat vyperTypeEvalCaseProofs bodyFullPostsMods
  exprBodyPreProps vyperTypeExprSoundness createCtorSnapshotTypingMods
  createSizeCopyReplay bodyFullShadowBodyInv abiEncodeMaterialize valueCopyBytes
  exprReasonOperand bodyInvSplit createCtorPayloadGasObsMods vyperStorageBackend

(* Visit the calls in the original suffix, while carrying their reached
   source states. The continuation is kept under its actual bind. *)

Theorem blueprint_ctor_source_walk_mods:
  !mods n i p k.
    i + n = LENGTH es /\ P i p /\
    bind (eval_exprs cx (DROP i es)) k p = (res,out) /\
    (!vs. storage_trace_frame (k vs)) /\
    (!j q l. j < LENGTH es /\ P j q /\ (!v. storage_trace_frame (l v)) /\
       bind (bind (eval_expr cx (EL j es)) (read_result cx)) l q = (res,out) ==>
       (?err. res = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err) \/
       ?v q'. bind (eval_expr cx (EL j es)) (read_result cx) q = (INL v,q') /\
              l v q' = (res,out) /\ P (SUC j) q') ==>
    (?err. res = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err) \/
    ?vs E. E i = p /\ LENGTH vs = n /\
       eval_exprs cx (DROP i es) p = (INL vs,E (LENGTH es)) /\
       k vs (E (LENGTH es)) = (res,out) /\
       (!j. i <= j /\ j <= LENGTH es ==> P j (E j)) /\
       (!j. i <= j /\ j < LENGTH es ==>
         bind (eval_expr cx (EL j es)) (read_result cx) (E j) =
           (INL (EL (j-i) vs),E (SUC j)))
Proof
  Induct_on `n`
  >- (rpt gen_tac >> strip_tac >> gvs[cj 49 vyperInterpreterTheory.evaluate_def, bind_return] >>
      disj2_tac >> qexists_tac `\j. p` >> simp[return_def] >>
      metis_tac[LESS_EQUAL_ANTISYM]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `i < LENGTH es /\ SUC i + n = LENGTH es` by decide_tac >>
  `DROP i es = EL i es :: DROP (SUC i) es` by metis_tac[DROP_CONS_EL] >>
  qabbrev_tac `l = \v. bind (eval_exprs cx (DROP (SUC i) es)) (\vs. k (v::vs))` >>
  `!v. storage_trace_frame (l v)` by simp[Abbr `l`, createSizeBlueprintKeywordReplayTheory.blueprint_read_list_frame] >>
  `bind (bind (eval_expr cx (EL i es)) (read_result cx)) l p = (res,out)` by
    (qpat_x_assum `bind (eval_exprs cx (DROP i es)) k p = _` mp_tac >>
     simp[createSizeCopyReplayTheory.create_copy_source_cons, Abbr `l`]) >>
  first_assum (qspecl_then [`i`,`p`,`l`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >- metis_tac[] >>
  rename1 `l v q = (res,out)` >>
  first_x_assum (qspecl_then [`mods`,`SUC i`,`q`,`\vs. k (v::vs)`] mp_tac) >>
  (impl_tac >- fs[Abbr `l`]) >> strip_tac >- metis_tac[] >>
  rename1 `E (SUC i) = q` >>
  disj2_tac >> qexistsl [`v::vs`,`\j. if j = i then p else E j`] >>
  simp[] >> rpt conj_tac
  >- (irule createSizeBlueprintKeywordReplayTheory.blueprint_eval_join_cons >> metis_tac[])
  >- gvs[]
  >- (rpt strip_tac >> Cases_on `j = i` >> simp[] >> first_assum irule >> decide_tac) >>
  rpt strip_tac >> Cases_on `j = i` >> gvs[] >>
  `?z. j-i = SUC z /\ j-SUC i = z` by (qexists_tac `j - SUC i` >> decide_tac) >>
  `SUC j <> i /\ SUC i <= j` by decide_tac >>
  qpat_assum `!j. SUC i <= j /\ j < LENGTH es ==> _` (qspec_then `j` mp_tac) >> simp[]
QED

Theorem blueprint_ctor_complete_mods:
  gas_completed_operand_mods (DF,lo,explicit,ctx,func,PG)
    mods cx st0 a b source (p,s,G,tn) Q /\
  create_expr_prefix a b explicit ctx func s marks t /\
  t.vs_current_bb = b.cs_current_bb /\ t.vs_inst_idx = LENGTH b.cs_current_insts /\
  source p = (rr,q) /\ valid_horizon cx st0 H q.storage_trace /\
  p.gas_obs = gas_explicit marks s.vs_gas_readings ++ suffix ==>
  (?err. rr = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err) \/
  ?G' tn'. q.gas_obs = suffix /\
    !h. valid_horizon cx st0 h q.storage_trace ==>
      gas_origin_ptr_path (DF h,lo,explicit,ctx,func,PG) (s,G,tn) marks (OK t,G',tn') /\
      Q h rr (q with gas_obs := []) G' tn' t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `p with gas_obs := gas_explicit marks s.vs_gas_readings ++ suffix = p` by
    (qpat_assum `p.gas_obs = _` (once_rewrite_tac o single o SYM) >> simp[]) >>
  qhdtm_x_assum `gas_completed_operand_mods`
    (qspecl_then [`H`,`marks`,`t`,`suffix`,`rr`,`q`] mp_tac o
     REWRITE_RULE [gas_completed_operand_mods_def]) >>
  asm_rewrite_tac[] >> metis_tac[]
QED

Theorem blueprint_ctor_vv_row_mods:
  contract_inv mods exps ctx ce cx /\
  module_body_inv mods src tops ce cx /\ shadow_body_inv_mods mods exps ctx shctx /\
  expr_body_pre_mods mods ce cx env e p /\ create_operand_completed_ok_mods mods exps cx e /\
  ~is_word_type (lowered_value_type ce e) /\
  compile_expr ce (expr_type e) e a = (vv,m) /\
  compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) sha = (vv,shm) /\
  expr_sim_full_code (ctx,shctx,func,shfunc) (a,m,sha,shm) /\
  compile_snapshot_vv ce (exprs_can_mutate ce xs)
    (ext_call_arg_value (lowered_value_type ce e) vv) m = (saved,b) /\
  local_ptrs_reserved ce a /\ (!h. dead_lo_ok_mods h (DF h) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  return_buf_frame d ce a s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!f i z. frag_reachable ctx func s f i z ==> dalloca_fmp_headroom i z) /\
  (!h. valid_horizon cx st0 h p.storage_trace ==>
     stmt_state_rel h ctx func ce cx p s /\
     immutable_frame_mods func ce cx p s /\ storage_well_formed_on cx p (FST h) /\
     ghost_inv_at_mods (DF h) lo d ce cx p G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  create_expr_prefix a m (gas_explicit_sites ctx shctx) ctx func s chunk mid /\
  mid.vs_current_bb = m.cs_current_bb /\ mid.vs_inst_idx = LENGTH m.cs_current_insts /\
  create_expr_prefix m b (gas_explicit_sites ctx shctx) ctx func mid snap t /\
  t.vs_current_bb = b.cs_current_bb /\ t.vs_inst_idx = LENGTH b.cs_current_insts /\
  (exprs_can_mutate ce xs ==>
    fn_has_code m b func /\
    (?j. ctor_segment_fetch func t = SOME j /\ j.inst_opcode <> PHI /\
         b.cs_next_id <= j.inst_id) /\
    (gas_origin_path T (gas_explicit_sites ctx shctx) ctx func mid [] (OK t) ==> snap = [])) /\
  bind (eval_expr cx e) (read_result cx) p = (rr,q) /\
  valid_horizon cx st0 H q.storage_trace /\
  p.gas_obs = gas_explicit (chunk ++ (snap ++ rest)) s.vs_gas_readings ++ tail ==>
  (?err. rr = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err) \/
  ?v raw Gm tm tv ann Gt tt.
    rr = INL v /\ eval_expr cx e p = (INL raw,q) /\ read_result cx raw q = (INL v,q) /\
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME ann /\
    arg_type_fits (lowered_value_type ce e) (expr_type e) /\
    value_has_type tv v /\ value_has_type ann v /\
    (!h. valid_horizon cx st0 h q.storage_trace ==>
       vv_post_mods h ctx func ce cx e p a m s (q with gas_obs := []) raw vv mid /\
       vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e)
         (q with gas_obs := []) raw vv mid /\
       ptr_vv_ok cx (post_value_type ce e) raw vv (q with gas_obs := []) Gm tm mid /\
       alloca_history func mid /\ s.vs_alloca_next <= mid.vs_alloca_next /\
       ghost_inv_at_mods (DF h) lo d ce cx (q with gas_obs := []) Gm tm mid /\
       ghost_kept_at lo ce p a G tn s Gm tm /\
       (!tag op. vv = StackValue tag op /\ ~is_word_type (post_value_type ce e) ==>
         ptr_buf_ok ce e op Gm mid) /\
       (!tag p0. vv = LocatedValue tag p0 /\ p0.ptr_location = LocMemory ==>
         ptr_buf_ok ce e p0.ptr_operand Gm mid) /\
       (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
         ?val. read_result cx raw (q with gas_obs := []) = (INL val,q with gas_obs := []) /\
           !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
             eval_operand (vv_operand vv) mid = SOME w ==>
             w2n w + type_memory_size rt <= lo /\
             (!mem. mem_agree_outside tm.t_mem mid.vs_memory mem ==>
                val_in_memory rt val (w2n w) mem))) /\
    q.gas_obs = gas_explicit rest t.vs_gas_readings ++ tail /\
    expr_sim_inv_mods mods ce cx env q /\ return_buf_frame d ce b t /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!f i z. frag_reachable ctx func t f i z ==> dalloca_fmp_headroom i z) /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts /\
    (!h. valid_horizon cx st0 h q.storage_trace ==>
      stmt_state_rel h ctx func ce cx q t /\
      immutable_frame_mods func ce cx q t /\ storage_well_formed_on cx q (FST h) /\
      ghost_inv_at_mods (DF h) lo d ce cx q Gt tt t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_vv_sim_full_pre_mods (DF,lo,d,ctx,shctx,PG:(num # num) option list,func,shfunc)
     ce cx (expr_type e) e p (st0,a,m,sha,shm,vv,s,G,tn)` by
    (fs[expr_vv_sim_full_pre_mods_def, expr_sim_full_code_def] >>
     conj_tac
     >- (irule create_raw_gas_admissible_mods >> goal_assum drule) >>
     conj_tac >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
     gen_tac >> disch_tac >> first_x_assum drule >> simp[]) >>
  drule_all create_size_replay_vv_cut_mods >> strip_tac >>
  Cases_on `eval_expr cx e p` >>
  qmatch_asmsub_rename_tac `eval_expr cx e p = (rv,rq)` >>
  `rq = q` by (Cases_on `rv` >> fs[bind_def] >> metis_tac[read_result_state]) >>
  qpat_x_assum `rq = q` SUBST_ALL_TAC >>
  `p.gas_obs = gas_explicit chunk s.vs_gas_readings ++
     (gas_explicit (snap ++ rest) mid.vs_gas_readings ++ tail)` by
    (qpat_assum `create_expr_prefix a m _ _ _ s chunk mid`
       (assume_tac o MATCH_MP createSizeRawReplayTheory.create_prefix_readings) >>
     qpat_assum `p.gas_obs = gas_explicit (chunk ++ (snap ++ rest)) _ ++ _`
       (pure_once_rewrite_tac o single) >>
     CONV_TAC (LAND_CONV (LAND_CONV (REWR_CONV gas_explicit_append))) >>
     simp[APPEND_ASSOC]) >>
  drule_all blueprint_ctor_complete_mods >> strip_tac
  >- (disj1_tac >> qexists_tac `err` >> fs[bind_def]) >>
  suspend "read"
QED

Resume blueprint_ctor_vv_row_mods[read]:
  qpat_x_assum `!h. _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (assume_tac o BETA_RULE) >>
  qpat_assum `!h. _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_x_assum `rv = INL _` SUBST_ALL_TAC >>
  rename1 `eval_expr cx e p = (INL raw,q)` >>
  `?v. read_result cx raw (q with gas_obs := []) = (INL v,q with gas_obs := [])` by
    (qpat_x_assum `vv_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     Cases_on `vv` >> simp[vv_post_mods_def, vv_holds_mods_def, vv_holds_def]
     >- metis_tac[] >>
     rename1 `compile_expr ce _ e a = (LocatedValue _ pp,m)` >>
     Cases_on `pp.ptr_location` >>
     simp[storage_holds_def, immutable_holds_mods_def, immutable_holds_def] >>
     metis_tac[]) >>
  `read_result cx raw q = (INL v,q)` by
    (drule read_result_gas_obs >> disch_then (qspec_then `q.gas_obs` mp_tac) >>
     simp[IgnAsm `q.gas_obs = _`]) >>
  `rr = INL v` by fs[bind_def] >>
  qpat_x_assum `rr = INL v` SUBST_ALL_TAC >>
  disj2_tac >> qexistsl [`v`,`raw`,`G'`,`tn'`] >> simp[] >>
  `expr_sim_inv_mods mods ce cx env q /\ value_runtime_typed env (expr_type e) v` by
    (drule_all (REWRITE_RULE [ETA_AX] bodySimStmtFactsTheory.expr_body_pre_eval_mods) >> simp[]) >>
  `env_consistent env cx q` by drule_then ACCEPT_TAC expr_sim_inv_mods_env >>
  `env.type_defs = get_tenv cx` by drule_then ACCEPT_TAC env_consistent_type_defs_get_tenv >>
  `?ann. evaluate_type (get_tenv cx) (expr_type e) = SOME ann /\ value_has_type ann v` by
    fs[value_runtime_typed_def] >>
  `~is_word_type (expr_type e)` by (drule ctor_snapshot_word_types_mods >> simp[]) >>
  drule_all (REWRITE_RULE [ETA_AX] ctor_source_readiness_mods) >> simp[] >> strip_tac >>
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    (drule expr_body_pre_mods_well_typed >> strip_tac >>
     `!id ty. FLOOKUP env.var_types id = SOME ty ==> well_formed_type env.type_defs ty` by
       metis_tac[env_consistent_var_type_evaluates, well_formed_type_def] >>
     `sfields_tenv_consistent ce.ce_struct_fields env.type_defs` by fs[expr_sim_inv_mods_def] >>
     `!fid sg. FLOOKUP env.fn_sigs fid = SOME sg ==>
                   ce.ce_func_return_type (nsid_to_string fid) = sg.ret_ty` by
       metis_tac[expr_sim_inv_mods_return_type] >>
     drule_all ifexp_lowered_type_classify >> strip_tac >> simp[ifexp_arg_type_fits_refl] >>
     PairCases_on `fid` >>
     gvs[well_typed_expr_def, lowered_value_type_def, vyperASTTheory.expr_type_def] >>
     qpat_x_assum `!fid sg. _` (drule_then SUBST1_TAC) >> fs[type_widens_to_def]) >>
  rename1 `evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv` >>
  qexists_tac `tv` >> simp[] >>
  suspend "advance"
QED

Resume blueprint_ctor_vv_row_mods[advance]:
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (fs[expr_sim_full_code_def] >> metis_tac[body_inv_no_phi_mods]) >>
  `!f i z. frag_reachable ctx func mid f i z ==> dalloca_fmp_headroom i z` by
    (drule gas_origin_ptr_path_dalloca_fmp_headroom >> simp[] >> metis_tac[]) >>
  `~mid.vs_halted` by (drule gas_origin_ptr_path_exec >> simp[exit_result_def]) >>
  `~is_word_type (post_value_type ce e)` by
    (drule_all materialize_post_lowered_classify >> metis_tac[is_bytestring_word_type]) >>
  Cases_on `exprs_can_mutate ce xs`
  >- suspend "copy" >>
  suspend "retain"
QED

Resume blueprint_ctor_vv_row_mods[retain]:
  `~is_word_type (vv_type (ext_call_arg_value (lowered_value_type ce e) vv))` by
    (Cases_on `vv` >> simp[ext_call_arg_value_def, vv_type_def] >>
     `well_typed_expr env e /\
      (!id ty. FLOOKUP env.var_types id = SOME ty ==>
                ?x sz. FLOOKUP ce.ce_vars id = SOME (PtrVar (Var x) sz))` by
       (drule_then assume_tac expr_body_pre_mods_well_typed >>
        fs[expr_sim_inv_mods_def]) >>
     drule_all compile_expr_reason_uniform >>
     disch_then (qspec_then `expr_type e` mp_tac) >>
     simp[reason_uniform_shape_def] >> strip_tac >>
     first_x_assum drule >> gvs[reason_result_shape_def]) >>
  `b = m` by
    (qpat_x_assum `compile_snapshot_vv _ _ _ _ = _` mp_tac >>
     simp[compile_snapshot_vv_def,comp_return_def]) >>
  qpat_x_assum `b = m` SUBST_ALL_TAC >>
  drule_all create_copy_empty_cut >> strip_tac >>
  `a.cs_next_var <= m.cs_next_var` by
    metis_tac[ci_mono_compile_expr_sa,SND,ci_mono_def] >>
  `return_buf_frame d ce m mid` by
    (irule return_buf_frame_frame >>
     qexistsl [`ce`,`s`,`a`] >> fs[vv_post_mods_def]) >>
  qexistsl [`G'`,`tn'`] >> gvs[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qx_gen_tac `h` >> disch_tac >>
  qpat_assum `!h. _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `h` (drule_then strip_assume_tac)) >>
  fs[vv_post_mods_def] >> conj_tac
  >- (qpat_assum `immutable_frame_mods _ _ _ (q with gas_obs := []) _` mp_tac >>
      pure_rewrite_tac[immutable_frame_mods_def, bodyInvSplitTheory.immutables_rel_mods_def,
                       bodyInvSplitTheory.immutable_alloca_sep_mods_def,
                       immutables_rel_def, immutable_alloca_sep_def,
                       evaluation_state_accfupds] >> disch_then ACCEPT_TAC) >>
  conj_tac
  >- (irule (iffLR storage_well_formed_on_backends) >>
      qexists_tac `q with gas_obs := []` >> simp[]) >>
  qpat_x_assum `ghost_inv_at_mods (DF h) _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac (srw_ss()) [ghost_inv_at_mods_def,ghost_inv_def,local_region_def] >>
  strip_tac >> first_assum ACCEPT_TAC
QED

Resume blueprint_ctor_vv_row_mods[copy]:
  qpat_x_assum `exprs_can_mutate ce xs ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `create_expr_prefix m b _ _ _ mid snap t`
    (assume_tac o MATCH_MP blueprint_ctor_segment_rtc) >>
  `storage_trace_domain cx st0 q.storage_trace` by
    (qpat_assum `valid_horizon cx st0 h q.storage_trace`
       (ACCEPT_TAC o MATCH_MP bodyFullExtCallPackingReadyTheory.extcall_packing_observed_domain)) >>
  `!h. valid_horizon cx st0 h q.storage_trace ==>
    vv_post_mods h ctx func ce cx e p a m s q raw vv mid /\
    ghost_inv_at_mods (DF h) lo d ce cx q G' tn' mid` by
    (qx_gen_tac `h` >> disch_tac >>
     qpat_assum `!h. _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (qspec_then `h` (drule_then strip_assume_tac)) >>
     qpat_x_assum `INL raw = INL _` (SUBST_ALL_TAC o SYM o REWRITE_RULE [sumTheory.INL_11]) >>
     conj_tac >- suspend "copy_postgas" >>
     fs[ctor_payload_vv_final_obs_mods]) >>
  `vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) q raw vv mid /\
   ptr_vv_ok cx (post_value_type ce e) raw vv q G' tn' mid` by
    fs[ctor_payload_vv_final_obs_mods] >>
  `!tag op. vv = StackValue tag op ==> ptr_buf_ok ce e op G' mid` by simp[] >>
  `compile_snapshot_vv ce T (ext_call_arg_value (lowered_value_type ce e) vv) m = (saved,b)` by fs[] >>
  `eval_expr cx e (p with gas_obs := p.gas_obs) = (INL raw,q)` by
    simp[IgnAsm `p.gas_obs = _`] >>
  `ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
     ?val. read_result cx raw q = (INL val,q) /\
       !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
       eval_operand (vv_operand vv) mid = SOME w ==>
       w2n w + type_memory_size rt <= lo /\
       (!mem. mem_agree_outside tn'.t_mem mid.vs_memory mem ==>
              val_in_memory rt val (w2n w) mem)` by fs[read_result_success_gas_iff] >>
  `fn_inst_ids_distinct func` by fs[expr_sim_full_code_def] >>
  drule_all ctor_private_snapshot_actual_mods >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  suspend "copied_entry"
QED

Resume blueprint_ctor_vv_row_mods[copy_postgas]:
  `storage_well_formed_on cx (q with gas_obs := []) (FST h) <=>
   storage_well_formed_on cx q (FST h)` by
    (irule storage_well_formed_on_backends >> simp[]) >>
  `!tr w tvt vl. read_storage_slot cx tr w tvt (q with gas_obs := []) =
       (INL vl,q with gas_obs := []) <=> read_storage_slot cx tr w tvt q = (INL vl,q)` by
    (rpt gen_tac >> qspecl_then [`PlaceR (StoragePlace tr w tvt)`,`vl`] mp_tac
       (Q.GENL [`r`,`v`] (Q.INST [`ee` |-> `q`, `gs` |-> `[]`] read_result_success_gas_iff)) >>
     simp[read_result_def,read_place_def]) >>
  `!ty. vv_holds_mods ce cx ty raw vv (q with gas_obs := []) mid <=>
        vv_holds_mods ce cx ty raw vv q mid` by
    (Cases_on `vv` >> simp[vv_holds_mods_def,vv_holds_def,read_result_success_gas_iff] >>
     rename1 `compile_expr ce _ e a = (LocatedValue _ pp,m)` >>
     Cases_on `pp.ptr_location` >>
     simp[vv_holds_def,storage_holds_def,immutable_holds_def,immutable_holds_mods_def,
          read_result_success_gas_iff,get_storage_def]) >>
  `!ty. vv_at ce cx ty a m (q with gas_obs := []) raw vv mid <=>
        vv_at ce cx ty a m q raw vv mid` by
    (Cases_on `vv` >> simp[vv_at_def,expr_val_at_def,read_result_success_gas_iff]) >>
  `vv_place_ptr_mods ce cx (q with gas_obs := []) mid raw vv <=>
   vv_place_ptr_mods ce cx q mid raw vv` by
    (Cases_on `vv` >> Cases_on `raw` >> simp[vv_place_ptr_mods_def,vv_place_ptr_def] >>
     rename1 `case place of _ => _` >> Cases_on `place` >> simp[vv_place_ptr_def]) >>
  `vv_storage_live h cx vv (q with gas_obs := []) mid <=> vv_storage_live h cx vv q mid` by
    (Cases_on `vv` >> simp[vv_storage_live_def,get_storage_def]) >>
  `immutable_frame_mods func ce cx (q with gas_obs := []) mid <=>
   immutable_frame_mods func ce cx q mid` by
    (pure_rewrite_tac[immutable_frame_mods_def,immutables_rel_mods_def,
       immutable_alloca_sep_mods_def,immutables_rel_def,immutable_alloca_sep_def,
       evaluation_state_accfupds] >> REFL_TAC) >>
  `!ty. vv_own ce cx ty a m (q with gas_obs := []) raw vv mid <=>
        vv_own ce cx ty a m q raw vv mid` by
    (Cases_on `vv` >> simp[vv_own_def,expr_val_own_def,read_result_success_gas_iff]) >>
  qpat_x_assum `vv_post_mods h _ _ _ _ _ _ _ _ _ (q with gas_obs := []) raw vv _` mp_tac >>
  pure_asm_rewrite_tac[vv_post_mods_def,stmt_state_rel_start_gas_obs,
       locals_kept_def,popped_kept_def,evaluation_state_accfupds] >>
  disch_then ACCEPT_TAC
QED

Resume blueprint_ctor_vv_row_mods[copied_entry]:
  qpat_assum `!h. _ ==> gas_origin_ptr_path _ (mid,_,_) [] _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  rename1 `gas_origin_ptr_path _ (mid,_,_) [] (OK t,Gout,tout)` >>
  `snap = []` by
    (qpat_assum `gas_origin_ptr_path _ (mid,_,_) [] _`
       (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections) >>
     first_assum (drule_then ACCEPT_TAC)) >>
  `mid.vs_gas_readings = t.vs_gas_readings` by
    (qpat_assum `create_expr_prefix m b _ _ _ mid snap t`
       (mp_tac o MATCH_MP createSizeRawReplayTheory.create_prefix_readings) >> simp[]) >>
  `!f i z. frag_reachable ctx func t f i z ==> dalloca_fmp_headroom i z` by
    (qpat_assum `gas_origin_ptr_path _ (mid,_,_) [] _` mp_tac >>
     qpat_assum `!f i z. frag_reachable ctx func mid f i z ==> _` mp_tac >>
     qpat_assum `!bb. MEM bb func.fn_blocks ==> _` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[gas_origin_ptr_path_dalloca_fmp_headroom]) >>
  `!h. valid_horizon cx st0 h q.storage_trace ==>
      stmt_state_rel h ctx func ce cx q t /\ immutable_frame_mods func ce cx q t /\
      storage_well_formed_on cx q (FST h) /\
      ghost_inv_at_mods (DF h) lo d ce cx q Gout tout t /\ return_buf_frame d ce b t /\
      alloca_history func t /\ ~t.vs_halted` by
    (qx_gen_tac `h` >> disch_tac >>
     qpat_assum `!h. _ ==> gas_origin_ptr_path _ (mid,_,_) [] _ /\ _`
       (qspec_then `h` (drule_then strip_assume_tac)) >>
     qpat_x_assum `!kw. extcall_positional_post_mods mods T DF lo d ctx func ce cx env kw [e] _ _ _ _ _ _ _ h _ q Gout tout t`
       (qspec_then `[]` (strip_assume_tac o SIMP_RULE (srw_ss())
          [extcall_positional_post_mods_def])) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!h. _ ==> stmt_state_rel h ctx func ce cx q t /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    metis_tac[stmt_state_rel_allocas_below_fmp] >>
  qexistsl [`Gout`,`tout`] >> simp[] >> conj_tac
  >- (rpt gen_tac >> disch_tac >>
      qpat_assum `!h. _ ==> gas_origin_ptr_path _ (s,_,_) _ _ /\ _`
        (drule_then strip_assume_tac) >> gvs[]) >>
  first_assum ACCEPT_TAC
QED
Finalise blueprint_ctor_vv_row_mods

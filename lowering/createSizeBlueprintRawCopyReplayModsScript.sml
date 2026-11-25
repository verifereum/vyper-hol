Theory createSizeBlueprintRawCopyReplayMods
Ancestors
  createSizeBlueprintRawCopyReplay createExprSizeExitDefsMods
  gasShadowCompileBase
  e2eDefs exprSimFullBundleProps fragExec fragGasOrigin fragGasOriginPtr gasExplicitSites
  gasSummary s1PrefixDefs venomExecSemantics venomInst venomState vyperState relation list
  words createMarkedPath pair bodyFullIfExpReach arithmetic exprLowering stmtLoweringMono
  vfmConstants compileEnv exprLoweringProps exprSimSource bodySimStmtFacts vyperStorageTrace
  bodyMemoryDefs exprOperandVar freshWrites rich_list exprSimHypsDefs exprSimHyps
  bodyPtrDefs loweringPosts context createSizeRawSourceMods fragGasPath vyperAST
  vyperStorageFootprint vyperValue integer_word valueEncoding createCtorSegmentArrival
  exprSimSubscriptArrayCompose loweringStateRelDefs exprSimMemDefs ptrDiscipline
  createBlueprintRawCopyLayoutMods createCtorObservedSilence bodyPtrMakeArrayEmission bodySim
  loweringShapeDefs createExprSizeExitDefs createSizePrefixReplayMods
  createSizeRawReplayMods createSizeBlueprintKeywordReplay
  createBlueprintRawCopyMods exprBodyPreTypingProps exprBodyPreCallSafetyProps
  vyperTypeEvalSoundness vyperTypeInvariants vyperExprNoControl exprSimDefs gasContext
  bodyFullPostsMods bodyFullShadowBodyInv bodyInvSplit vyperStorageBackend
  vyperEvalExprPreservesScopesDom bodyFullExtCallPackingReady
  createSizeRawReplay vyperTypeExprSoundness createSizePrefixReplay

Theorem blueprint_raw_copied_at_cut_mods:
  contract_inv mods exps ctx ce cx /\
  module_body_inv mods src tops ce cx /\ shadow_body_inv_mods mods exps ctx shctx /\
  expr_body_pre_mods mods ce cx env e p /\ create_operand_completed_ok_mods mods exps cx e /\
  expr_type e = BaseT (BytesT (Dynamic k)) /\ exprs_can_mutate ce later /\
  eval_operand target_op s = SOME aw /\ (!x. target_op = Var x ==> not_fresh_at ca x) /\
  local_ptrs_reserved ce ca /\ (!h. dead_lo_ok_mods h (DF h) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  return_buf_frame d ce ca s /\ alloca_history fnc s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!f i z. frag_reachable ctx fnc s f i z ==> dalloca_fmp_headroom i z) /\
  (!h. valid_horizon cx st0 h p.storage_trace ==>
    stmt_state_rel h ctx fnc ce cx p s /\
    immutable_frame_mods fnc ce cx p s /\ storage_well_formed_on cx p (FST h) /\
    ghost_inv_at_mods (DF h) lo d ce cx p Gi ti s) /\
  ~s.vs_halted /\ s.vs_current_bb = ca.cs_current_bb /\ s.vs_inst_idx = LENGTH ca.cs_current_insts /\
  compile_expr ce (expr_type e) e ca = (vv,cm) /\
  compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) sca = (vv,scm) /\
  expr_sim_full_code (ctx,shctx,fnc,shfnc) (ca,cm,sca,scm) /\
  compile_snapshot_vv ce (exprs_can_mutate ce later) vv cm = (saved,cs) /\
  unwrap_value ce saved cs = (raw_op,cu) /\
  emit_op MLOAD [raw_op] cu = (len,cl) /\
  fn_has_code cm cs fnc /\ fn_has_code cu cl fnc /\
  create_expr_prefix ca cm (gas_explicit_sites ctx shctx) ctx fnc s mc t /\
  t.vs_current_bb = cm.cs_current_bb /\ t.vs_inst_idx = LENGTH cm.cs_current_insts /\
  create_expr_prefix cm cs (gas_explicit_sites ctx shctx) ctx fnc t ms r /\
  r.vs_current_bb = cs.cs_current_bb /\ r.vs_inst_idx = LENGTH cs.cs_current_insts /\
  create_expr_prefix cs cu (gas_explicit_sites ctx shctx) ctx fnc r mu u /\
  u.vs_current_bb = cu.cs_current_bb /\ u.vs_inst_idx = LENGTH cu.cs_current_insts /\
  (!v. storage_trace_frame (kcont v)) /\
  bind (bind (eval_expr cx e) (read_result cx)) kcont p = (res,out) /\
  valid_horizon cx st0 H out.storage_trace /\
  p.gas_obs = gas_explicit (mc ++ (ms ++ (mu ++ rest))) s.vs_gas_readings ++ tail ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err) \/
  ?bs q G tn.
    bind (eval_expr cx e) (read_result cx) p = (INL (BytesV bs),q) /\
    kcont (BytesV bs) q = (res,out) /\ valid_horizon cx st0 H q.storage_trace /\
    q.gas_obs = gas_explicit rest u.vs_gas_readings ++ tail /\
    expr_val_rel cx (BaseT (BytesT (Dynamic k))) (BytesV bs) raw_op u /\
    eval_operand target_op u = SOME aw /\ (!x. target_op = Var x ==> not_fresh_at cu x) /\
    expr_sim_inv_mods mods ce cx env q /\ local_ptrs_reserved ce cu /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cu x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cu x) /\
    return_buf_frame d ce cu u /\ alloca_history fnc u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    (!f i z. frag_reachable ctx fnc u f i z ==> dalloca_fmp_headroom i z) /\
    (!h. valid_horizon cx st0 h q.storage_trace ==>
      stmt_state_rel h ctx fnc ce cx q u /\
      immutable_frame_mods fnc ce cx q u /\ storage_well_formed_on cx q (FST h) /\
      ghost_inv_at_mods (DF h) lo d ce cx q G tn u) /\ ~u.vs_halted
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_vv_sim_full_pre_mods (DF,lo,d,ctx,shctx,([]:(num#num) option list),fnc,shfnc) ce cx
      (expr_type e) e p (st0,ca,cm,sca,scm,vv,s,Gi,ti)` by
    (simp[expr_vv_sim_full_pre_mods_def] >>
     conj_tac >- suspend "admissible" >>
     rpt conj_tac >> rpt strip_tac >>
     first_assum (drule_then (fn th => strip_assume_tac th >> FIRST_ASSUM ACCEPT_TAC))) >>
  drule_at (Pat `expr_vv_sim_full_pre_mods _ _ _ _ _ _ _`) create_size_replay_vv_cut_mods >>
  disch_then (qspecl_then [`mods`,`exps`,`src`,`tops`,`env`] mp_tac) >>
  simp[] >> strip_tac >>
  `?rr q. eval_expr cx e p = (rr,q)` by (Cases_on `eval_expr cx e p` >> simp[]) >>
  `valid_horizon cx st0 H q.storage_trace` by
    (`!tv. storage_trace_frame (bind (read_result cx tv) kcont)` by
       simp[storage_trace_frame_bind_all,storage_trace_frame_read_result] >>
     qpat_assum `bind (bind (eval_expr cx e) (read_result cx)) kcont p = _` mp_tac >>
     pure_rewrite_tac[vyperStateTheory.bind_assoc] >> Cases_on `rr` >>
     simp[Once bind_def] >> strip_tac >>
     qpat_assum `bind (read_result cx _) kcont q = _`
       (mp_then Any irule vyperStorageFootprintTheory.valid_horizon_frame) >> simp[]) >>
  qabbrev_tac `suffix = gas_explicit (ms ++ (mu ++ rest)) t.vs_gas_readings ++ tail` >>
  `p.gas_obs = gas_explicit mc s.vs_gas_readings ++ suffix` by
    (qpat_assum `create_expr_prefix ca cm _ _ _ s mc t`
       (mp_then Any assume_tac create_prefix_readings) >>
     simp[Abbr `suffix`,gas_explicit_append,APPEND_ASSOC,DROP_DROP_T,
          AC ADD_ASSOC ADD_COMM]) >>
  `p with gas_obs := gas_explicit mc s.vs_gas_readings ++ suffix = p` by
    simp[evaluation_state_component_equality] >>
  qpat_x_assum `gas_completed_operand_mods _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE[gas_completed_operand_mods_def]) >>
  disch_then (qspecl_then [`H`,`mc`,`t`,`suffix`,`rr`,`q`] mp_tac) >>
  simp[] >> strip_tac
  >- suspend "source" >>
  disj1_tac >> qexists_tac `err` >> fs[vyperStateTheory.bind_assoc,bind_def]
QED

Resume blueprint_raw_copied_at_cut_mods[admissible]:
  rw[gas_admissible_def] >>
  `expr_body_pre_mods mods ce cx env e (p with gas_obs := gs)` by
    (qpat_assum `expr_body_pre_mods _ _ _ _ _ p` mp_tac >>
     pure_rewrite_tac[expr_body_pre_mods_def,expr_sim_inv_mods_def,
                      evaluation_state_accfupds,gas_obs_type_invariants] >>
     disch_then ACCEPT_TAC) >>
  pop_assum (fn th =>
    strip_assume_tac (MATCH_MP expr_body_pre_mods_runtime_typing th) >>
    assume_tac (MATCH_MP expr_body_pre_mods_call_evaluation_safe th)) >>
  qspecl_then [`cx`,`e`] (mp_tac o CONJUNCT1) (cj 5 eval_scc_type_sound_mutual) >>
  rename1 `eval_expr cx e (p with gas_obs := gs) = (evres,ee)` >>
  disch_then (qspecl_then [`env`,`p with gas_obs := gs`,`evres`,`ee`] mp_tac) >>
  impl_tac >- fs[runtime_consistent_def,env_consistent_def,state_well_typed_def] >>
  Cases_on `evres` >> simp[] >> strip_tac
  >- (rename1 `eval_result_typed _ tv _` >> Cases_on `tv` >>
      gvs[expr_vv_res_ok_def,eval_result_typed_def]) >>
  drule (cj 1 eval_expr_no_control) >>
  rename1 `INR exc` >> Cases_on `exc` >>
  gvs[no_control_exc_def,no_type_error_result_def,expr_vv_res_ok_def] >>
  rename1 `Error err` >> Cases_on `err` >> gvs[]
QED

Resume blueprint_raw_copied_at_cut_mods[source]:
  qmatch_asmsub_rename_tac `gas_origin_ptr_path _ (s,Gi,ti) mc (OK t,Gv,tvtn)` >>
  qpat_assum `!h. valid_horizon cx st0 h q.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >>
  impl_tac >- FIRST_ASSUM ACCEPT_TAC >> strip_tac >>
  rename1 `rr = INL tv` >>
  `eval_expr cx e (p with gas_obs := p.gas_obs) = (INL tv,q)` by simp[] >>
  drule_all create_raw_read_bytes_mods >> strip_tac >>
  rename1 `read_result cx tv q = (INL (BytesV bs),q)` >>
  `bind (eval_expr cx e) (read_result cx) p = (INL (BytesV bs),q)` by simp[bind_def] >>
  `kcont (BytesV bs) q = (res,out)` by
    (qpat_assum `bind (bind (eval_expr cx e) (read_result cx)) kcont p = _` mp_tac >>
     pure_once_rewrite_tac[bind_def] >> simp[]) >>
  `eval_expr cx e p = (INL tv,q)` by fs[] >>
  `~is_word_type (vv_type vv)` by
    (drule_all create_blueprint_raw_copy_layout_mods >>
     strip_tac >> simp[is_word_type_def]) >>
  `cu = cs` by
    (`?dst. saved = LocatedValue (vv_type vv) (mk_ptr dst LocMemory)` by
       (qpat_x_assum `compile_snapshot_vv _ _ _ _ = _` mp_tac >>
        Cases_on `compile_materialize_vv ce (vv_type vv) vv cm` >>
        simp[compile_snapshot_vv_def,comp_bind_def,comp_return_def] >> metis_tac[]) >>
     fs[unwrap_value_def,mk_ptr_def,comp_return_def]) >>
  `u = r /\ mu = []` by
    (qpat_assum `create_expr_prefix cs cu _ _ _ r mu u`
       (mp_tac o REWRITE_RULE [create_expr_prefix_marked]) >>
     ONCE_REWRITE_TAC[RTC_CASES1] >>
     simp[EXISTS_PROD,create_marked_edge_def,create_prefix_step_def]) >>
  `storage_trace_domain cx st0 q.storage_trace` by
    (qpat_assum `valid_horizon cx st0 H q.storage_trace`
       (ACCEPT_TAC o MATCH_MP extcall_packing_observed_domain)) >>
  `is_bytestring_type (expr_type e)` by simp[is_bytestring_type_def] >>
  `post_value_type ce e = expr_type e` by simp[post_value_type_bytestring] >>
  `~is_word_type (post_value_type ce e)` by simp[is_word_type_def] >>
  `!h. valid_horizon cx st0 h q.storage_trace ==>
    vv_post_mods h ctx fnc ce cx e p ca cm s q tv vv t /\
    ghost_inv_at_mods (DF h) lo d ce cx q Gv tvtn t` by suspend "postgas" >>
  `vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) q tv vv t /\
   ptr_vv_ok cx (post_value_type ce e) tv vv q Gv tvtn t` by
    (qpat_assum `vv_store_bound _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `ptr_vv_ok _ _ _ _ _ _ _ _` mp_tac >>
     Cases_on `vv` >>
     pure_rewrite_tac[vv_store_bound_def,ptr_vv_ok_def,read_result_success_gas_iff] >> simp[]) >>
  `ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
     ?v. read_result cx tv q = (INL v,q) /\
         !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
                eval_operand (vv_operand vv) t = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside tvtn.t_mem t.vs_memory mem ==> val_in_memory rt v (w2n w) mem)` by
    (strip_tac >>
     qpat_assum `ce.ce_is_ctor /\ vv_location vv = _ ==> _` mp_tac >>
     (impl_tac >- simp[]) >>
     rewrite_tac[read_result_success_gas_iff] >>
     disch_then (qx_choose_then `v` strip_assume_tac) >>
     qexists_tac `v` >> (conj_tac >- FIRST_ASSUM ACCEPT_TAC) >>
     pure_once_rewrite_tac[ADD_COMM] >> FIRST_ASSUM ACCEPT_TAC) >>
  suspend "machine"
QED

Resume blueprint_raw_copied_at_cut_mods[postgas]:
  gen_tac >> disch_tac >>
  qpat_assum `!h. valid_horizon cx st0 h q.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `h` mp_tac) >>
  (impl_tac >- FIRST_ASSUM ACCEPT_TAC) >>
  qpat_assum `rr = INL tv` (fn th => rewrite_tac[th, sumTheory.INL_11, UNWIND_THM2]) >>
  disch_then (strip_assume_tac o CONJUNCT2) >>
  qpat_x_assum `tv = _` SUBST_ALL_TAC >>
  reverse conj_tac
  >- (qpat_assum `ghost_inv_at_mods (DF h) _ _ _ _ (q with gas_obs := []) _ _ _` mp_tac >>
      pure_rewrite_tac[ghost_inv_at_mods_def,evaluation_state_accfupds] >>
      disch_then ACCEPT_TAC) >>
  `storage_well_formed_on cx (q with gas_obs := []) (FST h) <=>
   storage_well_formed_on cx q (FST h)` by
    (irule storage_well_formed_on_backends >> simp[]) >>
  `!tr w tvt v. read_storage_slot cx tr w tvt (q with gas_obs := []) =
       (INL v,q with gas_obs := []) <=> read_storage_slot cx tr w tvt q = (INL v,q)` by
    (rpt gen_tac >> qspec_then `PlaceR (StoragePlace tr w tvt)` mp_tac
       (Q.GEN `r` (Q.INST [`ee` |-> `q`, `gs` |-> `[]`] read_result_success_gas_iff)) >>
     simp[read_result_def,read_place_def]) >>
  rename1 `vv_post_mods h _ _ _ _ _ _ _ _ _ q result vv _` >>
  `!ty. vv_holds_mods ce cx ty result vv (q with gas_obs := []) t <=>
        vv_holds_mods ce cx ty result vv q t` by
    (Cases_on `vv` >> simp[vv_holds_mods_def,vv_holds_def,read_result_success_gas_iff] >>
     Cases_on `p'.ptr_location` >>
     simp[vv_holds_def,storage_holds_def,immutable_holds_def,immutable_holds_mods_def,
          read_result_success_gas_iff,get_storage_def]) >>
  `!ty. vv_at ce cx ty ca cm (q with gas_obs := []) result vv t <=>
        vv_at ce cx ty ca cm q result vv t` by
    (Cases_on `vv` >> simp[vv_at_def,expr_val_at_def,read_result_success_gas_iff]) >>
  `vv_place_ptr_mods ce cx (q with gas_obs := []) t result vv <=>
   vv_place_ptr_mods ce cx q t result vv` by
    (Cases_on `vv` >> Cases_on `result` >> simp[vv_place_ptr_mods_def,vv_place_ptr_def] >>
     rename1 `case place of _ => _` >> Cases_on `place` >> simp[vv_place_ptr_def]) >>
  `vv_storage_live h cx vv (q with gas_obs := []) t <=> vv_storage_live h cx vv q t` by
    (Cases_on `vv` >> simp[vv_storage_live_def,get_storage_def]) >>
  qpat_x_assum `vv_post_mods h _ _ _ _ _ _ _ _ _ (q with gas_obs := []) result vv _` mp_tac >>
  pure_asm_rewrite_tac[vv_post_mods_def,stmt_state_rel_start_gas_obs,
       immutable_frame_mods_def,immutables_rel_mods_def,immutable_alloca_sep_mods_def,
       immutables_rel_def,immutable_alloca_sep_def,locals_kept_def,popped_kept_def,
       evaluation_state_accfupds] >>
  simp_tac bool_ss [] >> strip_tac >> rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC
QED

Resume blueprint_raw_copied_at_cut_mods[machine]:
  `ci_mono ca cm` by
    (qspecl_then [`ce`,`expr_type e`,`e`,`ca`] mp_tac (cj 1 ci_mono_compile_expr_sa) >> simp[]) >>
  `ci_mono cm cs` by
    (qspecl_then [`ce`,`exprs_can_mutate ce later`,`vv`,`cm`] mp_tac ci_mono_compile_snapshot_vv >> simp[]) >>
  `ca.cs_next_var <= cm.cs_next_var /\ ca.cs_next_id <= cm.cs_next_id /\
   cm.cs_next_var <= cs.cs_next_var` by fs[ci_mono_def] >>
  `local_ptrs_reserved ce cm /\ local_ptrs_reserved ce cs` by
    (conj_asm1_tac >> metis_tac[local_ptrs_reserved_next_var]) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at cm x` by
    (gen_tac >> disch_tac >>
     drule_all (cj 1 exprOperandVarTheory.compiler_compile_var) >> simp[]) >>
  `!x. target_op = Var x ==> not_fresh_at cm x` by metis_tac[not_fresh_at_mono] >>
  `MAP FDOM p.scopes = MAP FDOM q.scopes` by
    (qpat_assum `eval_expr cx e p = (INL tv,q)`
      (mp_then Any mp_tac eval_expr_preserves_scopes_dom) >> simp[]) >>
  `expr_sim_inv_mods mods ce cx env q` by
    (drule_all (REWRITE_RULE[ETA_THM] expr_body_pre_eval_mods) >> simp[]) >>
  `MEM fnc ctx.ctx_functions` by fs[expr_sim_full_code_def] >>
  `fn_inst_ids_distinct fnc` by fs[expr_sim_full_code_def] >>
  `!bb. MEM bb fnc.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (gen_tac >> disch_tac >> drule_all body_inv_no_phi_mods >> simp[]) >>
  `~t.vs_halted` by
    (qpat_assum `create_expr_prefix ca cm _ _ _ s mc t`
       (mp_then Any mp_tac create_prefix_gas_path) >>
     simp[] >> metis_tac[gas_path_normal]) >>
  `!x w. not_fresh_at ca x /\ lookup_var x s = SOME w ==> lookup_var x t = SOME w` by
    (qpat_assum `!h. valid_horizon cx st0 h q.storage_trace ==> vv_post_mods _ _ _ _ _ _ _ _ _ _ q _ _ _ /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- FIRST_ASSUM ACCEPT_TAC) >>
     disch_then (strip_assume_tac o REWRITE_RULE[vv_post_mods_def]) >> FIRST_ASSUM ACCEPT_TAC) >>
  `eval_operand target_op t = SOME aw` by
    (`t.vs_labels = s.vs_labels` by
       (qpat_assum `create_expr_prefix ca cm _ _ _ s mc t`
          (mp_then Any mp_tac create_prefix_labels) >> simp[]) >>
     irule blueprint_eval_operand_frame >> qexistsl_tac [`ca`,`s`] >> simp[]) >>
  `return_buf_frame d ce cm t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`ce`,`s`,`ca`] >> simp[]) >>
  `?next. ctor_segment_fetch fnc u = SOME next /\ next.inst_opcode = MLOAD /\ cs.cs_next_id <= next.inst_id` by
    (drule_all emit_op_fetch_boundary >>
     disch_then (qx_choosel_then [`tmp`,`bb`] (map_every assume_tac o CONJUNCTS)) >>
     qexists_tac `mk_inst cu.cs_next_id MLOAD [raw_op] [tmp]` >>
     (conj_tac >-
       (pure_rewrite_tac[ctor_segment_fetch_def] >>
        qpat_assum `lookup_block u.vs_current_bb _ = SOME bb` (once_rewrite_tac o single) >>
        pure_rewrite_tac[optionTheory.OPTION_BIND_def] >> BETA_TAC >> FIRST_ASSUM ACCEPT_TAC)) >>
     simp[mk_inst_def]) >>
  suspend "cut"
QED

Resume blueprint_raw_copied_at_cut_mods[cut]:
  qabbrev_tac `R = \x y. (x.vs_current_bb <> cs.cs_current_bb \/
                            x.vs_inst_idx <> LENGTH cs.cs_current_insts) /\
        ?ms. gas_origin_edge F (gas_explicit_sites ctx shctx) ctx fnc x ms (OK y)` >>
  `RTC R t u` by
    (qpat_assum `u = r` SUBST_ALL_TAC >>
     qpat_assum `create_expr_prefix cm cs _ _ _ t ms r`
       (mp_then Any irule create_expr_prefix_rtc_project) >>
     simp[Abbr `R`,create_prefix_step_def] >> metis_tac[]) >>
  `!x y. R x y ==> (x.vs_current_bb <> cs.cs_current_bb \/ x.vs_inst_idx <> LENGTH cs.cs_current_insts) /\
        ?ms. gas_origin_edge F (gas_explicit_sites ctx shctx) ctx fnc x ms (OK y)` by simp[Abbr `R`] >>
  `compile_snapshot_vv ce T vv cm = (saved,cs)` by
    (qpat_assum `exprs_can_mutate ce later` (fn th =>
       qpat_assum `compile_snapshot_vv _ _ _ _ = _`
         (ACCEPT_TAC o PURE_REWRITE_RULE [EQT_INTRO th]))) >>
  `!ty op. vv = StackValue ty op ==> ptr_buf_ok ce e op Gv t` by
    (rpt strip_tac >> qpat_assum `!ty op. vv = StackValue ty op /\ _ ==> _`
       (qspecl_then [`ty`,`op`] mp_tac) >> simp[]) >>
  `u.vs_current_bb = cs.cs_current_bb /\ u.vs_inst_idx = LENGTH cs.cs_current_insts` by fs[] >>
  suspend "copy"
QED

Resume blueprint_raw_copied_at_cut_mods[copy]:
  drule_all (Q.INST [`PG` |-> `[]:(num # num) option list`,
                    `explicit` |-> `gas_explicit_sites ctx shctx`]
               create_blueprint_raw_copy_at_cut_mods) >>
  disch_then (qx_choosel_then [`dst`,`w`,`Gu`,`tu`] strip_assume_tac) >>
  `gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shctx,ctx,fnc,[])
      (t,Gv,tvtn) [] (OK u,Gu,tu)` by
    (qpat_assum `!h. _ ==> gas_origin_ptr_path _ (t,Gv,tvtn) [] _ /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >> FIRST_ASSUM ACCEPT_TAC) >>
  `ms = []` by
    (drule gas_origin_ptr_path_projections >> strip_tac >>
     irule ctor_observed_cut_silent >>
     qexistsl_tac [`ctx`,`(cs.cs_current_bb,LENGTH cs.cs_current_insts)`,
       `gas_explicit_sites ctx shctx`,`fnc`,`u`,`t`] >> simp[] >>
     irule RTC_MONOTONE >>
     qpat_assum `create_expr_prefix cm cs _ _ _ t ms r`
       (irule_at Any o REWRITE_RULE[create_expr_prefix_marked]) >>
     simp[create_marked_edge_def,FORALL_PROD,create_prefix_step_def] >> metis_tac[]) >>
  `q.gas_obs = gas_explicit rest u.vs_gas_readings ++ tail` by
    (qpat_assum `create_expr_prefix cm cs _ _ _ t ms r`
       (mp_then Any assume_tac create_prefix_readings) >> simp[Abbr `suffix`]) >>
  `raw_op = Var dst` by fs[unwrap_value_def,mk_ptr_def,comp_return_def] >>
  `!f i z. frag_reachable ctx fnc t f i z ==> dalloca_fmp_headroom i z` by
    (qpat_assum `gas_origin_ptr_path _ (s,Gi,ti) mc _`
       (mp_then Any mp_tac gas_origin_ptr_path_dalloca_fmp_headroom) >> asm_rewrite_tac[]) >>
  `!f i z. frag_reachable ctx fnc u f i z ==> dalloca_fmp_headroom i z` by
    (qpat_assum `gas_origin_ptr_path _ (t,Gv,tvtn) [] _`
       (mp_then Any mp_tac gas_origin_ptr_path_dalloca_fmp_headroom) >> asm_rewrite_tac[]) >>
  `!h. valid_horizon cx st0 h q.storage_trace ==> storage_well_formed_on cx q (FST h)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!h. _ ==> vv_post_mods h _ _ _ _ _ _ _ _ _ q _ _ _ /\ _`
       (qspec_then `h` mp_tac) >>
     (impl_tac >- FIRST_ASSUM ACCEPT_TAC) >>
     disch_then (strip_assume_tac o REWRITE_RULE[vv_post_mods_def]) >> FIRST_ASSUM ACCEPT_TAC) >>
  qpat_x_assum `cu = cs` SUBST_ALL_TAC >>
  disj2_tac >> qexistsl_tac [`bs`,`q`,`Gu`,`tu`] >> simp[] >>
  rpt conj_tac
  >- metis_tac[not_fresh_at_mono,LESS_EQ_TRANS]
  >- metis_tac[not_fresh_at_mono,LESS_EQ_TRANS]
  >- metis_tac[not_fresh_at_mono,LESS_EQ_TRANS]
  >- (qpat_assum `u = r` SUBST_ALL_TAC >> FIRST_ASSUM ACCEPT_TAC)
  >> qpat_x_assum `u = r` SUBST_ALL_TAC >> gen_tac >> disch_tac >>
  qpat_assum `!h. _ ==> gas_origin_ptr_path _ (t,Gv,tvtn) [] _ /\ _`
    (qspec_then `h` (drule_then strip_assume_tac)) >> simp[]
QED

Finalise blueprint_raw_copied_at_cut_mods

Theory createSizeBlueprintRawScalarsMods
Ancestors
  createSizeBlueprintRawScalars createExprSizeExitDefsMods
  gasShadowCompileBase
  abiEncoderProps e2eDefs exprSimFullBundleProps fragExec fragGasOrigin gasExplicitSites
  gasSummary venomExecSemantics venomInst venomState vyperState relation list words
  createMarkedPath pair bodyFullIfExpReach arithmetic exprLowering stmtLoweringMono
  vfmConstants loweringShapeRules compileEnv exprLoweringProps exprBodyPreProps
  vyperStorageTrace bodyMemoryDefs freshWrites rich_list exprSimHypsDefs
  vyperTypeExprSoundness exprSimHyps bodyPtrDefs loweringPosts context vyperAST
  vyperStorageFootprint vyperTyping vyperValue ghostPcTransportPtr integer_word
  aggregateEvaluatedLayout loweringStateRelDefs createSizeByteLength createBlueprintRawCopyMods
  bodyFullGhostFrame assignTuplePtrLoadStep augAssignFullLoadFrame contextRawReachable
  stateFrame ptrDiscipline stmtReasonMemory emitHelperProps bodyPtrMakeArrayEmission
  venomInstProofs1 gasEvents bodySim loweringShapeDefs createExprSizeExitDefs
  createSizePrefixReplayMods createSizeObservedPrefix createCtorSegmentArrival
  createSizeBlueprintKeywordReplayMods exprSimHyps exprSimIfExpCompat
  vyperTypeEvalCaseProofs

(* A retained operand is replayed through its unwrap as one scalar read. *)

Theorem blueprint_raw_nonword_tag_mods[local]:
  expr_body_pre_mods mods ce cx env e p /\ expr_type e = BaseT (BytesT (Dynamic k)) /\
  compile_expr ce (expr_type e) e ca = (vv,cm) ==>
  ~is_word_type (vv_type vv)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule exprBodyPrePropsTheory.expr_body_pre_mods_well_typed >> strip_tac >>
  drule exprBodyPrePropsTheory.expr_body_pre_mods_inv >> strip_tac >>
  `!fid sg. FLOOKUP env.fn_sigs fid = SOME sg ==>
            ce.ce_func_return_type (nsid_to_string fid) = sg.ret_ty` by
    metis_tac[exprBodyPrePropsTheory.expr_sim_inv_mods_return_type] >>
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    (Cases_on `?ty fid args drv. e = Call ty (IntCall fid) args drv`
     >- (pop_assum strip_assume_tac >> gvs[] >> PairCases_on `fid` >>
         gvs[vyperTypeSystemTheory.well_typed_expr_def, lowered_value_type_def,
             vyperASTTheory.expr_type_def] >>
         first_x_assum (drule_then SUBST1_TAC) >>
         fs[vyperTypeSystemTheory.type_widens_to_def])
     >- (`env_consistent env cx p` by
       metis_tac[exprBodyPrePropsTheory.expr_sim_inv_mods_env] >>
     `env.type_defs = get_tenv cx` by
       metis_tac[env_consistent_type_defs_get_tenv] >>
     `!id t. FLOOKUP env.var_types id = SOME t ==>
             well_formed_type env.type_defs t` by
       metis_tac[exprSimSourceTheory.env_consistent_var_type_evaluates,
                  vyperTypeSystemTheory.well_formed_type_def] >>
     `sfields_tenv_consistent ce.ce_struct_fields env.type_defs` by
       fs[expr_sim_inv_mods_def] >>
     drule_all ifexp_lowered_type_classify >> strip_tac >>
     gvs[ifexp_arg_type_fits_refl])) >>
  `~is_word_type (expr_type e)` by simp[is_word_type_def] >>
  `~is_word_type (lowered_value_type ce e)` by
    (drule aggregateEvaluatedLayoutTheory.arg_type_fits_word_type >> simp[]) >>
  `reason_uniform_shape compile_expr ce (expr_type e) e` by
    (irule exprReasonOperandTheory.compile_expr_reason_uniform >>
     qexists_tac `env` >> fs[expr_sim_inv_mods_def]) >>
  pop_assum (strip_assume_tac o REWRITE_RULE[exprReasonOperandTheory.reason_uniform_shape_def]) >>
  qpat_x_assum `!sa vv sb. _ ==> reason_result_shape _ _ _`
    (drule_then assume_tac) >>
  Cases_on `vv` >> gvs[exprReasonOperandTheory.reason_result_shape_def,vv_type_def]
QED

Theorem blueprint_raw_retained_at_cut_mods:
  contract_inv mods exps ctx ce cx /\
  module_body_inv mods src tops ce cx /\ shadow_body_inv_mods mods exps ctx shctx /\
  expr_body_pre_mods mods ce cx env e p /\ create_operand_completed_ok_mods mods exps cx e /\
  expr_type e = BaseT (BytesT (Dynamic k)) /\ ~exprs_can_mutate ce later /\
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
    ghost_inv_at_mods (DF h) lo d ce cx p G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = ca.cs_current_bb /\
  s.vs_inst_idx = LENGTH ca.cs_current_insts /\
  compile_expr ce (expr_type e) e ca = (vv,cm) /\
  compile_snapshot_vv ce (exprs_can_mutate ce later) vv cm = (saved,cs) /\
  unwrap_value ce saved cs = (raw_op,cu) /\
  compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) sca = (vv,scm) /\
  compile_snapshot_vv ce (exprs_can_mutate ce (MAP gas_shadow_expr later)) vv scm = (ssaved,scs) /\
  unwrap_value ce ssaved scs = (raw_op,scu) /\
  expr_sim_full_code (ctx,shctx,fnc,shfnc) (ca,cu,sca,scu) /\
  emit_op MLOAD [raw_op] cu = (len,cl) /\ fn_has_code cu cl fnc /\
  create_expr_prefix ca cm (gas_explicit_sites ctx shctx) ctx fnc s mc m /\
  create_expr_prefix cm cs (gas_explicit_sites ctx shctx) ctx fnc m ms v /\
  create_expr_prefix cs cu (gas_explicit_sites ctx shctx) ctx fnc v mu u /\
  u.vs_current_bb = cu.cs_current_bb /\ u.vs_inst_idx = LENGTH cu.cs_current_insts /\
  (!v. storage_trace_frame (kont v)) /\
  bind (bind (eval_expr cx e) (read_result cx)) kont p = (res,out) /\
  valid_horizon cx st0 H out.storage_trace /\
  p.gas_obs = gas_explicit (mc ++ (ms ++ (mu ++ rest))) s.vs_gas_readings ++ tail ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err) \/
  ?bs q G' tn'.
    bind (eval_expr cx e) (read_result cx) p = (INL (BytesV bs),q) /\
    kont (BytesV bs) q = (res,out) /\ valid_horizon cx st0 H q.storage_trace /\
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
      ghost_inv_at_mods (DF h) lo d ce cx q G' tn' u) /\
    ~u.vs_halted /\ u.vs_current_bb = cu.cs_current_bb /\
    u.vs_inst_idx = LENGTH cu.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all blueprint_raw_nonword_tag_mods >> strip_tac >>
  gvs[gasShadowCompileHelpersTheory.gas_shadow_expr_can_mutate,
      compile_snapshot_vv_def,comp_return_def] >>
  qpat_x_assum `create_expr_prefix cm cm _ _ _ m ms v`
    (strip_assume_tac o MATCH_MP createSizePrefixReplayTheory.create_prefix_empty) >>
  gvs[] >>
  `lower_value compile_expr ce (expr_type e) e ca = (raw_op,cu) /\
   lower_value compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) sca = (raw_op,scu)` by
    simp[lower_value_def,comp_bind_def] >>
  `ca.cs_next_id <= cm.cs_next_id /\ cm.cs_next_id <= cu.cs_next_id` by
    (conj_tac
     >- (qspecl_then [`ce`,`expr_type e`,`e`,`ca`] mp_tac
           (cj 1 ci_mono_compile_expr_sa) >> simp[ci_mono_def]) >>
     qspecl_then [`ce`,`saved`,`cm`] mp_tac ci_mono_unwrap_value >> simp[ci_mono_def]) >>
  `create_expr_prefix ca cu (gas_explicit_sites ctx shctx) ctx fnc s (mc ++ mu) u` by
    (drule_all bodyPtrMakeArrayEmissionTheory.emit_op_fetch_boundary >> strip_tac >>
     irule createSizeObservedPrefixTheory.raw_observed_prefix_join >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac
     >- (qexists_tac `mk_inst cu.cs_next_id MLOAD [raw_op] [tmp]` >>
         gvs[ctor_segment_fetch_def,mk_inst_def]) >>
     qexistsl_tac [`cm`,`m`] >> simp[]) >>
  `p.gas_obs = gas_explicit ((mc ++ mu) ++ rest) s.vs_gas_readings ++ tail` by
    simp[APPEND_ASSOC] >>
  drule_all blueprint_read_at_cut_mods >> strip_tac >- metis_tac[] >>
  rename1 `bind (eval_expr cx e) (read_result cx) p = (INL bv,q)` >>
  `?bs. bv = BytesV bs` by
    (`value_has_type (BaseTV (BytesT (Dynamic k))) bv` by
       (qpat_x_assum `value_runtime_typed env _ bv` mp_tac >>
        simp[value_runtime_typed_def,evaluate_type_def]) >>
     drule_then strip_assume_tac exprSimConvertFromBytesTheory.dynamic_bytes_value_typed >>
     goal_assum (drule_at Any)) >>
  pop_assum strip_assume_tac >>
  drule_all createSizeBlueprintKeywordReplayTheory.blueprint_keyword_mono >> strip_tac >>
  `u.vs_labels = s.vs_labels` by
    (qpat_assum `create_expr_prefix ca cu _ _ _ s (mc ++ mu) u`
       (ACCEPT_TAC o MATCH_MP createSizePrefixReplayTheory.create_prefix_labels)) >>
  `eval_operand target_op u = SOME aw` by
    (irule createSizeBlueprintKeywordReplayTheory.blueprint_eval_operand_frame >> qexistsl [`ca`,`s`] >> simp[] >>
     FIRST_ASSUM ACCEPT_TAC) >>
  `post_value_type ce e = expr_type e` by
    (irule post_value_type_bytestring >> simp[is_bytestring_type_def]) >>
  disj2_tac >> qexistsl [`bs`,`q`,`G'`,`tn'`] >> simp[] >>
  metis_tac[freshWritesTheory.not_fresh_at_mono]
QED

Theorem blueprint_raw_load_add_frame_mods:
  fn_has_code cu cprep fn /\ cprep.cs_current_bb = cu.cs_current_bb /\
  cprep.cs_current_insts = cu.cs_current_insts ++ emitted_insts cu cprep /\
  EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts cu cprep) /\
  a.vs_current_bb = cu.cs_current_bb /\ a.vs_inst_idx = LENGTH cu.cs_current_insts /\
  u.vs_inst_idx = LENGTH cprep.cs_current_insts /\ cu.cs_next_var <= cprep.cs_next_var /\
  state_frame u = state_frame (a with vs_inst_idx := u.vs_inst_idx) /\
  (!x. not_fresh_at cu x ==> lookup_var x u = lookup_var x a) /\
  local_ptrs_reserved ce cu /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cu x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cu x) /\
  return_buf_frame d ce cu a /\ alloca_history fn a /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp a) /\
  (!h. valid_horizon cx st0 h p.storage_trace ==>
    stmt_state_rel h ctx fn ce cx p a /\
    immutable_frame_mods fn ce cx p a /\ ghost_inv_at_mods (DF h) lo d ce cx p G tn a) ==>
  return_buf_frame d ce cprep u /\ alloca_history fn u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  (!h. valid_horizon cx st0 h p.storage_trace ==>
    stmt_state_rel h ctx fn ce cx p u /\
    immutable_frame_mods fn ce cx p u /\ ghost_inv_at_mods (DF h) lo d ce cx p G tn u)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `u.vs_allocas = a.vs_allocas /\ u.vs_alloca_next = a.vs_alloca_next /\
   u.vs_call_ctx = a.vs_call_ctx /\ u.vs_memory = a.vs_memory /\
   u.vs_accounts = a.vs_accounts /\ u.vs_transient = a.vs_transient /\
   u.vs_immutables = a.vs_immutables /\ u.vs_fmp = a.vs_fmp /\
   u.vs_initial_fmp = a.vs_initial_fmp /\ u.vs_data_section = a.vs_data_section` by
    (qpat_assum `state_frame _ = _` mp_tac >> simp[state_frame_def]) >>
  rpt conj_tac
  >- (irule return_buf_frame_frame >> qexistsl [`ce`,`a`,`cu`] >> simp[])
  >- (irule augassign_load_endpoint_history >> qexistsl [`a`,`cu`,`cprep`] >>
      PURE_ASM_REWRITE_TAC [] >> simp[])
  >- (`allocas_below_fmp u = allocas_below_fmp a` by simp[allocas_below_fmp_def] >> simp[]) >>
  gen_tac >> disch_tac >>
  qpat_assum `!h. valid_horizon _ _ h _ ==> _` (drule_then strip_assume_tac) >>
  conj_tac >- (irule stmt_state_rel_old_vars_frame_ptr >> metis_tac[]) >>
  conj_tac
  >- (qpat_x_assum `immutable_frame_mods _ _ _ _ a` mp_tac >>
      simp[bodyFullPostsModsTheory.immutable_frame_mods_def,
           bodyInvSplitTheory.immutables_rel_mods_def, immutables_rel_def,
           bodyInvSplitTheory.immutable_alloca_sep_mods_def] >>
      strip_tac >> conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
      rpt gen_tac >> strip_tac >>
      irule immutable_alloca_sep_frame >> qexistsl_tac [`a`,`p`] >> simp[] >>
      rpt strip_tac >> disj1_tac >> qexists_tac `id` >>
      fs[local_region_def,local_ptrs_reserved_def] >> metis_tac[]) >>
  `!x sz. not_fresh_at cu x /\ ptr_covers G tn x a sz ==> ptr_covers G tn x u sz` by
    (simp[ptr_covers_def] >> metis_tac[]) >>
  fs[bodyFullShadowBodyInvTheory.ghost_inv_at_mods_def,stor_taint_ok_at_def,allocas_from_def] >>
  rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at cu p'` by metis_tac[local_ptrs_reserved_def] >>
      first_x_assum drule_all >> metis_tac[])
  >- (Cases_on `d` >> gvs[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME rb)` >> PairCases_on `rb` >>
      gvs[return_buf_ptr_def] >> metis_tac[]) >>
  first_assum ACCEPT_TAC
QED

Theorem blueprint_raw_finish_at_cut_mods:
  expr_type e = BaseT (BytesT (Dynamic k)) /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic k))) =
    SOME (BaseTV (BytesT (Dynamic k))) /\
  compile_expr ce (expr_type e) e ca = (vv,cm) /\
  compile_snapshot_vv ce (exprs_can_mutate ce later) vv cm = (saved,cs) /\
  unwrap_value ce saved cs = (raw_op,cu) /\
  compile_create_blueprint_args compile_expr ce T later [e] ca = ((data,len),cprep) /\
  expr_val_rel cx (BaseT (BytesT (Dynamic k))) (BytesV bs) raw_op u /\
  eval_operand target_op u = SOME aw /\
  (!x. target_op = Var x ==> not_fresh_at cu x) /\
  expr_sim_inv_mods mods ce cx env q /\
  local_ptrs_reserved ce cu /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cu x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cu x) /\
  return_buf_frame d ce cu u /\ alloca_history fnc u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  (!f i z. frag_reachable ctx fnc u f i z ==> dalloca_fmp_headroom i z) /\
  (!h. valid_horizon cx st0 h q.storage_trace ==>
    stmt_state_rel h ctx fnc ce cx q u /\
    immutable_frame_mods fnc ce cx q u /\ storage_well_formed_on cx q (FST h) /\
    ghost_inv_at_mods (DF h) lo d ce cx q G tn u) /\
  ~u.vs_halted /\ u.vs_current_bb = cu.cs_current_bb /\
  u.vs_inst_idx = LENGTH cu.cs_current_insts /\
  emit_op MLOAD [raw_op] cu = (len,cl) /\
  emit_op ADD [raw_op;Lit 32w] cl = (data,cprep) /\ fn_has_code cu cprep fnc /\
  b.vs_current_bb = cl.cs_current_bb /\ b.vs_inst_idx = LENGTH cl.cs_current_insts /\
  t.vs_current_bb = cprep.cs_current_bb /\ t.vs_inst_idx = LENGTH cprep.cs_current_insts /\
  create_expr_prefix cu cl explicit ctx fnc u ml b /\
  create_expr_prefix cl cprep explicit ctx fnc b ma t /\
  (!bb. MEM bb fnc.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  q.gas_obs = gas_explicit (ml ++ ma ++ rest) u.vs_gas_readings ++ tail ==>
  eval_operand len t = SOME (n2w (LENGTH bs)) /\
  (!x. len = Var x ==> not_fresh_at cprep x) /\
  eval_operand target_op t = SOME aw /\
  (!x. target_op = Var x ==> not_fresh_at cprep x) /\
  expr_sim_inv_mods mods ce cx env q /\
  local_ptrs_reserved ce cprep /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cprep x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cprep x) /\
  return_buf_frame d ce cprep t /\ alloca_history fnc t /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  (!f i z. frag_reachable ctx fnc t f i z ==> dalloca_fmp_headroom i z) /\
  (!h. valid_horizon cx st0 h q.storage_trace ==>
    stmt_state_rel h ctx fnc ce cx q t /\
    immutable_frame_mods fnc ce cx q t /\ storage_well_formed_on cx q (FST h) /\
    ghost_inv_at_mods (DF h) lo d ce cx q G tn t) /\
  ~t.vs_halted /\ t.vs_current_bb = cprep.cs_current_bb /\
  t.vs_inst_idx = LENGTH cprep.cs_current_insts /\
  q.gas_obs = gas_explicit rest t.vs_gas_readings ++ tail
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `cs_extends cu cl /\ cs_extends cl cprep` by
    metis_tac[exprSimAccountsTheory.emit_op_extends_next_var] >>
  drule_all fn_has_code_split >> strip_tac >>
  `run_inst_seq (emitted_insts cu cprep) u = OK (t with vs_inst_idx := u.vs_inst_idx) /\
   state_frame t = state_frame (u with vs_inst_idx := t.vs_inst_idx) /\
   cprep.cs_current_bb = cu.cs_current_bb /\
   cprep.cs_current_insts = cu.cs_current_insts ++ emitted_insts cu cprep /\
   EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts cu cprep) /\
   (!x. not_fresh_at cu x ==> lookup_var x t = lookup_var x u) /\
   (!x. len = Var x ==> not_fresh_at cprep x) /\ cu.cs_next_var <= cprep.cs_next_var /\
   ml = [] /\ ma = [] /\ t.vs_gas_readings = u.vs_gas_readings /\ ~b.vs_halted /\ ~t.vs_halted`
    by suspend "scalar_steps" >>
  `eval_operand len (t with vs_inst_idx := u.vs_inst_idx) = SOME (n2w (LENGTH bs))` by
    (irule create_blueprint_raw_arg_length_word >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >>
     qexists_tac `u` >> fs[]) >>
  `!h. valid_horizon cx st0 h q.storage_trace ==>
     stmt_state_rel h ctx fnc ce cx q u /\ immutable_frame_mods fnc ce cx q u /\
     ghost_inv_at_mods (DF h) lo d ce cx q G tn u` by
    (gen_tac >> disch_tac >> first_x_assum (drule_then strip_assume_tac) >> simp[]) >>
  drule_all blueprint_raw_load_add_frame_mods >> strip_tac >>
  drule_all createSizeBlueprintKeywordReplayTheory.blueprint_keyword_mono >> strip_tac >>
  `!f i z. frag_reachable ctx fnc b f i z ==> dalloca_fmp_headroom i z` by
    (qpat_assum `create_expr_prefix cu cl _ _ _ _ _ _`
       (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] blueprint_raw_reach_at_cut)) >>
     rpt (impl_tac >- first_assum ACCEPT_TAC) >> simp[]) >>
  `!f i z. frag_reachable ctx fnc t f i z ==> dalloca_fmp_headroom i z` by
    (qpat_assum `create_expr_prefix cl cprep _ _ _ _ _ _`
       (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO] blueprint_raw_reach_at_cut)) >>
     rpt (impl_tac >- first_assum ACCEPT_TAC) >> simp[]) >>
  `t.vs_labels = u.vs_labels` by
    (qpat_assum `state_frame t = _` mp_tac >> simp[state_frame_def]) >>
  `eval_operand target_op t = SOME aw` by
    (irule createSizeBlueprintKeywordReplayTheory.blueprint_eval_operand_frame >>
     qexistsl [`cu`,`u`] >> simp[]) >>
  fs[ghostPcTransportPtrTheory.eval_operand_inst_idx] >>
  metis_tac[freshWritesTheory.not_fresh_at_mono]
QED

Resume blueprint_raw_finish_at_cut_mods[scalar_steps]:
  drule_all (Q.INST [`opc` |-> `MLOAD`] blueprint_raw_scalar_step |>
             SIMP_RULE (srw_ss()) [is_terminator_def]) >>
  disch_then (qx_choosel_then [`lvar`,`ra`] (map_every assume_tac o CONJUNCTS)) >>
  drule_all (Q.INST [`opc` |-> `ADD`] blueprint_raw_scalar_step |>
             SIMP_RULE (srw_ss()) [is_terminator_def]) >>
  disch_then (qx_choosel_then [`pvar`,`rb`] (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `emit_op MLOAD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  `cl.cs_current_insts = cu.cs_current_insts ++ emitted_insts cu cl /\
   cprep.cs_current_insts = cl.cs_current_insts ++ emitted_insts cl cprep /\
   cprep.cs_current_bb = cu.cs_current_bb` by
    (drule_all emit_op_facts >> strip_tac >>
     qpat_assum `emit_op MLOAD _ _ = _` (mp_then Any strip_assume_tac emit_op_facts) >>
     fs[]) >>
  `emitted_insts cu cprep = emitted_insts cu cl ++ emitted_insts cl cprep` by
    (irule emitted_insts_append >> metis_tac[]) >>
  `~not_fresh_at cu lvar /\ ~not_fresh_at cl pvar` by metis_tac[emit_op_facts, operand_11] >>
  `!x. not_fresh_at cu x ==> x <> lvar /\ x <> pvar` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `not_fresh_at cprep lvar /\ cu.cs_next_var <= cprep.cs_next_var` by
    metis_tac[freshWritesTheory.not_fresh_at_mono, LESS_EQ_TRANS] >>
  gvs[stmtReasonMemoryTheory.step_mload_eq, stmtReasonMemoryTheory.step_add_eq,
      AllCaseEqs(), eval_operand_def] >>
  simp[run_inst_seq_def, stmtReasonMemoryTheory.step_mload_eq, stmtReasonMemoryTheory.step_add_eq,
       eval_operand_def, lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE,
       state_frame_def, mk_inst_def, APPEND_ASSOC] >>
  fs[update_var_def, venom_state_component_equality]
QED

Finalise blueprint_raw_finish_at_cut_mods

(* The raw call's own instruction supplies the request site before adoption. *)
Theory s1PrefixRawCall
Ancestors
  s1PrefixDefs s1PrefixProps bodyFullRawCallCall gasOutcomeFull exprLoweringProps
  loweringStateRelDefs fragGasOriginPtr fragExec contextCodegenRelProps
  ptrSafeRun memSafeRun bodyPtrDefs venomInst venomExecSemantics emitHelperProps
  vyperCallOutcomeProps vyperCallOutcome vyperState extCallOracle
  e2eRequestCutDefs vyperStorageFootprint gasSummary list rich_list arithmetic option
  s1PrefixPreds bodyFullRawCall bodyFullRawCallPrefix
  s1PrefixRawCallForcedArgs s1PrefixRawCallKeywordSuffix bodyFullRawCallKeywordSuffix
  exprSimRawCall s1PrefixInvalidTraceDomain vyperStorageTrace
  bodyFullRawCallPreparedEntry bodyFullRawCallGeneratedPrefix
Libs
  monadsyntax

Theorem raw_call_actual_call_prefix:
  emit_op (case call_ty of
    RegularCall => CALL | StaticCall => STATICCALL | DelegateCall => DELEGATECALL)
    (if call_ty = RegularCall then [gas_op;to_op;val_op;dp;dl;op;Lit (n2w cap)]
     else [gas_op;to_op;dp;dl;op;Lit (n2w cap)]) sa = (ok,sb) /\
  inst = mk_inst sa.cs_next_id (case call_ty of
    RegularCall => CALL | StaticCall => STATICCALL | DelegateCall => DELEGATECALL)
    (if call_ty = RegularCall then [gas_op;to_op;val_op;dp;dl;op;Lit (n2w cap)]
     else [gas_op;to_op;dp;dl;op;Lit (n2w cap)])
    [STRING #"%" (toString sa.cs_next_var)] /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  local_ptrs_rel func cenv es.scopes s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  eval_operand gas_op s = SOME gas /\ eval_operand to_op s = SOME aw /\
  eval_operand dp s = SOME ao /\ eval_operand dl s = SOME az /\
  eval_operand op s = SOME ro /\ eval_operand val_op s = SOME val_word /\
  w2w aw = target /\
  w2n (if call_ty = RegularCall then val_word else 0w) =
    (case value_opt of NONE => 0 | SOME n => n) /\
  (call_ty = StaticCall \/ cx.txn.is_static) = IS_NONE value_opt /\
  (!g. gas_cap = SOME g ==> g = w2n gas) /\
  (if call_ty = DelegateCall then take_delegate_outcome else take_call_outcome)
    gas_cap target (read_memory (w2n ao) (w2n az) s) value_opt es =
    (INL (rq,outcome),es1) /\ cap < dimword (:256) /\
  EVERY (\p. op_taint tn p = {}) inst.inst_operands /\
  (!j. w2n ao <= j /\ j < w2n ao + w2n az ==> j NOTIN tn.t_mem) /\
  (az <> 0w ==> ?p. dp = Var p /\ ptr_covers G tn p s (w2n az)) /\
  (cap <> 0 ==> ?p. op = Var p /\ ptr_covers G tn p s cap) /\
  (w2n az = 0 \/ w2n ao + w2n az <= s.vs_alloca_next) /\
  (cap = 0 \/ w2n ro + cap <= s.vs_alloca_next) /\
  (cap = 0 \/ lo <= w2n ro) /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
    regions_disjoint (w2n ro) cap b sz) /\
  (cenv.ce_is_ctor ==> !src name tv v off.
    (src = cenv.ce_module \/ IS_SOME (ALOOKUP cenv.ce_modules src)) /\
    FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables src imms) name = SOME (tv,v) ==>
    off + type_memory_size tv <= w2n ro \/ w2n ro + cap <= off) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s /\
     ghost_inv_at (DF H) lo d cenv cx es G tn s) ==>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
    ((if call_ty = DelegateCall then take_delegate_outcome else take_call_outcome)
      gas_cap target (read_memory (w2n ao) (w2n az) s) value_opt) (es,s,G,tn)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  PURE_REWRITE_TAC[gas_prefix_full_def] >> qexists_tac `[]` >> conj_tac
  >- (qexistsl_tac [`storage_trace_horizon es.storage_trace`,
         `func`, `PG`, `G`, `tn`, `s`] >>
      simp[storage_trace_domain_def, gas_origin_ptr_focus_nil]) >>
  map_every qx_gen_tac [`tail`, `result`, `ee`, `obs_pre`, `observed_rq`,
    `observed_outcome`, `sfx`, `H`] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  `ee.storage_trace = es1.storage_trace` by
    (qpat_x_assum `ee.storage_trace = _` kall_tac >>
     qpat_assum `(if _ then _ else _) _ _ _ _ (es with gas_obs := _) = _` mp_tac >>
     qpat_assum `(if _ then _ else _) _ _ _ _ es = _` mp_tac >>
     Cases_on `call_ty` >>
     simp[NoAsms] >> disch_tac >>
     simp[NoAsms, take_delegate_gas_obs, take_call_outcome_gas_obs] >>
     qpat_assum `_ es = (INL (rq,outcome),es1)`
       (fn th => PURE_REWRITE_TAC[th]) >>
     simp[NoAsms] >> strip_tac >>
     qpat_assum `es1 with gas_obs := tail = ee` (SUBST1_TAC o SYM) >>
     simp[NoAsms]) >>
  `es1.storage_trace = obs_pre ++ StorageOutcome observed_rq observed_outcome :: sfx` by
    metis_tac[] >>
  `obs_pre = es.storage_trace /\ observed_rq = rq /\ observed_outcome = outcome` by
    (qpat_x_assum `(if _ then _ else _) _ _ _ _ es = _` mp_tac >>
     Cases_on `call_ty` >> simp[NoAsms] >>
     PURE_REWRITE_TAC[take_call_outcome_def, take_delegate_outcome_def] >>
     disch_tac >> drule_all observed_take_at_start >> simp[]) >>
  qpat_x_assum `obs_pre = es.storage_trace` SUBST_ALL_TAC >>
  qpat_x_assum `observed_rq = rq` SUBST_ALL_TAC >>
  qpat_x_assum `observed_outcome = outcome` SUBST_ALL_TAC >>
  qpat_assum `valid_horizon cx st0 H es.storage_trace` (fn horizon =>
    qpat_assum `!H. valid_horizon _ _ H _ ==> _`
      (qspec_then `H` (strip_assume_tac o C MATCH_MP horizon))) >>
  drule_all raw_call_actual_call_full >>
  disch_then (qspecl_then [`explicit`, `PG`] (qx_choose_then `u` strip_assume_tac)) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `step_inst_base inst s = OK u` by
    (qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
     simp[run_inst_seq_def, AllCaseEqs()] >> metis_tac[]) >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (drule emit_op_same_blocks >> simp[same_blocks_def]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx = SOME inst` by
    (drule fn_has_code_same_block >>
     disch_then (qspec_then `[inst]` mp_tac) >> simp[] >>
     metis_tac[ADD_0, EL, prim_recTheory.LESS_0]) >>
  `MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL]` by
    (Cases_on `call_ty` >> fs[mk_inst_def]) >>
  `LENGTH sb.cs_current_insts = SUC s.vs_inst_idx` by simp[] >>
  qpat_assum `LENGTH sb.cs_current_insts = SUC s.vs_inst_idx` SUBST_ALL_TAC >>
  drule_all call_step_checks >> strip_tac >>
  `LENGTH s.vs_requests = recorded_outcomes_count es.storage_trace /\
    recorded_outcomes_count es.storage_trace < LENGTH u.vs_requests /\
    request_agree H cx.txn.target rq
      (EL (recorded_outcomes_count es.storage_trace) u.vs_requests) /\
    outcome = (if s.vs_outcomes = [] then failed_outcome rq else HD s.vs_outcomes)` by
    (qpat_x_assum `(if _ then _ else _) _ _ _ _ es = _` mp_tac >>
     Cases_on `call_ty` >> simp[NoAsms] >>
     PURE_REWRITE_TAC[take_call_outcome_def, take_delegate_outcome_def] >>
     disch_tac >> drule_all ordinary_request_index >> simp[]) >>
  `active_inst func inst s` by
    (irule lookup_instruction_active >> qexists_tac `bb` >> simp[]) >>
  `inst.inst_opcode <> INVOKE` by (Cases_on `call_ty` >> fs[mk_inst_def]) >>
  `stor_taint_ok_at (DF H) tn s` by
    (qpat_assum `ghost_inv_at (DF H) lo d cenv cx es G tn s` mp_tac >>
     simp[NoAsms, ghost_inv_at_def]) >>
  rewrite_tac[request_site_def] >>
  qexistsl_tac [`[]`, `func`, `PG`, `G`, `tn`, `s`, `inst`, `0`, `u`] >>
  fs[gas_origin_ptr_focus_nil, step_inst_non_invoke]
QED

Theorem raw_call_expr_vv_prefix:
  body_exprs_full_ok cx args /\
  body_exprs_prefix_ok cx args /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) args dflt) es ==>
  expr_vv_sim_prefix (DF,lo,dframe,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Call ann (RawCallTarget flags) args dflt) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule raw_call_pre_operands >> strip_tac >>
  drule raw_call_pre_flags >> strip_tac >> gvs[] >>
  rewrite_tac[expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule compile_expr_raw_call >> strip_tac >>
  drule raw_call_kwargs_types >> simp[] >> strip_tac >>
  drule_all raw_call_kwargs_word_args >> strip_tac >>
  drule_all raw_call_code_spans >> strip_tac >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (irule gas_prefix_full_invalid_trace_domain >>
      simp[evaluate_storage_trace_frame]) >>
  CONV_TAC (SIMP_CONV bool_ss [raw_call_eval_action]) >>
  ho_match_mp_tac (GEN_ALL raw_call_forced_args_prefix) >>
  qexistsl_tac [`tops`,`shadow_sa`,`h2`,`h1`,`shadow_func`,`sa`,`s2`,`s1`,
                `kws`,`flags`,`env`,`dframe`,`data`,`cenv`,`raw_call_return_type flags`,
                `addr`,`\H res ee gt r. T`,`\H res ee G tn t. T`] >>
  ASM_REWRITE_TAC [] >> BETA_TAC >> conj_tac
  >- (rpt gen_tac >> irule storage_trace_frame_bind_all >>
      simp[cj 6 evaluate_storage_trace_frame] >> gen_tac >>
      irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_checks] >>
      irule storage_trace_frame_bind_all >> simp[storage_trace_frame_lifts] >> gen_tac >>
      irule storage_trace_frame_bind_all >> simp[storage_trace_frame_lifts] >> gen_tac >>
      irule storage_trace_frame_bind_all >> simp[storage_trace_frame_lifts,storage_trace_frame_raw_call]) >>
  qx_genl_tac [`gsA`,`av`,`esA`,`tA`,`GA`,`tnA`,`gsD`,`bs`,`esD`,`tD`,`GD`,`tnD`] >>
  strip_tac >> conj_tac
  >- (ho_match_mp_tac (GEN_ALL raw_call_forced_data_kwargs_full_from_action) >>
      qexistsl_tac [`xs`,`tops`,`tA`,`shadow_func`,`sa`,`s5`,`s4`,`s3`,`s2`,
        `s1`,`s0`,`len`,`h5`,`h4`,`flags`,`esA`,`es`,`env`,`dp`,`dframe`,
        `data`,`d`,`cenv`,`n`,`bs`,`av`,`raw_call_return_type flags`,`addr`,`a`] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >- (gen_tac >> strip_tac >>
          qpat_assum `!H. valid_horizon _ _ H esD.storage_trace ==> _`
            (drule_then (map_every assume_tac o CONJUNCTS)) >> simp[])
      >- (gen_tac >> irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_checks] >>
          rpt (irule storage_trace_frame_bind_all >> simp[storage_trace_frame_lifts] >> gen_tac) >>
          irule storage_trace_frame_raw_call)
      >- simp[] >>
      qx_genl_tac [`b`,`x`,`l`,`p`,`base_addr`,`extent`,`t4`,`G4`,`tn4`,
                   `marks`,`kvs`,`esK`,`tk`,`GK`,`tnK`] >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      `esK with gas_obs := [] = esK` by
        simp[vyperStateTheory.evaluation_state_component_equality] >>
      `eval_exprs cx kws (esD with gas_obs := gasSummary$gas_explicit marks t4.vs_gas_readings) =
          (INL kvs,esK)` by
        (qpat_assum `esK with gas_obs := [] = esK` (fn eq =>
           qpat_assum `!tail. eval_exprs cx kws _ = _`
             (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [APPEND_NIL,eq])))) >>
      `valid_horizon cx st0 (storage_trace_horizon esD.storage_trace) esD.storage_trace` by
        (qpat_assum `storage_trace_domain cx st0 esD.storage_trace`
          (ACCEPT_TAC o REWRITE_RULE [storage_trace_domain_def])) >>
      qpat_assum `!H. valid_horizon _ _ H esD.storage_trace ==> _`
        (drule_then (map_every assume_tac o CONJUNCTS)) >>
      mp_tac (Q.INST [`ann` |-> `raw_call_return_type flags`, `cap` |-> `n`,
        `base'` |-> `base_addr`, `cap'` |-> `extent`,
        `gsK` |-> `gasSummary$gas_explicit marks t4.vs_gas_readings`]
        raw_call_kwargs_prepared_entry) >>
      (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        gen_tac >> strip_tac >>
        first_assum (fn th =>
          drule_then (map_every assume_tac o CONJUNCTS) th >>
          rpt conj_tac >> first_assum ACCEPT_TAC))) >>
      disch_then (qx_choose_then `t7` (qx_choose_then `G7` (qx_choose_then `tn7`
        (qx_choose_then `ng` (qx_choose_then `ob` (qx_choose_then `gw`
          (map_every assume_tac o CONJUNCTS))))))) >>
      irule raw_call_generated_prefix_full >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >- (irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_checks] >>
          rpt (irule storage_trace_frame_bind_all >> simp[storage_trace_frame_lifts] >> gen_tac) >>
          irule storage_trace_frame_raw_call) >>
      qexistsl_tac [`G7`,`ng`,`t7`,`tn7`] >>
      (conj_tac >- (gen_tac >> strip_tac >>
        qpat_assum `!H. valid_horizon _ _ H esK.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
          (drule_then (ACCEPT_TAC o CONJUNCT1)))) >>
      qabbrev_tac `gsK = gasSummary$gas_explicit marks t4.vs_gas_readings` >>
      suspend "prepared_action") >>
  mp_tac (BETA_RULE (Q.INST [`cap` |-> `n`, `Q` |-> `\H res ee G tn t. T`,
    `R` |-> `\H res ee gt r. T`] raw_call_forced_data_kwargs_prefix_from_action)) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
    >- (gen_tac >> strip_tac >>
        qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
          (drule_then (map_every assume_tac o CONJUNCTS)) >> first_assum ACCEPT_TAC)
    >- (gen_tac >> strip_tac >>
        qpat_assum `!H. valid_horizon _ _ H esD.storage_trace ==> _`
          (drule_then (map_every assume_tac o CONJUNCTS)) >>
        rpt conj_tac >> first_assum ACCEPT_TAC) >>
    qx_genl_tac [`gsK`,`kvs`,`esK`,`t4`,`tk`,`t7`,`G7`,`tn7`,`b`,`ob`,`gw`] >>
    disch_then (map_every assume_tac o CONJUNCTS) >>
    suspend "prepared_action")) >>
  disch_then ACCEPT_TAC
QED

Resume raw_call_expr_vv_prefix[prepared_action]:
  markerLib.RESUME_TAC >>
  mp_tac raw_call_prepared_action_full >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    gen_tac >> strip_tac >>
    qpat_assum `!H. valid_horizon _ _ H esK.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
      (drule_then (map_every assume_tac o CONJUNCTS)) >>
    rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (mp_then Any irule gasOutcomeFullTheory.gas_outcome_full_post_mono) >>
  simp[NoAsms]
QED

Finalise raw_call_expr_vv_prefix

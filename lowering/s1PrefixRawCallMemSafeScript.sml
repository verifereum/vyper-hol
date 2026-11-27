(* A raw call can read from a dynamic allocation: use instruction memory
   safety rather than a bound by the static allocation frontier. *)
Theory s1PrefixRawCallMemSafe
Ancestors
  s1PrefixDefs s1PrefixProps bodyFullRawCallCall gasOutcomeFull exprLoweringProps
  loweringStateRelDefs fragGasOriginPtr fragExec contextCodegenRelProps
  ptrSafeRun memSafeRun bodyPtrDefs
  venomInst venomExecSemantics emitHelperProps bodyPtrMakeArrayEmission
  vyperCallOutcomeProps vyperCallOutcome vyperState extCallOracle
  e2eRequestCutDefs vyperStorageFootprint gasSummary list arithmetic option

Theorem raw_call_actual_call_mem_safe_prefix:
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
  mem_safe_step 0 ctx inst s /\
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
    (qpat_assum `(if _ then _ else _) _ _ _ _ (es with gas_obs := _) = _` mp_tac >>
     qpat_assum `(if _ then _ else _) _ _ _ _ es = _` mp_tac >>
     Cases_on `call_ty` >>
     simp[NoAsms] >> disch_tac >>
     simp[NoAsms, take_delegate_gas_obs, take_call_outcome_gas_obs] >>
     qpat_assum `_ es = (INL (rq,outcome),es1)`
       (fn th => PURE_REWRITE_TAC[th]) >>
     simp[] >> strip_tac >> gvs[]) >>
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
  drule_all raw_call_actual_call_mem_safe_full >>
  disch_then (qspecl_then [`explicit`, `PG`] (qx_choose_then `u` strip_assume_tac)) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `step_inst_base inst s = OK u` by
    (qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
     simp[run_inst_seq_def, AllCaseEqs()] >> metis_tac[]) >>
  `LENGTH sb.cs_current_insts = SUC s.vs_inst_idx /\
    ?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
         get_instruction bb s.vs_inst_idx = SOME inst` by
    (drule_all emit_op_fetch_boundary >> simp[] >> metis_tac[]) >>
  `MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL]` by
    (Cases_on `call_ty` >> fs[mk_inst_def]) >>
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
  `inst.inst_opcode <> INVOKE` by fs[] >>
  `stor_taint_ok_at (DF H) tn s` by
    (qpat_assum `ghost_inv_at (DF H) lo d cenv cx es G tn s` mp_tac >>
     simp[NoAsms, ghost_inv_at_def]) >>
  rewrite_tac[request_site_def] >>
  qexistsl_tac [`[]`, `func`, `PG`, `G`, `tn`, `s`, `inst`, `0`, `u`] >>
  fs[gas_origin_ptr_focus_nil, step_inst_non_invoke]
QED

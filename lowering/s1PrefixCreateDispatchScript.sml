(* The request is certified at the prepared CREATE instruction, before adoption. *)
Theory s1PrefixCreateDispatch
Ancestors
  s1PrefixDefs bodyFullCreateHeld stateRelProj vyperStorageFootprint gasSummary
  loweringStateRelDefs fragGasOriginPtr bodyPtrDefs gasOutcomeFull
  builtinCreate venomMemDefs ptrDiscipline contextCodegenRel vyperCallOutcome
  vyperInterpreter vyperCreate vyperState extCallOracle
  venomExecSemantics venomInst venomState memSafeRun ptrSafeRun list
  contextCodegenRelProps rich_list

Theorem create_observed_outcome[local]:
  pre ++ StorageOutcome rq oc :: sfx =
    trace ++ [StorageOutcome rq0 oc0; StorageBackend acc trans] /\
  LENGTH trace <= LENGTH pre ==>
  pre = trace /\ rq = rq0 /\ oc = oc0
Proof
  rewrite_tac[APPEND_EQ_APPEND] >> strip_tac >>
  rename1 `LENGTH trace <= LENGTH pre` >>
  Cases_on `l` >> gvs[] >>
  TRY (decide_tac >> NO_TAC) >>
  rename1 `[StorageBackend _ _] = rest ++ [StorageOutcome _ _] ++ _` >>
  Cases_on `rest` >> gvs[]
QED

Theorem create_edge_checks[local]:
  gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) marks (r,G',tn') /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  (inst.inst_opcode = CREATE \/ inst.inst_opcode = CREATE2) ==>
  ptr_inst_ok D lo 0 ctx func G tn inst s /\ mem_safe_step 0 ctx inst s
Proof
  strip_tac >>
  drule gas_origin_ptr_edge_common_fuel >> strip_tac >> gvs[] >>
  drule ptr_safe_step_inst_ok >> strip_tac >>
  gvs[ptr_inst_ok_def,step_inst_non_invoke,mem_safe_step_non_invoke] >>
  drule_all revert_forward_at_opcode >> simp[]
QED

Theorem create_dispatch_prefix:
  compile_create_dispatch codep len amount sop rof sm = (result,sb) /\
  fn_has_code sm sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
  outcomes_accounts_typed ee.outcomes /\
  eval_operand codep s = SOME pv /\ eval_operand len s = SOME sz /\
  (sz <> 0w ==> ?p. codep = Var p /\ ptr_covers G tn p s (w2n sz)) /\
  (sz <> 0w ==> w2n pv + w2n sz <= s.vs_alloca_next \/
    (ctx_has_dalloca ctx /\ w2n s.vs_initial_fmp <= w2n pv /\
     w2n pv + w2n sz <= w2n s.vs_fmp)) /\
  read_memory (w2n pv) (w2n sz) s = initcode /\
  (!i. w2n pv <= i /\ i < w2n pv + w2n sz ==> i NOTIN tn.t_mem) /\
  op_taint tn codep = {} /\ op_taint tn len = {} /\
  eval_operand amount s = SOME aw /\ op_taint tn amount = {} /\
  (case sop of NONE => sw = NONE | SOME op =>
     ?w. sw = SOME w /\ eval_operand op s = SOME w /\ op_taint tn op = {}) /\
  (!tail. source (ee with gas_obs := tail) =
    if w2n sz > 2 * max_code_size then
      (INR (Error (RuntimeError "create initcode too large")),ee with gas_obs := tail)
    else
      bind (ignore_bind (check_not_static cx)
        (create_oracle_result sw (w2n aw) initcode rof))
        (read_result cx) (ee with gas_obs := tail)) ==>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0 source (ee,s,G,tn)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  PURE_REWRITE_TAC[gas_prefix_full_def] >> qexists_tac `[]` >> conj_tac
  >- (qexistsl_tac [`storage_trace_horizon ee.storage_trace`, `func`, `PG`, `G`, `tn`, `s`] >>
      fs[storage_trace_domain_def,gas_origin_ptr_focus_nil]) >>
  simp[] >>
  map_every qx_gen_tac [`tail`,`res`,`efinal`,`obs_pre`,`observed_rq`,`observed_oc`,`sfx`,`H`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace`
    by fs[storage_trace_domain_def] >>
  `ee.outcomes = SOME s.vs_outcomes /\ s.vs_call_ctx.cc_static = cx.txn.is_static /\
   LENGTH s.vs_requests = LENGTH ee.requests` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
     drule stmt_state_rel_state_rel >>
     simp[state_rel_def,call_ctx_rel_def] >> metis_tac[LIST_REL_LENGTH]) >>
  Cases_on `w2n sz > 2 * max_code_size \/ cx.txn.is_static \/ s.vs_outcomes = []`
  >- suspend "preconsume" >>
  `w2n sz <= 2 * max_code_size /\ ~cx.txn.is_static /\ s.vs_outcomes <> []` by
    (gvs[] >> decide_tac) >>
  drule_all create_dispatch_code >> strip_tac >>
  qabbrev_tac `inst = mk_inst sm.cs_next_id (if IS_SOME sop then CREATE2 else CREATE)
    ([amount;codep;len] ++ (case sop of NONE => [] | SOME p => [p])) [out]` >>
  `inst.inst_outputs = [out] /\ EVERY (\op. op_taint tn op = {}) inst.inst_operands` by
    (Cases_on `sop` >> gvs[Abbr `inst`,mk_inst_def]) >>
  `step_inst_base inst s = exec_create inst s aw pv sz sw` by
    (Cases_on `sop` >> gvs[Abbr `inst`,mk_inst_def,step_inst_base_def,eval_operands_def]) >>
  Cases_on `s.vs_outcomes` >> gns[] >>
  suspend "consume"
QED

Resume create_dispatch_prefix[preconsume]:
  `efinal.storage_trace = ee.storage_trace` by
    (qpat_assum `!tail. source _ = _` (qspec_then `tail` assume_tac) >>
     Cases_on `w2n sz > 2 * max_code_size` >> gvs[] >>
     Cases_on `cx.txn.is_static` >> gvs[bind_def,ignore_bind_def,
       create_oracle_result_def,take_create_outcome_exhausted]) >>
  `LENGTH ee.storage_trace = LENGTH obs_pre + SUC (LENGTH sfx)` by fs[] >>
  decide_tac
QED

Resume create_dispatch_prefix[consume]:
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee s /\ storage_well_formed_on cx ee (FST H)` by
    (gen_tac >> disch_tac >> first_assum (drule_then strip_assume_tac) >> simp[]) >>
  `outcomes_accounts_typed ee.outcomes` by simp[] >>
  drule_all (PURE_REWRITE_RULE [REFL_CLAUSE,AND_CLAUSES]
    (Q.INST [`value` |-> `w2n w`] create_paired_adoption)) >>
  disch_then (qspecl_then [`aw`,`sw`,`rof`]
    (qx_choose_then `adopted_src` (qx_choose_then `adopted`
      (qx_choose_then `a` (qx_choose_then `rq` (qx_choose_then `rq'`
        (map_every assume_tac o CONJUNCTS))))))) >>
  rename1 `s.vs_outcomes = oc::rest` >>
  `efinal.storage_trace = adopted_src.storage_trace` by
    (qpat_x_assum `efinal.storage_trace = _` kall_tac >>
     qpat_x_assum `adopted_src.storage_trace = _` kall_tac >>
     qpat_x_assum `a = if _ then _ else _` kall_tac >>
     qpat_x_assum `monad_bind _ _ _ = (res,efinal)` mp_tac >>
     simp[bind_def,ignore_bind_def] >>
     qpat_assum `!tail. create_oracle_result _ _ _ _ _ = _`
       (fn th => rewrite_tac[th]) >>
     IF_CASES_TAC >> simp[read_result_def,return_def] >>
     disch_then (SUBST1_TAC o SYM o CONJUNCT2) >> simp[]) >>
  suspend "site"
QED

Resume create_dispatch_prefix[site]:
  `obs_pre = ee.storage_trace /\ observed_rq = rq /\ observed_oc = oc` by
    (irule create_observed_outcome >> simp[] >> metis_tac[]) >>
  qpat_x_assum `obs_pre = _` SUBST_ALL_TAC >>
  qpat_x_assum `observed_rq = _` SUBST_ALL_TAC >>
  qpat_x_assum `observed_oc = _` SUBST_ALL_TAC >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ ee s /\ _ /\ _`
    (drule_then strip_assume_tac) >>
  `allocas_from lo s /\ stor_taint_ok_at (DF H) tn s` by fs[ghost_inv_at_def] >>
  `((inst.inst_opcode = CREATE /\ inst.inst_operands = [amount;codep;len]) \/
    (inst.inst_opcode = CREATE2 /\ inst.inst_operands = [amount;codep;len;THE sop] /\
       ?w. eval_operand (THE sop) s = SOME w))` by
    (Cases_on `sop` >> gvs[Abbr `inst`,mk_inst_def]) >>
  qabbrev_tac `raw = update_var out (w2w a) adopted` >>
  `step_inst_base inst s = OK raw` by simp[Abbr `raw`] >>
  `gas_origin_ptr_edge (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (raw with vs_inst_idx := SUC s.vs_inst_idx),
       step_prov PG G inst raw, step_taint inst s raw tn)` by
    (irule create_origin_edge >> simp[] >>
     qexistsl_tac [`amount`,`bb`,`codep`,`len`,`pv`,`THE sop`,`sz`,`aw`] >> simp[]) >>
  `active_inst func inst s` by (irule lookup_instruction_active >> qexists_tac `bb` >> simp[]) >>
  `inst.inst_opcode = CREATE \/ inst.inst_opcode = CREATE2` by
    (Cases_on `sop` >> simp[Abbr `inst`,mk_inst_def]) >>
  `ptr_inst_ok (DF H) lo 0 ctx func G tn inst s /\ mem_safe_step 0 ctx inst s` by
    (irule create_edge_checks >>
     qpat_assum `gas_origin_ptr_edge _ _ _ _` (irule_at Any) >>
     qexists_tac `bb` >> simp[]) >>
  `inst.inst_opcode <> INVOKE` by
    (Cases_on `sop` >> simp[Abbr `inst`,mk_inst_def]) >>
  `raw.vs_requests = s.vs_requests ++ [rq']` by simp[Abbr `raw`,update_var_def] >>
  `EL (recorded_outcomes_count ee.storage_trace) raw.vs_requests = rq'` by
    (qpat_assum `LENGTH s.vs_requests = recorded_outcomes_count _`
       (fn th => PURE_REWRITE_TAC[GSYM th]) >>
     qpat_assum `raw.vs_requests = _` (fn th => PURE_REWRITE_TAC[th]) >>
     simp[NoAsms,EL_LENGTH_APPEND_0]) >>
  `request_agree H cx.txn.target rq rq'` by
    (qpat_assum `!h. valid_horizon _ _ h ee.storage_trace ==> request_agree _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >> simp[]) >>
  rewrite_tac[request_site_def] >>
  qexistsl_tac [`[]`, `func`, `PG`, `G`, `tn`, `s`, `inst`, `0`, `raw`] >>
  qpat_assum `EL _ raw.vs_requests = _` (fn th => PURE_REWRITE_TAC[th]) >>
  simp[gas_origin_ptr_focus_nil,step_inst_non_invoke]
QED

Finalise create_dispatch_prefix

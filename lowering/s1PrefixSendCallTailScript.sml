(* The prepared Send CALL is the request site, even when its ASSERT fails. *)
Theory s1PrefixSendCallTail
Ancestors
  s1PrefixDefs s1PrefixProps gasOutcomeFull exprSendPtr extCallOracleStep
  contextCodegenRelProps stateRelProj bodyPtrDefs fragGasOriginPtr
  vyperStorageTrace vyperStorageFootprint vyperCallOutcomeProps vyperCallOutcome vyperInterpreter
  loweringStateRelDefs venomCallOracleDefs venomExecSemantics venomInst
  venomState venomMemProps memSafeRun contextCodegenRel codegenRel unitTransformDefs extCallOracle
  vyperState list words

Theorem send_trace_event_at_start[local]:
  (trace ++ [StorageOutcome r o'] = (pre ++ [StorageOutcome rq outcome]) ++ sfx \/
   trace ++ [StorageOutcome r o'; StorageBackend acc ts] =
     (pre ++ [StorageOutcome rq outcome]) ++ sfx) /\
  LENGTH trace <= LENGTH pre ==>
  pre = trace /\ rq = r /\ outcome = o'
Proof
  PURE_REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >>
  simp[APPEND_EQ_APPEND] >> rpt strip_tac >> gvs[] >>
  Cases_on `l` >> gvs[] >> rename1 `_ = _ ++ l` >> Cases_on `l` >> gvs[] >>
  qpat_x_assum `_ = _ ++ _` (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]
QED

Theorem send_observed_outcome[local]:
  LENGTH gas_vs = (if has_gas then 1 else 0) /\
  dest_AddressV to_v = SOME target /\ dest_NumV amount_v = SOME amount /\
  gas = (case OPTION_BIND (ext_call_kwarg EKGas [EKGas] gas_vs) dest_NumV of
           NONE => 0 | SOME g => g) /\
  st.outcomes = SOME os /\
  eval_send cx has_gas (to_v::amount_v::gas_vs) st = (res,ee) /\
  ee.storage_trace = pre ++ StorageOutcome rq outcome :: sfx /\
  LENGTH st.storage_trace <= LENGTH pre ==>
  pre = st.storage_trace /\ os <> [] /\ (cx.txn.is_static ==> amount = 0) /\
  rq = (call_outcome_request target []
         (if cx.txn.is_static then NONE else SOME amount) st with cr_gas := SOME gas) /\
  outcome = FST (take_outcome rq os)
Proof
  strip_tac >>
  Cases_on `cx.txn.is_static /\ amount <> 0`
  >- (fs[eval_send_def, type_check_def, bind_def,
         ignore_bind_def, frame_call_value_def, check_def, assert_def, vyperStateTheory.return_def] >> gvs[]) >>
  `frame_call_value cx (SOME amount) st =
     (INL (if cx.txn.is_static then NONE else SOME amount),st)` by
    (Cases_on `cx.txn.is_static` >>
     fs[frame_call_value_def, check_def, assert_def, vyperStateTheory.return_def, ignore_bind_def, bind_def]) >>
  qpat_assum `gas = _` (fn th => assume_tac (SYM th)) >>
  qpat_x_assum `gas = _` kall_tac >>
  qpat_x_assum `eval_send _ _ _ _ = _` mp_tac >>
  simp[eval_send_def, type_check_def, bind_def,
       ignore_bind_def, assert_def, vyperStateTheory.return_def] >>
  qmatch_goalsub_abbrev_tac `take_call_outcome (SOME gas) target [] value_opt st` >>
  qabbrev_tac `r = call_outcome_request target [] value_opt st with cr_gas := SOME gas` >>
  `take_call_outcome (SOME gas) target [] value_opt st = take_request_outcome r st` by
    simp[take_call_outcome_def, Abbr `r`] >>
  simp[Once take_request_outcome_def] >> Cases_on `os` >> simp[]
  >- (rpt strip_tac >> gvs[]) >>
  pairarg_tac >> rename1 `take_outcome r (_::_) = (o',rest)` >> simp[] >>
  Cases_on `o'.co_success` >> Cases_on `r.cr_static` >>
  Cases_on `accounts_runtime_well_typed o'.co_accounts` >>
  simp[check_def, assert_def, vyperStateTheory.return_def, bind_def,
       ignore_bind_def, adopt_call_outcome_equation] >>
  strip_tac >> qpat_x_assum `_ = ee` (SUBST_ALL_TAC o SYM) >>
  fs[] >>
  `pre = st.storage_trace /\ rq = r /\ outcome = o'` by
    metis_tac[send_trace_event_at_start] >> simp[] >> metis_tac[]
QED

Theorem send_call_tail_prefix:
  emit_op CALL [gas_op;addr_op;val_op;Lit 0w;Lit 0w;Lit 0w;Lit 0w] sm = (success,s3) /\
  emit_void ASSERT [success] s3 = (u,sb) /\ fn_has_code sm sb func /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  eval_operand gas_op t = SOME gw /\
  w2n gw = (case OPTION_BIND (ext_call_kwarg EKGas [EKGas] gas_vs) dest_NumV of
               NONE => 0 | SOME g => g) /\
  eval_operand addr_op t = SOME aw /\ dest_AddressV to_v = SOME (w2w aw) /\
  eval_operand val_op t = SOME vw /\ dest_NumV amount_v = SOME (w2n vw) /\
  LENGTH gas_vs = (if has_gas then 1 else 0) /\
  op_taint tn gas_op = {} /\ op_taint tn addr_op = {} /\ op_taint tn val_op = {} /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ allocas_from lo t /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid t /\ ghost_inv_at (DF H) lo d cenv cx mid G tn t) ==>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
    (eval_send cx has_gas (to_v::amount_v::gas_vs)) (mid,t,G,tn)
Proof
  strip_tac >> drule_all call_assert_code_lookup >> strip_tac >>
  PURE_REWRITE_TAC[gas_prefix_full_def] >> qexists_tac `[]` >> conj_tac
  >- (qexistsl_tac [`storage_trace_horizon mid.storage_trace`, `func`, `PG`, `G`, `tn`, `t`] >>
      simp[storage_trace_domain_def, gas_origin_ptr_focus_nil]) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (drule_at (Pat `_ _ = (_,_)`) storage_trace_frame_prefix >>
     simp[storage_trace_frame_send] >> strip_tac >>
     `TAKE (LENGTH mid.storage_trace) obs_pre = mid.storage_trace` by
       (qpat_x_assum `_ = mid.storage_trace ++ observations`
          (mp_tac o Q.AP_TERM `TAKE (LENGTH mid.storage_trace)`) >>
        PURE_REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >>
        simp[TAKE_APPEND1, rich_listTheory.TAKE_LENGTH_APPEND]) >>
     `mid.storage_trace ++ DROP (LENGTH mid.storage_trace) obs_pre = obs_pre` by
       (pop_assum (SUBST1_TAC o SYM) >> simp[TAKE_DROP]) >>
     metis_tac[valid_horizon_append]) >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` drule >> strip_tac >>
  drule stmt_state_rel_state_rel >> strip_tac >>
  `mid.outcomes = SOME t.vs_outcomes /\ accounts_rel H cx mid t /\
   t.vs_call_ctx.cc_static = cx.txn.is_static /\ LENGTH t.vs_requests = LENGTH mid.requests` by
    (fs[state_rel_def, call_ctx_rel_def] >> metis_tac[LIST_REL_LENGTH]) >>
  `stor_taint_ok_at (DF H) tn t` by fs[ghost_inv_at_def] >>
  `obs_pre = (mid with gas_obs := tail).storage_trace /\ t.vs_outcomes <> [] /\
   (cx.txn.is_static ==> w2n vw = 0) /\
   rq = (call_outcome_request (w2w aw) []
     (if cx.txn.is_static then NONE else SOME (w2n vw)) (mid with gas_obs := tail)
       with cr_gas := SOME (w2n gw)) /\
   outcome = FST (take_outcome rq t.vs_outcomes)` by
    (irule send_observed_outcome >>
     conj_tac >- simp[] >> conj_tac >- simp[] >>
     map_every qexists_tac [`amount_v`,`ee`,`gas_vs`,`has_gas`,`res`,`sfx`,`to_v`] >>
     simp[APPEND_ASSOC]) >>
  `obs_pre = mid.storage_trace` by simp[] >>
  qpat_x_assum `obs_pre = (mid with gas_obs := tail).storage_trace` kall_tac >>
  pop_assum SUBST_ALL_TAC >>
  qabbrev_tac `rq' = venom_call_request t aw vw 0w 0w cx.txn.is_static
                             with cr_gas := SOME (w2n gw)` >>
  `request_agree H cx.txn.target rq rq'` by
    (qpat_x_assum `rq = _` mp_tac >>
     `call_outcome_request (w2w aw) []
        (if cx.txn.is_static then NONE else SOME (w2n vw)) (mid with gas_obs := tail) =
      call_outcome_request (w2w aw) []
        (if cx.txn.is_static then NONE else SOME (w2n vw)) mid` by
       simp[call_outcome_request_def] >>
     qpat_x_assum `call_outcome_request _ _ _ _ = _`
       (fn th => disch_then (SUBST1_TAC o PURE_REWRITE_RULE[th])) >>
     simp[NoAsms, Abbr `rq'`] >>
     `read_memory (w2n (0w:bytes32)) (w2n (0w:bytes32)) t = []` by simp[read_memory_def] >>
     pop_assum (fn th => PURE_REWRITE_TAC[GSYM th]) >>
     irule venom_call_request_source >> Cases_on `cx.txn.is_static` >> simp[]) >>
  `~computed_precompile rq'` by
    (fs[request_agree_def, computed_precompile_def] >>
     qpat_x_assum `_ = rq'` (SUBST1_TAC o SYM) >> simp[]) >>
  `outcome = HD t.vs_outcomes` by
    (Cases_on `t.vs_outcomes` >> gvs[take_outcome_ordinary]) >>
  qmatch_asmsub_abbrev_tac `get_instruction bb (LENGTH sm.cs_current_insts) = SOME inst` >>
  `active_inst func inst t` by
    (irule lookup_instruction_active >> qexists_tac `bb` >> simp[]) >>
  `inst.inst_opcode = CALL /\
   inst.inst_operands = [gas_op;addr_op;val_op;Lit 0w;Lit 0w;Lit 0w;Lit 0w] /\
   inst.inst_outputs = [out]` by simp[Abbr `inst`, mk_inst_def] >>
  `ptr_inst_ok (DF H) lo 0 ctx func G tn inst t` by
    (irule ptr_inst_ok_send_call_at >> metis_tac[]) >>
  `mem_safe_step 0 ctx inst t` by
    simp[mem_safe_step_non_invoke, inst_mem_below_frontier_def, inst_dload_in_section_def,
         source_memory_read_ranges_def, source_memory_write_ranges_def,
         memory_range_of_operands_def, eval_operand_def] >>
  `?z. step_inst_base inst t = OK z /\ z.vs_requests = t.vs_requests ++ [rq']` by
    (qpat_assum `eval_operand gas_op t = _` mp_tac >>
     simp[step_inst_base_opcode_eqs, eval_operand_def, exec_ext_call_def, Abbr `rq'`,
          update_var_def, record_request_def] >>
     Cases_on `cx.txn.is_static` >> gvs[w2n_eq_0]) >>
  qpat_x_assum `w2n gw = _` kall_tac >>
  qpat_x_assum `rq = _` kall_tac >>
  qpat_x_assum `outcome = FST _` kall_tac >>
  PURE_REWRITE_TAC[request_site_def] >>
  qexistsl_tac [`[]`,`func`,`PG`,`G`,`tn`,`t`,`inst`,`0`,`z`] >>
  fs[gas_origin_ptr_focus_nil, step_inst_non_invoke, EL_APPEND_EQN]
QED

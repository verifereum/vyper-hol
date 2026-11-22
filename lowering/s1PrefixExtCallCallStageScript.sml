(* Request-prefix companion to bodyFullExtCallCallStage. *)
Theory s1PrefixExtCallCallStage
Ancestors
  s1PrefixPreds bodyFullExtCallCallStage s1PrefixDefs s1PrefixProps
  bodyFullExtCallPrecheck bodyFullExtCallDispatch bodyFullRawCallCallOrigin
  fragGasOriginPtr fragExec vyperStorageFootprint vyperCallOutcome
  vyperCallOutcomeProps vyperInterpreter vyperState bodyPtrDefs
  exprSimExtCallCase extCallOracleStep venomInst venomState venomExecSemantics
  contextCodegenRelProps gasSummary gasEvents stateRelProj abiCallerAllocation
  instMemFrontier gasOutcomeFull exprSafeOperand list rich_list words
  bodyFullHashKeccakFixed ptrDiscipline

Theorem extcall_call_stage_prefix:
  comp_ignore_bind
    (if ret_type = NoneT /\ ~skip then compile_extcodesize_check addr
     else comp_return ())
    (comp_bind
      (if stat then emit_op STATICCALL [gas;addr;off;len;buf;Lit (n2w cap)]
       else emit_op CALL [gas;addr;value;off;len;buf;Lit (n2w cap)])
      (\success. comp_bind (fresh_label "extcall_fail") (\fail_lbl.
       comp_bind (fresh_label "extcall_cont") (\cont_lbl.
       comp_ignore_bind (emit_inst JNZ [success;Label cont_lbl;Label fail_lbl] [])
       (comp_ignore_bind (new_block fail_lbl)
       (comp_bind (emit_op RETURNDATASIZE []) (\rds.
       comp_bind (compile_alloc_buffer 0) (\fail_buf.
       comp_ignore_bind
         (emit_void RETURNDATACOPY [fail_buf.buf_operand;Lit 0w;rds])
       (comp_ignore_bind (emit_inst REVERT [fail_buf.buf_operand;rds] [])
         (new_block cont_lbl)))))))))) sp = (u,sr) /\
  fn_has_code sp sr func /\ fn_inst_ids_distinct func /\
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr value gas buf off len cap target value_opt calldata has_default
    default_op default_ty default_opt ee s /\
  (IS_SOME default_opt /\ ~is_word_type default_ty ==>
    ?w aid tv. eval_operand default_op s = SOME w /\
      evaluate_type (get_tenv cx) default_ty = SOME tv /\
      FLOOKUP s.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
      aid < sp.cs_next_id) /\
  alloca_history func s /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
  (!gw g. eval_operand gas s = SOME gw /\ OPTION_BIND source_gas dest_NumV = SOME g ==>
          g = w2n gw) /\
  EVERY (\p. op_taint tn p = {}) [addr;value;gas;buf;off;len;default_op] /\
  (!ao az. eval_operand off s = SOME ao /\ eval_operand len s = SOME az ==>
    (az <> 0w ==> (?p. off = Var p /\ ptr_covers G tn p s (w2n az)) /\
                  w2n ao + w2n az <= s.vs_alloca_next) /\
    (!j. w2n ao <= j /\ j < w2n ao + w2n az ==> j NOTIN tn.t_mem)) /\
  (cap <> 0 ==> ?p. buf = Var p /\ ptr_covers G tn p s cap) /\
  (!dv. default_opt = SOME dv /\ ~is_word_type default_ty ==>
    ptr_mem_ok cx default_ty dv default_op G tn s /\
    (type_memory_bytes cenv default_ty <> 0 ==>
      (?p. default_op = Var p /\ ptr_covers G tn p s (type_memory_bytes cenv default_ty)) /\
      (!w. eval_operand default_op s = SOME w ==>
          w2n w + type_memory_bytes cenv default_ty <= s.vs_alloca_next))) ==>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
    (do accounts <- get_accounts;
        check (ext_call_precheck_ok skip ret_type target accounts)
          "ExtCall target has no code";
        framed <- frame_call_value cx value_opt;
        eval_ext_call_effects cx target calldata framed source_gas accounts
     od) (ee,s,G,tn)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule extcall_call_layout >> strip_tac >>
  drule_all extcall_call_intervals >> strip_tac >>
  `~s.vs_halted /\ op_taint tn addr = {} /\
   EVERY (safe_operand sp) [addr;value;gas;buf;off;len;default_op] /\
   ?gw. eval_operand gas s = SOME gw` by
    (qhdtm_assum `extcall_request_ready`
       (strip_assume_tac o REWRITE_RULE [extcall_request_ready_def]) >>
     fs[EVERY_DEF] >> Cases_on `eval_operand gas s` >> gs[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> stor_taint_ok_at (DF H) tn s` by
    (rpt strip_tac >> qpat_assum `!H. _ ==> ghost_inv_at _ _ _ _ _ _ _ _ _`
       (drule_then (ACCEPT_TAC o cj 4 o REWRITE_RULE [ghost_inv_at_def]))) >>
  drule_all extcall_precheck_to_call >>
  disch_then (qspecl_then [`explicit`,`d`,`PG`] mp_tac) >>
  ASM_SIMP_TAC bool_ss [] >> strip_tac >>
  PURE_REWRITE_TAC[gas_prefix_full_def] >> qexists_tac `[]` >>
  conj_tac
  >- (qexistsl_tac [`storage_trace_horizon ee.storage_trace`,`func`,`PG`,`G`,`tn`,`s`] >>
      simp[storage_trace_domain_def,gas_origin_ptr_focus_nil]) >>
  simp[gas_explicit_def] >>
  map_every qx_gen_tac [`tail`,`res`,`ef`,`obs_pre`,`observed_rq`,`observed_oc`,`sfx`,`H`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  reverse (Cases_on `ext_call_precheck_ok skip ret_type target ee.accounts`)
  >- (qpat_x_assum `_ (ee with gas_obs := tail) = (res,ef)` mp_tac >>
      simp[get_accounts_def,vyperStateTheory.bind_def,vyperStateTheory.ignore_bind_def,
           check_def,assert_def,vyperStateTheory.return_def,raise_def] >>
      disch_then (strip_assume_tac) >>
      qpat_x_assum `ee with gas_obs := tail = ef` (SUBST_ALL_TAC o SYM) >>
      qpat_x_assum `_.storage_trace = _` (mp_tac o Q.AP_TERM `LENGTH`) >> simp[] >> decide_tac) >>
  qpat_assum `ext_call_precheck_ok _ _ _ _` (fn h =>
    qpat_x_assum `if ext_call_precheck_ok _ _ _ _ then _ else _`
      (strip_assume_tac o SIMP_RULE bool_ss [h])) >>
  qpat_x_assum `r = OK t` SUBST_ALL_TAC >>
  drule_all extcall_precheck_dispatch_operands >> strip_tac >>
  `bind (frame_call_value cx value_opt)
     (\framed. eval_ext_call_effects cx target calldata framed source_gas ee.accounts)
     (ee with gas_obs := tail) = (res,ef)` by
    (qpat_x_assum `_ (ee with gas_obs := tail) = (res,ef)` mp_tac >>
     simp[get_accounts_def,vyperStateTheory.bind_def,vyperStateTheory.ignore_bind_def,
          check_def,assert_def,vyperStateTheory.return_def]) >>
  qabbrev_tac `inst = mk_inst s1.cs_next_id (if stat then STATICCALL else CALL)
    (if stat then [gas;addr;off;len;buf;Lit (n2w cap)]
     else [gas;addr;value;off;len;buf;Lit (n2w cap)]) [out]` >>
  qpat_assum `Abbrev (inst = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  `EVERY (\p. op_taint tn1 p = {}) [addr;value;gas;buf;off;len]` by
    (qpat_assum `EVERY (\p. op_taint tn1 p = {}) [addr;value;gas;buf;off;len;default_op]`
      mp_tac >> simp[NoAsms,EVERY_DEF]) >>
  suspend "source_trace"
QED

(* Expose the first outcome, allowing the optional backend event after it. *)
Resume extcall_call_stage_prefix[source_trace]:
  drule_all extcall_fetched_select >>
  disch_then (qspecl_then [`source_gas`,`explicit`,`PG`] strip_assume_tac)
  >- (`ef = ee with gas_obs := tail` by
        (qpat_assum `!tail. bind (frame_call_value _ _) _ _ = _`
           (qspec_then `tail` mp_tac) >> simp[]) >>
      qpat_x_assum `ef = _` SUBST_ALL_TAC >>
      qpat_x_assum `_.storage_trace = _` (mp_tac o Q.AP_TERM `LENGTH`) >> simp[] >> decide_tac) >>
  `eval_ext_call_effects cx target calldata framed source_gas ee.accounts
     (ee with gas_obs := tail) = (res,ef)` by
    (drule extcall_frame_value_replay >> strip_tac >>
     qpat_x_assum `bind (frame_call_value _ _) _ _ = _` mp_tac >>
     simp[Once vyperStateTheory.bind_def]) >>
  `consumed.storage_trace = ee.storage_trace ++ [StorageOutcome rq oc]` by
    (drule take_call_outcome_success >> strip_tac >> simp[]) >>
  `?extra. ef.storage_trace = ee.storage_trace ++ StorageOutcome rq oc :: extra /\
           MEM extra [[];[StorageBackend oc.co_accounts oc.co_tStorage]]` by
    (qpat_x_assum `ef.storage_trace = _` kall_tac >>
     reverse (Cases_on `oc.co_success`)
     >- (drule_all extcall_dispatch_failed_source >>
         disch_then (qspecl_then [`cx`,`tail`] mp_tac) >>
         simp[] >> strip_tac >> qexists_tac `[]` >> simp[]) >>
     Cases_on `adopt_call_outcome rq oc consumed` >>
     rename1 `adopt_call_outcome rq oc consumed = (ar,adopted)` >>
     `ar = INL ()` by
       (drule adopt_call_outcome_frame >> simp[]) >>
     qpat_x_assum `ar = _` SUBST_ALL_TAC >>
     drule_all extcall_dispatch_adopted_source >>
     strip_tac >>
     `ef.storage_trace = adopted.storage_trace` by
       (qpat_assum `!tail. eval_ext_call_effects _ _ _ _ _ _ _ = _`
          (qspec_then `tail` mp_tac) >> simp[] >> strip_tac >> simp[]) >>
     qpat_x_assum `adopt_call_outcome _ _ _ = _` mp_tac >>
     simp[adopt_call_outcome_equation] >>
     IF_CASES_TAC >> disch_then (SUBST_ALL_TAC o SYM)
     >- (qexists_tac `[]` >> simp[]) >>
     qexists_tac `[StorageBackend oc.co_accounts oc.co_tStorage]` >>
     simp[APPEND_ASSOC]) >>
  `obs_pre = ee.storage_trace /\ observed_rq = rq /\ observed_oc = oc` by
    (`obs_pre ++ (StorageOutcome observed_rq observed_oc :: sfx) =
        ee.storage_trace ++ (StorageOutcome rq oc :: extra)` by
       (qpat_assum `ef.storage_trace = _ ++ [StorageOutcome observed_rq observed_oc] ++ sfx`
          (mp_tac o SYM) >> simp[]) >>
     pop_assum (mp_tac o ONCE_REWRITE_RULE [APPEND_EQ_APPEND]) >>
     disch_then (DISJ_CASES_THEN strip_assume_tac)
     >- (qpat_assum `MEM extra _` (strip_assume_tac o REWRITE_RULE [MEM]) >>
         Cases_on `l` >>
         qpat_x_assum `StorageOutcome rq oc :: extra = _` mp_tac >> simp[] >>
         rename1 `_ ==> _ <> chunk ++ [StorageOutcome _ _] ++ _` >>
         Cases_on `chunk` >> simp[]) >>
     `l = []` by
       (qpat_x_assum `ee.storage_trace = obs_pre ++ l` (mp_tac o Q.AP_TERM `LENGTH`) >>
        simp[] >> Cases_on `l` >> simp[] >> decide_tac) >>
     qpat_x_assum `ee.storage_trace = obs_pre ++ l` (mp_tac o SYM) >>
     qpat_x_assum `StorageOutcome observed_rq observed_oc :: sfx = _` mp_tac >>
     simp[]) >>
  suspend "request_match"
QED

(* Match the target's next request at exactly the source trace index. *)
Resume extcall_call_stage_prefix[request_match]:
  qpat_x_assum `obs_pre = _` SUBST_ALL_TAC >>
  qpat_x_assum `observed_rq = _` SUBST_ALL_TAC >>
  qpat_x_assum `observed_oc = _` SUBST_ALL_TAC >>
  qpat_x_assum `success = _` SUBST_ALL_TAC >>
  `!g. OPTION_BIND source_gas dest_NumV = SOME g ==> g = w2n gw` by
    (rpt strip_tac >> qpat_assum `!gw g. _ ==> _` drule_all >> simp[]) >>
  drule_all extcall_dispatch_instruction >> strip_tac >>
  rename1 `step_inst_base inst t = OK post` >>
  qhdtm_assum `extcall_request_ready`
    (strip_assume_tac o REWRITE_RULE [extcall_request_ready_def]) >>
  `stmt_state_rel H ctx func cenv cx ee t` by
    (qpat_assum `!H. _ ==> stmt_state_rel H ctx func cenv cx ee t /\ _`
       (drule_then (ACCEPT_TAC o cj 1))) >>
  `LENGTH t.vs_requests = recorded_outcomes_count ee.storage_trace /\
   recorded_outcomes_count ee.storage_trace < LENGTH post.vs_requests /\
   request_agree H cx.txn.target rq
     (EL (recorded_outcomes_count ee.storage_trace) post.vs_requests) /\
   oc = (if t.vs_outcomes = [] then failed_outcome rq else HD t.vs_outcomes)` by
    (qpat_assum `take_call_outcome _ _ _ _ ee = _` mp_tac >>
     pure_rewrite_tac[take_call_outcome_def] >> disch_tac >>
     `stmt_state_rel H ctx func cenv cx (SND (adopt_call_outcome rq oc consumed)) post` by simp[] >>
     drule_all ordinary_request_index >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (drule stmt_state_rel_allocas_below_fmp >> simp[]) >>
  `w2n (n2w cap : bytes32) = cap` by (simp[w2n_n2w] >> decide_tac) >>
  `eval_operand (Lit (n2w cap)) t = SOME (n2w cap)` by simp[eval_operand_def] >>
  qpat_x_assum `eval_operand buf t = SOME ro` mp_tac >> simp[] >>
  disch_then SUBST_ALL_TAC >>
  `w2n ro + cap <= t.vs_alloca_next` by
    (irule abi_caller_allocation_end >> conj_tac
     >- (drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
     qexistsl_tac [`buf_size`,`live`,`w2n ro`] >> simp[]) >>
  qpat_assum `!ao az. eval_operand off t = _ /\ _ ==> _` (drule_all_then strip_assume_tac) >>
  `az <> 0w ==> w2n ao + w2n az <= t.vs_alloca_next` by
    (qpat_assum `az <> 0w ==> _ /\ _` mp_tac >> metis_tac[]) >>
  suspend "call_checks"
QED

(* Check the instruction without extending the focus past the call. *)
Resume extcall_call_stage_prefix[call_checks]:
  `inst_mem_below_frontier inst t` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`inst = mk_inst _ _ _ _`,`eval_operand off t = SOME ao`,
        `eval_operand len t = SOME az`,`eval_operand buf t = SOME ro`,
        `eval_operand (Lit (n2w cap)) t = SOME (n2w cap)`,
        `w2n (n2w cap:bytes32) = cap`,
        `az <> 0w ==> w2n ao + w2n az <= t.vs_alloca_next`,
        `w2n ro + cap <= t.vs_alloca_next`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >> Cases_on `stat` >>
     Cases_on `az = 0w` >>
     simp[below_frontier_CALL,below_frontier_STATICCALL,Excl "w2n_n2w"]) >>
  `EVERY (\p. op_taint tn1 p = {}) inst.inst_operands` by
    (qpat_assum `EVERY (\p. op_taint tn1 p = {}) [addr;value;gas;buf;off;len]` mp_tac >>
     qpat_assum `inst = mk_inst _ _ _ _` SUBST1_TAC >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `stat` >>
     simp[mk_inst_def,op_taint_def,EVERY_DEF]) >>
  `stor_taint_ok_at (DF H) tn1 t` by
    (qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stor_taint_ok_at (DF H) tn1 t`
       (drule_then ACCEPT_TAC)) >>
  `(n2w cap : bytes32) <> 0w ==> ?p. buf = Var p /\ ptr_covers G1 tn1 p t (w2n (n2w cap:bytes32))` by
    (qpat_assum `w2n (n2w cap:bytes32) = cap` SUBST1_TAC >>
     qpat_assum `cap <> 0 ==> ?p. buf = Var p /\ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `cap = 0` >> simp[]) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G1,tn1) []
     (OK (post with vs_inst_idx := SUC t.vs_inst_idx),
      step_prov PG G1 inst post,step_taint inst t post tn1)` by
    (irule raw_call_step_origin_full >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- (qexists_tac `bb` >> conj_tac >> first_assum ACCEPT_TAC) >>
     qexistsl_tac [`ao`,`az`,`len`,`off`,`gas`,`buf`,
                   `n2w cap`,`ro`,`Lit (n2w cap)`,`addr`,`value`] >>
     `az <> 0w ==> ?p. off = Var p /\ ptr_covers G1 tn1 p t (w2n az)` by
       (qpat_assum `az <> 0w ==> _ /\ _` mp_tac >> metis_tac[]) >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     qpat_assum `inst = mk_inst _ _ _ _` SUBST1_TAC >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `stat` >> simp[mk_inst_def]) >>
  `MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL] /\ inst.inst_opcode <> INVOKE` by
    (qpat_assum `inst = mk_inst _ _ _ _` SUBST1_TAC >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `stat` >> simp[mk_inst_def]) >>
  drule_all call_step_checks >> strip_tac >>
  `active_inst func inst t` by
    (irule lookup_instruction_active >> qexists_tac `bb` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  rewrite_tac[request_site_def] >>
  qexistsl_tac [`[]`,`func`,`PG`,`G1`,`tn1`,`t`,`inst`,`0`,`post`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (irule (cj 1 gas_origin_ptr_focus_rules) >>
      qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> gas_origin_ptr_path _ _ _ _`
        (drule_then ACCEPT_TAC))
  >- (drule step_inst_non_invoke >> disch_then (fn th => rewrite_tac[th]) >>
      first_assum ACCEPT_TAC) >>
  REFL_TAC
QED

Finalise extcall_call_stage_prefix

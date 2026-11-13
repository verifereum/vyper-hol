(* The code-presence guard and the source side of the oracle call. *)
Theory extcallEffectMemory
Ancestors
  extcallCallMemory extcallPrecheckMemory extcallCompilerStages
  exprSimExtCallCase exprSafeOperand exprSimWordArgs exprSimProps exprLoweringProps
  loweringPosts loweringStateRelDefs localPtrsProps compileEnv freshWrites
  vyperInterpreter vyperState vyperCallOutcome vyperRuntimeAccounts
  venomExecSemantics venomState venomInst words list arithmetic finite_map
  accountsRelProps fragGasPathMem allocaHistory exprLowering emitHelper emitHelperProps
Libs monadsyntax

Theorem extcall_effect_source_run:
  ~cx.txn.is_static /\ IS_SOME es.outcomes /\
  ext_call_precheck_ok skip rt target es.accounts /\
  take_call_outcome target data vo es = (INL (rq,oc),es1) ==>
  !tail.
    (do accounts <- get_accounts;
        check (ext_call_precheck_ok skip rt target accounts)
          "ExtCall target has no code";
        value <- frame_call_value cx vo;
        eval_ext_call_effects cx target data value gas accounts
     od) (es with gas_obs := tail) =
    if oc.co_success then
      (INL oc.co_returnData,SND (adopt_call_outcome rq oc es1) with gas_obs := tail)
    else (INR (Error (RevertData oc.co_returnData)),es1 with gas_obs := tail)
Proof
  strip_tac >> gen_tac >>
  simp[get_accounts_def, bind_def, ignore_bind_def, check_def, assert_def,
    frame_call_value_def, vyperStateTheory.return_def] >>
  metis_tac[extcall_effects_outcome_tail]
QED

Theorem extcall_request_vars_frame[local]:
  extcall_request_ready ctx func ce cx rt es sa s0 sp stat
    addr value gas buf offset len cap target vo data has def dt opt ee s /\
  ci_mono sp sg /\ sg.cs_current_bb = sp.cs_current_bb /\
  stmt_state_rel ctx func ce cx ee t /\ ~t.vs_halted /\
  t.vs_current_bb = sg.cs_current_bb /\
  t.vs_inst_idx = LENGTH sg.cs_current_insts /\
  (!x. not_fresh_at sp x ==> lookup_var x t = lookup_var x s) /\
  t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
  t.vs_alloca_next = s.vs_alloca_next ==>
  extcall_request_ready ctx func ce cx rt es sa s0 sg stat
    addr value gas buf offset len cap target vo data has def dt opt ee t
Proof
  strip_tac >>
  `!op. safe_operand sp op ==> eval_operand op t = eval_operand op s` by
    (Cases >> simp[safe_operand_def, eval_operand_def]) >>
  `sp.cs_next_var <= sg.cs_next_var /\ sp.cs_next_id <= sg.cs_next_id` by
    fs[ci_mono_def] >>
  `wb_frame ce es ee sa s0 t` by
    (irule wb_frame_readonly_tail >> qexistsl_tac [`sp`,`s`] >>
     fs[extcall_request_ready_def] >> metis_tac[]) >>
  `local_ptrs_reserved ce sg` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sp` >>
     fs[extcall_request_ready_def]) >>
  `extcall_default_ready cx rt has def dt opt t` by
    (irule extcall_default_memory_frame >> qexists_tac `s` >>
     fs[extcall_request_ready_def] >> metis_tac[]) >>
  suspend "regions"
QED

Resume extcall_request_vars_frame[regions]:
  `!name b sz. local_region ce ee.scopes t name b sz <=>
    local_region ce ee.scopes s name b sz` by
    (rpt gen_tac >> irule local_region_lookup_cong >> rpt strip_tac >>
     qpat_x_assum `!x. not_fresh_at sp x ==> _` irule >>
     fs[extcall_request_ready_def, local_ptrs_reserved_def] >> metis_tac[]) >>
  fs[extcall_request_ready_def] >>
  `EVERY (safe_operand sg) [addr;value;gas;buf;offset;len;def]` by
    (fs[EVERY_MEM] >> metis_tac[safe_operand_mono]) >>
  `live < sg.cs_next_id` by decide_tac >>
  fs[EVERY_DEF, read_memory_def] >> rpt conj_tac >> rpt strip_tac >> metis_tac[]
QED

Finalise extcall_request_vars_frame[local]

Theorem extcall_request_precheck_mem:
  (if rt = NoneT /\ ~skip then compile_extcodesize_check addr else comp_return ())
    sp = ((),sg) /\ fn_has_code sp sg func /\ fn_inst_ids_distinct func /\
  extcall_request_ready ctx func ce cx rt es sa s0 sp stat
    addr value gas buf offset len cap target vo data has def dt opt ee s /\
  alloca_history func s ==>
  (ext_call_precheck_ok skip rt target ee.accounts /\
   ?t. gas_path_mem ctx func s 0 (OK t) /\ alloca_history func t /\
     extcall_request_ready ctx func ce cx rt es sa s0 sg stat
       addr value gas buf offset len cap target vo data has def dt opt ee t /\
     (!x. not_fresh_at sp x ==> lookup_var x t = lookup_var x s) /\
     (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s) \/
  (~ext_call_precheck_ok skip rt target ee.accounts /\
   ?t. gas_path_mem ctx func s 0 (Abort Revert_abort t) /\ t.vs_returndata = [])
Proof
  strip_tac >> Cases_on `rt = NoneT /\ ~skip`
  >- suspend "check" >>
  `ext_call_precheck_ok skip rt target ee.accounts` by
    (Cases_on `rt` >> fs[ext_call_precheck_ok_def]) >>
  gvs[comp_return_def] >> qexists_tac `s` >>
  simp[gas_path_mem_rules, venom_state_component_equality] >>
  fs[extcall_request_ready_def] >> irule (cj 1 gas_path_mem_rules) >> simp[]
QED

Resume extcall_request_precheck_mem[check]:
  gvs[] >>
  `stmt_state_rel ctx func ce cx ee s /\ local_ptrs_reserved ce sp /\
   ~s.vs_halted /\ s.vs_current_bb = sp.cs_current_bb /\
   s.vs_inst_idx = LENGTH sp.cs_current_insts /\
   ?aw. eval_operand addr s = SOME aw /\ w2w aw = target` by
    fs[extcall_request_ready_def] >>
  `accounts_agree cx ee.accounts s.vs_accounts` by
    fs[stmt_state_rel_def, state_rel_def, accounts_rel_def] >>
  `(lookup_account target s.vs_accounts).code =
    (lookup_account target ee.accounts).code` by
    metis_tac[accounts_agree_lookup] >>
  `LENGTH (lookup_account target ee.accounts).code < dimword (:256)` by
    (fs[extcall_request_ready_def, accounts_runtime_well_typed_def,
        account_runtime_well_typed_def] >>
     qpat_x_assum `!addr. _` (qspec_then `target` mp_tac) >>
     simp[dimword_def] >> decide_tac) >>
  `((n2w (LENGTH (lookup_account target s.vs_accounts).code):bytes32) <> 0w) <=>
    ext_call_has_code target ee.accounts` by
    simp[ext_call_has_code_def, n2w_11, LENGTH_NIL, NULL_EQ] >>
  qabbrev_tac `w:bytes32 = n2w (LENGTH (lookup_account target s.vs_accounts).code)` >>
  `w = n2w (LENGTH (lookup_account (w2w aw) s.vs_accounts).code)` by simp[Abbr `w`] >>
  drule_all extcall_codecheck_path_mem >>
  simp[Abbr `w`] >> strip_tac
  >- suspend "accept" >>
  disj2_tac >> simp[ext_call_precheck_ok_def, ext_call_has_code_def, NULL_EQ] >>
  metis_tac[]
QED

Resume extcall_request_precheck_mem[accept]:
  qmatch_asmsub_abbrev_tac `gas_path_mem ctx func s 0 (OK t)` >>
  `ci_mono sp sg /\ sg.cs_current_bb = sp.cs_current_bb` by
    (qpat_x_assum `compile_extcodesize_check _ _ = _` mp_tac >>
     simp[compile_extcodesize_check_def, comp_bind_def, comp_ignore_bind_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
       comp_return_def] >> strip_tac >>
     qpat_x_assum `_ = sg` (SUBST1_TAC o SYM) >>
     simp[ci_mono_def, cs_extends_def, GSYM APPEND_ASSOC,
       rich_listTheory.IS_PREFIX_APPEND]) >>
  `!x. not_fresh_at sp x ==> lookup_var x t = lookup_var x s` by
    (simp[Abbr `t`, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
     fs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  qpat_x_assum `sp.cs_current_bb = sg.cs_current_bb` kall_tac >>
  `~t.vs_halted /\ t.vs_current_bb = sg.cs_current_bb /\
   t.vs_inst_idx = LENGTH sg.cs_current_insts /\
   t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
   t.vs_alloca_next = s.vs_alloca_next /\
   (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s` by
    (qpat_assum `Abbrev (t = _)` mp_tac >>
     simp[markerTheory.Abbrev_def, update_var_def,
       venom_state_component_equality] >> metis_tac[]) >>
  `extcall_request_ready ctx func ce cx NoneT es sa s0 sg stat
     addr value gas buf offset len cap target vo data has def dt opt ee t` by
    (irule (Q.INST [`sp` |-> `sp`,`s` |-> `s`] extcall_request_vars_frame) >>
     simp[] >> qexistsl_tac [`s`,`sp`] >> simp[]) >>
  disj1_tac >> simp[ext_call_precheck_ok_def] >> qexists_tac `t` >>
  simp[] >> qpat_assum `s.vs_inst_idx = LENGTH sp.cs_current_insts`
    (fn th => rewrite_tac[GSYM th]) >> first_assum ACCEPT_TAC
QED

Finalise extcall_request_precheck_mem

Theory lowerDloadPtrCreateInterfaces
Ancestors
  lowerDloadPtrResidualInterfaces lowerDloadPtrCall venomExecSemantics venomCallOracleDefs venomState extCallOracle ptrDiscipline codegenRel list finite_map pred_set

Theorem dload_create_request_observations:
  read_memory (w2n off) (w2n sz) s =
    read_memory (w2n off') (w2n sz) t /\
  rq = venom_create_request s value off sz salt /\
  rr = venom_create_request t value off' sz salt ==>
  rq.cr_kind = rr.cr_kind /\ rq.cr_gas = rr.cr_gas /\
  rq.cr_data_len = rr.cr_data_len /\ rq.cr_target = rr.cr_target /\
  rq.cr_value = rr.cr_value /\ rq.cr_data = rr.cr_data /\
  rq.cr_static = rr.cr_static
Proof
  simp[venom_create_request_def] >> rpt strip_tac >> gvs[]
QED

Theorem ld_venom_create_request_masked:
  accounts_agree_except D s.vs_accounts t.vs_accounts /\
  transient_agree_except D s.vs_transient t.vs_transient /\
  read_memory (w2n off) (w2n sz) s =
    read_memory (w2n off') (w2n sz) t ==>
  request_agree_except D
    (venom_create_request s value off sz salt)
    (venom_create_request t value off' sz salt)
Proof
  simp[request_agree_except_def, venom_create_request_def,
       call_request_component_equality]
QED

Theorem dload_exec_create_success_iff:
  exec_create i s value off sz salt = OK u <=>
  ?out w v. i.inst_outputs = [out] /\
    w2n sz <= 2 * max_code_size /\
    s.vs_outcomes <> [] /\
    consume_create_outcome (venom_create_request s value off sz salt) s = (w,v) /\
    u = update_var out w v
Proof
  Cases_on `i.inst_outputs` >>
  simp[exec_create_def, Excl "consume_create_outcome_eq"] >>
  rename1 `h::tl` >> Cases_on `tl` >>
  simp[exec_create_def, Excl "consume_create_outcome_eq"] >>
  IF_CASES_TAC >- simp[] >>
  Cases_on `s.vs_outcomes = []` >>
  simp[Excl "consume_create_outcome_eq"] >>
  pairarg_tac >> gvs[Excl "consume_create_outcome_eq"] >> metis_tac[]
QED

Theorem dload_consume_create_footprint:
  consume_create_outcome rq s = (w,v) ==>
  v.vs_memory = s.vs_memory /\ v.vs_allocas = s.vs_allocas /\
  v.vs_alloca_next = s.vs_alloca_next /\
  v.vs_current_bb = s.vs_current_bb /\ v.vs_prev_bb = s.vs_prev_bb /\
  v.vs_inst_idx = s.vs_inst_idx /\ v.vs_call_ctx = s.vs_call_ctx
Proof
  simp[consume_create_outcome_eq] >> strip_tac >> gvs[]
QED

Theorem dload_consume_create_state:
  consume_create_outcome rq s = (w,r) ==>
  r = s with <|vs_accounts := r.vs_accounts; vs_transient := r.vs_transient;
    vs_logs := r.vs_logs; vs_outcomes := r.vs_outcomes;
    vs_pending_deletions := r.vs_pending_deletions;
    vs_returndata := r.vs_returndata;
    vs_requests := record_request rq s.vs_requests|>
Proof
  simp[consume_create_outcome_eq] >> strip_tac >>
  gvs[venom_state_fupdcanon]
QED

(* Every CREATE outcome adopts its account and transient state, including an
   outcome reporting failure. The execution guard supplies the nonempty queue. *)
Theorem dload_consume_creation_requests_world:
  s.vs_outcomes = t.vs_outcomes /\ s.vs_outcomes <> [] /\
  (rq.cr_kind = CreateCall \/ ?salt. rq.cr_kind = Create2Call salt) /\
  (rq'.cr_kind = CreateCall \/ ?salt. rq'.cr_kind = Create2Call salt) /\
  ~rq.cr_static /\ ~rq'.cr_static /\
  consume_create_outcome rq s = (w,r) /\
  consume_create_outcome rq' t = (w',r') ==>
  w = w' /\ r.vs_accounts = r'.vs_accounts /\
  r.vs_transient = r'.vs_transient /\ r.vs_outcomes = r'.vs_outcomes /\
  r.vs_returndata = r'.vs_returndata /\
  (s.vs_logs = t.vs_logs ==> r.vs_logs = r'.vs_logs) /\
  (s.vs_pending_deletions = t.vs_pending_deletions ==>
    r.vs_pending_deletions = r'.vs_pending_deletions)
Proof
  strip_tac >>
  `?co rest. s.vs_outcomes = co::rest /\ t.vs_outcomes = co::rest` by
    (Cases_on `s.vs_outcomes` >> fs[] >> metis_tac[]) >>
  qpat_x_assum `s.vs_outcomes = t.vs_outcomes` kall_tac >>
  qpat_x_assum `consume_create_outcome _ s = _` mp_tac >>
  qpat_x_assum `consume_create_outcome _ t = _` mp_tac >>
  gvs[consume_create_outcome_eq, computed_precompile_def, take_outcome_def,
      adopt_outcome_def, adopt_outcome_deletions_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem dload_consume_create_world:
  s.vs_outcomes = t.vs_outcomes /\ s.vs_outcomes <> [] /\
  consume_create_outcome (venom_create_request s value off sz salt) s = (w,r) /\
  consume_create_outcome (venom_create_request t value' off' sz' salt') t = (w',r') ==>
  w = w' /\ r.vs_accounts = r'.vs_accounts /\
  r.vs_transient = r'.vs_transient /\ r.vs_outcomes = r'.vs_outcomes /\
  r.vs_returndata = r'.vs_returndata /\
  (s.vs_logs = t.vs_logs ==> r.vs_logs = r'.vs_logs) /\
  (s.vs_pending_deletions = t.vs_pending_deletions ==>
    r.vs_pending_deletions = r'.vs_pending_deletions)
Proof
  strip_tac >>
  irule dload_consume_creation_requests_world >>
  simp[Excl "consume_create_outcome_eq"] >>
  conj_tac
  >- (qexists `venom_create_request s value off sz salt` >>
      Cases_on `salt` >> simp[Excl "consume_create_outcome_eq", venom_create_request_def]) >>
  qexists `venom_create_request t value' off' sz' salt'` >>
  Cases_on `salt'` >> simp[Excl "consume_create_outcome_eq", venom_create_request_def]
QED

Theorem dload_exec_create_forward:
  s.vs_outcomes = t.vs_outcomes /\ s.vs_logs = t.vs_logs /\
  s.vs_pending_deletions = t.vs_pending_deletions /\
  exec_create inst s value off sz salt = OK s1 ==>
  ?out w r. inst.inst_outputs = [out] /\ s1 = update_var out w r /\
    r = s with <|vs_accounts := r.vs_accounts; vs_transient := r.vs_transient;
      vs_logs := r.vs_logs; vs_outcomes := r.vs_outcomes;
      vs_pending_deletions := r.vs_pending_deletions;
      vs_returndata := r.vs_returndata;
      vs_requests := record_request (venom_create_request s value off sz salt) s.vs_requests|> /\
    exec_create inst t value off' sz salt = OK (update_var out w (t with <|
      vs_accounts := r.vs_accounts; vs_transient := r.vs_transient;
      vs_logs := r.vs_logs; vs_outcomes := r.vs_outcomes;
      vs_pending_deletions := r.vs_pending_deletions;
      vs_returndata := r.vs_returndata;
      vs_requests := record_request (venom_create_request t value off' sz salt) t.vs_requests|>))
Proof
  strip_tac >>
  qpat_x_assum `exec_create _ _ _ _ _ _ = _`
    (strip_assume_tac o REWRITE_RULE [dload_exec_create_success_iff]) >>
  rename1 `consume_create_outcome _ s = (w,r)` >>
  Cases_on `consume_create_outcome (venom_create_request t value off' sz salt) t` >>
  rename1 `consume_create_outcome _ t = (wt,rt)` >>
  drule_all dload_consume_create_world >> strip_tac >>
  qexistsl_tac [`out`,`w`,`r`] >>
  simp[Excl "consume_create_outcome_eq"] >>
  conj_tac
  >- (qpat_assum `consume_create_outcome _ s = _`
         (mp_tac o MATCH_MP dload_consume_create_state) >>
      simp[]) >>
  pure_rewrite_tac[dload_exec_create_success_iff] >>
  qexistsl_tac [`out`,`wt`,`rt`] >> conj_tac >- simp[] >>
  conj_tac >- simp[] >> conj_tac >- metis_tac[] >>
  conj_tac >- simp[Excl "consume_create_outcome_eq"] >>
  qpat_assum `consume_create_outcome _ t = _`
    (fn th => ONCE_REWRITE_TAC[MATCH_MP dload_consume_create_state th]) >>
  simp[venom_state_fupdcanon]
QED

Theorem dload_exec_create_footprint:
  exec_create i s value off sz salt = OK u ==>
  u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
  u.vs_alloca_next = s.vs_alloca_next /\
  u.vs_current_bb = s.vs_current_bb /\ u.vs_prev_bb = s.vs_prev_bb /\
  u.vs_inst_idx = s.vs_inst_idx /\ u.vs_call_ctx = s.vs_call_ctx
Proof
  pure_rewrite_tac[dload_exec_create_success_iff] >> strip_tac >>
  drule dload_consume_create_footprint >> strip_tac >>
  gvs[update_var_def]
QED

Theorem ld_create_step_request_growth:
  MEM i.inst_opcode [CREATE;CREATE2] /\ step_inst fuel C i s = OK s' ==>
  LENGTH s.vs_requests < LENGTH s'.vs_requests
Proof
  strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  qpat_x_assum `MEM i.inst_opcode _` (strip_assume_tac o REWRITE_RULE [MEM]) >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[dload_exec_create_success_iff, Excl "consume_create_outcome_eq"] >>
  gvs[consume_create_outcome_eq, record_request_def, update_var_def]
QED

Theorem dload_create_taint_after_consume:
  MEM i.inst_opcode [CREATE;CREATE2] /\
  s.vs_outcomes <> [] /\
  consume_create_outcome (venom_create_request s value off sz salt) s = (w,r) ==>
  step_taint i s (update_var out w r) tn =
    tn with <|t_var := set_var_taint tn.t_var i.inst_outputs (out_taint tn i s);
      t_stor := if s.vs_call_ctx.cc_static then tn.t_stor else {};
      t_trans := if s.vs_call_ctx.cc_static then tn.t_trans else {}|>
Proof
  strip_tac >>
  Cases_on `s.vs_outcomes` >> fs[Excl "consume_create_outcome_eq"] >>
  qpat_x_assum `consume_create_outcome _ s = _` mp_tac >>
  Cases_on `salt` >>
  simp[consume_create_outcome_eq, venom_create_request_def, take_outcome_def,
       record_request_def, computed_precompile_def] >>
  rpt (disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  gvs[MEM, step_taint_def, adopt_reset_def, store_taint_def, imm_taint_def,
      update_var_def, mem_taint_def, new_site_bytes_def, step_writes_def,
      source_memory_write_ranges_def, range_bytes_def, written_taint_def,
      taint_component_equality, FLOOKUP_DEF, SF CONJ_ss] >>
  Cases_on `s.vs_call_ctx.cc_static` >> simp[] >>
  rpt CASE_TAC >> simp[]
QED

Theorem dload_create_step_taint:
  MEM i.inst_opcode [CREATE;CREATE2] /\ step_inst fuel C i s = OK r ==>
  step_taint i s r tn =
    tn with <|t_var := set_var_taint tn.t_var i.inst_outputs (out_taint tn i s);
      t_stor := {}; t_trans := {}|>
Proof
  strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  qpat_assum `MEM i.inst_opcode _` (strip_assume_tac o REWRITE_RULE [MEM]) >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[eval_operands_def, dload_exec_create_success_iff, Excl "consume_create_outcome_eq"] >>
  `MEM i.inst_opcode [CREATE;CREATE2]` by simp[] >>
  drule_all dload_create_taint_after_consume >> simp[]
QED

Theorem dload_consume_create_environment:
  dload_equal_environment s t /\
  rq = venom_create_request s value off sz salt /\
  rr = venom_create_request t value off' sz salt /\
  read_memory (w2n off) (w2n sz) s = read_memory (w2n off') (w2n sz) t /\
  consume_create_outcome rq s = (w,s') /\
  consume_create_outcome rr t = (v,t') ==>
  w = v /\ dload_equal_environment s' t'
Proof
  strip_tac >>
  `s.vs_outcomes = t.vs_outcomes` by
    fs[dload_equal_environment_def, venom_state_component_equality] >>
  Cases_on `salt` >> Cases_on `t.vs_outcomes` >>
  gvs[consume_create_outcome_eq, venom_create_request_def,
      take_outcome_def, computed_precompile_def, failed_outcome_def] >>
  gvs[dload_equal_environment_def, venom_state_component_equality,
      adopt_outcome_def, adopt_outcome_deletions_def]
QED

Theorem dload_exec_create_environment:
  dload_equal_environment s t /\
  read_memory (w2n off) (w2n sz) s = read_memory (w2n off') (w2n sz) t /\
  exec_create i t value off' sz salt = OK t1 ==>
  ?s1. exec_create i s value off sz salt = OK s1 /\
    dload_equal_environment s1 t1 /\
    (!out. MEM out i.inst_outputs ==> lookup_var out s1 = lookup_var out t1)
Proof
  pure_rewrite_tac[dload_exec_create_success_iff] >> strip_tac >>
  `s.vs_outcomes = t.vs_outcomes` by
    fs[dload_equal_environment_def, venom_state_component_equality] >>
  Cases_on `consume_create_outcome (venom_create_request s value off sz salt) s` >>
  rename1 `consume_create_outcome _ s = (x,u)` >>
  `x = w /\ dload_equal_environment u v` by
    (irule dload_consume_create_environment >> metis_tac[]) >>
  qexists_tac `update_var out x u` >>
  conj_tac >- (qexistsl_tac [`out`,`x`,`u`] >> simp[]) >>
  qpat_x_assum `consume_create_outcome _ s = _` kall_tac >>
  qpat_x_assum `consume_create_outcome _ t = _` kall_tac >>
  gvs[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
      Excl "consume_create_outcome_eq"] >>
  fs[dload_equal_environment_def, venom_state_component_equality]
QED

Theorem dload_consume_create_shared_store:
  dload_equal_environment s t /\ dload_shared_store tn un s t /\
  s.vs_outcomes <> [] /\
  read_memory (w2n off) (w2n sz) s = read_memory (w2n off') (w2n sz) t /\
  consume_create_outcome (venom_create_request s value off sz salt) s = (w,s1) /\
  consume_create_outcome (venom_create_request t value off' sz salt) t = (v,t1) ==>
  dload_shared_store tn un s1 t1
Proof
  strip_tac >>
  `s.vs_outcomes = t.vs_outcomes` by
    fs[dload_equal_environment_def, venom_state_component_equality] >>
  Cases_on `t.vs_outcomes` >- fs[] >>
  Cases_on `salt` >>
  gvs[consume_create_outcome_eq, venom_create_request_def,
      take_outcome_def, computed_precompile_def, failed_outcome_def] >>
  gvs[dload_shared_store_def, adopt_outcome_def, storage_agree_except_def,
      word_agree_except_def] >> metis_tac[]
QED

Theorem dload_exec_create_shared_store:
  dload_equal_environment s t /\ dload_shared_store tn un s t /\
  read_memory (w2n off) (w2n sz) s = read_memory (w2n off') (w2n sz) t /\
  (i.inst_opcode = CREATE \/ i.inst_opcode = CREATE2) /\
  exec_create i s value off sz salt = OK s1 /\
  exec_create i t value off' sz salt = OK t1 ==>
  dload_shared_store (step_taint i s s1 tn) (step_taint i t t1 un) s1 t1
Proof
  pure_rewrite_tac[dload_exec_create_success_iff] >> strip_tac >>
  `s.vs_outcomes = t.vs_outcomes /\
    s.vs_call_ctx.cc_static = t.vs_call_ctx.cc_static` by
    fs[dload_equal_environment_def, venom_state_component_equality] >>
  drule_all dload_consume_create_world >> strip_tac >>
  `dload_shared_store tn un v v'` by
    (irule dload_consume_create_shared_store >> metis_tac[]) >>
  `MEM i.inst_opcode [CREATE;CREATE2]` by simp[] >>
  qpat_assum `consume_create_outcome _ s = _`
    (mp_then (Pat `consume_create_outcome _ _ = _`) mp_tac dload_create_taint_after_consume) >>
  disch_then (qspecl_then [`tn`,`out`,`i`] mp_tac) >>
  simp[Excl "consume_create_outcome_eq"] >> strip_tac >>
  qpat_assum `consume_create_outcome _ t = _`
    (mp_then (Pat `consume_create_outcome _ _ = _`) mp_tac dload_create_taint_after_consume) >>
  disch_then (qspecl_then [`un`,`out'`,`i`] mp_tac) >>
  simp[Excl "consume_create_outcome_eq"] >> strip_tac >>
  gvs[dload_shared_store_def, update_var_def, storage_agree_except_def,
      word_agree_except_def, Excl "consume_create_outcome_eq"] >>
  Cases_on `t.vs_call_ctx.cc_static` >> gvs[]
QED

Theorem dload_create_frame_fields:
  exec_create i s value off sz salt = OK s1 ==>
  (?out. i.inst_outputs = [out]) /\
  s1.vs_fmp = s.vs_fmp /\ s1.vs_params = s.vs_params /\
  (!v. ~MEM v i.inst_outputs ==> lookup_var v s1 = lookup_var v s)
Proof
  pure_rewrite_tac[dload_exec_create_success_iff] >> strip_tac >>
  qpat_x_assum `consume_create_outcome _ _ = _` mp_tac >>
  simp[consume_create_outcome_eq] >> strip_tac >>
  gvs[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]
QED

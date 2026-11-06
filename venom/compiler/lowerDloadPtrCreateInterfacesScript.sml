Theory lowerDloadPtrCreateInterfaces
Ancestors
  lowerDloadPtrResidualInterfaces lowerDloadPtrCall venomExecSemantics venomCallOracleDefs venomState extCallOracle ptrDiscipline

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

Theorem dload_exec_create_success_iff:
  exec_create i s value off sz salt = OK u <=>
  ?out w v. i.inst_outputs = [out] /\
    w2n sz <= 2 * max_code_size /\
    consume_create_outcome (venom_create_request s value off sz salt) s = (w,v) /\
    u = update_var out w v
Proof
  Cases_on `i.inst_outputs` >>
  simp[exec_create_def, Excl "consume_create_outcome_eq"] >>
  rename1 `h::tl` >> Cases_on `tl` >>
  simp[exec_create_def, Excl "consume_create_outcome_eq"] >>
  IF_CASES_TAC >- simp[] >>
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

val _ = List.app (fn th => if null (hyp th) then ()
  else raise Fail "CREATE interface: nonempty hypotheses")
  [dload_create_request_observations, dload_exec_create_success_iff,
   dload_consume_create_footprint, dload_exec_create_footprint];

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

val _ = if null (hyp dload_consume_create_environment) then ()
        else raise Fail "CREATE environment: nonempty hypotheses";

Theorem dload_exec_create_environment:
  dload_equal_environment s t /\
  read_memory (w2n off) (w2n sz) s = read_memory (w2n off') (w2n sz) t /\
  exec_create i t value off' sz salt = OK t1 ==>
  ?s1. exec_create i s value off sz salt = OK s1 /\
    dload_equal_environment s1 t1 /\
    (!out. MEM out i.inst_outputs ==> lookup_var out s1 = lookup_var out t1)
Proof
  pure_rewrite_tac[dload_exec_create_success_iff] >> strip_tac >>
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

val _ = if null (hyp dload_exec_create_environment) then ()
        else raise Fail "CREATE exec environment: nonempty hypotheses";

Theorem dload_consume_create_shared_store:
  dload_equal_environment s t /\ dload_shared_store tn un s t /\
  tn.t_stor = {} /\ tn.t_trans = {} /\
  read_memory (w2n off) (w2n sz) s = read_memory (w2n off') (w2n sz) t /\
  consume_create_outcome (venom_create_request s value off sz salt) s = (w,s1) /\
  consume_create_outcome (venom_create_request t value off' sz salt) t = (v,t1) ==>
  dload_shared_store tn un s1 t1
Proof
  strip_tac >>
  `s.vs_outcomes = t.vs_outcomes` by
    fs[dload_equal_environment_def, venom_state_component_equality] >>
  Cases_on `salt` >> Cases_on `t.vs_outcomes` >>
  gvs[consume_create_outcome_eq, venom_create_request_def,
      take_outcome_def, computed_precompile_def, failed_outcome_def] >>
  gvs[dload_shared_store_def, adopt_outcome_def, storage_agree_except_def,
      word_agree_except_def] >> metis_tac[]
QED

Theorem dload_exec_create_shared_store:
  dload_equal_environment s t /\ dload_shared_store tn un s t /\
  tn.t_stor = {} /\ tn.t_trans = {} /\
  read_memory (w2n off) (w2n sz) s = read_memory (w2n off') (w2n sz) t /\
  (i.inst_opcode = CREATE \/ i.inst_opcode = CREATE2) /\
  exec_create i s value off sz salt = OK s1 /\
  exec_create i t value off' sz salt = OK t1 ==>
  dload_shared_store (step_taint i s s1 tn) (step_taint i t t1 un) s1 t1
Proof
  pure_rewrite_tac[dload_exec_create_success_iff] >> strip_tac >>
  `dload_shared_store tn un v v'` by
    (irule dload_consume_create_shared_store >> metis_tac[]) >>
  qpat_x_assum `consume_create_outcome _ s = _` kall_tac >>
  qpat_x_assum `consume_create_outcome _ t = _` kall_tac >>
  gvs[dload_shared_store_def, update_var_def, step_taint_def,
      adopt_reset_def, store_taint_def, imm_taint_def]
QED

val _ = List.app (fn th => if null (hyp th) then ()
  else raise Fail "CREATE shared store: nonempty hypotheses")
  [dload_consume_create_shared_store, dload_exec_create_shared_store];

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

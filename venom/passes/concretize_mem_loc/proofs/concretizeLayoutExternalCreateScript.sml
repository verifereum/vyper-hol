Theory concretizeLayoutExternalCreate
Ancestors concretizeLayoutExternalRequests concretizeLayoutSupplement
  venomCallOracleDefs extCallOracle ptrDiscipline venomState venomExecSemantics
  venomInst list pred_set

(* CREATE's clean-storage side condition makes the adopted external snapshot
   exact; immutable taint and historical request agreement are retained. *)
Theorem concretize_clean_create_completion:
  concretize_local_obs s t /\ concretize_supplement D tn s t /\
  tn.t_stor = {} /\ tn.t_trans = {} /\
  rq.cr_accounts = s.vs_accounts /\ rq.cr_tStorage = s.vs_transient /\
  consume_create_outcome rq s = (w,post) /\
  consume_create_outcome rq t = (w',post') ==>
  w = w' /\ concretize_local_obs post post' /\
  concretize_supplement D tn post post' /\
  post.vs_vars = s.vs_vars /\ post'.vs_vars = t.vs_vars /\
  post.vs_memory = s.vs_memory /\ post'.vs_memory = t.vs_memory
Proof
  strip_tac >> drule_all concretize_supplement_clean_accounts >> strip_tac >>
  `s.vs_logs = t.vs_logs /\ s.vs_pending_deletions = t.vs_pending_deletions` by
    fs[concretize_local_obs_def, dead_result_rel_def] >>
  `request_agree_except D rq rq` by
    simp[request_agree_except_def, call_request_component_equality,
         accounts_agree_except_def, transient_agree_except_def,
         storage_agree_except_def, word_agree_except_def] >>
  `LIST_REL (request_agree_except D)
     (record_request rq s.vs_requests) (record_request rq t.vs_requests)` by
    (irule request_agree_record_request >> fs[concretize_supplement_def]) >>
  `s.vs_outcomes = t.vs_outcomes` by fs[concretize_supplement_def] >>
  qpat_x_assum `consume_create_outcome rq s = _` mp_tac >>
  qpat_x_assum `consume_create_outcome rq t = _` mp_tac >>
  simp[consume_create_outcome_eq] >> rpt strip_tac >> gvs[] >>
  gvs[concretize_local_obs_def, dead_result_rel_def, concretize_supplement_def,
      accounts_agree_except_def, transient_agree_except_def,
      storage_agree_except_def, word_agree_except_def] >>
  irule request_agree_record_request >>
  simp[request_agree_except_def, call_request_component_equality,
       accounts_agree_except_def, transient_agree_except_def,
       storage_agree_except_def, word_agree_except_def]
QED

Theorem create_success_envelope[local]:
  exec_create inst s value off sz salt = OK post ==>
  ?out w p. inst.inst_outputs = [out] /\ ~(w2n sz > 2 * max_code_size) /\
    consume_create_outcome (venom_create_request s value off sz salt) s = (w,p) /\
    post = update_var out w p
Proof
  simp[exec_create_def, AllCaseEqs(), Excl "consume_create_outcome_eq"] >>
  strip_tac >> pairarg_tac >> gvs[Excl "consume_create_outcome_eq"] >> metis_tac[]
QED

Theorem concretize_create_observation:
  MEM inst.inst_opcode [CREATE; CREATE2] /\
  concretize_local_obs s t /\ concretize_supplement D tn s t /\
  tn.t_stor = {} /\ tn.t_trans = {} /\
  read_memory (w2n off) (w2n sz) s = read_memory (w2n offT) (w2n sz) t /\
  exec_create inst s value off sz salt = OK post ==>
  ?post'. exec_create inst t value offT sz salt = OK post' /\
    concretize_local_obs post post' /\
    concretize_supplement D (step_taint inst s post tn) post post' /\
    post.vs_memory = s.vs_memory /\ post'.vs_memory = t.vs_memory /\
    (?out w. inst.inst_outputs = [out] /\
      post.vs_vars = (update_var out w s).vs_vars /\
      post'.vs_vars = (update_var out w t).vs_vars)
Proof
  strip_tac >> drule_all concretize_supplement_clean_accounts >> strip_tac >>
  `venom_create_request s value off sz salt =
   venom_create_request t value offT sz salt` by simp[venom_create_request_def] >>
  drule create_success_envelope >> strip_tac >>
  Cases_on `consume_create_outcome (venom_create_request s value off sz salt) t` >>
  rename1 `consume_create_outcome _ t = (wT,pT)` >>
  `(venom_create_request s value off sz salt).cr_accounts = s.vs_accounts /\
   (venom_create_request s value off sz salt).cr_tStorage = s.vs_transient` by
    simp[venom_create_request_def] >>
  drule_all concretize_clean_create_completion >> strip_tac >>
  gns[Excl "consume_create_outcome_eq"] >>
  qexists_tac `update_var out wT pT` >> conj_tac
  >- (simp[exec_create_def, Excl "consume_create_outcome_eq"] >>
      qpat_x_assum `venom_create_request s _ _ _ _ = _`
        (fn th => rewrite_tac[GSYM th]) >>
      simp[Excl "consume_create_outcome_eq"]) >>
  conj_tac
  >- gvs[concretize_local_obs_def, dead_result_rel_def, update_var_def,
          Excl "consume_create_outcome_eq"] >>
  `concretize_supplement D tn (update_var out w p) (update_var out wT pT)` by
    metis_tac[concretize_supplement_update_var] >>
  (conj_tac >- gvs[concretize_supplement_def, step_taint_def, adopt_reset_def,
     store_taint_def, imm_taint_def, update_var_def, MEM,
     Excl "consume_create_outcome_eq"]) >>
  simp[update_var_def] >> qexists_tac `wT` >> simp[]
QED

Theorem concretize_create_abort_observation:
  MEM inst.inst_opcode [CREATE; CREATE2] /\
  concretize_local_obs s t /\ concretize_supplement D tn s t /\
  tn.t_stor = {} /\ tn.t_trans = {} /\
  exec_create inst s value off sz salt = Abort a post ==>
  ?post'. exec_create inst t value offT sz salt = Abort a post' /\
    concretize_local_obs post post' /\
    concretize_supplement D (step_taint inst s post tn) post post'
Proof
  pure_rewrite_tac[exec_create_abort_iff] >> strip_tac >>
  qexists_tac `halt_state (set_returndata [] t)` >>
  gvs[concretize_local_obs_def, dead_result_rel_def, concretize_supplement_def,
      halt_state_def, set_returndata_def, step_taint_def, adopt_reset_def,
      store_taint_def, imm_taint_def, MEM, Excl "consume_create_outcome_eq"]
QED

Theorem create_execution_fields:
  exec_create inst s value off sz salt = OK post ==>
  ?out w. inst.inst_outputs = [out] /\
    post.vs_vars = (update_var out w s).vs_vars /\
    post.vs_memory = s.vs_memory /\
    post.vs_allocas = s.vs_allocas /\ post.vs_fmp = s.vs_fmp /\
    post.vs_labels = s.vs_labels /\ post.vs_call_ctx = s.vs_call_ctx /\
    post.vs_gas_readings = s.vs_gas_readings /\
    post.vs_tx_ctx = s.vs_tx_ctx /\ post.vs_block_ctx = s.vs_block_ctx /\
    post.vs_code = s.vs_code /\ post.vs_data_section = s.vs_data_section
Proof
  strip_tac >> drule create_success_envelope >> strip_tac >>
  qexistsl_tac [`out`,`w`] >>
  gvs[consume_create_outcome_eq, update_var_def]
QED

val _ = export_theory();

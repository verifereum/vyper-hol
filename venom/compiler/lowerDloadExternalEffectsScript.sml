Theory lowerDloadExternalEffects
Ancestors
  lowerDloadExternalInputs lowerDloadOracleAdoption lowerDloadOracleSelection
  lowerDloadSharedState lowerDloadExternalBackward venomCallOracleDefs
  extCallOracle ptrDiscipline venomState venomExecSemantics list
  o1LowerDloadConcreteExternal lowerDloadOwnership

(* Synchronize the actual CALL adoption test without equating histories. *)
Theorem ld_call_consume_adoption_test:
  rq.cr_kind = rt.cr_kind /\ rq.cr_value = rt.cr_value /\
  rq.cr_target = rt.cr_target /\ rq.cr_data = rt.cr_data /\
  s.vs_call_ctx.cc_static = t.vs_call_ctx.cc_static /\
  s.vs_outcomes = t.vs_outcomes /\
  consume_call_outcome rq roS rs s = (wS,s') /\
  consume_call_outcome rt roT rs t = (wT,t') ==>
  ((~s.vs_call_ctx.cc_static /\ s'.vs_requests <> s.vs_requests /\
    s'.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success) <=>
   (~t.vs_call_ctx.cc_static /\ t'.vs_requests <> t.vs_requests /\
    t'.vs_outcomes <> t.vs_outcomes /\ (HD t.vs_outcomes).co_success))
Proof
  strip_tac >> drule_all ld_computed_precompile_cong >> strip_tac >>
  gvs[consume_call_outcome_eq, take_outcome_rest, ld_record_request_growth]
QED

(* Record the unchanged frame fields at the primitive consumer boundary. *)
Theorem ld_consume_call_frame_fields:
  consume_call_outcome rq ro rs s = (w,r) ==>
  r.vs_params = s.vs_params /\ r.vs_allocas = s.vs_allocas /\
  r.vs_alloca_next = s.vs_alloca_next /\
  r.vs_fmp = s.vs_fmp /\ r.vs_call_entry_fmp = s.vs_call_entry_fmp /\
  r.vs_initial_fmp = s.vs_initial_fmp /\
  r.vs_call_ctx = s.vs_call_ctx /\ r.vs_gas_readings = s.vs_gas_readings
Proof
  simp[consume_call_outcome_eq] >> strip_tac >> gvs[]
QED

Theorem ld_consume_create_frame_fields:
  consume_create_outcome rq s = (w,r) ==>
  r.vs_params = s.vs_params /\ r.vs_allocas = s.vs_allocas /\
  r.vs_alloca_next = s.vs_alloca_next /\
  r.vs_fmp = s.vs_fmp /\ r.vs_call_entry_fmp = s.vs_call_entry_fmp /\
  r.vs_initial_fmp = s.vs_initial_fmp /\
  r.vs_call_ctx = s.vs_call_ctx /\ r.vs_gas_readings = s.vs_gas_readings
Proof
  simp[consume_create_outcome_eq] >> strip_tac >> gvs[]
QED

Theorem ld_external_taint_projections:
  MEM i.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2] ==>
  (step_taint i s r tn).t_imm = tn.t_imm /\
  (step_taint i s r tn).t_stor =
    adopt_reset i (~s.vs_call_ctx.cc_static /\
      r.vs_requests <> s.vs_requests /\ r.vs_outcomes <> s.vs_outcomes /\
      (HD s.vs_outcomes).co_success) tn.t_stor /\
  (step_taint i s r tn).t_trans =
    adopt_reset i (~s.vs_call_ctx.cc_static /\
      r.vs_requests <> s.vs_requests /\ r.vs_outcomes <> s.vs_outcomes /\
      (HD s.vs_outcomes).co_success) tn.t_trans
Proof
  simp[MEM] >> strip_tac >>
  simp[step_taint_def, store_taint_def, imm_taint_def]
QED

(* A true reset test selects an ordinary successful oracle head, never a
   computed precompile or an empty-stream fallback. *)
Theorem ld_call_consume_reset_maps:
  s.vs_outcomes = t.vs_outcomes /\
  rq.cr_kind = MessageCall /\ rt.cr_kind = MessageCall /\
  ~rq.cr_static /\ ~rt.cr_static /\
  rq.cr_value = rt.cr_value /\ rq.cr_target = rt.cr_target /\
  rq.cr_data = rt.cr_data /\
  consume_call_outcome rq roS rs s = (wS,s') /\
  consume_call_outcome rt roT rs t = (wT,t') /\
  s'.vs_requests <> s.vs_requests /\
  s'.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success ==>
  s'.vs_accounts = t'.vs_accounts /\ s'.vs_transient = t'.vs_transient
Proof
  strip_tac >>
  `rq.cr_kind = rt.cr_kind` by simp[] >>
  drule_all ld_computed_precompile_cong >> strip_tac >>
  gvs[consume_call_outcome_eq, ld_record_request_growth, take_outcome_rest] >>
  Cases_on `t.vs_outcomes` >> gvs[take_outcome_def, adopt_outcome_def]
QED

Theorem ld_external_shared_taint:
  MEM i.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2] /\
  ld_shared_state tn un s' t' /\
  (adopted <=> (~s.vs_call_ctx.cc_static /\
    s'.vs_requests <> s.vs_requests /\ s'.vs_outcomes <> s.vs_outcomes /\
    (HD s.vs_outcomes).co_success)) /\
  (adopted <=> (~t.vs_call_ctx.cc_static /\
    t'.vs_requests <> t.vs_requests /\ t'.vs_outcomes <> t.vs_outcomes /\
    (HD t.vs_outcomes).co_success)) /\
  (i.inst_opcode = CALL /\ adopted ==>
    s'.vs_accounts = t'.vs_accounts /\ s'.vs_transient = t'.vs_transient) ==>
  ld_shared_state (step_taint i s s' tn) (step_taint i t t' un) s' t'
Proof
  strip_tac >>
  `!x r u. imm_taint u i x = u.t_imm /\
    store_taint SSTORE u i x u.t_stor = u.t_stor /\
    store_taint TSTORE u i x u.t_trans = u.t_trans` by
    (qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >>
     strip_tac >> simp[imm_taint_def, store_taint_def]) >>
  Cases_on `i.inst_opcode = CALL /\ adopted` >>
  gvs[ld_shared_state_def, step_taint_def, adopt_reset_def,
      storage_agree_except_def, word_agree_except_def]
QED

Theorem ld_call_consume_shared:
  ld_shared_state tn un s t /\
  rq.cr_kind = rt.cr_kind /\ rq.cr_value = rt.cr_value /\
  rq.cr_target = rt.cr_target /\ rq.cr_data = rt.cr_data /\
  rq.cr_static = rt.cr_static /\
  rq.cr_accounts = s.vs_accounts /\ rq.cr_tStorage = s.vs_transient /\
  rt.cr_accounts = t.vs_accounts /\ rt.cr_tStorage = t.vs_transient /\
  consume_call_outcome rq roS rs s = (wS,s') /\
  consume_call_outcome rt roT rs t = (wT,t') ==>
  ld_shared_state tn un s' t'
Proof
  strip_tac >> drule_all ld_take_adopt_shared_state >>
  gvs[consume_call_outcome_eq, ld_shared_state_def]
QED

Theorem ld_create_consume_shared:
  ld_shared_state tn un s t /\
  rq.cr_kind = rt.cr_kind /\ rq.cr_value = rt.cr_value /\
  rq.cr_target = rt.cr_target /\ rq.cr_data = rt.cr_data /\
  rq.cr_static = rt.cr_static /\
  rq.cr_accounts = s.vs_accounts /\ rq.cr_tStorage = s.vs_transient /\
  rt.cr_accounts = t.vs_accounts /\ rt.cr_tStorage = t.vs_transient /\
  consume_create_outcome rq s = (wS,s') /\
  consume_create_outcome rt t = (wT,t') ==>
  ld_shared_state tn un s' t'
Proof
  strip_tac >> drule_all ld_take_adopt_shared_state >>
  gvs[consume_create_outcome_eq, ld_shared_state_def]
QED

Theorem ld_call_consume_tainted_shared:
  MEM i.inst_opcode [CALL;STATICCALL] /\ ld_shared_state tn un s t /\
  rq.cr_kind = MessageCall /\ rt.cr_kind = MessageCall /\
  rq.cr_value = rt.cr_value /\ rq.cr_target = rt.cr_target /\
  rq.cr_data = rt.cr_data /\
  rq.cr_static = (i.inst_opcode = STATICCALL \/ s.vs_call_ctx.cc_static) /\
  rt.cr_static = (i.inst_opcode = STATICCALL \/ t.vs_call_ctx.cc_static) /\
  rq.cr_accounts = s.vs_accounts /\ rq.cr_tStorage = s.vs_transient /\
  rt.cr_accounts = t.vs_accounts /\ rt.cr_tStorage = t.vs_transient /\
  consume_call_outcome rq roS rs s = (wS,s') /\
  consume_call_outcome rt roT rs t = (wT,t') ==>
  ld_shared_state (step_taint i s s' tn) (step_taint i t t' un) s' t'
Proof
  strip_tac >>
  drule ld_shared_state_environment >> strip_tac >>
  `rq.cr_kind = rt.cr_kind /\ rq.cr_static = rt.cr_static /\
    s.vs_call_ctx.cc_static = t.vs_call_ctx.cc_static` by simp[] >>
  `ld_shared_state tn un s' t'` by
    (drule_all ld_call_consume_shared >> simp[Excl "consume_call_outcome_eq"]) >>
  `(~s.vs_call_ctx.cc_static /\ s'.vs_requests <> s.vs_requests /\
     s'.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success) <=>
   (~t.vs_call_ctx.cc_static /\ t'.vs_requests <> t.vs_requests /\
     t'.vs_outcomes <> t.vs_outcomes /\ (HD t.vs_outcomes).co_success)` by
    (drule_all ld_call_consume_adoption_test >> simp[Excl "consume_call_outcome_eq"]) >>
  irule ld_external_shared_taint >>
  goal_assum (drule_at (Pat `ld_shared_state _ _ s' t'`)) >>
  reverse conj_tac >- gvs[MEM] >>
  qexists_tac `(~s.vs_call_ctx.cc_static /\ s'.vs_requests <> s.vs_requests /\
     s'.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success)` >>
  simp[] >> strip_tac >>
  `~rq.cr_static /\ ~rt.cr_static` by gvs[MEM] >>
  `s'.vs_requests <> s.vs_requests /\ s'.vs_outcomes <> s.vs_outcomes /\
    (HD s.vs_outcomes).co_success` by metis_tac[] >>
  drule_all ld_call_consume_reset_maps >> simp[]
QED

(* The CREATE variants never reset masks; the single generic mask boundary
   therefore applies without an adoption-test premise at their consumer. *)
Theorem ld_create_consume_tainted_shared:
  MEM i.inst_opcode [CREATE;CREATE2] /\ ld_shared_state tn un s t /\
  rq.cr_kind = rt.cr_kind /\ rq.cr_value = rt.cr_value /\
  rq.cr_target = rt.cr_target /\ rq.cr_data = rt.cr_data /\
  rq.cr_static = rt.cr_static /\
  rq.cr_accounts = s.vs_accounts /\ rq.cr_tStorage = s.vs_transient /\
  rt.cr_accounts = t.vs_accounts /\ rt.cr_tStorage = t.vs_transient /\
  consume_create_outcome rq s = (wS,s') /\
  consume_create_outcome rt t = (wT,t') ==>
  ld_shared_state (step_taint i s s' tn) (step_taint i t t' un) s' t'
Proof
  strip_tac >> drule_all ld_create_consume_shared >>
  qpat_x_assum `MEM i.inst_opcode _` mp_tac >> simp[MEM] >>
  strip_tac >>
  simp[ld_shared_state_def, step_taint_def, adopt_reset_def,
       store_taint_def, imm_taint_def]
QED

Theorem ld_extract_result_shared:
  ld_shared_state tn un s t /\ tn.t_stor = {} /\ tn.t_trans = {} /\
  extract_venom_result s v roS rs rr = SOME (wS,rS) /\
  extract_venom_result t v roT rs rr = SOME (wT,rT) ==>
  ld_shared_state tn un rS rT /\
  rS.vs_accounts = rT.vs_accounts /\ rS.vs_transient = rT.vs_transient
Proof
  strip_tac >> drule_all ld_shared_state_empty_exact >> strip_tac >>
  Cases_on `rr` >- gvs[extract_venom_result_def] >>
  rename1 `extract_venom_result s v roS rs (SOME p) = _` >>
  PairCases_on `p` >> gvs[extract_venom_result_def] >>
  Cases_on `p1.contexts` >> gvs[] >>
  rename1 `p1.contexts = h::rest` >>
  Cases_on `rest` >> gvs[] >> PairCases_on `h` >>
  Cases_on `p0`
  >- gvs[ld_shared_state_def] >>
  Cases_on `y` >> gvs[ld_shared_state_def, storage_agree_except_def,
    word_agree_except_def]
QED

Theorem ld_extract_result_frame_fields:
  extract_venom_result s v ro rs rr = SOME (w,r) ==>
  r.vs_params = s.vs_params /\ r.vs_allocas = s.vs_allocas /\
  r.vs_alloca_next = s.vs_alloca_next /\
  r.vs_fmp = s.vs_fmp /\ r.vs_call_entry_fmp = s.vs_call_entry_fmp /\
  r.vs_initial_fmp = s.vs_initial_fmp /\
  r.vs_call_ctx = s.vs_call_ctx /\ r.vs_gas_readings = s.vs_gas_readings
Proof
  strip_tac >> drule ld_extract_concrete_shape >>
  disch_then SUBST1_TAC >> simp[]
QED

Theorem ld_delegate_extract_tainted_shared:
  i.inst_opcode = DELEGATECALL /\
  ld_shared_state tn un s t /\ tn.t_stor = {} /\ tn.t_trans = {} /\
  extract_venom_result s v roS rs rr = SOME (wS,rS) /\
  extract_venom_result t v roT rs rr = SOME (wT,rT) ==>
  ld_shared_state (step_taint i s rS tn) (step_taint i t rT un) rS rT /\
  rS.vs_accounts = rT.vs_accounts /\ rS.vs_transient = rT.vs_transient
Proof
  strip_tac >> drule_all ld_extract_result_shared >> strip_tac >>
  gvs[ld_shared_state_def, step_taint_def, adopt_reset_def,
       store_taint_def, imm_taint_def]
QED

Theorem ld_external_clean_output:
  MEM i.inst_opcode [CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2] ==>
  out_taint tn i s = {} /\
  (step_taint i s r tn).t_var = set_var_taint tn.t_var i.inst_outputs {} /\
  ld_step_prov AP AG L i = DRESTRICT AG (COMPL (set i.inst_outputs))
Proof
  simp[MEM] >> strip_tac >>
  `out_taint tn i s = {}` by
    (simp[out_taint_def] >>
     Cases_on `i.inst_operands` >> simp[] >>
     Cases_on `t`
     >- (Cases_on `eval_operand h s` >> simp[]) >>
     Cases_on `t'`
     >- (Cases_on `eval_operand h s` >> simp[]) >>
     simp[]) >>
  simp[step_taint_def, ld_step_prov_def, ld_out_prov_def, ld_set_prov_def] >>
  Cases_on `i.inst_outputs` >> simp[]
QED

(* Both oracle consumers differ from the adoption boundary only in fields
   irrelevant to off-current-address storage. *)
Theorem ld_external_consume_noncurrent:
  ld_shared_state tn un s t /\
  (!a. a <> s.vs_call_ctx.cc_address ==>
    (s.vs_accounts a).storage = (t.vs_accounts a).storage) /\
  (!a. a <> s.vs_call_ctx.cc_address ==>
    s.vs_transient a = t.vs_transient a) /\
  rq.cr_kind = rt.cr_kind /\ rq.cr_value = rt.cr_value /\
  rq.cr_target = rt.cr_target /\ rq.cr_data = rt.cr_data /\
  rq.cr_static = rt.cr_static /\
  rq.cr_accounts = s.vs_accounts /\ rq.cr_tStorage = s.vs_transient /\
  rt.cr_accounts = t.vs_accounts /\ rt.cr_tStorage = t.vs_transient /\
  ((consume_call_outcome rq roS rs s = (wS,s') /\
    consume_call_outcome rt roT rs t = (wT,t')) \/
   (consume_create_outcome rq s = (wS,s') /\
    consume_create_outcome rt t = (wT,t'))) ==>
  (!a. a <> s'.vs_call_ctx.cc_address ==>
    (s'.vs_accounts a).storage = (t'.vs_accounts a).storage) /\
  (!a. a <> s'.vs_call_ctx.cc_address ==>
    s'.vs_transient a = t'.vs_transient a)
Proof
  strip_tac >>
  drule_all (SRULE [] (GEN_ALL ld_take_adopt_noncurrent)) >>
  gvs[consume_call_outcome_eq, consume_create_outcome_eq]
QED

(* Keep the memory/variable components abstract: they belong to the separate
   memory and owned-value boundaries, not shared external effects. *)
Theorem ld_external_bind_tainted_shared:
  ld_shared_state (step_taint i s rS tn) (step_taint i t rT un) rS rT ==>
  ld_shared_state (step_taint i s (update_var out w rS) tn)
    (step_taint i t (update_var out w rT) un)
    (update_var out w rS) (update_var out w rT)
Proof
  simp[ld_shared_state_def, step_taint_def, update_var_def] >>
  strip_tac >> gvs[]
QED

Theorem ld_consume_call_vars:
  consume_call_outcome rq ro rs s = (w,r) ==> r.vs_vars = s.vs_vars
Proof
  simp[consume_call_outcome_eq] >> strip_tac >> gvs[]
QED

Theorem ld_consume_create_vars:
  consume_create_outcome rq s = (w,r) ==> r.vs_vars = s.vs_vars
Proof
  simp[consume_create_outcome_eq] >> strip_tac >> gvs[]
QED

Theorem ld_extract_result_vars:
  extract_venom_result s v ro rs rr = SOME (w,r) ==> r.vs_vars = s.vs_vars
Proof
  strip_tac >> drule ld_extract_concrete_shape >>
  disch_then (mp_tac o Q.AP_TERM `\s. s.vs_vars`) >> simp[]
QED

Theorem ld_consume_call_labels:
  consume_call_outcome rq ro rs s = (w,r) ==> r.vs_labels = s.vs_labels
Proof
  simp[consume_call_outcome_eq] >> strip_tac >> gvs[]
QED

Theorem ld_consume_create_labels:
  consume_create_outcome rq s = (w,r) ==> r.vs_labels = s.vs_labels
Proof
  simp[consume_create_outcome_eq] >> strip_tac >> gvs[]
QED

Theorem ld_extract_result_labels:
  extract_venom_result s v ro rs rr = SOME (w,r) ==> r.vs_labels = s.vs_labels
Proof
  strip_tac >> drule ld_extract_concrete_shape >>
  disch_then (mp_tac o Q.AP_TERM `\s. s.vs_labels`) >> simp[]
QED

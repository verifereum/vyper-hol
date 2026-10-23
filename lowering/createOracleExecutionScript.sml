(* Production CREATE oracle boundary; no concrete initcode execution. *)
Theory createOracleExecution
Ancestors
  venomExecSemantics venomCallOracleDefs extCallOracle venomState

Theorem venom_create_request_fields:
  !s v off sz salt.
  let rq = venom_create_request s v off sz salt in
    rq.cr_kind = (case salt of NONE => CreateCall | SOME x => Create2Call x) /\
    rq.cr_target = 0w /\ rq.cr_static = F /\ rq.cr_gas = NONE /\
    rq.cr_value = w2n v /\
    rq.cr_data = read_memory (w2n off) (w2n sz) s /\
    rq.cr_data_len = LENGTH rq.cr_data /\
    rq.cr_accounts = s.vs_accounts /\ rq.cr_tStorage = s.vs_transient
Proof
  simp[venom_create_request_def]
QED

Theorem venom_create_not_precompile[simp]:
  ~computed_precompile (venom_create_request s v off sz salt)
Proof
  Cases_on `salt` >> simp[venom_create_request_def, computed_precompile_def]
QED

Theorem consume_create_head:
  s.vs_outcomes = outcome::rest ==>
  consume_create_outcome (venom_create_request s v off sz salt) s =
    (if outcome.co_success then w2w outcome.co_created else 0w,
     s with <| vs_outcomes := rest;
       vs_requests := s.vs_requests ++ [venom_create_request s v off sz salt];
       vs_accounts := outcome.co_accounts;
       vs_transient := outcome.co_tStorage;
       vs_logs := if outcome.co_success then s.vs_logs ++ outcome.co_logs else s.vs_logs;
       vs_toDelete := if outcome.co_success then outcome.co_toDelete else s.vs_toDelete;
       vs_returndata := outcome.co_returnData |>)
Proof
  strip_tac >> simp[consume_create_outcome_eq, take_outcome_def, record_request_def] >>
  Cases_on `salt` >>
  simp[venom_create_request_def, adopt_outcome_def, adopt_outcome_deletions_def]
QED

Theorem consume_create_empty:
  s.vs_outcomes = [] ==>
  consume_create_outcome (venom_create_request s v off sz salt) s =
    (0w, s with <|
       vs_requests := s.vs_requests ++ [venom_create_request s v off sz salt];
       vs_returndata := [] |>)
Proof
  strip_tac >> simp[consume_create_outcome_eq, take_outcome_def, record_request_def] >>
  Cases_on `salt` >>
  simp[venom_create_request_def, failed_outcome_def,
       adopt_outcome_def, adopt_outcome_deletions_def] >>
  simp[venom_state_component_equality]
QED

Theorem consume_create_memory[simp]:
  (SND (consume_create_outcome rq s)).vs_memory = s.vs_memory
Proof
  simp[]
QED

Theorem consume_create_frames:
  let t = SND (consume_create_outcome rq s) in
    t.vs_vars = s.vs_vars /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_fmp = s.vs_fmp /\ t.vs_immutables = s.vs_immutables /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx
Proof
  simp[]
QED

Theorem exec_create_single:
  inst.inst_outputs = [out] ==>
  exec_create inst s v off sz salt =
    OK (update_var out
      (FST (consume_create_outcome (venom_create_request s v off sz salt) s))
      (SND (consume_create_outcome (venom_create_request s v off sz salt) s)))
Proof
  simp[exec_create_def]
QED

Theorem exec_create_invalid_outputs:
  (!out. inst.inst_outputs <> [out]) ==>
  exec_create inst s v off sz salt = Error "create requires single output"
Proof
  strip_tac >> simp[exec_create_def] >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  Cases_on `t` >> gvs[]
QED

Theorem consume_call_deletions:
  (SND (consume_call_outcome rq ro rs s)).vs_toDelete =
  adopt_outcome_deletions rq (FST (take_outcome rq s.vs_outcomes)) s.vs_toDelete
Proof
  simp[]
QED

Theorem consume_static_call_deletions:
  rq.cr_static ==>
  (SND (consume_call_outcome rq ro rs s)).vs_toDelete = s.vs_toDelete
Proof
  simp[adopt_outcome_deletions_def]
QED

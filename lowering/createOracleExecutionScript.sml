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

Theorem consume_call_deletions[local]:
  (SND (consume_call_outcome rq ro rs s)).vs_toDelete =
  if computed_precompile rq then s.vs_toDelete
  else adopt_outcome_deletions rq
    (FST (take_outcome rq s.vs_outcomes)) s.vs_toDelete
Proof
  simp[]
QED

Theorem consume_static_call_deletions:
  rq.cr_static ==>
  (SND (consume_call_outcome rq ro rs s)).vs_toDelete = s.vs_toDelete
Proof
  simp[adopt_outcome_deletions_def]
QED

(* Regressions quantify over the observed snapshots, rather than running any
   particular constructor.  Both salts use exactly the same consumption path. *)
Theorem create_oracle_request_regression:
  let rq = venom_create_request s value offset sz salt in
    rq.cr_kind = (case salt of NONE => CreateCall | SOME x => Create2Call x) /\
    rq.cr_data = TAKE (w2n sz)
      (DROP (w2n offset) s.vs_memory ++ REPLICATE (w2n sz) 0w) /\
    rq.cr_value = w2n value /\ rq.cr_target = 0w /\
    rq.cr_static = F /\ rq.cr_gas = NONE /\
    rq.cr_data_len = LENGTH rq.cr_data
Proof
  simp[venom_create_request_fields, venom_create_request_def, read_memory_def]
QED

Theorem exec_create_success_regression:
  inst.inst_outputs = [out] /\ s.vs_outcomes = outcome::rest /\
  outcome.co_success ==>
  exec_create inst s value offset sz salt =
    OK (update_var out (w2w outcome.co_created)
      (s with <| vs_outcomes := rest;
        vs_requests := s.vs_requests ++
          [venom_create_request s value offset sz salt];
        vs_accounts := outcome.co_accounts;
        vs_transient := outcome.co_tStorage;
        vs_logs := s.vs_logs ++ outcome.co_logs;
        vs_toDelete := outcome.co_toDelete;
        vs_returndata := outcome.co_returnData |>))
Proof
  strip_tac >> drule consume_create_head >> disch_then assume_tac >>
  drule exec_create_single >> disch_then (fn th => pure_rewrite_tac[th]) >>
  asm_rewrite_tac[]
QED

Theorem exec_create_failure_regression:
  inst.inst_outputs = [out] /\ s.vs_outcomes = outcome::rest /\
  ~outcome.co_success ==>
  exec_create inst s value offset sz salt =
    OK (update_var out 0w
      (s with <| vs_outcomes := rest;
        vs_requests := s.vs_requests ++
          [venom_create_request s value offset sz salt];
        vs_accounts := outcome.co_accounts;
        vs_transient := outcome.co_tStorage;
        vs_logs := s.vs_logs;
        vs_toDelete := s.vs_toDelete;
        vs_returndata := outcome.co_returnData |>))
Proof
  strip_tac >> drule consume_create_head >> disch_then assume_tac >>
  drule exec_create_single >> disch_then (fn th => pure_rewrite_tac[th]) >>
  asm_rewrite_tac[]
QED

(* A pre-entry failure still consumes and adopts the observed nonce/account
   snapshot.  Empty returndata does not mean an exhausted oracle. *)
Theorem exec_create_preentry_failure_regression:
  inst.inst_outputs = [out] /\ s.vs_outcomes = outcome::rest /\
  ~outcome.co_success /\ outcome.co_returnData = [] ==>
  exec_create inst s value offset sz salt =
    OK (update_var out 0w
      (s with <| vs_outcomes := rest;
        vs_requests := s.vs_requests ++
          [venom_create_request s value offset sz salt];
        vs_accounts := outcome.co_accounts;
        vs_transient := outcome.co_tStorage;
        vs_logs := s.vs_logs;
        vs_toDelete := s.vs_toDelete;
        vs_returndata := [] |>))
Proof
  strip_tac >> drule_all exec_create_failure_regression >> simp[]
QED

Theorem exec_create_exhausted_regression:
  inst.inst_outputs = [out] /\ s.vs_outcomes = [] ==>
  exec_create inst s value offset sz salt =
    OK (update_var out 0w
      (s with <| vs_requests := s.vs_requests ++
          [venom_create_request s value offset sz salt];
        vs_returndata := [] |>))
Proof
  strip_tac >> drule consume_create_empty >> disch_then assume_tac >>
  drule exec_create_single >> disch_then (fn th => pure_rewrite_tac[th]) >>
  asm_rewrite_tac[]
QED

Theorem exec_create_frame_regression:
  inst.inst_outputs = [out] /\
  exec_create inst s value offset sz salt = OK t ==>
    lookup_var out t = SOME
      (FST (consume_create_outcome
        (venom_create_request s value offset sz salt) s)) /\
    t.vs_memory = s.vs_memory /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_fmp = s.vs_fmp /\
    t.vs_immutables = s.vs_immutables /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx /\
    (!other. other <> out ==> lookup_var other t = lookup_var other s)
Proof
  strip_tac >> drule exec_create_single >>
  disch_then (fn th => fs[th]) >>
  gvs[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem exec_create_bad_outputs_regression:
  (inst.inst_outputs = [] \/ inst.inst_outputs = [a;b]) ==>
  exec_create inst s value offset sz salt = Error "create requires single output"
Proof
  strip_tac >> irule exec_create_invalid_outputs >> simp[]
QED

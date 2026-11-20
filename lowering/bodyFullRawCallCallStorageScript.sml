(* Storage taint follows the specified successful oracle-call execution.
   The dead mask is arbitrary, including constructor immutable masks. *)
Theory bodyFullRawCallCallStorage
Ancestors
  oracleCallStepPtr bodyPtrDefs ptrDiscipline pred_set
  venomExecSemantics venomCallOracleDefs venomState venomInst extCallOracle list

Theorem raw_call_exec_stor_taint_at:
  (inst.inst_opcode = CALL \/
   (inst.inst_opcode = STATICCALL /\ stat)) /\
  exec_ext_call inst s gas addr value ao az ro rz stat = OK u /\
  u.vs_immutables = s.vs_immutables /\
  stor_taint_ok_at D tn s ==>
  stor_taint_ok_at D (step_taint inst s u tn) u
Proof
  strip_tac >> drule exec_ext_call_storage_cases >> strip_tac >>
  gvs[stor_taint_ok_at_def, step_taint_def, adopt_reset_def,
      store_taint_def, imm_taint_def] >>
  metis_tac[EMPTY_SUBSET]
QED

Theorem raw_delegate_call_exec_stor_taint_at:
  inst.inst_opcode = DELEGATECALL /\
  exec_delegatecall inst s gas addr ao az ro rz = OK u /\
  u.vs_immutables = s.vs_immutables /\
  stor_taint_ok_at D tn s ==>
  stor_taint_ok_at D (step_taint inst s u tn) u
Proof
  strip_tac >>
  qabbrev_tac `rq = venom_call_request s addr 0w ao az F with
    <| cr_kind := DelegateMessageCall; cr_gas := SOME (w2n gas) |>` >>
  `rq.cr_static = s.vs_call_ctx.cc_static /\
   rq.cr_kind = DelegateMessageCall /\ ~computed_precompile rq` by
    simp[Abbr `rq`, venom_call_request_def, computed_precompile_def] >>
  qpat_x_assum `exec_delegatecall _ _ _ _ _ _ _ _ = _` mp_tac >>
  namedCases_on `inst.inst_outputs` ["", "out outs"] >>
  simp[exec_delegatecall_def] >>
  Cases_on `outs` >> simp[exec_delegatecall_def] >>
  namedCases_on `s.vs_outcomes` ["", "outcome rest"] >>
  qpat_assum `Abbrev (rq = _)`
    (fn th => simp[GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th),
                   take_outcome_def]) >>
  strip_tac >>
  `rest <> outcome::rest` by
    (strip_tac >> pop_assum (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  `u.vs_call_ctx = s.vs_call_ctx /\
   u.vs_requests = record_request rq s.vs_requests /\
   u.vs_outcomes = rest /\
   (~outcome.co_success \/ s.vs_call_ctx.cc_static ==>
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient)` by
    (Cases_on `outcome.co_success` >> Cases_on `s.vs_call_ctx.cc_static` >>
     gvs[update_var_def, adopt_outcome_def]) >>
  `LAST u.vs_requests = rq /\ u.vs_requests <> s.vs_requests` by
    (conj_tac
     >- simp[record_request_def, LAST_APPEND_CONS]
     >> simp[record_request_changed]) >>
  Cases_on `outcome.co_success` >> Cases_on `s.vs_call_ctx.cc_static` >>
  gvs[stor_taint_ok_at_def, step_taint_def, adopt_reset_def, store_taint_def,
      imm_taint_def] >>
  metis_tac[EMPTY_SUBSET]
QED

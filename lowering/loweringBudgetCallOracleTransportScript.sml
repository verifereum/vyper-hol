Theory loweringBudgetCallOracleTransport
Ancestors
  venomExecSemantics venomCallOracleDefs venomState extCallOracle list
  sourceCallCount vyperCallOutcome accountsRelProps

Theorem call_take_outcome_head[local]:
  !rq oc os.
    FST (take_outcome rq (oc::os)) = FST (take_outcome rq [oc])
Proof
  rpt gen_tac >> Cases_on `computed_precompile rq` >>
  simp[take_outcome_def] >>
  Cases_on `precompile_result rq.cr_target rq.cr_data` >> simp[] >>
  Cases_on `x` >> simp[] >> Cases_on `oc.co_success` >> simp[]
QED

Theorem call_operand_outcome_update[local]:
  !op s os. eval_operand op (s with vs_outcomes := os) = eval_operand op s
Proof
  Cases >> simp[eval_operand_def, lookup_var_def]
QED

Theorem call_step_same_outcome_head:
  !fuel ctx i s t oc os rest.
    MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL] /\
    s.vs_outcomes = oc::os /\
    step_inst fuel ctx i s = OK t ==>
    step_inst fuel ctx i (s with vs_outcomes := oc::rest) =
      OK (t with vs_outcomes := rest)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[] >> gvs[Once step_inst_def] >>
  simp[Once step_inst_def] >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  simp[step_inst_base_opcode_eqs, eval_operand_def, lookup_var_def] >>
  gvs[exec_ext_call_def, exec_delegatecall_def, AllCaseEqs(),
    consume_call_outcome_eq, take_outcome_rest,
    update_var_def] >>
  simp[call_operand_outcome_update, venom_call_request_def, read_memory_def,
    write_memory_with_expansion_def, call_take_outcome_head]
QED

Theorem call_take_outcome_failed_fields[local]:
  !rq rest.
    ~(FST (take_outcome rq (empty_failed_outcome::rest))).co_success /\
    (FST (take_outcome rq (empty_failed_outcome::rest))).co_returnData = [] /\
    (FST (take_outcome rq (empty_failed_outcome::rest))).co_toDelete = []
Proof
  rpt gen_tac >> Cases_on `computed_precompile rq`
  >- (Cases_on `precompile_result rq.cr_target rq.cr_data` >>
      simp[take_outcome_def, empty_failed_outcome_def, failed_outcome_def] >>
      Cases_on `x` >> simp[]) >>
  simp[take_outcome_def, empty_failed_outcome_def]
QED

Theorem call_step_empty_failed_head:
  !fuel ctx i s t rest.
    MEM i.inst_opcode [CALL;STATICCALL;DELEGATECALL] /\
    s.vs_outcomes = [] /\ step_inst fuel ctx i s = OK t ==>
    step_inst fuel ctx i (s with vs_outcomes := empty_failed_outcome::rest) =
      OK (t with vs_outcomes := rest)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[] >> gvs[Once step_inst_def] >>
  simp[Once step_inst_def] >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  simp[step_inst_base_opcode_eqs, eval_operand_def, lookup_var_def] >>
  simp[call_operand_outcome_update] >>
  gvs[exec_ext_call_def, exec_delegatecall_def, AllCaseEqs(),
    consume_call_outcome_eq, take_outcome_rest, update_var_def] >>
  simp[venom_call_request_def, read_memory_def] >>
  simp[adopt_outcome_def, adopt_outcome_deletions_def,
    call_take_outcome_failed_fields, take_outcome_def, failed_outcome_def,
    write_memory_with_expansion_def]
QED

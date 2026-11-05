Theory callStepPtr
Ancestors
  bodyPtrDefs ptrDiscipline venomCallOracleDefs vyperValue valueEncoding
  loweringPosts compileEnv exprLowering vyperAST extCallOracle

(* The reset test is exposed without imposing restrictions on the old taint. *)
Theorem call_step_storage_taint:
  inst.inst_opcode = CALL ==>
  (step_taint inst s s' tn).t_stor =
    (if ~s.vs_call_ctx.cc_static /\
        s'.vs_requests <> s.vs_requests /\
        s'.vs_outcomes <> s.vs_outcomes /\
        (HD s.vs_outcomes).co_success then {} else tn.t_stor) /\
  (step_taint inst s s' tn).t_trans =
    (if ~s.vs_call_ctx.cc_static /\
        s'.vs_requests <> s.vs_requests /\
        s'.vs_outcomes <> s.vs_outcomes /\
        (HD s.vs_outcomes).co_success then {} else tn.t_trans)
Proof
  simp[step_taint_def, adopt_reset_def, store_taint_def]
QED

Theorem ptr_val_ok_none:
  ptr_val_ok cx NoneT NoneV (Lit 0w) G tn s
Proof
  simp[ptr_val_ok_def, ptr_mem_ok_def, op_taint_def,
       evaluate_type_def, val_in_memory_def, val_footprint_def,
       type_memory_size_def]
QED

Theorem ptr_buf_ok_zero_type:
  type_memory_bytes cenv (lowered_value_type cenv e) = 0 ==>
  ptr_buf_ok cenv e op G s
Proof
  simp[ptr_buf_ok_def]
QED

Theorem send_none_buffer_size:
  type_memory_bytes cenv
    (lowered_value_type cenv (Call NoneT (Send has_gas) es ann)) = 0
Proof
  simp[lowered_value_type_def, expr_type_def, type_memory_bytes_def]
QED

Theorem consume_call_outcome_no_adoption:
  rq.cr_kind = MessageCall /\
  (rq.cr_static \/ ~(FST (take_outcome rq s.vs_outcomes)).co_success) ==>
  (SND (consume_call_outcome rq ro rz s)).vs_accounts = s.vs_accounts /\
  (SND (consume_call_outcome rq ro rz s)).vs_transient = s.vs_transient
Proof
  simp[consume_call_outcome_eq, adopt_outcome_def] >>
  strip_tac >> gvs[]
QED

Theorem consume_computed_call_accounts:
  computed_precompile rq /\ rq.cr_kind = MessageCall /\
  rq.cr_accounts = s.vs_accounts /\ rq.cr_tStorage = s.vs_transient ==>
  (SND (consume_call_outcome rq ro rz s)).vs_accounts = s.vs_accounts /\
  (SND (consume_call_outcome rq ro rz s)).vs_transient = s.vs_transient
Proof
  strip_tac >>
  simp[consume_call_outcome_eq, adopt_outcome_def] >>
  Cases_on `s.vs_outcomes` >> simp[take_outcome_def, failed_outcome_def] >>
  Cases_on `precompile_result rq.cr_target rq.cr_data` >> simp[] >>
  rename1 `precompile_result _ _ = SOME result` >>
  Cases_on `result` >> simp[failed_outcome_def] >>
  rename1 `s.vs_outcomes = outcome::rest` >>
  Cases_on `outcome.co_success` >> simp[failed_outcome_def]
QED

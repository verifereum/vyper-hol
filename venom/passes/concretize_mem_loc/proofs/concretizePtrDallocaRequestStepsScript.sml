Theory concretizePtrDallocaRequestSteps
Ancestors
  concretizePtrRequestHistory concretizePtrTaintContent concretizePtrSharedFields
  concretizePtrOpaqueRetpc ptrDiscipline venomExecSemantics venomCallOracleDefs
  venomState venomInst contextCodegenRel extCallOracle words list pred_set

(* The descriptor below contains only evaluated input operands and the request
   built from the pre-state, never a source outgoing execution.  Gas and memory
   offsets are source-local; request shell agreement is the relative-content
   boundary.  In particular neither equal pointers nor equal accounts is used. *)
Theorem ptr_dalloca_request_execution:
  inst.inst_outputs = [out] /\
  ((inst.inst_opcode = CALL /\
    LIST_REL (\op w. eval_operand op s = SOME w) inst.inst_operands
      [gas;addr;value;ao;az;ro;rz] /\
    (s.vs_call_ctx.cc_static ==> value = 0w) /\
    rq = venom_call_request s addr value ao az s.vs_call_ctx.cc_static) \/
   (inst.inst_opcode = STATICCALL /\
    LIST_REL (\op w. eval_operand op s = SOME w) inst.inst_operands
      [gas;addr;ao;az;ro;rz] /\
    rq = venom_call_request s addr 0w ao az T) \/
   (inst.inst_opcode = DELEGATECALL /\
    LIST_REL (\op w. eval_operand op s = SOME w) inst.inst_operands
      [gas;addr;ao;az;ro;rz] /\
    rq = (venom_call_request s addr 0w ao az F with cr_kind := DelegateMessageCall)) \/
   (inst.inst_opcode = CREATE /\ ~s.vs_call_ctx.cc_static /\
    LIST_REL (\op w. eval_operand op s = SOME w) inst.inst_operands
      [value;ao;az] /\ w2n az <= 2 * max_code_size /\
    rq = venom_create_request s value ao az NONE) \/
   (inst.inst_opcode = CREATE2 /\ ~s.vs_call_ctx.cc_static /\
    LIST_REL (\op w. eval_operand op s = SOME w) inst.inst_operands
      [value;ao;az;salt] /\ w2n az <= 2 * max_code_size /\
    rq = venom_create_request s value ao az (SOME salt))) ==>
  ?sh. step_inst fuel CS inst s = OK sh /\
       sh.vs_requests = record_request rq s.vs_requests /\
       sh.vs_call_ctx = s.vs_call_ctx
Proof
  strip_tac >>
  gvs[LIST_REL_CONS2] >>
  simp[Once step_inst_non_invoke, Excl "consume_call_outcome_eq",
       Excl "consume_create_outcome_eq"] >>
  pure_rewrite_tac[step_inst_base_def] >> asm_rewrite_tac[] >>
  simp[eval_operands_def, exec_ext_call_def, exec_delegatecall_def,
       exec_create_def, Excl "consume_call_outcome_eq",
       Excl "consume_create_outcome_eq"] >>
  pairarg_tac >> gvs[Excl "consume_call_outcome_eq",
                    Excl "consume_create_outcome_eq"] >>
  gvs[consume_call_outcome_eq, consume_create_outcome_eq, update_var_def] >>
  Cases_on `s.vs_call_ctx.cc_static` >> gvs[]
QED

Theorem ptr_dalloca_request_step:
  frame_reachable vs CS stk PG G tn fn inst s /\ active_inst fn inst s /\
  ptr_history_content tn s t /\
  un.t_stor SUBSET tn.t_stor /\ un.t_trans SUBSET tn.t_trans /\
  inst.inst_outputs = [out] /\ inst.inst_opcode = it.inst_opcode /\
  step_inst fuelt CT it t = OK th /\ th.vs_requests <> t.vs_requests /\
  th.vs_requests = record_request rqt t.vs_requests /\
  ptr_request_shell rq rqt /\
  ((inst.inst_opcode = CALL /\
    LIST_REL (\op w. eval_operand op s = SOME w) inst.inst_operands
      [gas;addr;value;ao;az;ro;rz] /\
    (s.vs_call_ctx.cc_static ==> value = 0w) /\
    rq = venom_call_request s addr value ao az s.vs_call_ctx.cc_static) \/
   (inst.inst_opcode = STATICCALL /\
    LIST_REL (\op w. eval_operand op s = SOME w) inst.inst_operands
      [gas;addr;ao;az;ro;rz] /\
    rq = venom_call_request s addr 0w ao az T) \/
   (inst.inst_opcode = DELEGATECALL /\
    LIST_REL (\op w. eval_operand op s = SOME w) inst.inst_operands
      [gas;addr;ao;az;ro;rz] /\
    rq = (venom_call_request s addr 0w ao az F with cr_kind := DelegateMessageCall)) \/
   (inst.inst_opcode = CREATE /\ ~s.vs_call_ctx.cc_static /\
    LIST_REL (\op w. eval_operand op s = SOME w) inst.inst_operands
      [value;ao;az] /\ w2n az <= 2 * max_code_size /\
    rq = venom_create_request s value ao az NONE) \/
   (inst.inst_opcode = CREATE2 /\ ~s.vs_call_ctx.cc_static /\
    LIST_REL (\op w. eval_operand op s = SOME w) inst.inst_operands
      [value;ao;az;salt] /\ w2n az <= 2 * max_code_size /\
    rq = venom_create_request s value ao az (SOME salt))) ==>
  ?sh. step_inst fuel CS inst s = OK sh /\
       sh.vs_requests <> s.vs_requests /\
       t.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address /\
       storage_agree_except tn.t_stor
         (s.vs_accounts s.vs_call_ctx.cc_address).storage
         (t.vs_accounts t.vs_call_ctx.cc_address).storage /\
       storage_agree_except tn.t_trans
         (s.vs_transient s.vs_call_ctx.cc_address)
         (t.vs_transient t.vs_call_ctx.cc_address) /\
       un.t_stor SUBSET tn.t_stor /\ un.t_trans SUBSET tn.t_trans
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ptr_dalloca_request_execution >>
  disch_then (qspecl_then [`fuel`,`CS`] strip_assume_tac) >>
  `ptr_request_history s.vs_requests t.vs_requests` by
    gvs[ptr_history_content_def] >>
  drule_all ptr_request_record_change >> strip_tac >>
  qexists `sh` >>
  gvs[ptr_history_content_def, ptr_taint_content_def, ptr_taint_control_def,
      ptr_core_shared_def, ptr_shared_fields_def,
      contract_storage_def, contract_transient_def, vfmStateTheory.lookup_account_def]
QED

Theory readonlyInvokeCopyFwdStepsExternalErrors
Ancestors
  readonlyInvokeCopyFwdStepsControl venomExecSemantics venomState
  venomInst venomExecProofs words list
Libs
  stepInstBaseLib

Theorem ricf_ext_call_error_iff:
  exec_ext_call inst s gas addr value ao az ro rz static = Error e <=>
  ~(?out. inst.inst_outputs = [out]) /\
  e = "ext_call requires single output"
Proof
  simp[exec_ext_call_def] >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  rename1 `h::tl` >> Cases_on `tl` >> simp[]
QED

Theorem ricf_create_error_iff:
  exec_create inst s value off sz salt = Error e <=>
  ~(?out. inst.inst_outputs = [out]) /\
  e = "create requires single output"
Proof
  Cases_on `inst.inst_outputs` >> simp[exec_create_def] >>
  rename1 `h::tl` >> Cases_on `tl` >> simp[exec_create_def] >>
  IF_CASES_TAC >> simp[] >> pairarg_tac >> simp[]
QED

Theorem ricf_delegatecall_error_iff:
  exec_delegatecall inst s gas addr ao az ro rz = Error e <=>
  ~(?out. inst.inst_outputs = [out]) /\
  e = "delegatecall requires single output"
Proof
  Cases_on `inst.inst_outputs` >> simp[exec_delegatecall_def] >>
  rename1 `h::tl` >> Cases_on `tl` >> simp[exec_delegatecall_def] >>
  pairarg_tac >> simp[]
QED

Theorem ricf_delegatecall_error:
  exec_delegatecall inst s gas addr ao az ro rz = Error e ==>
  exec_delegatecall inst t gas' addr' ao' az' ro' rz' = Error e
Proof
  simp[ricf_delegatecall_error_iff]
QED

Theorem ricf_staticcall_error:
  inst.inst_opcode = STATICCALL /\
  (!op. MEM op inst.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)) /\
  step_inst_base inst s = Error e ==> step_inst_base inst t = Error e
Proof
  strip_tac >> with_opcode_clause (fn ths => gvs(ths @ [AllCaseEqs(), ricf_ext_call_error_iff])) >>
  fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `eval_operand gas_op t` >> Cases_on `eval_operand addr_op t` >>
  Cases_on `eval_operand ao_op t` >> Cases_on `eval_operand as_op t` >>
  Cases_on `eval_operand ro_op t` >> Cases_on `eval_operand rs_op t` >>
  gvs[ricf_ext_call_error_iff] >> metis_tac[optionTheory.NOT_SOME_NONE]
QED

Theorem ricf_call_error:
  inst.inst_opcode = CALL /\
  (!op. MEM op inst.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)) /\
  s.vs_call_ctx.cc_static = t.vs_call_ctx.cc_static /\
  (!g a v ao az ro rz value value'.
    inst.inst_operands = [g;a;v;ao;az;ro;rz] /\
    eval_operand v s = SOME value /\ eval_operand v t = SOME value' ==>
    (value = 0w <=> value' = 0w)) /\
  step_inst_base inst s = Error e ==> step_inst_base inst t = Error e
Proof
  strip_tac >> with_opcode_clause (fn ths => gvs(ths @ [AllCaseEqs(), ricf_ext_call_error_iff])) >>
  fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `eval_operand gas_op t` >> gvs[] >>
  Cases_on `eval_operand addr_op t` >> gvs[] >>
  Cases_on `eval_operand val_op t` >> gvs[] >>
  Cases_on `eval_operand ao_op t` >> gvs[] >>
  Cases_on `eval_operand as_op t` >> gvs[] >>
  Cases_on `eval_operand ro_op t` >> gvs[] >>
  Cases_on `eval_operand rs_op t` >>
  gvs[ricf_ext_call_error_iff] >> metis_tac[optionTheory.NOT_SOME_NONE]
QED

Theorem ricf_create_error:
  inst.inst_opcode = CREATE /\
  (!op. MEM op inst.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)) /\
  s.vs_call_ctx.cc_static = t.vs_call_ctx.cc_static /\
  step_inst_base inst s = Error e ==> step_inst_base inst t = Error e
Proof
  strip_tac >>
  `IS_SOME (eval_operands inst.inst_operands s) <=>
   IS_SOME (eval_operands inst.inst_operands t)` by
    (simp[eval_operands_IS_SOME_EVERY, EVERY_MEM,
          optionTheory.IS_SOME_EQ_NOT_NONE] >> metis_tac[]) >>
  with_opcode_clause (fn ths => gvs(ths @ [AllCaseEqs(), ricf_create_error_iff])) >>
  Cases_on `eval_operand val_op t` >> Cases_on `eval_operand off_op t` >>
  Cases_on `eval_operand sz_op t` >>
  gvs[ricf_create_error_iff, optionTheory.IS_SOME_EQ_NOT_NONE] >>
  metis_tac[optionTheory.NOT_SOME_NONE]
QED

Theorem ricf_create2_error:
  inst.inst_opcode = CREATE2 /\
  (!op. MEM op inst.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)) /\
  s.vs_call_ctx.cc_static = t.vs_call_ctx.cc_static /\
  step_inst_base inst s = Error e ==> step_inst_base inst t = Error e
Proof
  strip_tac >>
  `IS_SOME (eval_operands inst.inst_operands s) <=>
   IS_SOME (eval_operands inst.inst_operands t)` by
    (simp[eval_operands_IS_SOME_EVERY, EVERY_MEM,
          optionTheory.IS_SOME_EQ_NOT_NONE] >> metis_tac[]) >>
  with_opcode_clause (fn ths => gvs(ths @ [AllCaseEqs(), ricf_create_error_iff])) >>
  Cases_on `eval_operand val_op t` >> Cases_on `eval_operand off_op t` >>
  Cases_on `eval_operand sz_op t` >> Cases_on `eval_operand salt_op t` >>
  gvs[ricf_create_error_iff, optionTheory.IS_SOME_EQ_NOT_NONE] >>
  metis_tac[optionTheory.NOT_SOME_NONE]
QED

Theorem ricf_delegatecall_dispatch_error:
  inst.inst_opcode = DELEGATECALL /\
  (!op. MEM op inst.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)) /\
  step_inst_base inst s = Error e ==> step_inst_base inst t = Error e
Proof
  strip_tac >> with_opcode_clause (fn ths => gvs(ths @ [AllCaseEqs()])) >>
  fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `eval_operand gas_op t` >> gvs[] >>
  Cases_on `eval_operand addr_op t` >> gvs[] >>
  Cases_on `eval_operand ao_op t` >> gvs[] >>
  Cases_on `eval_operand as_op t` >> gvs[] >>
  Cases_on `eval_operand ro_op t` >> gvs[] >>
  Cases_on `eval_operand rs_op t` >> gvs[] >>
  metis_tac[ricf_delegatecall_error, optionTheory.NOT_SOME_NONE]
QED

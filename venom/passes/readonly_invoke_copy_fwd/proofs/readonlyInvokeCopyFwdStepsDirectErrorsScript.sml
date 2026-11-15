Theory readonlyInvokeCopyFwdStepsDirectErrors
Ancestors
  readonlyInvokeCopyFwdStepsControl venomExecSemantics venomState
  o1LowerDloadOpaque fnFrameBoundaryInvoke list finite_map words

Theorem ricf_assign_error:
  inst.inst_opcode = ASSIGN /\
  (!op. MEM op inst.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)) /\
  step_inst_base inst s = Error e ==> step_inst_base inst t = Error e
Proof
  strip_tac >> gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  Cases_on `eval_operand op1 t` >> gvs[] >> metis_tac[optionTheory.NOT_SOME_NONE]
QED

Theorem ricf_alloca_error:
  inst.inst_opcode = ALLOCA /\ step_inst_base inst s = Error e ==>
  step_inst_base inst t = Error e
Proof
  strip_tac >> gvs[step_inst_base_opcode_eqs, exec_alloca_def, AllCaseEqs()]
QED

Theorem ricf_getfmp_error:
  inst.inst_opcode = GETFMP /\ step_inst_base inst s = Error e ==>
  step_inst_base inst t = Error e
Proof
  strip_tac >> gvs[step_inst_base_opcode_eqs, AllCaseEqs()]
QED

Theorem ricf_initial_fmp_error:
  inst.inst_opcode = INITIAL_FMP /\ step_inst_base inst s = Error e ==>
  step_inst_base inst t = Error e
Proof
  strip_tac >> gvs[step_inst_base_opcode_eqs, AllCaseEqs()]
QED

Theorem ricf_retpc_param_error:
  inst.inst_opcode = RETPC_PARAM /\ step_inst_base inst s = Error e ==>
  step_inst_base inst t = Error e
Proof
  strip_tac >> gvs[step_inst_base_opcode_eqs, AllCaseEqs()]
QED

Theorem ricf_setfmp_error:
  inst.inst_opcode = SETFMP /\
  (!op. MEM op inst.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)) /\
  step_inst_base inst s = Error e ==> step_inst_base inst t = Error e
Proof
  strip_tac >> gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  Cases_on `eval_operand op t` >> gvs[] >> metis_tac[optionTheory.NOT_SOME_NONE]
QED

Theorem ricf_dalloca_error:
  inst.inst_opcode = DALLOCA /\
  (!op. MEM op inst.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)) /\
  step_inst_base inst s = Error e ==> step_inst_base inst t = Error e
Proof
  strip_tac >> gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  Cases_on `eval_operand size_op t` >> gvs[] >> metis_tac[optionTheory.NOT_SOME_NONE]
QED

Theorem ricf_bump_error:
  inst.inst_opcode = BUMP /\
  (!op. MEM op inst.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)) /\
  step_inst_base inst s = Error e ==> step_inst_base inst t = Error e
Proof
  strip_tac >> gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  Cases_on `eval_operand base_op t` >> Cases_on `eval_operand size_op t` >>
  gvs[] >> metis_tac[optionTheory.NOT_SOME_NONE]
QED

Theorem ricf_param_error:
  inst.inst_opcode = PARAM /\ LENGTH s.vs_params = LENGTH t.vs_params /\
  step_inst_base inst s = Error e ==> step_inst_base inst t = Error e
Proof
  strip_tac >> gvs[step_inst_base_opcode_eqs, AllCaseEqs()]
QED

Theorem ricf_fmp_param_error:
  inst.inst_opcode = FMP_PARAM /\ LENGTH s.vs_params = LENGTH t.vs_params /\
  step_inst_base inst s = Error e ==> step_inst_base inst t = Error e
Proof
  strip_tac >> gvs[step_inst_base_opcode_eqs, AllCaseEqs()]
QED

Theorem ricf_mcopy_error:
  inst.inst_opcode = MCOPY /\
  (!op. MEM op inst.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)) /\
  step_inst_base inst s = Error e ==> step_inst_base inst t = Error e
Proof
  strip_tac >> gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  Cases_on `eval_operand op_dst t` >> Cases_on `eval_operand op_src t` >>
  Cases_on `eval_operand op_size t` >>
  gvs[] >> metis_tac[optionTheory.NOT_SOME_NONE]
QED

Theorem ricf_calldatacopy_error:
  inst.inst_opcode = CALLDATACOPY /\
  (!op. MEM op inst.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)) /\
  step_inst_base inst s = Error e ==> step_inst_base inst t = Error e
Proof
  strip_tac >> gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  Cases_on `eval_operand op_destOffset t` >> Cases_on `eval_operand op_offset t` >>
  Cases_on `eval_operand op_size t` >>
  gvs[] >> metis_tac[optionTheory.NOT_SOME_NONE]
QED

Theorem ricf_returndatacopy_error:
  inst.inst_opcode = RETURNDATACOPY /\
  (!op. MEM op inst.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)) /\
  step_inst_base inst s = Error e ==> step_inst_base inst t = Error e
Proof
  strip_tac >> gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  Cases_on `eval_operand op_destOffset t` >> Cases_on `eval_operand op_offset t` >>
  Cases_on `eval_operand op_size t` >>
  gvs[] >> metis_tac[optionTheory.NOT_SOME_NONE]
QED

Theorem ricf_dloadbytes_error:
  inst.inst_opcode = DLOADBYTES /\
  (!op. MEM op inst.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)) /\
  step_inst_base inst s = Error e ==> step_inst_base inst t = Error e
Proof
  strip_tac >> gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  Cases_on `eval_operand op_dst t` >> Cases_on `eval_operand op_src t` >>
  Cases_on `eval_operand op_size t` >>
  gvs[] >> metis_tac[optionTheory.NOT_SOME_NONE]
QED

Theorem ricf_codecopy_error:
  inst.inst_opcode = CODECOPY /\
  (!op. MEM op inst.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)) /\
  step_inst_base inst s = Error e ==> step_inst_base inst t = Error e
Proof
  strip_tac >> gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  Cases_on `eval_operand op_dst t` >> Cases_on `eval_operand op_src t` >>
  Cases_on `eval_operand op_size t` >>
  gvs[] >> metis_tac[optionTheory.NOT_SOME_NONE]
QED

Theorem ricf_extcodecopy_error:
  inst.inst_opcode = EXTCODECOPY /\
  (!op. MEM op inst.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)) /\
  step_inst_base inst s = Error e ==> step_inst_base inst t = Error e
Proof
  strip_tac >> gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  Cases_on `eval_operand op_addr t` >>
  Cases_on `eval_operand op_dst t` >> Cases_on `eval_operand op_src t` >>
  Cases_on `eval_operand op_size t` >>
  gvs[] >> metis_tac[optionTheory.NOT_SOME_NONE]
QED

Theorem ricf_istore_error:
  inst.inst_opcode = ISTORE /\
  (!op. MEM op inst.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)) /\
  step_inst_base inst s = Error e ==> step_inst_base inst t = Error e
Proof
  strip_tac >> gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  Cases_on `eval_operand offset_op t` >> Cases_on `eval_operand val_op t` >>
  gvs[] >> metis_tac[optionTheory.NOT_SOME_NONE]
QED

Theorem ricf_sha3_error:
  inst.inst_opcode = SHA3 /\
  (!op. MEM op inst.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)) /\
  step_inst_base inst s = Error e ==> step_inst_base inst t = Error e
Proof
  strip_tac >> gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  Cases_on `eval_operand op_offset t` >> Cases_on `eval_operand op_size t` >>
  gvs[] >> metis_tac[optionTheory.NOT_SOME_NONE]
QED

Theorem ricf_dret_error:
  inst.inst_opcode = DRET /\
  (!op. MEM op inst.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)) /\
  step_inst_base inst s = Error e ==> step_inst_base inst t = Error e
Proof
  strip_tac >>
  `IS_SOME (eval_operands inst.inst_operands s) <=>
   IS_SOME (eval_operands inst.inst_operands t)` by
    (irule eval_operands_defined_iff >> rpt strip_tac >>
     first_x_assum drule >> Cases_on `eval_operand op s` >>
     Cases_on `eval_operand op t` >> simp[]) >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  TRY (pairarg_tac >> gvs[] >> NO_TAC) >>
  Cases_on `eval_operands inst.inst_operands t` >> gvs[] >>
  imp_res_tac eval_operands_some_length >>
  `LENGTH (TAKE (2 * dynamic) (DROP (1 + ordinary) vals)) =
   LENGTH (TAKE (2 * dynamic) (DROP (1 + ordinary) x))` by simp[LENGTH_TAKE_EQ, LENGTH_DROP] >>
  drule pair_dret_words_none_length >> simp[]
QED

Theorem ricf_sstore_error:
  inst.inst_opcode = SSTORE /\
  s.vs_call_ctx.cc_static = t.vs_call_ctx.cc_static /\
  (!op. MEM op inst.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)) /\
  step_inst_base inst s = Error e ==> step_inst_base inst t = Error e
Proof
  strip_tac >>
  `IS_SOME (eval_operands inst.inst_operands s) <=>
   IS_SOME (eval_operands inst.inst_operands t)` by
    (irule eval_operands_defined_iff >> rpt strip_tac >>
     first_x_assum drule >> Cases_on `eval_operand op s` >>
     Cases_on `eval_operand op t` >> simp[]) >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  irule ricf_write2_error >> metis_tac[]
QED

Theorem ricf_tstore_error:
  inst.inst_opcode = TSTORE /\
  s.vs_call_ctx.cc_static = t.vs_call_ctx.cc_static /\
  (!op. MEM op inst.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)) /\
  step_inst_base inst s = Error e ==> step_inst_base inst t = Error e
Proof
  strip_tac >>
  `IS_SOME (eval_operands inst.inst_operands s) <=>
   IS_SOME (eval_operands inst.inst_operands t)` by
    (irule eval_operands_defined_iff >> rpt strip_tac >>
     first_x_assum drule >> Cases_on `eval_operand op s` >>
     Cases_on `eval_operand op t` >> simp[]) >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  irule ricf_write2_error >> metis_tac[]
QED

Theorem ricf_selfdestruct_error:
  inst.inst_opcode = SELFDESTRUCT /\
  s.vs_call_ctx.cc_static = t.vs_call_ctx.cc_static /\
  (!op. MEM op inst.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)) /\
  step_inst_base inst s = Error e ==> step_inst_base inst t = Error e
Proof
  strip_tac >>
  `IS_SOME (eval_operands inst.inst_operands s) <=>
   IS_SOME (eval_operands inst.inst_operands t)` by
    (irule eval_operands_defined_iff >> rpt strip_tac >>
     first_x_assum drule >> Cases_on `eval_operand op s` >>
     Cases_on `eval_operand op t` >> simp[]) >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  Cases_on `eval_operand addr_op t` >> gvs[] >> metis_tac[optionTheory.NOT_SOME_NONE]
QED

Theorem ricf_log_error:
  inst.inst_opcode = LOG /\
  s.vs_call_ctx.cc_static = t.vs_call_ctx.cc_static /\
  (!op. MEM op inst.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)) /\
  step_inst_base inst s = Error e ==> step_inst_base inst t = Error e
Proof
  strip_tac >>
  `IS_SOME (eval_operands inst.inst_operands s) <=>
   IS_SOME (eval_operands inst.inst_operands t)` by
    (irule eval_operands_defined_iff >> rpt strip_tac >>
     first_x_assum drule >> Cases_on `eval_operand op s` >>
     Cases_on `eval_operand op t` >> simp[]) >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  `MEM (EL 0 (REVERSE rest)) rest /\ MEM (EL 1 (REVERSE rest)) rest` by
    (once_rewrite_tac[GSYM MEM_REVERSE] >> conj_tac >> irule EL_MEM >> simp[]) >>
  `IS_SOME (eval_operands (DROP 2 (REVERSE rest)) s) <=>
   IS_SOME (eval_operands (DROP 2 (REVERSE rest)) t)` by
    (irule eval_operands_defined_iff >> rpt strip_tac >>
     `MEM op rest` by
       (drule rich_listTheory.MEM_DROP_IMP >> simp[]) >>
     qpat_x_assum `!op. _` (qspec_then `op` mp_tac) >>
     simp[] >> Cases_on `eval_operand op s` >>
     Cases_on `eval_operand op t` >> simp[]) >>
  Cases_on `eval_operand (EL 0 (REVERSE rest)) t` >>
  Cases_on `eval_operand (EL 1 (REVERSE rest)) t` >>
  Cases_on `eval_operands (DROP 2 (REVERSE rest)) t` >>
  gvs[] >> metis_tac[optionTheory.NOT_SOME_NONE]
QED

Theorem ricf_ret_error:
  inst.inst_opcode = RET /\
  (!op. MEM op inst.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)) /\
  step_inst_base inst s = Error e ==> step_inst_base inst t = Error e
Proof
  strip_tac >>
  `IS_SOME (eval_operands inst.inst_operands s) <=>
   IS_SOME (eval_operands inst.inst_operands t)` by
    (irule eval_operands_defined_iff >> rpt strip_tac >>
     first_x_assum drule >> Cases_on `eval_operand op s` >>
     Cases_on `eval_operand op t` >> simp[]) >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  Cases_on `eval_operands inst.inst_operands t` >> gvs[] >>
  imp_res_tac eval_operands_some_length >> gvs[eval_operands_def]
QED

Theorem ricf_retfmp_error:
  inst.inst_opcode = RETFMP /\
  (!op. MEM op inst.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)) /\
  step_inst_base inst s = Error e ==> step_inst_base inst t = Error e
Proof
  strip_tac >>
  `IS_SOME (eval_operands inst.inst_operands s) <=>
   IS_SOME (eval_operands inst.inst_operands t)` by
    (irule eval_operands_defined_iff >> rpt strip_tac >>
     first_x_assum drule >> Cases_on `eval_operand op s` >>
     Cases_on `eval_operand op t` >> simp[]) >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  Cases_on `eval_operands inst.inst_operands t` >> gvs[] >>
  imp_res_tac eval_operands_some_length >> gvs[eval_operands_def]
QED

Theorem ricf_return_error:
  inst.inst_opcode = RETURN /\
  (!op. MEM op inst.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)) /\
  step_inst_base inst s = Error e ==> step_inst_base inst t = Error e
Proof
  strip_tac >> gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  Cases_on `eval_operand off_op t` >> Cases_on `eval_operand sz_op t` >>
  gvs[] >> metis_tac[optionTheory.NOT_SOME_NONE]
QED

Theorem ricf_revert_error:
  inst.inst_opcode = REVERT /\
  (!op. MEM op inst.inst_operands ==>
    (eval_operand op s = NONE <=> eval_operand op t = NONE)) /\
  step_inst_base inst s = Error e ==> step_inst_base inst t = Error e
Proof
  strip_tac >> gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  Cases_on `eval_operand off_op t` >> Cases_on `eval_operand sz_op t` >>
  gvs[] >> metis_tac[optionTheory.NOT_SOME_NONE]
QED

Theorem ricf_gas_error:
  inst.inst_opcode = GAS /\ step_inst_base inst s = Error e ==>
  step_inst_base inst t = Error e
Proof
  strip_tac >> gvs[step_inst_base_opcode_eqs, exec_gas_def, AllCaseEqs()]
QED

Theory concretizeAnalysisSuccessfulWrites
Ancestors
  concretizeAnalysisWriteSafety concretizePtrProtectedPrefix concretizePtrReadCoverage
  concretizeMemLocDefs memLocDefs ptrDiscipline venomExecSemantics
  venomState venomInst finite_map pred_set

Theorem literal_write_success_ready:
  inst_write_size inst = SOME n /\ step_inst fuel ctx inst s = OK s' ==>
  ?vals. eval_operands inst.inst_operands s = SOME vals
Proof
  Cases_on `inst.inst_opcode` >>
  simp[inst_write_size_def, mem_write_ops_def] >>
  rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [Once step_inst_def] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs, exec_write2_def] >>
  strip_tac >>
  gvs[AllCaseEqs(), eval_operands_def]
QED

Theorem literal_write_step_ranges:
  inst_write_size inst = SOME n ==>
  step_writes inst s s' = source_memory_write_ranges inst s
Proof
  Cases_on `inst.inst_opcode` >>
  simp[step_writes_def, inst_write_size_def, mem_write_ops_def] >>
  strip_tac >> gvs[AllCaseEqs()] >> gvs[]
QED

Theorem literal_write_ready_destination[local]:
  inst_write_size inst = SOME n /\ mem_write_ops inst = SOME ops /\
  eval_operands inst.inst_operands s = SOME vals ==>
  ?dst. eval_operand ops.iao_ofst s = SOME dst
Proof
  Cases_on `inst.inst_opcode` >>
  simp[inst_write_size_def, mem_write_ops_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> gvs[eval_operands_def, AllCaseEqs()]
QED

Theorem successful_full_write_covers:
  inst_write_size inst = SOME sz /\ step_inst fuel ctx inst s = OK s' /\
  mem_write_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
  FLOOKUP G v = SOME (b,sz) /\ access_ok lo G fn inst s /\
  ~in_revert_forward fn s /\ b <= byte /\ byte < b + sz ==>
  byte IN range_bytes (step_writes inst s s')
Proof
  strip_tac >>
  `?vals. eval_operands inst.inst_operands s = SOME vals` by
    metis_tac[literal_write_success_ready] >>
  `?dst. eval_operand ops.iao_ofst s = SOME dst` by
    metis_tac[literal_write_ready_destination] >>
  `MEM (w2n dst,sz) (source_memory_write_ranges inst s)` by
    metis_tac[ptr_ready_literal_write_range] >>
  `sz <> 0` by decide_tac >>
  `w2n dst = b` by metis_tac[access_ok_full_write_start] >>
  `step_writes inst s s' = source_memory_write_ranges inst s` by
    metis_tac[literal_write_step_ranges] >>
  simp[range_bytes_def] >> qexistsl_tac [`b`,`sz`] >> simp[arithmeticTheory.ADD_COMM] >> metis_tac[]
QED

Theorem successful_protected_byte_no_kill:
  sizes a = SOME sz /\ step_inst fuel ctx inst s = OK s' /\
  mem_write_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
  FLOOKUP G v = SOME (b,sz) /\ access_ok lo G fn inst s /\
  ~in_revert_forward fn s /\ b <= byte /\ byte < b + sz /\
  byte NOTIN range_bytes (step_writes inst s s') ==>
  ~ptr_ml_can_kill a bp sizes inst
Proof
  rpt strip_tac >>
  `inst_write_size inst = SOME sz` by gvs[ptr_ml_can_kill_def] >>
  metis_tac[successful_full_write_covers]
QED

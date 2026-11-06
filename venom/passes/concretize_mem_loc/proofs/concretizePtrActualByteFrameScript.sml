Theory concretizePtrActualByteFrame
Ancestors regularCallEmitSim stepWriteFootprintBase ptrDiscipline venomMemProps venomExecSemantics
  venomCallOracleDefs codegenRel venomState venomInst list pred_set arithmetic

Theorem ptr_extract_venom_result_actual_byte_frame:
  extract_venom_result s output ro rz result = SOME (value,t) /\
  ~(ro <= x /\ x < ro + MIN rz (LENGTH t.vs_returndata)) ==>
  read_byte x t.vs_memory = read_byte x s.vs_memory
Proof
  strip_tac >> drule extract_venom_result_memory >>
  disch_then (fn th => once_rewrite_tac[th]) >>
  irule write_memory_byte_frame >>
  qexists `LENGTH (TAKE rz t.vs_returndata)` >>
  gvs[LENGTH_TAKE_EQ, MIN_DEF]
QED

Theorem ptr_exec_ext_call_actual_byte_frame:
  exec_ext_call inst s gas addr value ao az ro rz static = OK t /\
  ~(w2n ro <= x /\ x < w2n ro + MIN (w2n rz) (LENGTH t.vs_returndata)) ==>
  read_byte x t.vs_memory = read_byte x s.vs_memory
Proof
  simp[exec_ext_call_def, consume_call_outcome_eq] >>
  strip_tac >> gvs[AllCaseEqs(), update_var_def] >>
  qmatch_goalsub_abbrev_tac `write_memory_with_expansion (w2n ro) bytes s` >>
  irule write_memory_byte_frame >> qexists `LENGTH bytes` >>
  gvs[Abbr `bytes`, LENGTH_TAKE_EQ, MIN_DEF]
QED

Theorem ptr_exec_delegatecall_actual_byte_frame:
  exec_delegatecall inst s gas addr ao az ro rz = OK t /\
  ~(w2n ro <= x /\ x < w2n ro + MIN (w2n rz) (LENGTH t.vs_returndata)) ==>
  read_byte x t.vs_memory = read_byte x s.vs_memory
Proof
  strip_tac >>
  qpat_x_assum `exec_delegatecall _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[exec_delegatecall_def, AllCaseEqs()] >> strip_tac >>
  gvs[update_var_def] >> metis_tac[ptr_extract_venom_result_actual_byte_frame]
QED

Theorem ptr_step_inst_base_OK_actual_byte_frame:
  step_inst_base inst s = OK t /\
  x NOTIN range_bytes (step_writes inst s t) ==>
  read_byte x t.vs_memory = read_byte x s.vs_memory
Proof
  strip_tac >>
  Cases_on `inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL \/
            inst.inst_opcode = DELEGATECALL`
  >- (gvs[] >> qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
      asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
      strip_tac >> gvs[AllCaseEqs()] >>
      gvs[step_writes_def, source_memory_write_ranges_def, range_bytes_def] >>
      metis_tac[ptr_exec_ext_call_actual_byte_frame,
                ptr_exec_delegatecall_actual_byte_frame]) >>
  irule step_inst_base_OK_byte_frame >>
  qexists `inst` >> simp[] >>
  gvs[step_writes_def, range_bytes_def] >> metis_tac[ADD_COMM]
QED

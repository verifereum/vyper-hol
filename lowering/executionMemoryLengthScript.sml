(* Physical memory growth, independent of compiler policy. *)
Theory executionMemoryLength
Ancestors
  venomExecSemantics venomMemProps venomState venomCallOracleDefs
  calleeTransport list arithmetic

Theorem pack_dret_dynamic_memory_length[local]:
  !pairs cursor s ptrs last t.
    pack_dret_dynamic cursor pairs s = (ptrs,last,t) ==>
    LENGTH s.vs_memory <= LENGTH t.vs_memory
Proof
  Induct >> simp[pack_dret_dynamic_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[pack_dret_dynamic_def] >> pairarg_tac >> simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  irule LESS_EQ_TRANS >> goal_assum (drule_at Any) >>
  simp[mcopy_def, write_memory_with_expansion_nondecreasing]
QED

Theorem read_pure_memory_length[local]:
  (!f inst s. case exec_pure1 f inst s of
     OK t => LENGTH s.vs_memory <= LENGTH t.vs_memory
   | Halt t => LENGTH s.vs_memory <= LENGTH t.vs_memory
   | Abort a t => LENGTH s.vs_memory <= LENGTH t.vs_memory
   | IntRet ir t => LENGTH s.vs_memory <= LENGTH t.vs_memory | Error e => T) /\
  (!f inst s. case exec_pure2 f inst s of
     OK t => LENGTH s.vs_memory <= LENGTH t.vs_memory
   | Halt t => LENGTH s.vs_memory <= LENGTH t.vs_memory
   | Abort a t => LENGTH s.vs_memory <= LENGTH t.vs_memory
   | IntRet ir t => LENGTH s.vs_memory <= LENGTH t.vs_memory | Error e => T) /\
  (!f inst s. case exec_pure3 f inst s of
     OK t => LENGTH s.vs_memory <= LENGTH t.vs_memory
   | Halt t => LENGTH s.vs_memory <= LENGTH t.vs_memory
   | Abort a t => LENGTH s.vs_memory <= LENGTH t.vs_memory
   | IntRet ir t => LENGTH s.vs_memory <= LENGTH t.vs_memory | Error e => T) /\
  (!f inst s. case exec_read0 f inst s of
     OK t => LENGTH s.vs_memory <= LENGTH t.vs_memory
   | Halt t => LENGTH s.vs_memory <= LENGTH t.vs_memory
   | Abort a t => LENGTH s.vs_memory <= LENGTH t.vs_memory
   | IntRet ir t => LENGTH s.vs_memory <= LENGTH t.vs_memory | Error e => T) /\
  (!f inst s. case exec_read1 f inst s of
     OK t => LENGTH s.vs_memory <= LENGTH t.vs_memory
   | Halt t => LENGTH s.vs_memory <= LENGTH t.vs_memory
   | Abort a t => LENGTH s.vs_memory <= LENGTH t.vs_memory
   | IntRet ir t => LENGTH s.vs_memory <= LENGTH t.vs_memory | Error e => T) /\
  (!inst s. case exec_gas inst s of
     OK t => LENGTH s.vs_memory <= LENGTH t.vs_memory
   | Halt t => LENGTH s.vs_memory <= LENGTH t.vs_memory
   | Abort a t => LENGTH s.vs_memory <= LENGTH t.vs_memory
   | IntRet ir t => LENGTH s.vs_memory <= LENGTH t.vs_memory | Error e => T)
Proof
  rpt conj_tac >> rpt gen_tac >> BasicProvers.TOP_CASE_TAC >>
  gvs[exec_pure1_def, exec_pure2_def, exec_pure3_def,
      exec_read0_def, exec_read1_def, exec_gas_def,
      AllCaseEqs(), update_var_def]
QED

Theorem exec_write2_memory_length[local]:
  (!x y. LENGTH s.vs_memory <= LENGTH (f x y s).vs_memory) ==>
  case exec_write2 f inst s of
     OK t => LENGTH s.vs_memory <= LENGTH t.vs_memory
   | Halt t => LENGTH s.vs_memory <= LENGTH t.vs_memory
   | Abort a t => LENGTH s.vs_memory <= LENGTH t.vs_memory
   | IntRet ir t => LENGTH s.vs_memory <= LENGTH t.vs_memory | Error e => T
Proof
  strip_tac >> BasicProvers.TOP_CASE_TAC >>
  gvs[exec_write2_def, AllCaseEqs()]
QED

Theorem copy_opcode_memory_length[local]:
  (inst.inst_opcode = MCOPY \/ inst.inst_opcode = CALLDATACOPY \/
   inst.inst_opcode = RETURNDATACOPY \/ inst.inst_opcode = DLOADBYTES \/
   inst.inst_opcode = CODECOPY \/ inst.inst_opcode = EXTCODECOPY \/
   inst.inst_opcode = ISTORE) ==>
  case step_inst_base inst s of
     OK t => LENGTH s.vs_memory <= LENGTH t.vs_memory
   | Halt t => LENGTH s.vs_memory <= LENGTH t.vs_memory
   | Abort a t => LENGTH s.vs_memory <= LENGTH t.vs_memory
   | IntRet ir t => LENGTH s.vs_memory <= LENGTH t.vs_memory | Error e => T
Proof
  strip_tac >> asm_simp_tac bool_ss [step_inst_base_opcode_eqs] >>
  BasicProvers.TOP_CASE_TAC >>
  gvs[AllCaseEqs(), mcopy_def, istore_def, halt_state_def,
      set_returndata_def, write_memory_with_expansion_nondecreasing,
      mstore_memory_nondecreasing]
QED

Theorem control_opcode_memory_length[local]:
  (inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ \/
   inst.inst_opcode = DJMP \/ inst.inst_opcode = RET \/
   inst.inst_opcode = RETFMP \/ inst.inst_opcode = STOP \/
   inst.inst_opcode = RETURN \/ inst.inst_opcode = REVERT \/
   inst.inst_opcode = SINK \/ inst.inst_opcode = ASSERT \/
   inst.inst_opcode = ASSERT_UNREACHABLE \/ inst.inst_opcode = INVALID) ==>
  case step_inst_base inst s of
     OK t => LENGTH s.vs_memory <= LENGTH t.vs_memory
   | Halt t => LENGTH s.vs_memory <= LENGTH t.vs_memory
   | Abort a t => LENGTH s.vs_memory <= LENGTH t.vs_memory
   | IntRet ir t => LENGTH s.vs_memory <= LENGTH t.vs_memory | Error e => T
Proof
  strip_tac >> Cases_on `step_inst_base inst s` >> gvs[] >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs(), halt_state_def,
      revert_state_def, set_returndata_def, jump_to_def]
QED

Theorem frame_opcode_memory_length[local]:
  (inst.inst_opcode = GETFMP \/ inst.inst_opcode = SETFMP \/
   inst.inst_opcode = DALLOCA \/ inst.inst_opcode = INITIAL_FMP \/
   inst.inst_opcode = BUMP \/ inst.inst_opcode = FMP_PARAM \/
   inst.inst_opcode = RETPC_PARAM \/ inst.inst_opcode = PARAM \/
   inst.inst_opcode = PHI \/ inst.inst_opcode = ASSIGN \/
   inst.inst_opcode = NOP \/ inst.inst_opcode = SHA3 \/
   inst.inst_opcode = LOG \/ inst.inst_opcode = SELFDESTRUCT \/
   inst.inst_opcode = SSTORE \/ inst.inst_opcode = TSTORE) ==>
  case step_inst_base inst s of
     OK t => LENGTH s.vs_memory <= LENGTH t.vs_memory
   | Halt t => LENGTH s.vs_memory <= LENGTH t.vs_memory
   | Abort a t => LENGTH s.vs_memory <= LENGTH t.vs_memory
   | IntRet ir t => LENGTH s.vs_memory <= LENGTH t.vs_memory | Error e => T
Proof
  strip_tac >> Cases_on `step_inst_base inst s` >> gvs[] >>
  qpat_x_assum `step_inst_base inst s = _` mp_tac >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs] >> strip_tac >>
  gvs[AllCaseEqs(), halt_state_def, set_returndata_def,
      update_var_def, exec_write2_def, sstore_def, tstore_def]
QED

Theorem oracle_opcode_memory_length[local]:
  (inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL \/
   inst.inst_opcode = CREATE \/ inst.inst_opcode = CREATE2) ==>
  case step_inst_base inst s of
     OK t => LENGTH s.vs_memory <= LENGTH t.vs_memory
   | Halt t => LENGTH s.vs_memory <= LENGTH t.vs_memory
   | Abort a t => LENGTH s.vs_memory <= LENGTH t.vs_memory
   | IntRet ir t => LENGTH s.vs_memory <= LENGTH t.vs_memory | Error e => T
Proof
  strip_tac >> Cases_on `step_inst_base inst s` >> gvs[] >>
  qpat_x_assum `step_inst_base inst s = _` mp_tac >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs] >>
  simp[exec_ext_call_def, exec_create_def, AllCaseEqs(),
       update_var_def, halt_state_def, set_returndata_def,
       write_memory_with_expansion_nondecreasing] >>
  rpt strip_tac >> gvs[] >>
  irule write_memory_with_expansion_nondecreasing
QED

Theorem delegatecall_memory_length[local]:
  exec_delegatecall inst s gas addr ao az ro rz = r ==>
  case r of
     OK t => LENGTH s.vs_memory <= LENGTH t.vs_memory
   | Halt t => LENGTH s.vs_memory <= LENGTH t.vs_memory
   | Abort a t => LENGTH s.vs_memory <= LENGTH t.vs_memory
   | IntRet ir t => LENGTH s.vs_memory <= LENGTH t.vs_memory | Error e => T
Proof
  strip_tac >> Cases_on `r` >> gvs[] >>
  gvs[exec_delegatecall_def, extract_venom_result_def,
      AllCaseEqs(), update_var_def] >>
  pairarg_tac >> gvs[] >>
  irule write_memory_with_expansion_nondecreasing
QED

Theorem step_inst_base_memory_length[local]:
  !inst s. case step_inst_base inst s of
     OK t => LENGTH s.vs_memory <= LENGTH t.vs_memory
   | Halt t => LENGTH s.vs_memory <= LENGTH t.vs_memory
   | Abort a t => LENGTH s.vs_memory <= LENGTH t.vs_memory
   | IntRet ir t => LENGTH s.vs_memory <= LENGTH t.vs_memory | Error e => T
Proof
  rpt gen_tac >> Cases_on `inst.inst_opcode` >>
  simp[copy_opcode_memory_length, control_opcode_memory_length,
       frame_opcode_memory_length, oracle_opcode_memory_length] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, read_pure_memory_length] >>
  simp[exec_write2_memory_length, mstore_memory_nondecreasing,
       mstore8_memory_nondecreasing]
  >~ [`inst.inst_opcode = DELEGATECALL`]
  >- (BasicProvers.TOP_CASE_TAC >> gvs[AllCaseEqs()] >>
      drule delegatecall_memory_length >> simp[])
  >~ [`inst.inst_opcode = ALLOCA`]
  >- (BasicProvers.TOP_CASE_TAC >>
      gvs[exec_alloca_def, AllCaseEqs(), update_var_def]) >>
  BasicProvers.TOP_CASE_TAC >> gvs[AllCaseEqs()] >>
  pairarg_tac >> gvs[] >>
  drule pack_dret_dynamic_memory_length >> simp[]
QED

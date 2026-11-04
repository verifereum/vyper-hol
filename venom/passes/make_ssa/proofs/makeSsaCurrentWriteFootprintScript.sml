Theory makeSsaCurrentWriteFootprint
Ancestors
  venomExecSemantics venomCallOracleDefs venomWf venomState finite_map list rich_list

Definition current_output_writes_def:
  current_output_writes outs before after <=>
    ?writes. EVERY (\dv. MEM (FST dv) outs) writes /\
      after.vs_vars = FOLDL (\m dv. m |+ dv) before.vs_vars writes
End

Definition current_result_output_writes_def:
  current_result_output_writes outs before result <=>
    case result of
      OK after => current_output_writes outs before after
    | Halt after => current_output_writes outs before after
    | Abort reason after => current_output_writes outs before after
    | IntRet ret after => current_output_writes outs before after
    | Error msg => T
End

Theorem current_output_writes_unchanged:
  after.vs_vars = before.vs_vars ==> current_output_writes outs before after
Proof
  strip_tac >> simp[current_output_writes_def] >> qexists_tac `[]` >> simp[]
QED

Theorem current_output_writes_update:
  current_output_writes outs before after /\ MEM dst outs ==>
  current_output_writes outs before (update_var dst value after)
Proof
  simp[current_output_writes_def, update_var_def] >> rpt strip_tac >>
  qexists_tac `writes ++ [(dst,value)]` >> simp[FOLDL_APPEND]
QED

Theorem current_result_output_writes_constructors[simp]:
  (current_result_output_writes outs before (OK after) <=> current_output_writes outs before after) /\
  (current_result_output_writes outs before (Halt after) <=> current_output_writes outs before after) /\
  (current_result_output_writes outs before (Abort reason after) <=> current_output_writes outs before after) /\
  (current_result_output_writes outs before (IntRet ret after) <=> current_output_writes outs before after) /\
  current_result_output_writes outs before (Error msg)
Proof
  simp[current_result_output_writes_def]
QED

Theorem current_output_fold_lookup[local]:
  !writes m. EVERY (\dv. MEM (FST dv) outs) writes /\ ~MEM v outs ==>
  FLOOKUP (FOLDL (\m dv. m |+ dv) m writes) v = FLOOKUP m v
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> simp[FLOOKUP_UPDATE] >>
  PairCases_on `h` >> gvs[] >>
  `h0 <> v` by metis_tac[] >> simp[FLOOKUP_UPDATE]
QED

Theorem current_output_writes_lookup:
  current_output_writes outs before after /\ ~MEM v outs ==>
  lookup_var v after = lookup_var v before
Proof
  simp[current_output_writes_def, lookup_var_def] >> rpt strip_tac >>
  gvs[] >> irule current_output_fold_lookup >> qexists_tac `outs` >> simp[]
QED

Theorem current_single_output_writes:
  MEM dst outs ==> current_output_writes outs st (update_var dst value st)
Proof
  strip_tac >> irule current_output_writes_update >> simp[] >>
  irule current_output_writes_unchanged >> simp[]
QED

Theorem current_exec_read0_writes:
  current_result_output_writes inst.inst_outputs st (exec_read0 f inst st)
Proof
  Cases_on `inst.inst_outputs` >> simp[exec_read0_def] >>
  rename1 `h::t` >> Cases_on `t` >> simp[exec_read0_def] >>
  irule current_single_output_writes >> simp[]
QED

Theorem current_exec_pure1_writes:
  current_result_output_writes inst.inst_outputs st (exec_pure1 f inst st)
Proof
  Cases_on `inst.inst_operands` >> simp[exec_pure1_def] >>
  rename1 `h::t` >> Cases_on `t` >> simp[exec_pure1_def] >>
  Cases_on `eval_operand h st` >> simp[] >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  rename1 `out::rest` >> Cases_on `rest` >> simp[] >>
  irule current_single_output_writes >> simp[]
QED

Theorem current_exec_pure2_writes:
  current_result_output_writes inst.inst_outputs st (exec_pure2 f inst st)
Proof
  Cases_on `exec_pure2 f inst st` >>
  gvs[exec_pure2_def, AllCaseEqs()] >>
  irule current_single_output_writes >> simp[]
QED

Theorem current_exec_pure3_writes:
  current_result_output_writes inst.inst_outputs st (exec_pure3 f inst st)
Proof
  Cases_on `exec_pure3 f inst st` >>
  gvs[exec_pure3_def, AllCaseEqs()] >>
  irule current_single_output_writes >> simp[]
QED

Theorem current_exec_read1_writes:
  current_result_output_writes inst.inst_outputs st (exec_read1 f inst st)
Proof
  Cases_on `exec_read1 f inst st` >>
  gvs[exec_read1_def, AllCaseEqs()] >>
  irule current_single_output_writes >> simp[]
QED

Theorem current_exec_write2_writes:
  (!a b. (f a b st).vs_vars = st.vs_vars) ==>
  current_result_output_writes inst.inst_outputs st (exec_write2 f inst st)
Proof
  strip_tac >> Cases_on `exec_write2 f inst st` >>
  gvs[exec_write2_def, AllCaseEqs()] >>
  irule current_output_writes_unchanged >> simp[]
QED

Theorem current_output_writes_same_store:
  current_output_writes outs before middle /\ after.vs_vars = middle.vs_vars ==>
  current_output_writes outs before after
Proof
  simp[current_output_writes_def] >> metis_tac[]
QED

Theorem current_consume_call_vars:
  consume_call_outcome rq off sz st = (value,after) ==>
  after.vs_vars = st.vs_vars
Proof
  simp[consume_call_outcome_eq] >> rpt strip_tac >> gvs[]
QED

Theorem current_consume_create_vars:
  consume_create_outcome rq st = (value,after) ==>
  after.vs_vars = st.vs_vars
Proof
  simp[consume_create_outcome_eq] >> rpt strip_tac >> gvs[]
QED

Theorem current_exec_ext_call_writes:
  current_result_output_writes inst.inst_outputs st
    (exec_ext_call inst st gas addr value ao az ro rz static)
Proof
  Cases_on `consume_call_outcome (venom_call_request st addr value ao az static)
    (w2n ro) (w2n rz) st` >>
  drule current_consume_call_vars >> strip_tac >>
  simp[exec_ext_call_def, Excl "consume_call_outcome_eq"] >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  rename1 `h::t` >> Cases_on `t` >> simp[] >>
  irule current_output_writes_update >> simp[] >>
  irule current_output_writes_unchanged >> simp[]
QED

Theorem current_exec_create_writes:
  current_result_output_writes inst.inst_outputs st (exec_create inst st value off sz salt)
Proof
  Cases_on `consume_create_outcome (venom_create_request st value off sz salt) st` >>
  drule current_consume_create_vars >> strip_tac >>
  simp[exec_create_def, Excl "consume_create_outcome_eq"] >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  rename1 `h::t` >> Cases_on `t` >> simp[] >>
  IF_CASES_TAC >> simp[]
  >- (irule current_output_writes_unchanged >> simp[halt_state_def, set_returndata_def]) >>
  irule current_output_writes_update >> simp[] >>
  irule current_output_writes_unchanged >> simp[]
QED

Theorem current_extract_result_vars:
  extract_venom_result st output off sz result = SOME (value,after) ==>
  after.vs_vars = st.vs_vars
Proof
  Cases_on `result` >> simp[extract_venom_result_def] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `x1.contexts` >> simp[] >>
  Cases_on `t` >> simp[] >> PairCases_on `h` >> simp[] >>
  pairarg_tac >> simp[] >> rpt strip_tac >> gvs[]
QED

Theorem current_exec_delegatecall_writes:
  current_result_output_writes inst.inst_outputs st
    (exec_delegatecall inst st gas addr ao az ro rz)
Proof
  simp[exec_delegatecall_def] >>
  qmatch_goalsub_abbrev_tac `extract_venom_result st 1w _ _ result` >>
  Cases_on `extract_venom_result st 1w (w2n ro) (w2n rz) result` >> simp[] >>
  PairCases_on `x` >> drule current_extract_result_vars >> strip_tac >> simp[] >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  rename1 `h::t` >> Cases_on `t` >> simp[] >>
  irule current_output_writes_update >> simp[] >>
  irule current_output_writes_unchanged >> simp[]
QED

Theorem current_mcopy_vars:
  (mcopy dst src sz st).vs_vars = st.vs_vars
Proof
  simp[mcopy_def, write_memory_with_expansion_def]
QED

Theorem current_pack_dret_vars:
  !pairs cursor st ptrs final after.
  pack_dret_dynamic cursor pairs st = (ptrs,final,after) ==>
  after.vs_vars = st.vs_vars
Proof
  Induct >- (simp[pack_dret_dynamic_def] >> rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> PairCases_on `h` >> simp[pack_dret_dynamic_def] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  first_x_assum drule >> simp[current_mcopy_vars]
QED

Theorem current_exec_alloca_writes:
  current_result_output_writes inst.inst_outputs st (exec_alloca inst st sz)
Proof
  Cases_on `exec_alloca inst st sz` >>
  gvs[exec_alloca_def, AllCaseEqs()] >>
  irule current_output_writes_update >> simp[] >>
  irule current_output_writes_unchanged >> simp[]
QED

Theorem current_bump_writes:
  inst.inst_opcode = BUMP ==>
  current_result_output_writes inst.inst_outputs st (step_inst_base inst st)
Proof
  strip_tac >> Cases_on `step_inst_base inst st` >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  irule current_output_writes_update >> simp[] >>
  irule current_output_writes_update >> simp[] >>
  irule current_output_writes_unchanged >> simp[]
QED

Theorem current_scalar_output_writes:
  (inst.inst_opcode = ASSIGN \/ inst.inst_opcode = GETFMP \/
   inst.inst_opcode = INITIAL_FMP \/ inst.inst_opcode = DALLOCA \/
   inst.inst_opcode = PARAM \/ inst.inst_opcode = FMP_PARAM \/
   inst.inst_opcode = RETPC_PARAM \/ inst.inst_opcode = SHA3) ==>
  current_result_output_writes inst.inst_outputs st (step_inst_base inst st)
Proof
  strip_tac >> Cases_on `step_inst_base inst st` >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  irule current_output_writes_update >> simp[] >>
  irule current_output_writes_unchanged >> simp[]
QED

Theorem current_storage_output_writes:
  (inst.inst_opcode = MSTORE \/ inst.inst_opcode = MSTORE8 \/
   inst.inst_opcode = SSTORE \/ inst.inst_opcode = TSTORE) ==>
  current_result_output_writes inst.inst_outputs st (step_inst_base inst st)
Proof
  strip_tac >> Cases_on `step_inst_base inst st` >>
  gvs[step_inst_base_opcode_eqs, exec_write2_def, AllCaseEqs()] >>
  irule current_output_writes_unchanged >>
  simp[mstore_def, mstore8_def, sstore_def, tstore_def, write_memory_with_expansion_def]
QED

Theorem current_jump_output_writes:
  (inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ \/ inst.inst_opcode = DJMP) ==>
  current_result_output_writes inst.inst_outputs st (step_inst_base inst st)
Proof
  strip_tac >> Cases_on `step_inst_base inst st` >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  irule current_output_writes_unchanged >> simp[jump_to_def]
QED

Theorem current_terminal_output_writes:
  (inst.inst_opcode = STOP \/ inst.inst_opcode = RETURN \/
   inst.inst_opcode = REVERT \/ inst.inst_opcode = SINK \/
   inst.inst_opcode = INVALID \/ inst.inst_opcode = SELFDESTRUCT) ==>
  current_result_output_writes inst.inst_outputs st (step_inst_base inst st)
Proof
  strip_tac >> Cases_on `step_inst_base inst st` >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  irule current_output_writes_unchanged >>
  simp[halt_state_def, revert_state_def, set_returndata_def]
QED

Theorem current_assert_output_writes:
  (inst.inst_opcode = ASSERT \/ inst.inst_opcode = ASSERT_UNREACHABLE \/
   inst.inst_opcode = SETFMP \/ inst.inst_opcode = NOP \/
   inst.inst_opcode = RET \/ inst.inst_opcode = RETFMP) ==>
  current_result_output_writes inst.inst_outputs st (step_inst_base inst st)
Proof
  strip_tac >> Cases_on `step_inst_base inst st` >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  irule current_output_writes_unchanged >>
  simp[halt_state_def, revert_state_def, set_returndata_def]
QED

Theorem current_memory_copy_output_writes:
  (inst.inst_opcode = MCOPY \/ inst.inst_opcode = CALLDATACOPY \/
   inst.inst_opcode = DLOADBYTES \/ inst.inst_opcode = CODECOPY \/
   inst.inst_opcode = EXTCODECOPY \/ inst.inst_opcode = ISTORE) ==>
  current_result_output_writes inst.inst_outputs st (step_inst_base inst st)
Proof
  strip_tac >> Cases_on `step_inst_base inst st` >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  irule current_output_writes_unchanged >>
  simp[current_mcopy_vars, write_memory_with_expansion_def, istore_def, mstore_def]
QED

Theorem current_other_effect_output_writes:
  (inst.inst_opcode = RETURNDATACOPY \/ inst.inst_opcode = LOG) ==>
  current_result_output_writes inst.inst_outputs st (step_inst_base inst st)
Proof
  strip_tac >> Cases_on `step_inst_base inst st` >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  irule current_output_writes_unchanged >>
  simp[write_memory_with_expansion_def, halt_state_def, set_returndata_def]
QED

Theorem current_dret_output_writes:
  inst.inst_opcode = DRET ==>
  current_result_output_writes inst.inst_outputs st (step_inst_base inst st)
Proof
  strip_tac >> Cases_on `step_inst_base inst st` >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  pairarg_tac >> gvs[] >>
  irule current_output_writes_unchanged >> simp[] >>
  drule current_pack_dret_vars >> simp[]
QED

Theorem current_external_call_output_writes:
  (inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL) ==>
  current_result_output_writes inst.inst_outputs st (step_inst_base inst st)
Proof
  strip_tac >> Cases_on `step_inst_base inst st` >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  metis_tac[current_exec_ext_call_writes, current_result_output_writes_constructors]
QED

Theorem current_create_output_writes:
  (inst.inst_opcode = CREATE \/ inst.inst_opcode = CREATE2) ==>
  current_result_output_writes inst.inst_outputs st (step_inst_base inst st)
Proof
  strip_tac >> Cases_on `step_inst_base inst st` >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  metis_tac[current_exec_create_writes, current_result_output_writes_constructors]
QED

Theorem current_delegatecall_output_writes:
  inst.inst_opcode = DELEGATECALL ==>
  current_result_output_writes inst.inst_outputs st (step_inst_base inst st)
Proof
  strip_tac >> Cases_on `step_inst_base inst st` >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  metis_tac[current_exec_delegatecall_writes, current_result_output_writes_constructors]
QED

Theorem current_alloca_output_writes:
  inst.inst_opcode = ALLOCA ==>
  current_result_output_writes inst.inst_outputs st (step_inst_base inst st)
Proof
  strip_tac >> Cases_on `step_inst_base inst st` >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  metis_tac[current_exec_alloca_writes, current_result_output_writes_constructors]
QED

Theorem current_step_inst_base_output_writes:
  inst_wf inst /\ inst.inst_opcode <> PHI ==>
  current_result_output_writes inst.inst_outputs st (step_inst_base inst st)
Proof
  strip_tac >>
  Cases_on `inst.inst_opcode = BUMP`
  >- (irule current_bump_writes >> simp[]) >>
  Cases_on `inst.inst_opcode = ASSIGN \/ inst.inst_opcode = GETFMP \/ inst.inst_opcode = INITIAL_FMP \/ inst.inst_opcode = DALLOCA \/ inst.inst_opcode = PARAM \/ inst.inst_opcode = FMP_PARAM \/ inst.inst_opcode = RETPC_PARAM \/ inst.inst_opcode = SHA3`
  >- (irule current_scalar_output_writes >> simp[]) >>
  Cases_on `inst.inst_opcode = MSTORE \/ inst.inst_opcode = MSTORE8 \/ inst.inst_opcode = SSTORE \/ inst.inst_opcode = TSTORE`
  >- (irule current_storage_output_writes >> simp[]) >>
  Cases_on `inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ \/ inst.inst_opcode = DJMP`
  >- (irule current_jump_output_writes >> simp[]) >>
  Cases_on `inst.inst_opcode = STOP \/ inst.inst_opcode = RETURN \/ inst.inst_opcode = REVERT \/ inst.inst_opcode = SINK \/ inst.inst_opcode = INVALID \/ inst.inst_opcode = SELFDESTRUCT`
  >- (irule current_terminal_output_writes >> simp[]) >>
  Cases_on `inst.inst_opcode = ASSERT \/ inst.inst_opcode = ASSERT_UNREACHABLE \/ inst.inst_opcode = SETFMP \/ inst.inst_opcode = NOP \/ inst.inst_opcode = RET \/ inst.inst_opcode = RETFMP`
  >- (irule current_assert_output_writes >> simp[]) >>
  Cases_on `inst.inst_opcode = MCOPY \/ inst.inst_opcode = CALLDATACOPY \/ inst.inst_opcode = DLOADBYTES \/ inst.inst_opcode = CODECOPY \/ inst.inst_opcode = EXTCODECOPY \/ inst.inst_opcode = ISTORE`
  >- (irule current_memory_copy_output_writes >> simp[]) >>
  Cases_on `inst.inst_opcode = RETURNDATACOPY \/ inst.inst_opcode = LOG`
  >- (irule current_other_effect_output_writes >> simp[]) >>
  Cases_on `inst.inst_opcode = DRET`
  >- (irule current_dret_output_writes >> simp[]) >>
  Cases_on `inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL`
  >- (irule current_external_call_output_writes >> simp[]) >>
  Cases_on `inst.inst_opcode = CREATE \/ inst.inst_opcode = CREATE2`
  >- (irule current_create_output_writes >> simp[]) >>
  Cases_on `inst.inst_opcode = DELEGATECALL`
  >- (irule current_delegatecall_output_writes >> simp[]) >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (irule current_alloca_output_writes >> simp[]) >>
  Cases_on `inst.inst_opcode` >> gvs[] >>
  simp[step_inst_base_opcode_eqs,
       current_exec_pure1_writes, current_exec_pure2_writes,
       current_exec_pure3_writes, current_exec_read0_writes,
       current_exec_read1_writes]
QED

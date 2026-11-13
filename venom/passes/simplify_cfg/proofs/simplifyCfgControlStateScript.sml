(* Payload state primitives commute with the control-coordinate mask. *)
Theory simplifyCfgControlState
Ancestors
  simplifyCfgControl instIdxIndep venomExecSemantics venomState list
Libs
  BasicProvers

val ctrl_record_ss = pure_ss ++ boolSimps.BOOL_ss ++ rewrites
  [scfg_ctrl_def, venom_state_accfupds, venom_state_fupdcanon,
   venom_state_fupdfupds, combinTheory.K_THM, LET_THM];

Theorem scfg_ctrl_update_var[simp]:
  update_var x v (scfg_ctrl c p n s) =
  scfg_ctrl c p n (update_var x v s)
Proof
  simp_tac ctrl_record_ss [update_var_def]
QED

Theorem scfg_ctrl_read_memory[simp]:
  read_memory off sz (scfg_ctrl c p n s) = read_memory off sz s
Proof
  simp_tac ctrl_record_ss [read_memory_def]
QED

Theorem scfg_ctrl_mload[simp]:
  mload off (scfg_ctrl c p n s) = mload off s
Proof
  simp_tac ctrl_record_ss [mload_def]
QED

Theorem scfg_ctrl_sload[simp]:
  sload key (scfg_ctrl c p n s) = sload key s
Proof
  simp_tac ctrl_record_ss [sload_def, contract_storage_def]
QED

Theorem scfg_ctrl_tload[simp]:
  tload key (scfg_ctrl c p n s) = tload key s
Proof
  simp_tac ctrl_record_ss [tload_def, contract_transient_def]
QED

Theorem scfg_ctrl_write_memory[simp]:
  write_memory_with_expansion off bytes (scfg_ctrl c p n s) =
  scfg_ctrl c p n (write_memory_with_expansion off bytes s)
Proof
  simp_tac ctrl_record_ss [write_memory_with_expansion_def]
QED

Theorem scfg_ctrl_mstore[simp]:
  mstore off v (scfg_ctrl c p n s) = scfg_ctrl c p n (mstore off v s)
Proof
  simp_tac ctrl_record_ss [mstore_def]
QED

Theorem scfg_ctrl_mstore8[simp]:
  mstore8 off v (scfg_ctrl c p n s) = scfg_ctrl c p n (mstore8 off v s)
Proof
  simp_tac ctrl_record_ss [mstore8_def]
QED

Theorem scfg_ctrl_istore[simp]:
  istore off v (scfg_ctrl c p n s) = scfg_ctrl c p n (istore off v s)
Proof
  simp_tac ctrl_record_ss [istore_def, mstore_def]
QED

Theorem scfg_ctrl_mcopy[simp]:
  mcopy dst src sz (scfg_ctrl c p n s) = scfg_ctrl c p n (mcopy dst src sz s)
Proof
  simp_tac ctrl_record_ss [mcopy_def, write_memory_with_expansion_def]
QED

Theorem scfg_ctrl_sstore[simp]:
  sstore key v (scfg_ctrl c p n s) = scfg_ctrl c p n (sstore key v s)
Proof
  simp_tac ctrl_record_ss [sstore_def]
QED

Theorem scfg_ctrl_tstore[simp]:
  tstore key v (scfg_ctrl c p n s) = scfg_ctrl c p n (tstore key v s)
Proof
  simp_tac ctrl_record_ss [tstore_def]
QED

Theorem scfg_ctrl_halt[simp]:
  halt_state (scfg_ctrl c p n s) = scfg_ctrl c p n (halt_state s)
Proof
  simp_tac ctrl_record_ss [halt_state_def]
QED

Theorem scfg_ctrl_revert[simp]:
  revert_state (scfg_ctrl c p n s) = scfg_ctrl c p n (revert_state s)
Proof
  simp_tac ctrl_record_ss [revert_state_def]
QED

Theorem scfg_ctrl_set_returndata[simp]:
  set_returndata rd (scfg_ctrl c p n s) = scfg_ctrl c p n (set_returndata rd s)
Proof
  simp_tac ctrl_record_ss [set_returndata_def]
QED

Theorem scfg_ctrl_alloca:
  exec_alloca i (scfg_ctrl c p n s) sz =
  exec_result_map (scfg_ctrl c p n) (exec_alloca i s sz)
Proof
  Cases_on `i.inst_outputs`
  >- simp[exec_alloca_def, exec_result_map_def] >>
  rename1 `i.inst_outputs = out::outs` >> Cases_on `outs`
  >- (Cases_on `FLOOKUP s.vs_allocas i.inst_id`
      >- simp[exec_alloca_def, exec_result_map_def, scfg_ctrl_def, update_var_def] >>
      rename1 `FLOOKUP _ _ = SOME pair` >> Cases_on `pair` >>
      simp[exec_alloca_def, exec_result_map_def, scfg_ctrl_def, update_var_def]) >>
  simp[exec_alloca_def, exec_result_map_def]
QED

Theorem scfg_ctrl_pack_dret:
  !pairs cursor s ptrs last t.
    pack_dret_dynamic cursor pairs s = (ptrs,last,t) ==>
    pack_dret_dynamic cursor pairs (scfg_ctrl c p n s) =
      (ptrs,last,scfg_ctrl c p n t)
Proof
  Induct >> simp[pack_dret_dynamic_def] >>
  Cases >> rpt gen_tac >>
  simp[pack_dret_dynamic_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  first_x_assum drule >> simp[]
QED

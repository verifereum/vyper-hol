(* Storage projections of actual internal entry execution. *)
Theory augAssignEntryHistory
Ancestors
  intCallCallee immutableWordExecution venomExecSemantics venomState
  compileEnv vyperStorageBackend

Theorem setup_callee_storage_history:
  setup_callee func args caller = SOME s0 ==>
  !a. sload a s0 = sload a caller /\ tload a s0 = tload a caller
Proof
  simp[setup_callee_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[sload_def, tload_def, contract_storage_def, contract_transient_def]
QED

Theorem mat_frame_storage_history:
  mat_frame st s u ==>
  !a. sload a u = sload a s /\ tload a u = tload a s
Proof
  simp[mat_frame_def] >> rpt strip_tac >>
  qpat_x_assum `u = _` SUBST1_TAC >>
  simp[sload_def, tload_def, contract_storage_def, contract_transient_def]
QED

Theorem fixed_region_storage_history:
  compile_fixed_region_with_id nbytes st = ((id,buf),st') /\
  run_inst_seq (emitted_insts st st') s = OK u ==>
  !a. sload a u = sload a s /\ tload a u = tload a s
Proof
  strip_tac >> drule compile_fixed_region_execution >> strip_tac >>
  gvs[update_var_def, sload_def, tload_def,
      contract_storage_def, contract_transient_def]
QED


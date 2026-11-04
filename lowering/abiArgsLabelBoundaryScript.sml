Theory abiArgsLabelBoundary
Ancestors compileEnv exprSim fragExec venomExecProofs venomExecSemantics

(* Operational steps include returning INVOKE: the caller label map survives. *)
Theorem abi_args_step_labels:
  step_inst fuel ctx inst s = OK t ==> t.vs_labels = s.vs_labels
Proof
  metis_tac[step_inst_preserves_labels_always]
QED

Theorem abi_args_merge_labels:
  (merge_callee_state caller callee).vs_labels = caller.vs_labels
Proof
  simp[merge_callee_state_def]
QED

Theorem abi_args_operand_control_only:
  eval_operand op (s with <|vs_halted := halted; vs_current_bb := bb; vs_inst_idx := idx|>) =
  eval_operand op s
Proof
  Cases_on `op` >> simp[venomStateTheory.eval_operand_def,
    venomStateTheory.lookup_var_def]
QED

(* Control changes are harmless only when the label map is retained. *)
Theorem abi_args_state_rel_control_only:
  stmt_state_rel ctx func ce cx es
    (s with <|vs_halted := halted; vs_current_bb := bb; vs_inst_idx := idx|>) <=>
  stmt_state_rel ctx func ce cx es s
Proof
  simp[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def,
       local_ptrs_rel_def, local_region_def, local_backed_def,
       venomStateTheory.lookup_var_def, storage_rel_def, transient_rel_def,
       accounts_rel_def, immutables_rel_def, logs_rel_def, call_ctx_rel_def,
       venomStateTheory.contract_storage_def, venomStateTheory.contract_transient_def,
       venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.allocas_non_overlapping_def,
       venomMemDefsTheory.alloca_next_valid_def,
       exprLoweringPropsTheory.alloca_room_def,
       exprLoweringPropsTheory.pending_alloca_size_def,
       exprLoweringPropsTheory.immutable_alloca_sep_def,
       exprLoweringPropsTheory.fmp_room_def, immutable_base_zero_def,
       abi_args_operand_control_only]
QED

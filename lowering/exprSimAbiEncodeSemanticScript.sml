(* Semantic observations retained by the same concrete encoder execution. *)
Theory exprSimAbiEncodeSemantic
Ancestors
  stmtSimLogExecFields exprLoweringProps venomExecSemantics venomState
  venomInst list finite_map

Definition abi_encode_semantic_obs_def:
  abi_encode_semantic_obs (s:venom_state) =
    (s.vs_tx_ctx,s.vs_block_ctx,s.vs_outcomes,s.vs_immutables,s.vs_code)
End

Theorem abi_encode_semantic_obs_fields:
  abi_encode_semantic_obs t = abi_encode_semantic_obs s <=>
  t.vs_tx_ctx = s.vs_tx_ctx /\ t.vs_block_ctx = s.vs_block_ctx /\
  t.vs_outcomes = s.vs_outcomes /\ t.vs_immutables = s.vs_immutables /\
  t.vs_code = s.vs_code
Proof
  simp[abi_encode_semantic_obs_def]
QED

Theorem abi_encode_semantic_obs_updates[simp]:
  abi_encode_semantic_obs (s with vs_inst_idx := idx) = abi_encode_semantic_obs s /\
  abi_encode_semantic_obs (s with vs_current_bb := bb) = abi_encode_semantic_obs s /\
  abi_encode_semantic_obs (s with vs_prev_bb := prev) = abi_encode_semantic_obs s /\
  abi_encode_semantic_obs (s with vs_returndata := rd) = abi_encode_semantic_obs s
Proof
  simp[abi_encode_semantic_obs_def]
QED

Theorem abi_encode_semantic_step:
  log_encode_safe_opcode i.inst_opcode /\ step_inst_base i s = OK t ==>
  abi_encode_semantic_obs t = abi_encode_semantic_obs s
Proof
  strip_tac >> drule_all log_encode_step_external >>
  strip_tac >> drule log_encode_external_fields >>
  simp[abi_encode_semantic_obs_fields]
QED

Theorem abi_encode_semantic_sequence:
  EVERY (\i. log_encode_safe_opcode i.inst_opcode) code /\
  run_inst_seq code s = OK t ==>
  abi_encode_semantic_obs t = abi_encode_semantic_obs s
Proof
  strip_tac >> drule_all log_encode_run_external >>
  strip_tac >> drule log_encode_external_fields >>
  simp[abi_encode_semantic_obs_fields]
QED

(* Probe the allocation, read and write instruction families, followed by
   the cursor changes made when re-entering the surrounding fragment. *)
Theorem abi_encode_semantic_phase_probe:
  EVERY (\i. MEM i.inst_opcode [ALLOCA; ADD; MLOAD; MSTORE; MCOPY]) code /\
  run_inst_seq code s = OK t ==>
  abi_encode_semantic_obs
    (t with <| vs_inst_idx := idx; vs_current_bb := bb;
               vs_prev_bb := prev; vs_returndata := rd |>) =
  abi_encode_semantic_obs s
Proof
  strip_tac >> simp[] >> irule abi_encode_semantic_sequence >>
  goal_assum (drule_at Any) >>
  gvs[EVERY_MEM, log_encode_safe_opcode_def] >> metis_tac[]
QED

Theorem abi_encode_semantic_obs_storage_updates[simp]:
  abi_encode_semantic_obs (s with vs_memory := mem) = abi_encode_semantic_obs s /\
  abi_encode_semantic_obs (s with vs_vars := vars) = abi_encode_semantic_obs s /\
  abi_encode_semantic_obs (s with vs_allocas := allocas) = abi_encode_semantic_obs s /\
  abi_encode_semantic_obs (s with vs_alloca_next := next) = abi_encode_semantic_obs s
Proof
  simp[abi_encode_semantic_obs_def]
QED

Theorem abi_encode_semantic_ordinary_step:
  ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode /\
  ~is_ext_call_op i.inst_opcode /\ i.inst_opcode <> INVOKE /\
  i.inst_opcode <> SETFMP /\ i.inst_opcode <> DALLOCA /\
  i.inst_opcode <> ISTORE /\ i.inst_opcode <> CALL /\
  i.inst_opcode <> STATICCALL /\ i.inst_opcode <> DELEGATECALL /\
  i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2 /\
  step_inst_base i s = OK t ==>
  abi_encode_semantic_obs t = abi_encode_semantic_obs s
Proof
  strip_tac >> Cases_on `i.inst_opcode` >>
  gvs[is_terminator_def, is_alloca_op_def, is_ext_call_op_def] >>
  qpat_x_assum `step_inst_base _ _ = OK _` mp_tac >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs] >>
  simp[exec_pure1_def, exec_pure2_def, exec_pure3_def,
       exec_read0_def, exec_read1_def, exec_write2_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[abi_encode_semantic_obs_def, update_var_def] >>
  gvs[mstore_def, mstore8_def, mcopy_def, sstore_def, tstore_def,
      write_memory_with_expansion_def, exec_gas_def, AllCaseEqs(), update_var_def]
QED

Theorem abi_encode_semantic_ordinary_sequence:
  EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode /\
    ~is_ext_call_op i.inst_opcode /\ i.inst_opcode <> INVOKE /\
    i.inst_opcode <> SETFMP /\ i.inst_opcode <> DALLOCA /\
    i.inst_opcode <> ISTORE /\ i.inst_opcode <> CALL /\
    i.inst_opcode <> STATICCALL /\ i.inst_opcode <> DELEGATECALL /\
    i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) code /\
  run_inst_seq code s = OK t ==>
  abi_encode_semantic_obs t = abi_encode_semantic_obs s
Proof
  strip_tac >> irule run_inst_seq_preserves_field >>
  qexists_tac `code` >> asm_simp_tac bool_ss [] >> rpt strip_tac >>
  irule abi_encode_semantic_ordinary_step >> qexists_tac `i` >>
  asm_simp_tac bool_ss [] >> fs[EVERY_MEM]
QED

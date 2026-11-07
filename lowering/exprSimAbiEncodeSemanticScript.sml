(* Semantic observations retained by the same concrete encoder execution. *)
Theory exprSimAbiEncodeSemantic
Ancestors
  stmtSimLogExecFields exprLoweringProps venomExecSemantics venomState
  venomInst list finite_map

Definition abi_encode_semantic_obs_def:
  abi_encode_semantic_obs (s:venom_state) =
    (s.vs_tx_ctx,s.vs_block_ctx,s.vs_outcomes,s.vs_immutables)
End

Theorem abi_encode_semantic_obs_fields:
  abi_encode_semantic_obs t = abi_encode_semantic_obs s <=>
  t.vs_tx_ctx = s.vs_tx_ctx /\ t.vs_block_ctx = s.vs_block_ctx /\
  t.vs_outcomes = s.vs_outcomes /\ t.vs_immutables = s.vs_immutables
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

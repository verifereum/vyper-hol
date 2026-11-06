Theory concretizeLayoutReaderContext
Ancestors venomExecSemantics venomState

(* A supplement for immutable transaction and block readers, independent of
   call-local environment, opaque tokens and allocation metadata. *)
Definition relocation_reader_context_def:
  relocation_reader_context s t <=>
    s.vs_tx_ctx = t.vs_tx_ctx /\ s.vs_block_ctx = t.vs_block_ctx /\
    s.vs_prev_hashes = t.vs_prev_hashes
End

Theorem relocation_reader_context_refl[simp]:
  relocation_reader_context s s
Proof
  simp[relocation_reader_context_def]
QED

Theorem relocation_reader_context_update_var:
  relocation_reader_context s t ==>
  relocation_reader_context (update_var v x s) (update_var w y t)
Proof
  simp[relocation_reader_context_def, update_var_def]
QED

Theorem relocation_reader_context_gas_readings:
  relocation_reader_context s t ==>
  relocation_reader_context (s with vs_gas_readings := rs)
    (t with vs_gas_readings := rt)
Proof
  simp[relocation_reader_context_def]
QED

Definition context_read0_opcode_def:
  context_read0_opcode op <=>
    MEM op [ORIGIN; GASPRICE; CHAINID; COINBASE; TIMESTAMP; NUMBER;
            PREVRANDAO; GASLIMIT; BASEFEE; BLOBBASEFEE]
End

Theorem relocation_reader_context_execution:
  context_read0_opcode inst.inst_opcode /\ inst.inst_outputs = [v] /\
  relocation_reader_context s t /\ step_inst_base inst s = OK post ==>
  ?z. post = update_var v z s /\
    step_inst_base inst t = OK (update_var v z t) /\
    relocation_reader_context post (update_var v z t)
Proof
  simp[context_read0_opcode_def] >> strip_tac >>
  qpat_x_assum `step_inst_base inst s = OK post` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
  simp[exec_read0_def] >> strip_tac >> gvs[] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
  gvs[exec_read0_def, relocation_reader_context_def, update_var_def,
      venom_state_component_equality] >>
  metis_tac[]
QED

(* All immutable inputs observed by concrete EVM sub-execution. *)
Theorem relocation_reader_context_tx_params:
  relocation_reader_context s t ==> venom_to_tx_params s = venom_to_tx_params t
Proof
  simp[relocation_reader_context_def, venom_to_tx_params_def]
QED

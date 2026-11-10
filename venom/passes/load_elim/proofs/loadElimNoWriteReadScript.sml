Theory loadElimNoWriteRead
Ancestors
  loadElimKeyRead venomInstProofs venomExecSemantics venomState
  venomEffects venomInst words

Theorem le_terminator_mutable_reads:
  step_inst fuel ctx inst s = OK t /\ is_terminator inst.inst_opcode ==>
  le_read_address AddrSp_Memory a t = le_read_address AddrSp_Memory a s /\
  le_read_address AddrSp_Storage a t = le_read_address AddrSp_Storage a s /\
  le_read_address AddrSp_Transient a t = le_read_address AddrSp_Transient a s
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >> gvs[is_terminator_def] >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[Once step_inst_def] >>
  simp[step_inst_base_opcode_eqs, jump_to_def] >>
  gvs[AllCaseEqs(), PULL_EXISTS] >>
  rpt strip_tac >>
  gvs[mload_def, read_memory_def, sload_def, tload_def,
      contract_storage_def, contract_transient_def] >>
  pairarg_tac >> gvs[]
QED

Theorem le_alloca_mutable_reads:
  step_inst fuel ctx inst s = OK t /\ is_alloca_op inst.inst_opcode ==>
  le_read_address AddrSp_Memory a t = le_read_address AddrSp_Memory a s /\
  le_read_address AddrSp_Storage a t = le_read_address AddrSp_Storage a s /\
  le_read_address AddrSp_Transient a t = le_read_address AddrSp_Transient a s
Proof
  strip_tac >> drule_all step_alloca_preserves >> strip_tac >>
  simp[mload_def, read_memory_def, sload_def, tload_def,
       contract_storage_def, contract_transient_def]
QED

Theorem le_memory_read_no_write_step:
  step_inst fuel ctx inst s = OK t /\
  Eff_MEMORY NOTIN write_effects inst.inst_opcode ==>
  le_read_address AddrSp_Memory a t = le_read_address AddrSp_Memory a s
Proof
  strip_tac >> Cases_on `is_terminator inst.inst_opcode`
  >- metis_tac[le_terminator_mutable_reads] >>
  Cases_on `is_alloca_op inst.inst_opcode`
  >- metis_tac[le_alloca_mutable_reads] >>
  drule_all write_effects_sound_memory >>
  simp[mload_def, read_memory_def]
QED

Theorem le_storage_read_no_write_step:
  step_inst fuel ctx inst s = OK t /\
  Eff_STORAGE NOTIN write_effects inst.inst_opcode ==>
  le_read_address AddrSp_Storage a t = le_read_address AddrSp_Storage a s
Proof
  strip_tac >> Cases_on `is_terminator inst.inst_opcode`
  >- metis_tac[le_terminator_mutable_reads] >>
  Cases_on `is_alloca_op inst.inst_opcode`
  >- metis_tac[le_alloca_mutable_reads] >>
  drule_all write_effects_sound_storage >> simp[sload_def]
QED

Theorem le_transient_read_no_write_step:
  step_inst fuel ctx inst s = OK t /\
  Eff_TRANSIENT NOTIN write_effects inst.inst_opcode ==>
  le_read_address AddrSp_Transient a t = le_read_address AddrSp_Transient a s
Proof
  strip_tac >> Cases_on `is_terminator inst.inst_opcode`
  >- metis_tac[le_terminator_mutable_reads] >>
  Cases_on `is_alloca_op inst.inst_opcode`
  >- metis_tac[le_alloca_mutable_reads] >>
  drule_all step_preserves_call_ctx >> strip_tac >>
  drule_all write_effects_sound_transient >>
  simp[tload_def, contract_transient_def]
QED

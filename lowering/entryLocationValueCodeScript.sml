Theory entryLocationValueCode
Ancestors
  entryCodePredicate entryContextCodePredicate exprLowering context

Theorem entry_code_lit_byte_offset:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_lit_byte_offset op off)
Proof
  Cases_on `off = 0` >> Cases_on `op` >>
  simp[compile_lit_byte_offset_def, entry_code_return, entry_code_emit_op]
QED

Theorem entry_code_imm_copy_to_memory:
  !n off. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_imm_copy_to_memory is_ctor imm src dst n off)
Proof
  Induct_on `n` >- simp[compile_imm_copy_to_memory_def, entry_code_return] >>
  gen_tac >> simp[compile_imm_copy_to_memory_def, compileEnvTheory.comp_ignore_bind_def] >>
  ntac 4 (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_lit_byte_offset, entry_code_imm_load, entry_code_emit_void] >>
    rpt gen_tac >> BETA_TAC) >> simp[]
QED

Theorem entry_code_ensure_in_memory:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_ensure_in_memory ptr_op loc mem_bytes word_count is_ctor imm)
Proof
  Cases_on `loc` >>
  simp[compile_ensure_in_memory_def, entry_code_return,
       compileEnvTheory.comp_ignore_bind_def]
  >- suspend "storage"
  >- suspend "transient"
  >- suspend "code"
  >- suspend "calldata"
QED

Resume entry_code_ensure_in_memory[storage]:
  irule entry_code_bind >> reverse conj_tac >- simp[entry_code_alloc_buffer] >>
  rpt gen_tac >> BETA_TAC >> irule entry_code_bind >>
  simp[entry_code_return] >> Cases_on `word_count = 1` >> simp[]
  >- (irule entry_code_bind >> simp[entry_code_emit_op, entry_code_emit_void]) >>
  irule entry_code_bind >> simp[entry_code_storage_to_memory, entry_code_return]
QED

Resume entry_code_ensure_in_memory[transient]:
  irule entry_code_bind >> reverse conj_tac >- simp[entry_code_alloc_buffer] >>
  rpt gen_tac >> BETA_TAC >> irule entry_code_bind >>
  simp[entry_code_return] >> Cases_on `word_count = 1` >> simp[]
  >- (irule entry_code_bind >> simp[entry_code_emit_op, entry_code_emit_void]) >>
  irule entry_code_bind >> simp[entry_code_transient_to_memory, entry_code_return]
QED

Resume entry_code_ensure_in_memory[code]:
  irule entry_code_bind >> reverse conj_tac >- simp[entry_code_alloc_buffer] >>
  rpt gen_tac >> BETA_TAC >> irule entry_code_bind >>
  simp[entry_code_return, entry_code_imm_copy_to_memory]
QED

Resume entry_code_ensure_in_memory[calldata]:
  ntac 6 (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_emit_void, entry_code_alloc_buffer] >>
    rpt gen_tac >> BETA_TAC) >> simp[entry_code_return]
QED

Finalise entry_code_ensure_in_memory

Theorem entry_code_unwrap_value:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (unwrap_value cenv vv)
Proof
  Cases_on `vv` >> simp[unwrap_value_def, entry_code_return] >>
  rename1 `is_word_type ty` >> Cases_on `is_word_type ty`
  >- simp[entry_code_ptr_load] >>
  simp[] >> rename1 `p.ptr_location` >> Cases_on `p.ptr_location` >>
  simp[entry_code_return, entry_code_ensure_in_memory]
QED

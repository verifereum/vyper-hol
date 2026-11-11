Theory entryContextCodePredicate
Ancestors
  entryCodePredicate context emitHelper emitHelperProps

Theorem entry_code_emit_inst:
  opc <> DALLOCA ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (emit_inst opc operands outputs)
Proof
  strip_tac >> simp[emit_inst_def] >> irule entry_code_bind >>
  simp[entry_code_fresh_id, entry_code_emit]
QED

Theorem entry_code_emit_op:
  opc <> DALLOCA ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (emit_op opc operands)
Proof
  strip_tac >> simp[emit_op_def] >>
  irule entry_code_bind >> simp[entry_code_fresh_id] >> gen_tac >>
  irule entry_code_bind >> simp[entry_code_fresh_var] >> gen_tac >>
  irule entry_code_ignore_bind >> simp[entry_code_emit, entry_code_return]
QED

Theorem entry_code_emit_void:
  opc <> DALLOCA ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (emit_void opc operands)
Proof
  strip_tac >> simp[emit_void_def] >> irule entry_code_bind >>
  simp[entry_code_fresh_id, entry_code_emit]
QED

Theorem entry_code_alloc_buffer:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (compile_alloc_buffer sz)
Proof
  simp[compile_alloc_buffer_def] >> irule entry_code_bind >>
  simp[entry_code_emit_op, entry_code_return]
QED

Theorem entry_code_fixed_region:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_fixed_region_with_id sz)
Proof
  simp[compile_fixed_region_with_id_def] >>
  irule entry_code_bind >> simp[entry_code_fresh_id] >> gen_tac >>
  irule entry_code_bind >> simp[entry_code_fresh_var] >> gen_tac >>
  irule entry_code_ignore_bind >> simp[entry_code_emit, entry_code_return]
QED

Theorem entry_code_imm_load:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_imm_load_word is_ctor imm off)
Proof
  Cases_on `is_ctor` >> Cases_on `imm` >>
  simp[compile_imm_load_word_def, entry_code_emit_op] >>
  irule entry_code_bind >> simp[entry_code_emit_op]
QED

Theorem entry_code_imm_store:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_imm_store_word imm off v)
Proof
  Cases_on `imm` >>
  simp[compile_imm_store_word_def, entry_code_emit_void] >>
  irule entry_code_bind >> simp[entry_code_emit_op, entry_code_emit_void]
QED

Theorem entry_code_ptr_load:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_ptr_load is_ctor imm loc op)
Proof
  Cases_on `loc` >>
  simp[compile_ptr_load_def, entry_code_emit_op, entry_code_imm_load]
QED

Theorem entry_code_ptr_store:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_ptr_store is_ctor imm loc dst v)
Proof
  Cases_on `loc` >> Cases_on `is_ctor` >>
  simp[compile_ptr_store_def, entry_code_emit_void, entry_code_imm_store]
QED

Theorem entry_code_copy_memory:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_copy_memory dst src sz)
Proof
  Cases_on `sz` >>
  simp[compile_copy_memory_def, entry_code_return, entry_code_emit_void]
QED

Theorem entry_code_word_copy_loop:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_word_copy_loop src dst word_count load_loc store_loc is_ctor)
Proof
  `!ops base. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
      (comp_bind (emit_op MUL ops) (\scaled. emit_op ADD [base; scaled]))`
    by (rpt gen_tac >> irule entry_code_bind >> simp[entry_code_emit_op]) >>
  rewrite_tac[compile_word_copy_loop_def, compile_word_copy_loop_op_def,
              compile_word_copy_loop_base_def] >>
  Cases_on `word_scale load_loc = 1` >>
  Cases_on `word_scale store_loc = 1` >>
  simp[compileEnvTheory.comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >>
       simp[entry_code_fresh_label, entry_code_fresh_var,
            entry_code_emit_inst, entry_code_emit_op,
            entry_code_ptr_load, entry_code_ptr_store, entry_code_new_block] >>
       rpt gen_tac) >>
  simp[entry_code_new_block]
QED

Theorem entry_code_storage_to_memory:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_storage_to_memory slot buf word_count)
Proof
  simp[compile_storage_to_memory_def, entry_code_word_copy_loop]
QED

Theorem entry_code_memory_to_storage:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_memory_to_storage buf slot word_count)
Proof
  simp[compile_memory_to_storage_def, entry_code_word_copy_loop]
QED

Theorem entry_code_transient_to_memory:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_transient_to_memory slot buf word_count)
Proof
  simp[compile_transient_to_memory_def, entry_code_word_copy_loop]
QED

Theorem entry_code_memory_to_transient:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_memory_to_transient buf slot word_count)
Proof
  simp[compile_memory_to_transient_def, entry_code_word_copy_loop]
QED

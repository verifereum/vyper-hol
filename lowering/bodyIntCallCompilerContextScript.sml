Theory bodyIntCallCompilerContext
Ancestors
  bodyIntCallCompilerFloor bodyIntCallCompilerEmit bodyIntCallCompilerInterval
  context compileEnv

Theorem intcall_interval_alloc_buffer:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_alloc_buffer sz a))
Proof
  strip_tac >> rewrite_tac[compile_alloc_buffer_def] >>
  irule intcall_interval_bind_floor >>
  simp[intcall_interval_emit_op, intcall_interval_return]
QED

Theorem intcall_interval_imm_load:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_imm_load_word ctor imm off a))
Proof
  strip_tac >> Cases_on `ctor` >> Cases_on `imm` >>
  simp[compile_imm_load_word_def, intcall_interval_emit_op] >>
  irule intcall_interval_bind_floor >> simp[intcall_interval_emit_op]
QED

Theorem intcall_interval_imm_store:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_imm_store_word imm off v a))
Proof
  strip_tac >> Cases_on `imm` >>
  simp[compile_imm_store_word_def, intcall_interval_emit_void] >>
  irule intcall_interval_bind_floor >>
  simp[intcall_interval_emit_op, intcall_interval_emit_void]
QED

Theorem intcall_interval_ptr_load:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_ptr_load ctor imm loc op a))
Proof
  Cases_on `loc` >>
  simp[compile_ptr_load_def, intcall_interval_emit_op, intcall_interval_imm_load]
QED

Theorem intcall_interval_ptr_store:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_ptr_store ctor imm loc dst v a))
Proof
  Cases_on `loc` >> Cases_on `ctor` >>
  simp[compile_ptr_store_def, intcall_interval_emit_void, intcall_interval_imm_store]
QED

Theorem intcall_interval_copy_memory:
  intcall_compiler_interval k a (SND (compile_copy_memory dst src sz a))
Proof
  Cases_on `sz` >>
  simp[compile_copy_memory_def, intcall_interval_return, intcall_interval_emit_void]
QED

Theorem intcall_interval_word_copy_loop:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_word_copy_loop src dst wc ll sl ctor a))
Proof
  strip_tac >> Cases_on `word_scale ll = 1` >>
  Cases_on `word_scale sl = 1` >>
  simp[compile_word_copy_loop_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_fresh_label, intcall_interval_fresh_var,
            intcall_interval_new_block, intcall_interval_emit_inst,
            intcall_interval_emit_op, intcall_interval_ptr_load,
            intcall_interval_ptr_store]) >>
  simp[intcall_interval_new_block]
QED

Theorem intcall_interval_storage_to_memory:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_storage_to_memory src dst wc a))
Proof
  simp[compile_storage_to_memory_def, intcall_interval_word_copy_loop]
QED

Theorem intcall_interval_transient_to_memory:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_transient_to_memory src dst wc a))
Proof
  simp[compile_transient_to_memory_def, intcall_interval_word_copy_loop]
QED

Theorem intcall_interval_code_to_memory:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_code_to_memory src dst wc a))
Proof
  strip_tac >> Cases_on `wc = 0` >>
  simp[compile_code_to_memory_def, intcall_interval_return] >>
  irule intcall_interval_ignore_bind_floor >>
  simp[intcall_interval_word_copy_loop, intcall_interval_return]
QED

Theorem intcall_interval_lit_byte_offset:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_lit_byte_offset op off a))
Proof
  Cases_on `off = 0` >> Cases_on `op` >>
  simp[compile_lit_byte_offset_def, intcall_interval_return, intcall_interval_emit_op]
QED

Theorem intcall_interval_imm_copy:
  !n off a. k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_imm_copy_to_memory ctor imm src dst n off a))
Proof
  Induct >> simp[compile_imm_copy_to_memory_def, intcall_interval_return] >>
  rpt strip_tac >> rewrite_tac[comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_lit_byte_offset, intcall_interval_imm_load,
            intcall_interval_emit_void])
QED

Theorem intcall_interval_imm_store_words:
  !n off a. k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_imm_store_words imm src dst n off a))
Proof
  Induct >> simp[compile_imm_store_words_def, intcall_interval_return] >>
  rpt strip_tac >> rewrite_tac[comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_lit_byte_offset, intcall_interval_emit_op,
            intcall_interval_imm_store])
QED

Theorem intcall_interval_copy_memory_dynamic:
  intcall_compiler_interval k a (SND (compile_copy_memory_dynamic dst src len a))
Proof
  simp[compile_copy_memory_dynamic_def, intcall_interval_emit_void]
QED

Theorem intcall_interval_with_byte_offset:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_with_byte_offset op off a))
Proof
  Cases_on `off = 0` >>
  simp[compile_with_byte_offset_def, intcall_interval_return, intcall_interval_emit_op]
QED

Theorem intcall_interval_bytestring_len:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_bytestring_copy_len op a))
Proof
  strip_tac >> simp[compile_bytestring_copy_len_def] >>
  rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op])
QED

Theorem intcall_interval_store_bytestring:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_store_bytestring op dst a))
Proof
  strip_tac >> rewrite_tac[compile_store_bytestring_def] >>
  irule intcall_interval_bind_floor >>
  simp[intcall_interval_bytestring_len, intcall_interval_emit_void]
QED

Theorem intcall_interval_ensure_in_memory:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_ensure_in_memory op loc bytes wc ctor imm a))
Proof
  strip_tac >> Cases_on `loc` >> Cases_on `wc = 1` >>
  simp[compile_ensure_in_memory_def, comp_ignore_bind_def,
       intcall_interval_return] >>
  rpt (rpt strip_tac >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_alloc_buffer, intcall_interval_emit_op,
            intcall_interval_emit_void, intcall_interval_storage_to_memory,
            intcall_interval_transient_to_memory, intcall_interval_imm_copy,
            intcall_interval_return])
QED

Theory bodyPtrBytestringBuiltinsOpcodeValues
Ancestors bodyPtrBytestringBuiltinsOpcodeState exprLowering context
          compileEnv emitHelper list

Theorem no_extcode_imm_load_word:
  !is_ctor imm off s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_imm_load_word is_ctor imm off s))
Proof
  ntac 3 gen_tac >> Cases_on `is_ctor` >> Cases_on `imm` >>
  simp[compile_imm_load_word_def, no_extcode_emit_op] >>
  rpt gen_tac >> strip_tac >> irule no_extcode_bind >> simp[no_extcode_emit_op]
QED

Theorem no_extcode_imm_store_word:
  !imm off v s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_imm_store_word imm off v s))
Proof
  ntac 3 gen_tac >> Cases_on `imm` >>
  simp[compile_imm_store_word_def, no_extcode_emit_void] >>
  rpt gen_tac >> strip_tac >> irule no_extcode_bind >> simp[no_extcode_emit_op, no_extcode_emit_void]
QED

Theorem no_extcode_ptr_load:
  !is_ctor imm loc op s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_ptr_load is_ctor imm loc op s))
Proof
  ntac 4 gen_tac >> Cases_on `loc` >>
  simp[compile_ptr_load_def, no_extcode_emit_op, no_extcode_imm_load_word]
QED

Theorem no_extcode_ptr_store:
  !is_ctor imm loc dst v s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_ptr_store is_ctor imm loc dst v s))
Proof
  ntac 5 gen_tac >> Cases_on `loc` >> Cases_on `is_ctor` >>
  simp[compile_ptr_store_def, no_extcode_emit_void, no_extcode_imm_store_word]
QED

Theorem no_extcode_alloc_buffer:
  !size s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_alloc_buffer size s))
Proof
  gen_tac >> simp[compile_alloc_buffer_def] >>
  rpt gen_tac >> strip_tac >> irule no_extcode_bind >> simp[no_extcode_emit_op, no_extcode_fresh_ops]
QED

Theorem no_extcode_lit_byte_offset:
  !op off s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_lit_byte_offset op off s))
Proof
  ntac 2 gen_tac >> Cases_on `off = 0` >> Cases_on `op` >>
  simp[compile_lit_byte_offset_def, no_extcode_emit_op, no_extcode_fresh_ops]
QED

Theorem no_extcode_word_copy_loop:
  !src dst count load_loc store_loc is_ctor s. compiler_no_extcode s ==>
    compiler_no_extcode (SND
      (compile_word_copy_loop src dst count load_loc store_loc is_ctor s))
Proof
  ntac 6 gen_tac >>
  Cases_on `word_scale load_loc = 1` >>
  Cases_on `word_scale store_loc = 1` >>
  simp[compile_word_copy_loop_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac, irule no_extcode_bind,
    irule no_extcode_ignore_bind] >>
    simp[no_extcode_emit_inst, no_extcode_emit_op, no_extcode_emit_void,
      no_extcode_fresh_ops, no_extcode_new_block, no_extcode_ptr_load,
      no_extcode_ptr_store])
QED

Theorem no_extcode_storage_to_memory:
  !slot buf count s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_storage_to_memory slot buf count s))
Proof
  simp[compile_storage_to_memory_def, no_extcode_word_copy_loop]
QED

Theorem no_extcode_transient_to_memory:
  !slot buf count s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_transient_to_memory slot buf count s))
Proof
  simp[compile_transient_to_memory_def, no_extcode_word_copy_loop]
QED

Theorem no_extcode_imm_copy_to_memory:
  !is_ctor imm src dst count off s. compiler_no_extcode s ==>
    compiler_no_extcode (SND
      (compile_imm_copy_to_memory is_ctor imm src dst count off s))
Proof
  ntac 4 gen_tac >> Induct >>
  simp[compile_imm_copy_to_memory_def, no_extcode_fresh_ops] >> gen_tac >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac, irule no_extcode_bind,
    irule no_extcode_ignore_bind] >>
    simp[no_extcode_lit_byte_offset, no_extcode_imm_load_word,
      no_extcode_emit_void])
QED

Theorem no_extcode_ensure_in_memory:
  !op loc bytes count is_ctor imm s. compiler_no_extcode s ==>
    compiler_no_extcode (SND
      (compile_ensure_in_memory op loc bytes count is_ctor imm s))
Proof
  map_every qx_gen_tac [`op`, `loc`, `bytes`, `nwords`, `is_ctor`, `imm`] >>
  Cases_on `loc` >> Cases_on `nwords = 1` >>
  simp[compile_ensure_in_memory_def, no_extcode_fresh_ops] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac, irule no_extcode_bind,
    irule no_extcode_ignore_bind] >>
    simp[no_extcode_alloc_buffer, no_extcode_storage_to_memory,
      no_extcode_transient_to_memory, no_extcode_imm_copy_to_memory,
      no_extcode_emit_op, no_extcode_emit_void, no_extcode_fresh_ops])
QED

Theorem no_extcode_unwrap_value:
  !cenv vv s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (unwrap_value cenv vv s))
Proof
  ntac 2 gen_tac >> Cases_on `vv` >>
  simp[unwrap_value_def, no_extcode_fresh_ops] >>
  rename1 `is_word_type ty` >> Cases_on `is_word_type ty` >>
  simp[no_extcode_ptr_load] >> Cases_on `p.ptr_location` >>
  simp[no_extcode_ensure_in_memory, no_extcode_fresh_ops]
QED

Theorem no_extcode_lower_value:
  (!s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (cfn cenv ty e s))) ==>
  !s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (lower_value cfn cenv ty e s))
Proof
  strip_tac >> simp[lower_value_def] >> rpt strip_tac >>
  irule no_extcode_bind >> simp[no_extcode_unwrap_value]
QED

Theorem no_extcode_store_byte_chunks:
  !p bs off s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_store_byte_chunks p bs off s))
Proof
  recInduct compile_store_byte_chunks_ind >> rpt strip_tac >>
  simp[Once compile_store_byte_chunks_def, no_extcode_fresh_ops] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_emit_op, no_extcode_emit_void]) >> gvs[]
QED

Theorem no_extcode_bytelike_literal:
  !bs n s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_bytelike_literal bs n s))
Proof
  rpt strip_tac >> simp[compile_bytelike_literal_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_emit_void, no_extcode_alloc_buffer,
      no_extcode_store_byte_chunks, no_extcode_fresh_ops])
QED

Theorem no_extcode_literal_vv:
  !ty l s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_literal_vv ty l s))
Proof
  rpt strip_tac >> Cases_on `l` >>
  simp[compile_literal_vv_def, no_extcode_fresh_ops] >>
  TRY (rename1 `BoolL b` >> Cases_on `b` >>
    simp[compile_literal_vv_def, no_extcode_fresh_ops] >> NO_TAC) >>
  Cases_on `ty` >> simp[compile_literal_vv_def, no_extcode_fresh_ops] >>
  TRY (rename1 `BaseT bt` >> Cases_on `bt` >>
    simp[compile_literal_vv_def, no_extcode_fresh_ops]) >>
  TRY (rename1 `BytesT sz` >> Cases_on `sz` >>
    simp[compile_literal_vv_def, no_extcode_fresh_ops]) >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_bytelike_literal, no_extcode_fresh_ops])
QED

Theorem no_extcode_name_vv:
  !ce ty id s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_name_vv ce ty id s))
Proof
  rpt strip_tac >> simp[compile_name_vv_def] >>
  Cases_on `FLOOKUP ce.ce_vars id` >> simp[no_extcode_fresh_ops] >>
  TRY (rename1 `SOME loc` >> Cases_on `loc` >> simp[no_extcode_fresh_ops]) >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_emit_inst, no_extcode_fresh_ops])
QED

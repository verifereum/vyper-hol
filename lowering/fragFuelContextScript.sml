(*
 * Fuel bounds (fuel_ok) for the context-level emission helpers.
 *
 * TOP-LEVEL:
 *   fuel_ok_compile_alloc_buffer, fuel_ok_compile_alloc_dynamic,
 *   fuel_ok_compile_fixed_region_with_id, fuel_ok_compile_copy_memory,
 *   fuel_ok_compile_ptr_load, fuel_ok_compile_ptr_store
 *)

Theory fragFuelContext
Ancestors
  fragFuel fragFuelLoopWcopy emitHelper context venomInst
Libs
  fragFuelLib

Theorem fuel_ok_compile_alloc_buffer:
  !size Wv E. fuel_ok Wv {} E (compile_alloc_buffer size)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_alloc_buffer_def] >>
  fuel_auto [fuel_ok_emit_op] >> simp[is_terminator_def]
QED

Theorem fuel_ok_compile_alloc_dynamic:
  !size_op Wv E. fuel_ok Wv {} E (compile_alloc_dynamic size_op)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_alloc_dynamic_def] >>
  fuel_auto [fuel_ok_emit_op] >> simp[is_terminator_def]
QED

Theorem fuel_ok_compile_fixed_region_with_id:
  !size Wv E. fuel_ok Wv {} E (compile_fixed_region_with_id size)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_fixed_region_with_id_def] >>
  fuel_auto [fuel_ok_emit] >> simp[is_terminator_def, mk_inst_def]
QED

Theorem fuel_ok_compile_copy_memory:
  !dst src n Wv E. fuel_ok Wv {} E (compile_copy_memory dst src n)
Proof
  Cases_on `n` >> simp_tac std_ss [compile_copy_memory_def] >>
  rpt gen_tac >> fuel_auto [fuel_ok_emit_void_any] >> simp[is_terminator_def]
QED

Theorem fuel_ok_compile_imm_load_word:
  !is_ctor imm off Wv E. fuel_ok Wv {} E (compile_imm_load_word is_ctor imm off)
Proof
  Cases_on `imm` >> simp_tac (srw_ss()) [compile_imm_load_word_def] >>
  rpt gen_tac >> fuel_auto [fuel_ok_emit_op] >> simp[is_terminator_def]
QED

Theorem fuel_ok_compile_imm_store_word:
  !imm off v Wv E. fuel_ok Wv {} E (compile_imm_store_word imm off v)
Proof
  Cases_on `imm` >> simp_tac (srw_ss()) [compile_imm_store_word_def] >>
  rpt gen_tac >> fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_ptr_load:
  !is_ctor imm loc op Wv E.
    fuel_ok Wv {} E (compile_ptr_load is_ctor imm loc op)
Proof
  Cases_on `loc` >> simp_tac (srw_ss()) [compile_ptr_load_def] >>
  rpt gen_tac >> fuel_auto [fuel_ok_emit_op, fuel_ok_compile_imm_load_word] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_ptr_store:
  !is_ctor imm loc dst v Wv E.
    fuel_ok Wv {} E (compile_ptr_store is_ctor imm loc dst v)
Proof
  Cases_on `loc` >> simp_tac (srw_ss()) [compile_ptr_store_def] >>
  rpt gen_tac >> fuel_auto [fuel_ok_emit_void_any,
             fuel_ok_compile_imm_store_word] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_word_copy_loop:
  (!src dst count load_loc store_loc is_ctor Wv E.
     fuel_ok Wv {} E
       (compile_word_copy_loop_op src dst count load_loc store_loc is_ctor)) /\
  (!src dst n load_loc store_loc is_ctor Wv E.
     fuel_ok Wv {} E
       (compile_word_copy_loop src dst n load_loc store_loc is_ctor))
Proof
  simp[compile_word_copy_loop_op_def, compile_word_copy_loop_def,
       fuel_ok_compile_word_copy_loop_base]
QED

Theorem fuel_ok_context_copies:
  (!src. fuel_ok Wv {} E (compile_bytestring_word_count src)) /\
  (!imm src dst. fuel_ok Wv {} E (compile_store_immutable_bytestring imm src dst)) /\
  (!slot buf n. fuel_ok Wv {} E (compile_storage_to_memory slot buf n)) /\
  (!buf slot n. fuel_ok Wv {} E (compile_memory_to_storage buf slot n)) /\
  (!slot buf n. fuel_ok Wv {} E (compile_transient_to_memory slot buf n)) /\
  (!buf slot n. fuel_ok Wv {} E (compile_memory_to_transient buf slot n)) /\
  (!src dst n loc. fuel_ok Wv {} E (compile_slot_to_memory src dst n loc)) /\
  (!off dst n. fuel_ok Wv {} E (compile_code_to_memory off dst n))
Proof
  rpt conj_tac >> rpt gen_tac >>
  simp_tac std_ss [compile_bytestring_word_count_def,
    compile_store_immutable_bytestring_def, compile_storage_to_memory_def,
    compile_memory_to_storage_def, compile_transient_to_memory_def,
    compile_memory_to_transient_def, compile_slot_to_memory_def,
    compile_code_to_memory_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_compile_word_copy_loop_base,
             CONJUNCT1 fuel_ok_compile_word_copy_loop,
             CONJUNCT2 fuel_ok_compile_word_copy_loop] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_context_storage:
  (!slot p n sz. fuel_ok Wv {} E (compile_load_storage slot p n sz)) /\
  (!v slot p n. fuel_ok Wv {} E (compile_store_storage v slot p n)) /\
  (!slot p n sz. fuel_ok Wv {} E (compile_load_transient slot p n sz)) /\
  (!off p n sz c. fuel_ok Wv {} E (compile_load_immutable off p n sz c)) /\
  (!off p n sz. fuel_ok Wv {} E (compile_load_calldata off p n sz)) /\
  (!k t v. fuel_ok Wv {} E (compile_nonreentrant_lock k t v)) /\
  (!k t v. fuel_ok Wv {} E (compile_nonreentrant_unlock k t v)) /\
  (!d s l. fuel_ok Wv {} E (compile_copy_memory_dynamic d s l)) /\
  (!b off. fuel_ok Wv {} E (compile_with_byte_offset b off)) /\
  (!p loc. fuel_ok Wv {} E (compile_bytes_data_ptr p loc)) /\
  (!c imm p loc. fuel_ok Wv {} E (compile_bytestring_length c imm p loc)) /\
  (!v. fuel_ok Wv {} E (compile_bytestring_copy_len v)) /\
  (!v d. fuel_ok Wv {} E (compile_store_bytestring v d))
Proof
  rpt conj_tac >> rpt gen_tac >>
  simp_tac std_ss [compile_load_storage_def, compile_store_storage_def,
    compile_load_transient_def, compile_load_immutable_def,
    compile_load_calldata_def, compile_nonreentrant_lock_def,
    compile_nonreentrant_unlock_def, compile_copy_memory_dynamic_def,
    compile_with_byte_offset_def, compile_bytes_data_ptr_def,
    compile_bytestring_length_def, compile_bytestring_copy_len_def,
    compile_store_bytestring_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any, fuel_ok_compile_alloc_buffer,
             fuel_ok_compile_ptr_load, fuel_ok_context_copies,
             CONJUNCT2 fuel_ok_compile_word_copy_loop] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_lit_byte_offset:
  !op off Wv E. fuel_ok Wv {} E (compile_lit_byte_offset op off)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_lit_byte_offset_def] >>
  Cases_on `off = 0` >> simp[fuel_ok_return] >>
  Cases_on `op` >> simp[fuel_ok_return, fuel_ok_emit_op, is_terminator_def]
QED

Theorem fuel_ok_compile_imm_copy_to_memory:
  !n is_ctor imm src dst off Wv E.
    fuel_ok Wv {} E (compile_imm_copy_to_memory is_ctor imm src dst n off)
Proof
  Induct >> simp_tac std_ss [compile_imm_copy_to_memory_def] >> rpt gen_tac >>
  fuel_auto [fuel_ok_emit_void_any, fuel_ok_compile_lit_byte_offset,
             fuel_ok_compile_imm_load_word] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_imm_store_words:
  !n imm src dst off Wv E.
    fuel_ok Wv {} E (compile_imm_store_words imm src dst n off)
Proof
  Induct >> simp_tac std_ss [compile_imm_store_words_def] >> rpt gen_tac >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_compile_lit_byte_offset,
             fuel_ok_compile_imm_store_word] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_ensure_in_memory:
  !ptr loc mb wc is_ctor imm Wv E.
    fuel_ok Wv {} E (compile_ensure_in_memory ptr loc mb wc is_ctor imm)
Proof
  Cases_on `loc` >> simp_tac (srw_ss()) [compile_ensure_in_memory_def] >>
  rpt gen_tac >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any, fuel_ok_compile_alloc_buffer,
             fuel_ok_context_copies, fuel_ok_compile_imm_copy_to_memory] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_store_immutable:
  !imm src off n Wv E. fuel_ok Wv {} E (compile_store_immutable imm src off n)
Proof
  simp[compile_store_immutable_def, fuel_ok_compile_imm_store_words]
QED

Theorem fuel_ok_compile_zero_memory_loop:
  !p i words Wv E. fuel_ok Wv {} E (compile_zero_memory_loop p i words)
Proof
  recInduct compile_zero_memory_loop_ind >> rpt strip_tac >>
  ONCE_REWRITE_TAC [compile_zero_memory_loop_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any] >>
  simp[is_terminator_def]
QED

Theorem fuel_ok_compile_zero_memory:
  !p n Wv E. fuel_ok Wv {} E (compile_zero_memory p n)
Proof
  Cases_on `n` >> simp_tac std_ss [compile_zero_memory_def] >> rpt gen_tac >>
  fuel_auto [fuel_ok_compile_zero_memory_loop]
QED

(*
 * Fuel bounds (fuel_ok) for the straight-line context helpers that the
 * word-copy loop and the other context helpers build on.
 *
 * TOP-LEVEL:
 *   fuel_ok_compile_alloc_buffer, fuel_ok_compile_alloc_dynamic,
 *   fuel_ok_compile_fixed_region_with_id, fuel_ok_compile_copy_memory,
 *   fuel_ok_compile_ptr_load, fuel_ok_compile_ptr_store
 *)

Theory fragFuelContextBase
Ancestors
  fragFuel compileEnv emitHelper context venomInst
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

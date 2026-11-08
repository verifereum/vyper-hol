Theory bodyPtrBytestringBuiltinsOpcodeStmtMemory
Ancestors bodyPtrBytestringBuiltinsOpcodeMemory
          bodyPtrBytestringBuiltinsOpcodeValues
          bodyPtrBytestringBuiltinsOpcodeState stmtLowering context exprLowering compileEnv
Libs BasicProvers

Theorem no_extcode_imm_store_words:
  !imm src dst n off s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_imm_store_words imm src dst n off s))
Proof
  ntac 3 gen_tac >> Induct >> simp[compile_imm_store_words_def, no_extcode_fresh_ops] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_lit_byte_offset, no_extcode_imm_store_word, no_extcode_emit_op])
QED

Theorem no_extcode_dynarray_to_storage:
  !src dst ew em trans s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_dynarray_to_storage src dst ew em trans s))
Proof
  rpt strip_tac >> simp[compile_dynarray_to_storage_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, IF_CASES_TAC] >>
    simp[no_extcode_emit_op, no_extcode_emit_inst, no_extcode_emit_void,
      no_extcode_new_block, no_extcode_fresh_ops, no_extcode_word_copy_loop])
QED

Theorem no_extcode_assign_value:
  !ce dst loc v prim sl dt st da sz s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_assign_value ce dst loc v prim sl dt st da sz s))
Proof
  rpt gen_tac >> Cases_on `loc` >> strip_tac >> simp[compile_assign_value_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, IF_CASES_TAC] >>
    simp[no_extcode_emit_op, no_extcode_emit_inst, no_extcode_emit_void,
      no_extcode_fresh_ops, no_extcode_alloc_buffer, no_extcode_store_memory,
      cj 1 no_extcode_typed_copy, no_extcode_copy_memory,
      no_extcode_imm_store_word, no_extcode_imm_store_words,
      no_extcode_dynarray_to_storage, compile_memory_to_storage_def,
      compile_memory_to_transient_def, no_extcode_word_copy_loop]) >>
  namedCases_on `da` ["", "da_pair"] >> simp[] >>
  TRY (PairCases_on `da_pair` >> simp[]) >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, IF_CASES_TAC] >>
    simp[no_extcode_dynarray_to_storage, no_extcode_emit_op, no_extcode_emit_void,
      no_extcode_word_copy_loop, compile_memory_to_storage_def,
      compile_memory_to_transient_def, no_extcode_fresh_ops]) >>
  simp[no_extcode_dynarray_to_storage]
QED

Theorem no_extcode_store_at_loc:
  !imm dst v loc s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_store_at_loc imm dst v loc s))
Proof
  rpt gen_tac >> Cases_on `loc` >>
  simp[compile_store_at_loc_def, no_extcode_emit_void] >>
  Cases_on `x` >> simp[compile_store_at_loc_def,
    no_extcode_emit_void, no_extcode_imm_store_word]
QED

Theorem no_extcode_tuple_load_all:
  !ce src tys off s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_tuple_load_all ce src tys off s))
Proof
  ntac 2 gen_tac >> Induct >> simp[compile_tuple_load_all_def, no_extcode_fresh_ops] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_emit_op, compile_load_memory_def, no_extcode_fresh_ops]) >>
  rpt strip_tac >> IF_CASES_TAC >> simp[no_extcode_emit_op, no_extcode_fresh_ops]
QED

Theorem no_extcode_load_tuple_elements:
  !ce src tys off s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_load_tuple_elements ce src tys off s))
Proof
  ntac 2 gen_tac >> Induct >> simp[compile_load_tuple_elements_def, no_extcode_fresh_ops] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_emit_op, no_extcode_fresh_ops])
QED

Theorem no_extcode_range_bound_checks:
  !a b r n signed s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_range_bound_checks a b r n signed s))
Proof
  rpt strip_tac >> simp[compile_range_bound_checks_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, IF_CASES_TAC] >>
    simp[no_extcode_emit_op, no_extcode_emit_void])
QED

Theorem no_extcode_iter_elem_copy:
  !ce src dst sz loc slot dt st s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_iter_elem_copy ce src dst sz loc slot dt st s))
Proof
  rpt gen_tac >> Cases_on `loc` >> strip_tac >> simp[compile_iter_elem_copy_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, IF_CASES_TAC] >>
    simp[compile_slot_to_memory_def, no_extcode_word_copy_loop,
      no_extcode_ptr_load, no_extcode_emit_void, no_extcode_emit_op,
      no_extcode_imm_copy_to_memory, no_extcode_copy_memory,
      no_extcode_store_memory, no_extcode_fresh_ops])
QED

Theorem no_extcode_dynarray_append:
  !ce base v ws sz dt st cap prim load store s.
    load <> EXTCODECOPY /\ store <> EXTCODECOPY /\ compiler_no_extcode s ==>
    compiler_no_extcode (SND
      (compile_dynarray_append ce base v ws sz dt st cap prim load store s))
Proof
  rpt strip_tac >> simp[compile_dynarray_append_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, IF_CASES_TAC] >>
    simp[no_extcode_emit_op, no_extcode_emit_void, no_extcode_store_memory,
      no_extcode_word_copy_loop, no_extcode_fresh_ops])
QED

Theorem no_extcode_location_opcodes:
  !loc. load_opc_for loc <> EXTCODECOPY /\ store_opc_for loc <> EXTCODECOPY
Proof
  Cases >> simp[load_opc_for_def, store_opc_for_def]
QED

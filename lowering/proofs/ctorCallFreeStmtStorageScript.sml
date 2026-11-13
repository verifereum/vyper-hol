(* Assignment, local declaration, and loop scaffolding opcode boundaries. *)
Theory ctorCallFreeStmtStorage
Ancestors
  list pair stmtLowering context venomInst loweringShapeDefs
  ctorCallFreeRules ctorCallFreeValues

Theorem call_free_store_at_loc:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_store_at_loc imm dst value loc st)))
Proof
  Cases_on `loc` >- simp[compile_store_at_loc_def, call_free_emit_void] >>
  rename1 `SOME dl` >> Cases_on `dl` >>
  simp[compile_store_at_loc_def, call_free_emit_void, call_free_imm_store_word]
QED

Theorem call_free_tuple_load_all:
  !tys ce src off st.
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_tuple_load_all ce src tys off st)))
Proof
  Induct >> simp[compile_tuple_load_all_def, every_state_insts_return] >>
  rpt gen_tac >> qid_spec_tac `st` >> simp[compile_load_memory_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    gen_tac, IF_CASES_TAC,
    CHANGED_TAC (simp[call_free_emit_op, every_state_insts_return])])
QED

Theorem call_free_declare_local:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (declare_local ce id ty st)))
Proof
  Cases_on `ce.ce_alloca_locals` >>
  simp[declare_local_def, every_state_insts_bind, every_state_insts_return,
    every_state_insts_fresh_var]
QED

Theorem call_free_declare_stmt_local:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (declare_stmt_local ce s st)))
Proof
  Cases_on `s` >> simp[declare_stmt_local_def, call_free_declare_local,
    every_state_insts_return]
QED

Theorem call_free_emit_local_alloca:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (emit_local_alloca ce id st)))
Proof
  simp[emit_local_alloca_def] >>
  rpt (FIRST [CASE_TAC, CHANGED_TAC (simp[call_free_emit_inst, every_state_insts_return])])
QED

Theorem call_free_range_bound_checks:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_range_bound_checks start_op end_op rounds_op bound signed st)))
Proof
  Cases_on `signed` >> qid_spec_tac `st` >> simp[compile_range_bound_checks_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_emit_op, call_free_emit_void])])
QED

Theorem call_free_iter_elem_copy:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_iter_elem_copy ce src dst sz loc slots ty ety st)))
Proof
  Cases_on `slots` >> Cases_on `loc` >> Cases_on `sz <= 32` >>
  Cases_on `is_word_type ty` >> qid_spec_tac `st` >>
  simp[compile_iter_elem_copy_def, compile_slot_to_memory_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_emit_op, call_free_emit_void,
      every_state_insts_return, call_free_word_copy_loop, call_free_ptr_load,
      call_free_imm_copy_to_memory, call_free_copy_memory, call_free_store_memory])])
QED

Theorem call_free_imm_store_words[local]:
  !n imm src dst off st.
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_imm_store_words imm src dst n off st)))
Proof
  Induct >- simp[compile_imm_store_words_def, every_state_insts_return] >>
  rpt gen_tac >> qid_spec_tac `st` >> simp[compile_imm_store_words_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_lit_byte_offset,
      call_free_emit_op, call_free_imm_store_word])])
QED

Theorem call_free_store_immutable_bytestring[local]:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_store_immutable_bytestring imm src dst st)))
Proof
  qid_spec_tac `st` >>
  simp[compile_store_immutable_bytestring_def, compile_bytestring_word_count_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_emit_op,
      call_free_word_copy_loop_base, every_state_insts_return])])
QED

Theorem call_free_dynarray_to_storage[local]:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_dynarray_to_storage src dst ew em trans st)))
Proof
  Cases_on `ew = 1` >> Cases_on `trans` >> qid_spec_tac `st` >>
  simp[compile_dynarray_to_storage_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_emit_op, call_free_emit_void,
      call_free_emit_inst, every_state_insts_fresh_label,
      every_state_insts_fresh_var, every_state_insts_new_block,
      call_free_word_copy_loop])])
QED

Theorem call_free_assign_value:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_assign_value ce dst loc value prim src_loc dty sty da_info sz st)))
Proof
  Cases_on `loc` >> simp[compile_assign_value_def,
    compile_memory_to_storage_def, compile_memory_to_transient_def] >>
  qid_spec_tac `st` >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, IF_CASES_TAC >> qid_spec_tac `st`,
    CASE_TAC >> qid_spec_tac `st`,
    CHANGED_TAC (simp[call_free_emit_op, call_free_emit_void,
      call_free_emit_inst, every_state_insts_return, call_free_alloc_buffer,
      call_free_copy_memory, call_free_store_memory, cj 1 call_free_typed_copy,
      call_free_word_copy_loop, call_free_dynarray_to_storage,
      call_free_imm_store_word, call_free_imm_store_words,
      call_free_store_immutable_bytestring])])
QED

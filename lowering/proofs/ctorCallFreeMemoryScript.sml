(* Safe callback-free dispatcher memory operations. *)
Theory ctorCallFreeMemory
Ancestors
  list compileEnv venomInst loweringShapeDefs emitHelper context exprLowering
  builtinSimple builtinHashing builtinBytes builtinStrings
  ctorCallFreeRules ctorCallFreeValues

Theorem call_free_builtin_len:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_builtin_len ctor imm ptr_op loc st)))
Proof
  simp[compile_builtin_len_def, call_free_ptr_load]
QED

Theorem call_free_zero_words[local]:
  !n ptr_op st.
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_zero_words ptr_op n st)))
Proof
  Induct >- simp[compile_zero_words_def, every_state_insts_return] >>
  gen_tac >> simp[compile_zero_words_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_emit_op, call_free_emit_void])])
QED

Theorem call_free_empty_complex:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_builtin_empty_complex sz bs st)))
Proof
  Cases_on `bs` >> qid_spec_tac `st` >> simp[compile_builtin_empty_complex_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_alloc_buffer, call_free_zero_words,
      call_free_emit_void, every_state_insts_return])])
QED

Theorem call_free_bytestring_widen_copy:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_bytestring_widen_copy dst_size v src_size st)))
Proof
  simp[compile_bytestring_widen_copy_def, every_state_insts_bind,
    every_state_insts_ignore_bind, call_free_alloc_buffer,
    call_free_copy_memory, every_state_insts_return]
QED

Theorem call_free_keccak:
  (!v st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_keccak256_word v st)))) /\
  (!v m st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_keccak256_bytesm v m st)))) /\
  (!v st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_keccak256_bytes v st)))) /\
  (!v st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_bytestring_hash v st))))
Proof
  rpt conj_tac >> rpt gen_tac >> qid_spec_tac `st` >>
  simp[compile_keccak256_word_def, compile_keccak256_bytesm_def,
    compile_keccak256_bytes_def, compile_bytestring_hash_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_alloc_buffer, call_free_emit_op,
      call_free_emit_void, every_state_insts_return])])
QED

Theorem call_free_method_id_hash[local]:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_method_id_hash ty v st)))
Proof
  Cases_on `ty` >> simp[compile_method_id_hash_def, call_free_keccak] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[compile_method_id_hash_def, call_free_keccak] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  simp[compile_method_id_hash_def, call_free_keccak]
QED

Theorem call_free_method_id_runtime:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_method_id_runtime ty v bytes4 st)))
Proof
  Cases_on `bytes4` >> qid_spec_tac `st` >> simp[compile_method_id_runtime_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_method_id_hash, call_free_alloc_buffer,
      call_free_emit_op, call_free_emit_void, every_state_insts_return])])
QED

Theorem call_free_assert_slice_bounds[local]:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_assert_slice_bounds start len src_len st)))
Proof
  qid_spec_tac `st` >> simp[compile_assert_slice_bounds_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_emit_op, call_free_emit_void])])
QED

Theorem call_free_bytestring_src:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_bytestring_src src st)))
Proof
  simp[compile_bytestring_src_def, every_state_insts_bind,
    call_free_emit_op, every_state_insts_return]
QED

Theorem call_free_slice_out_buf:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_slice_out_buf out_size st)))
Proof
  simp[compile_slice_out_buf_def, every_state_insts_bind,
    call_free_alloc_buffer, call_free_emit_op, every_state_insts_return]
QED

Theorem call_free_slice_data:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_slice_data src_len src_data start len out_size st)))
Proof
  qid_spec_tac `st` >> simp[compile_slice_data_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_assert_slice_bounds, call_free_alloc_buffer,
      call_free_emit_op, call_free_emit_void, every_state_insts_return])])
QED

Theorem call_free_slice_adhoc:
  (!start len out_size st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_slice_calldata start len out_size st)))) /\
  (!start len out_size st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_slice_code start len out_size st)))) /\
  (!addr start len out_buf out_data st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_slice_extcode addr start len out_buf out_data st))))
Proof
  rpt conj_tac >> rpt gen_tac >> qid_spec_tac `st` >>
  simp[compile_slice_calldata_def, compile_slice_code_def, compile_slice_extcode_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    CHANGED_TAC (simp[call_free_slice_out_buf, call_free_assert_slice_bounds,
      call_free_emit_op, call_free_emit_void, every_state_insts_return]),
    gen_tac, pairarg_tac >> gvs[] >> qid_spec_tac `st`])
QED

Theorem call_free_extract32_load:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_extract32_load src_len src_data start st)))
Proof
  simp[compile_extract32_load_def, every_state_insts_bind,
    every_state_insts_ignore_bind, call_free_assert_slice_bounds, call_free_emit_op]
QED

Theorem call_free_uint2str:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_uint2str v nd sz st)))
Proof
  qid_spec_tac `st` >> simp[compile_uint2str_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_alloc_buffer, call_free_emit_inst,
      call_free_emit_op, call_free_emit_void, every_state_insts_return,
      every_state_insts_fresh_var, every_state_insts_fresh_label,
      every_state_insts_new_block])])
QED

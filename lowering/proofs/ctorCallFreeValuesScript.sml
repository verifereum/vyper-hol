(* Opcode preservation at the memory/value boundary. *)
Theory ctorCallFreeValues
Ancestors
  list compileEnv venomInst loweringShapeDefs emitHelper context exprLowering
  ctorCallFreeRules

Theorem call_free_alloc_buffer:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_alloc_buffer sz st)))
Proof
  simp[compile_alloc_buffer_def, every_state_insts_bind,
       every_state_insts_return, call_free_emit_op]
QED

Theorem call_free_imm_load_word:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_imm_load_word ctor imm off st)))
Proof
  Cases_on `ctor` >> Cases_on `imm` >>
  simp[compile_imm_load_word_def, every_state_insts_bind, call_free_emit_op]
QED

Theorem call_free_imm_store_word:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_imm_store_word imm off v st)))
Proof
  Cases_on `imm` >>
  simp[compile_imm_store_word_def, every_state_insts_bind,
       call_free_emit_op, call_free_emit_void]
QED

Theorem call_free_ptr_load:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_ptr_load ctor imm loc op st)))
Proof
  Cases_on `loc` >> simp[compile_ptr_load_def, call_free_imm_load_word,
                        call_free_emit_op]
QED

Theorem call_free_ptr_store:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_ptr_store ctor imm loc dst v st)))
Proof
  Cases_on `loc` >> Cases_on `ctor` >>
  simp[compile_ptr_store_def, call_free_imm_store_word, call_free_emit_void]
QED

Theorem call_free_copy_memory:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_copy_memory dst src sz st)))
Proof
  Cases_on `sz` >> simp[compile_copy_memory_def,
                       every_state_insts_return, call_free_emit_void]
QED

Theorem call_free_word_copy_loop_base:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND
      (compile_word_copy_loop_base src dst nwords ll sl ctor imm st)))
Proof
  Cases_on `word_scale ll = 1` >> Cases_on `word_scale sl = 1` >>
  qid_spec_tac `st` >> simp[compile_word_copy_loop_base_def] >>
  rpt (FIRST [
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac,
    CHANGED_TAC (simp[every_state_insts_fresh_label,
      every_state_insts_fresh_var, every_state_insts_new_block,
      call_free_emit_inst, call_free_emit_op, call_free_ptr_load,
      call_free_ptr_store])])
QED

Theorem call_free_word_copy_loop:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND
      (compile_word_copy_loop src dst nwords ll sl ctor st)))
Proof
  simp[compile_word_copy_loop_def, compile_word_copy_loop_op_def,
       call_free_word_copy_loop_base]
QED

Theorem call_free_store_byte_chunks:
  !dst bs off st.
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_store_byte_chunks dst bs off st)))
Proof
  recInduct compile_store_byte_chunks_ind >> conj_tac
  >- simp[compile_store_byte_chunks_def, every_state_insts_return] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  simp[Once compile_store_byte_chunks_def] >>
  ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- simp[call_free_emit_op] >>
  gen_tac >> ho_match_mp_tac every_state_insts_ignore_bind >>
  simp[call_free_emit_void]
QED

Theorem call_free_bytelike_literal:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_bytelike_literal bs max_len st)))
Proof
  simp[compile_bytelike_literal_def, every_state_insts_bind,
       every_state_insts_ignore_bind, call_free_alloc_buffer,
       call_free_store_byte_chunks, call_free_emit_void,
       every_state_insts_return]
QED

Theorem call_free_literal_vv:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_literal_vv ty lit st)))
Proof
  Cases_on `lit`
  >- (rename1 `BoolL b` >> Cases_on `b` >>
      simp[compile_literal_vv_def, every_state_insts_return]) >>
  simp[compile_literal_vv_def,
       call_free_bytelike_literal, every_state_insts_return,
       every_state_insts_bind] >>
  rpt (CASE_TAC >> simp[call_free_bytelike_literal,
       every_state_insts_return, every_state_insts_bind])
QED

Theorem call_free_name_vv:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_name_vv ce ty nm st)))
Proof
  simp[compile_name_vv_def] >>
  rpt (CASE_TAC >> simp[every_state_insts_return,
       every_state_insts_ignore_bind, call_free_emit_inst])
QED

Theorem call_free_lit_byte_offset:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_lit_byte_offset op off st)))
Proof
  Cases_on `off = 0` >> Cases_on `op` >>
  simp[compile_lit_byte_offset_def, every_state_insts_return, call_free_emit_op]
QED

Theorem call_free_imm_copy_to_memory:
  !n ctor imm src dst off st.
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_imm_copy_to_memory ctor imm src dst n off st)))
Proof
  Induct >- simp[compile_imm_copy_to_memory_def, every_state_insts_return] >>
  rpt gen_tac >> qid_spec_tac `st` >> simp[compile_imm_copy_to_memory_def] >>
  rpt (FIRST [
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac,
    CHANGED_TAC (simp[call_free_lit_byte_offset, call_free_imm_load_word,
                     call_free_emit_void])])
QED

Theorem call_free_ensure_in_memory:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_ensure_in_memory ptr_op loc sz nw ctor imm st)))
Proof
  Cases_on `loc` >> Cases_on `nw = 1` >> qid_spec_tac `st` >>
  simp[compile_ensure_in_memory_def, compile_storage_to_memory_def,
       compile_transient_to_memory_def] >>
  rpt (FIRST [
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac,
    CHANGED_TAC (simp[call_free_alloc_buffer, call_free_emit_op,
      call_free_emit_void, call_free_word_copy_loop,
      call_free_imm_copy_to_memory, every_state_insts_return])])
QED

Theorem call_free_unwrap_value:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (unwrap_value ce vv st)))
Proof
  Cases_on `vv` >> simp[unwrap_value_def, every_state_insts_return] >>
  rename1 `is_word_type ty` >> rename1 `pp.ptr_location` >>
  Cases_on `is_word_type ty` >>
  simp[call_free_ptr_load] >> Cases_on `pp.ptr_location` >>
  simp[call_free_ensure_in_memory, every_state_insts_return]
QED

Theorem call_free_with_byte_offset:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_with_byte_offset base_op off st)))
Proof
  Cases_on `off = 0` >>
  simp[compile_with_byte_offset_def, every_state_insts_return, call_free_emit_op]
QED

Theorem call_free_bytestring_copy_len:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_bytestring_copy_len src st)))
Proof
  qid_spec_tac `st` >> simp[compile_bytestring_copy_len_def] >>
  rpt (FIRST [
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_emit_op])])
QED

Theorem call_free_store_bytestring:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_store_bytestring src dst st)))
Proof
  simp[compile_store_bytestring_def, every_state_insts_bind,
       call_free_bytestring_copy_len, call_free_emit_void]
QED

Theorem call_free_copy_memory_dynamic:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_copy_memory_dynamic dst src len st)))
Proof
  simp[compile_copy_memory_dynamic_def, call_free_emit_void]
QED

Theorem call_free_typed_copy:
  (!ce dst dty src sty st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_store_memory_typed ce dst dty src sty st)))) /\
  (!ce dst src dtys stys doff soff st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_typed_copy_fields ce dst src dtys stys doff soff st)))) /\
  (!ce dst dty src sty ncopy st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_copy_sarray_typed ce dst dty src sty ncopy st)))) /\
  (!ce dst dty cap src sty st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_copy_dynarray_typed ce dst dty cap src sty st)))) /\
  (!ce dst src dfs sfs doff soff st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_struct_typed_copy ce dst src dfs sfs doff soff st))))
Proof
  ho_match_mp_tac compile_store_memory_typed_ind >>
  rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      simp[Once compile_store_memory_typed_def] >>
      rpt IF_CASES_TAC >>
      simp[every_state_insts_bind, call_free_emit_op, call_free_emit_void,
           call_free_store_bytestring] >>
      Cases_on `dty` >> Cases_on `sty` >>
      simp[call_free_copy_memory] >>
      rpt (CASE_TAC >> gvs[]) >>
      gvs[call_free_copy_memory]) >>
  rpt gen_tac >> strip_tac >>
  gvs[] >>
  simp[Once compile_store_memory_typed_def, every_state_insts_return] >>
  rpt (FIRST [
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    CHANGED_TAC (simp[call_free_with_byte_offset, call_free_copy_memory,
      call_free_copy_memory_dynamic, call_free_emit_op, call_free_emit_void,
      call_free_emit_inst, every_state_insts_fresh_label,
      every_state_insts_fresh_var, every_state_insts_new_block,
      every_state_insts_return]),
    IF_CASES_TAC >> gvs[],
    gen_tac]) >>
  pairarg_tac >> gvs[] >> qid_spec_tac `st` >>
  rpt (FIRST [
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    CHANGED_TAC (simp[call_free_with_byte_offset]), gen_tac])
QED

Theorem call_free_store_memory:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_store_memory ce src dst dty sty st)))
Proof
  simp[compile_store_memory_def] >> rpt IF_CASES_TAC >>
  simp[call_free_emit_void, call_free_store_bytestring,
       cj 1 call_free_typed_copy, call_free_copy_memory]
QED

Theorem call_free_ifexp_arm:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_ifexp_arm ce rty aty vv st)))
Proof
  qid_spec_tac `st` >> simp[compile_ifexp_arm_def] >> IF_CASES_TAC >>
  simp[call_free_unwrap_value] >>
  rpt (FIRST [
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_alloc_buffer,
      call_free_unwrap_value, call_free_store_memory, every_state_insts_return])])
QED

Theorem call_free_materialize_vv:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_materialize_vv ce ty vv st)))
Proof
  qid_spec_tac `st` >> simp[compile_materialize_vv_def] >>
  rpt (FIRST [
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_alloc_buffer,
      call_free_unwrap_value, call_free_store_memory, every_state_insts_return])])
QED

Theorem call_free_dynarray_pop:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_dynarray_pop ptr_op scale esz ctor imm loc st)))
Proof
  qid_spec_tac `st` >> simp[compile_dynarray_pop_def] >>
  rpt (FIRST [
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_ptr_load, call_free_ptr_store,
      call_free_emit_op, call_free_emit_void])])
QED

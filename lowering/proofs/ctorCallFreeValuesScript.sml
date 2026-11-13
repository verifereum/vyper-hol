(* Opcode preservation at the memory/value boundary. *)
Theory ctorCallFreeValues
Ancestors
  list compileEnv venomInst loweringShapeDefs emitHelper context exprLowering
  ctorCallFreeRules

Theorem opcode_every_alloc_buffer:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode)
    (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_alloc_buffer sz st)))
  )
Proof
  strip_tac >>
  simp[compile_alloc_buffer_def, every_state_insts_bind,
       every_state_insts_return, opcode_every_emit_op]
QED

Theorem call_free_alloc_buffer:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_alloc_buffer sz st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_alloc_buffer) >> simp[]
QED

Theorem opcode_every_imm_load_word:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode)
    (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_imm_load_word ctor imm off st)))
  )
Proof
  strip_tac >>
  Cases_on `ctor` >> Cases_on `imm` >>
  simp[compile_imm_load_word_def, every_state_insts_bind, opcode_every_emit_op]
QED

Theorem call_free_imm_load_word:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_imm_load_word ctor imm off st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_imm_load_word) >> simp[]
QED

Theorem opcode_every_imm_store_word:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode)
    (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_imm_store_word imm off v st)))
  )
Proof
  strip_tac >>
  Cases_on `imm` >>
  simp[compile_imm_store_word_def, every_state_insts_bind,
       opcode_every_emit_op, opcode_every_emit_void]
QED

Theorem call_free_imm_store_word:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_imm_store_word imm off v st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_imm_store_word) >> simp[]
QED

Theorem opcode_every_ptr_load:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode)
    (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_ptr_load ctor imm loc op st)))
  )
Proof
  strip_tac >>
  Cases_on `loc` >> simp[compile_ptr_load_def, (UNDISCH opcode_every_imm_load_word),
                        opcode_every_emit_op]
QED

Theorem call_free_ptr_load:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_ptr_load ctor imm loc op st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_ptr_load) >> simp[]
QED

Theorem opcode_every_ptr_store:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode)
    (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_ptr_store ctor imm loc dst v st)))
  )
Proof
  strip_tac >>
  Cases_on `loc` >> Cases_on `ctor` >>
  simp[compile_ptr_store_def, (UNDISCH opcode_every_imm_store_word), opcode_every_emit_void]
QED

Theorem call_free_ptr_store:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_ptr_store ctor imm loc dst v st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_ptr_store) >> simp[]
QED

Theorem opcode_every_copy_memory:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode)
    (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_copy_memory dst src sz st)))
  )
Proof
  strip_tac >>
  Cases_on `sz` >> simp[compile_copy_memory_def,
                       every_state_insts_return, opcode_every_emit_void]
QED

Theorem call_free_copy_memory:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_copy_memory dst src sz st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_copy_memory) >> simp[]
QED

Theorem opcode_every_word_copy_loop_base:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode)
    (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND
      (compile_word_copy_loop_base src dst nwords ll sl ctor imm st)))
  )
Proof
  strip_tac >>
  Cases_on `word_scale ll = 1` >> Cases_on `word_scale sl = 1` >>
  qid_spec_tac `st` >> simp[compile_word_copy_loop_base_def] >>
  rpt (FIRST [
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac,
    CHANGED_TAC (simp[every_state_insts_fresh_label,
      every_state_insts_fresh_var, every_state_insts_new_block,
      opcode_every_emit_inst, opcode_every_emit_op, (UNDISCH opcode_every_ptr_load),
      (UNDISCH opcode_every_ptr_store)])])
QED

Theorem call_free_word_copy_loop_base:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND
      (compile_word_copy_loop_base src dst nwords ll sl ctor imm st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_word_copy_loop_base) >> simp[]
QED

Theorem opcode_every_word_copy_loop:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode)
    (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND
      (compile_word_copy_loop src dst nwords ll sl ctor st)))
  )
Proof
  strip_tac >>
  simp[compile_word_copy_loop_def, compile_word_copy_loop_op_def,
       (UNDISCH opcode_every_word_copy_loop_base)]
QED

Theorem call_free_word_copy_loop:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND
      (compile_word_copy_loop src dst nwords ll sl ctor st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_word_copy_loop) >> simp[]
QED

Theorem opcode_every_store_byte_chunks:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  !dst bs off st.
  EVERY (\i. P i.inst_opcode)
    (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_store_byte_chunks dst bs off st)))
  )
Proof
  strip_tac >>
  recInduct compile_store_byte_chunks_ind >> conj_tac
  >- simp[compile_store_byte_chunks_def, every_state_insts_return] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  simp[Once compile_store_byte_chunks_def] >>
  ho_match_mp_tac every_state_insts_bind >> conj_tac
  >- simp[opcode_every_emit_op] >>
  gen_tac >> ho_match_mp_tac every_state_insts_ignore_bind >>
  simp[opcode_every_emit_void]
QED

Theorem call_free_store_byte_chunks:
  !dst bs off st.
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_store_byte_chunks dst bs off st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_store_byte_chunks) >> simp[]
QED

Theorem opcode_every_bytelike_literal:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode)
    (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_bytelike_literal bs max_len st)))
  )
Proof
  strip_tac >>
  simp[compile_bytelike_literal_def, every_state_insts_bind,
       every_state_insts_ignore_bind, (UNDISCH opcode_every_alloc_buffer),
       (UNDISCH opcode_every_store_byte_chunks), opcode_every_emit_void,
       every_state_insts_return]
QED

Theorem call_free_bytelike_literal:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_bytelike_literal bs max_len st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_bytelike_literal) >> simp[]
QED

Theorem opcode_every_literal_vv:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode)
    (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_literal_vv ty lit st)))
  )
Proof
  strip_tac >>
  Cases_on `lit`
  >- (rename1 `BoolL b` >> Cases_on `b` >>
      simp[compile_literal_vv_def, every_state_insts_return]) >>
  simp[compile_literal_vv_def,
       (UNDISCH opcode_every_bytelike_literal), every_state_insts_return,
       every_state_insts_bind] >>
  rpt (CASE_TAC >> simp[(UNDISCH opcode_every_bytelike_literal),
       every_state_insts_return, every_state_insts_bind])
QED

Theorem call_free_literal_vv:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_literal_vv ty lit st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_literal_vv) >> simp[]
QED

Theorem opcode_every_name_vv:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode)
    (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_name_vv ce ty nm st)))
  )
Proof
  strip_tac >>
  simp[compile_name_vv_def] >>
  rpt (CASE_TAC >> simp[every_state_insts_return,
       every_state_insts_ignore_bind, opcode_every_emit_inst])
QED

Theorem call_free_name_vv:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_name_vv ce ty nm st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_name_vv) >> simp[]
QED

Theorem opcode_every_lit_byte_offset:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode)
    (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_lit_byte_offset op off st)))
  )
Proof
  strip_tac >>
  Cases_on `off = 0` >> Cases_on `op` >>
  simp[compile_lit_byte_offset_def, every_state_insts_return, opcode_every_emit_op]
QED

Theorem call_free_lit_byte_offset:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_lit_byte_offset op off st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_lit_byte_offset) >> simp[]
QED

Theorem opcode_every_imm_copy_to_memory:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  !n ctor imm src dst off st.
  EVERY (\i. P i.inst_opcode)
    (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_imm_copy_to_memory ctor imm src dst n off st)))
  )
Proof
  strip_tac >>
  Induct >- simp[compile_imm_copy_to_memory_def, every_state_insts_return] >>
  rpt gen_tac >> qid_spec_tac `st` >> simp[compile_imm_copy_to_memory_def] >>
  rpt (FIRST [
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac,
    CHANGED_TAC (simp[(UNDISCH opcode_every_lit_byte_offset), (UNDISCH opcode_every_imm_load_word),
                     opcode_every_emit_void])])
QED

Theorem call_free_imm_copy_to_memory:
  !n ctor imm src dst off st.
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_imm_copy_to_memory ctor imm src dst n off st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_imm_copy_to_memory) >> simp[]
QED

Theorem opcode_every_ensure_in_memory:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode)
    (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_ensure_in_memory ptr_op loc sz nw ctor imm st)))
  )
Proof
  strip_tac >>
  Cases_on `loc` >> Cases_on `nw = 1` >> qid_spec_tac `st` >>
  simp[compile_ensure_in_memory_def, compile_storage_to_memory_def,
       compile_transient_to_memory_def] >>
  rpt (FIRST [
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac,
    CHANGED_TAC (simp[(UNDISCH opcode_every_alloc_buffer), opcode_every_emit_op,
      opcode_every_emit_void, (UNDISCH opcode_every_word_copy_loop),
      (UNDISCH opcode_every_imm_copy_to_memory), every_state_insts_return])])
QED

Theorem call_free_ensure_in_memory:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_ensure_in_memory ptr_op loc sz nw ctor imm st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_ensure_in_memory) >> simp[]
QED

Theorem opcode_every_unwrap_value:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode)
    (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (unwrap_value ce vv st)))
  )
Proof
  strip_tac >>
  Cases_on `vv` >> simp[unwrap_value_def, every_state_insts_return] >>
  rename1 `is_word_type ty` >> rename1 `pp.ptr_location` >>
  Cases_on `is_word_type ty` >>
  simp[(UNDISCH opcode_every_ptr_load)] >> Cases_on `pp.ptr_location` >>
  simp[(UNDISCH opcode_every_ensure_in_memory), every_state_insts_return]
QED

Theorem call_free_unwrap_value:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (unwrap_value ce vv st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_unwrap_value) >> simp[]
QED

Theorem opcode_every_with_byte_offset:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode)
    (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_with_byte_offset base_op off st)))
  )
Proof
  strip_tac >>
  Cases_on `off = 0` >>
  simp[compile_with_byte_offset_def, every_state_insts_return, opcode_every_emit_op]
QED

Theorem call_free_with_byte_offset:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_with_byte_offset base_op off st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_with_byte_offset) >> simp[]
QED

Theorem opcode_every_bytestring_copy_len:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode)
    (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_bytestring_copy_len src st)))
  )
Proof
  strip_tac >>
  qid_spec_tac `st` >> simp[compile_bytestring_copy_len_def] >>
  rpt (FIRST [
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[opcode_every_emit_op])])
QED

Theorem call_free_bytestring_copy_len:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_bytestring_copy_len src st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_bytestring_copy_len) >> simp[]
QED

Theorem opcode_every_store_bytestring:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode)
    (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_store_bytestring src dst st)))
  )
Proof
  strip_tac >>
  simp[compile_store_bytestring_def, every_state_insts_bind,
       (UNDISCH opcode_every_bytestring_copy_len), opcode_every_emit_void]
QED

Theorem call_free_store_bytestring:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_store_bytestring src dst st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_store_bytestring) >> simp[]
QED

Theorem opcode_every_copy_memory_dynamic:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode)
    (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_copy_memory_dynamic dst src len st)))
  )
Proof
  strip_tac >>
  simp[compile_copy_memory_dynamic_def, opcode_every_emit_void]
QED

Theorem call_free_copy_memory_dynamic:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_copy_memory_dynamic dst src len st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_copy_memory_dynamic) >> simp[]
QED

Theorem opcode_every_typed_copy:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!ce dst dty src sty st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_store_memory_typed ce dst dty src sty st)))) /\
  (!ce dst src dtys stys doff soff st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_typed_copy_fields ce dst src dtys stys doff soff st)))) /\
  (!ce dst dty src sty ncopy st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_copy_sarray_typed ce dst dty src sty ncopy st)))) /\
  (!ce dst dty cap src sty st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_copy_dynarray_typed ce dst dty cap src sty st)))) /\
  (!ce dst src dfs sfs doff soff st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_struct_typed_copy ce dst src dfs sfs doff soff st))))
  )
Proof
  strip_tac >>
  ho_match_mp_tac compile_store_memory_typed_ind >>
  rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      simp[Once compile_store_memory_typed_def] >>
      rpt IF_CASES_TAC >>
      simp[every_state_insts_bind, opcode_every_emit_op, opcode_every_emit_void,
           (UNDISCH opcode_every_store_bytestring)] >>
      Cases_on `dty` >> Cases_on `sty` >>
      simp[(UNDISCH opcode_every_copy_memory)] >>
      rpt (CASE_TAC >> gvs[]) >>
      gvs[(UNDISCH opcode_every_copy_memory)]) >>
  rpt gen_tac >> strip_tac >>
  gvs[] >>
  simp[Once compile_store_memory_typed_def, every_state_insts_return] >>
  rpt (FIRST [
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    CHANGED_TAC (simp[(UNDISCH opcode_every_with_byte_offset), (UNDISCH opcode_every_copy_memory),
      (UNDISCH opcode_every_copy_memory_dynamic), opcode_every_emit_op, opcode_every_emit_void,
      opcode_every_emit_inst, every_state_insts_fresh_label,
      every_state_insts_fresh_var, every_state_insts_new_block,
      every_state_insts_return]),
    IF_CASES_TAC >> gvs[],
    gen_tac]) >>
  pairarg_tac >> gvs[] >> qid_spec_tac `st` >>
  rpt (FIRST [
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    CHANGED_TAC (simp[(UNDISCH opcode_every_with_byte_offset)]), gen_tac])
QED

Theorem call_free_typed_copy:
  (!ce dst dty src sty st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_store_memory_typed ce dst dty src sty st)))) /\
  (!ce dst src dtys stys doff soff st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_typed_copy_fields ce dst src dtys stys doff soff st)))) /\
  (!ce dst dty src sty ncopy st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_copy_sarray_typed ce dst dty src sty ncopy st)))) /\
  (!ce dst dty cap src sty st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_copy_dynarray_typed ce dst dty cap src sty st)))) /\
  (!ce dst src dfs sfs doff soff st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_struct_typed_copy ce dst src dfs sfs doff soff st))))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_typed_copy) >> simp[]
QED

Theorem opcode_every_store_memory:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_store_memory ce src dst dty sty st)))
  )
Proof
  strip_tac >>
  simp[compile_store_memory_def] >> rpt IF_CASES_TAC >>
  simp[opcode_every_emit_void, (UNDISCH opcode_every_store_bytestring),
       cj 1 (UNDISCH opcode_every_typed_copy), (UNDISCH opcode_every_copy_memory)]
QED

Theorem call_free_store_memory:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_store_memory ce src dst dty sty st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_store_memory) >> simp[]
QED

Theorem opcode_every_ifexp_arm:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_ifexp_arm ce rty aty vv st)))
  )
Proof
  strip_tac >>
  qid_spec_tac `st` >> simp[compile_ifexp_arm_def] >> IF_CASES_TAC >>
  simp[(UNDISCH opcode_every_unwrap_value)] >>
  rpt (FIRST [
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[(UNDISCH opcode_every_alloc_buffer),
      (UNDISCH opcode_every_unwrap_value), (UNDISCH opcode_every_store_memory), every_state_insts_return])])
QED

Theorem call_free_ifexp_arm:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_ifexp_arm ce rty aty vv st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_ifexp_arm) >> simp[]
QED

Theorem opcode_every_materialize_vv:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_materialize_vv ce ty vv st)))
  )
Proof
  strip_tac >>
  qid_spec_tac `st` >> simp[compile_materialize_vv_def] >>
  rpt (FIRST [
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[(UNDISCH opcode_every_alloc_buffer),
      (UNDISCH opcode_every_unwrap_value), (UNDISCH opcode_every_store_memory), every_state_insts_return])])
QED

Theorem call_free_materialize_vv:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_materialize_vv ce ty vv st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_materialize_vv) >> simp[]
QED

Theorem opcode_every_snapshot_vv:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_snapshot_vv ce copy vv st)))
  )
Proof
  strip_tac >>
  qid_spec_tac `st` >> simp[compile_snapshot_vv_def] >>
  rpt (FIRST [IF_CASES_TAC >> qid_spec_tac `st`,
    ho_match_mp_tac every_state_insts_bind >> conj_tac, gen_tac,
    CHANGED_TAC (simp[(UNDISCH opcode_every_unwrap_value), (UNDISCH opcode_every_materialize_vv),
      every_state_insts_return])])
QED

Theorem call_free_snapshot_vv:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_snapshot_vv ce copy vv st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_snapshot_vv) >> simp[]
QED


Theorem opcode_every_dynarray_pop:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_dynarray_pop ptr_op scale esz ctor imm loc st)))
  )
Proof
  strip_tac >>
  qid_spec_tac `st` >> simp[compile_dynarray_pop_def] >>
  rpt (FIRST [
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[(UNDISCH opcode_every_ptr_load), (UNDISCH opcode_every_ptr_store),
      opcode_every_emit_op, opcode_every_emit_void])])
QED

Theorem call_free_dynarray_pop:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_dynarray_pop ptr_op scale esz ctor imm loc st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_dynarray_pop) >> simp[]
QED

(* Assignment, local declaration, and loop scaffolding opcode boundaries. *)
Theory ctorCallFreeStmtStorage
Ancestors
  list pair stmtLowering context venomInst loweringShapeDefs
  ctorCallFreeRules ctorCallFreeValues

Theorem opcode_every_store_at_loc:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_store_at_loc imm dst value loc st)))
  )
Proof
  strip_tac >>
  Cases_on `loc` >- simp[compile_store_at_loc_def, opcode_every_emit_void] >>
  rename1 `SOME dl` >> Cases_on `dl` >>
  simp[compile_store_at_loc_def, opcode_every_emit_void, (UNDISCH opcode_every_imm_store_word)]
QED

Theorem call_free_store_at_loc:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_store_at_loc imm dst value loc st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_store_at_loc) >> simp[]
QED

Theorem opcode_every_tuple_load_all:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  !tys ce src off st.
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_tuple_load_all ce src tys off st)))
  )
Proof
  strip_tac >>
  Induct >> simp[compile_tuple_load_all_def, every_state_insts_return] >>
  rpt gen_tac >> qid_spec_tac `st` >> simp[compile_load_memory_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    gen_tac, IF_CASES_TAC,
    CHANGED_TAC (simp[opcode_every_emit_op, every_state_insts_return])])
QED

Theorem call_free_tuple_load_all:
  !tys ce src off st.
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_tuple_load_all ce src tys off st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_tuple_load_all) >> simp[]
QED

Theorem opcode_every_declare_local:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (declare_local ce id ty st)))
  )
Proof
  strip_tac >>
  Cases_on `ce.ce_alloca_locals` >>
  simp[declare_local_def, every_state_insts_bind, every_state_insts_return,
    every_state_insts_fresh_var]
QED

Theorem call_free_declare_local:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (declare_local ce id ty st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_declare_local) >> simp[]
QED

Theorem opcode_every_declare_stmt_local:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (declare_stmt_local ce s st)))
  )
Proof
  strip_tac >>
  Cases_on `s` >> simp[declare_stmt_local_def, (UNDISCH opcode_every_declare_local),
    every_state_insts_return]
QED

Theorem call_free_declare_stmt_local:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (declare_stmt_local ce s st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_declare_stmt_local) >> simp[]
QED

Theorem opcode_every_emit_local_alloca:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (emit_local_alloca ce id st)))
  )
Proof
  strip_tac >>
  simp[emit_local_alloca_def] >>
  rpt (FIRST [CASE_TAC, CHANGED_TAC (simp[opcode_every_emit_inst, every_state_insts_return])])
QED

Theorem call_free_emit_local_alloca:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (emit_local_alloca ce id st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_emit_local_alloca) >> simp[]
QED

Theorem opcode_every_range_bound_checks:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_range_bound_checks start_op end_op rounds_op bound signed st)))
  )
Proof
  strip_tac >>
  Cases_on `signed` >> qid_spec_tac `st` >> simp[compile_range_bound_checks_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void])])
QED

Theorem call_free_range_bound_checks:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_range_bound_checks start_op end_op rounds_op bound signed st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_range_bound_checks) >> simp[]
QED

Theorem opcode_every_iter_elem_copy:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_iter_elem_copy ce src dst sz loc slots ty ety st)))
  )
Proof
  strip_tac >>
  Cases_on `slots` >> Cases_on `loc` >> Cases_on `sz <= 32` >>
  Cases_on `is_word_type ty` >> qid_spec_tac `st` >>
  simp[compile_iter_elem_copy_def, compile_slot_to_memory_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void,
      every_state_insts_return, (UNDISCH opcode_every_word_copy_loop), (UNDISCH opcode_every_ptr_load),
      (UNDISCH opcode_every_imm_copy_to_memory), (UNDISCH opcode_every_copy_memory), (UNDISCH opcode_every_store_memory)])])
QED

Theorem call_free_iter_elem_copy:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_iter_elem_copy ce src dst sz loc slots ty ety st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_iter_elem_copy) >> simp[]
QED

Theorem opcode_every_imm_store_words[local]:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  !n imm src dst off st.
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_imm_store_words imm src dst n off st)))
  )
Proof
  strip_tac >>
  Induct >- simp[compile_imm_store_words_def, every_state_insts_return] >>
  rpt gen_tac >> qid_spec_tac `st` >> simp[compile_imm_store_words_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[(UNDISCH opcode_every_lit_byte_offset),
      opcode_every_emit_op, (UNDISCH opcode_every_imm_store_word)])])
QED

Theorem opcode_every_store_immutable_bytestring[local]:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_store_immutable_bytestring imm src dst st)))
  )
Proof
  strip_tac >>
  qid_spec_tac `st` >>
  simp[compile_store_immutable_bytestring_def, compile_bytestring_word_count_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[opcode_every_emit_op,
      (UNDISCH opcode_every_word_copy_loop_base), every_state_insts_return])])
QED

Theorem opcode_every_store_slots:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!cenv src slot ty transient st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_store_slots cenv src slot ty transient st)))) /\
  (!cenv src slot members mem_off slot_off transient st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_store_slots_members cenv src slot members
                           mem_off slot_off transient st)))) /\
  (!cenv src slot elem count_op transient st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_copy_elements_to_slots cenv src slot elem
                           count_op transient st))))
  )
Proof
  strip_tac >>
  ho_match_mp_tac compile_store_slots_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> simp[Once compile_store_slots_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    IF_CASES_TAC, CASE_TAC, gen_tac,
    qid_spec_tac `st` >> ho_match_mp_tac every_state_insts_bind >> conj_tac,
    CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void,
      opcode_every_emit_inst, every_state_insts_return,
      every_state_insts_fresh_label, every_state_insts_fresh_var,
      every_state_insts_new_block, (UNDISCH opcode_every_lit_byte_offset),
      compile_bytestring_word_count_def, compile_word_copy_loop_op_def,
      (UNDISCH opcode_every_word_copy_loop_base), compile_memory_to_storage_def,
      compile_memory_to_transient_def, (UNDISCH opcode_every_word_copy_loop)])]) >>
  gvs[]
QED

Theorem call_free_store_slots:
  (!cenv src slot ty transient st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_store_slots cenv src slot ty transient st)))) /\
  (!cenv src slot members mem_off slot_off transient st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_store_slots_members cenv src slot members
                           mem_off slot_off transient st)))) /\
  (!cenv src slot elem count_op transient st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_copy_elements_to_slots cenv src slot elem
                           count_op transient st))))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_store_slots) >> simp[]
QED

Theorem opcode_every_assign_value:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_assign_value ce dst loc value prim src_loc dty sty sz st)))
  )
Proof
  strip_tac >>
  Cases_on `loc` >> simp[compile_assign_value_def,
    compile_memory_to_storage_def, compile_memory_to_transient_def] >>
  qid_spec_tac `st` >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, IF_CASES_TAC >> qid_spec_tac `st`,
    CASE_TAC >> qid_spec_tac `st`,
    CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void,
      opcode_every_emit_inst, every_state_insts_return, (UNDISCH opcode_every_alloc_buffer),
      (UNDISCH opcode_every_copy_memory), (UNDISCH opcode_every_store_memory), cj 1 (UNDISCH opcode_every_typed_copy),
      (UNDISCH opcode_every_word_copy_loop), cj 1 (UNDISCH opcode_every_store_slots),
      (UNDISCH opcode_every_imm_store_word), (UNDISCH opcode_every_imm_store_words),
      (UNDISCH opcode_every_store_immutable_bytestring)])])
QED

Theorem call_free_assign_value:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_assign_value ce dst loc value prim src_loc dty sty sz st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_assign_value) >> simp[]
QED

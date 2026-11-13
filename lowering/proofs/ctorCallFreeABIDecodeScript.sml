(* The memory-source decoder used by abi_decode. *)
Theory ctorCallFreeABIDecode
Ancestors
  list compileEnv venomInst loweringShapeDefs emitHelper context abiEncoder
  ctorCallFreeRules ctorCallFreeValues

Theorem call_free_abi_clamp:
  !cl val_op st.
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_abi_clamp_basetype val_op cl st)))
Proof
  Cases >> rpt gen_tac >> qid_spec_tac `st` >>
  simp[compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
    compile_abi_bytes_clamp_def] >>
  rpt (FIRST [IF_CASES_TAC >> gvs[],
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_emit_op, call_free_emit_void,
      every_state_insts_return])])
QED

Theorem call_free_abi_dec_addr[local]:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_abi_dec_addr base_op pos_op st)))
Proof
  simp[compile_abi_dec_addr_def] >> IF_CASES_TAC >>
  simp[call_free_emit_op, every_state_insts_return]
QED

Theorem call_free_abi_range_check[local]:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_abi_decode_range_check lo_op end_op hi_op st)))
Proof
  qid_spec_tac `st` >> simp[compile_abi_decode_range_check_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_emit_op, call_free_emit_void])])
QED

Theorem call_free_abi_element_ptr_opcode:
  (!src dyn off opc base_op hi_op st.
    opc <> RETURNDATACOPY /\ opc <> INVOKE /\
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_getelemptr_abi src dyn off opc base_op hi_op st)))) /\
  (!opc base_op elem_src src_data hi_op asz st.
    opc <> RETURNDATACOPY /\ opc <> INVOKE /\
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_abi_decode_dyn_elem_ptr opc base_op elem_src src_data hi_op asz st))))
Proof
  conj_tac >> rpt gen_tac >> strip_tac >> qpat_x_assum `EVERY _ _` mp_tac >>
  qid_spec_tac `st` >>
  simp[compile_getelemptr_abi_def, compile_abi_decode_dyn_elem_ptr_def] >>
  rpt (FIRST [IF_CASES_TAC >> gvs[],
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_emit_op, call_free_emit_void,
      call_free_abi_dec_addr, call_free_abi_range_check,
      every_state_insts_return])])
QED

Theorem call_free_abi_decode_opcode:
  (!dst src opc base_op hi_op info.
    opc <> RETURNDATACOPY /\ opc <> INVOKE ==> !st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_abi_decode_to_buf dst src opc base_op hi_op info st)))) /\
  (!dst src opc base_op hi_op elems ao vo.
    opc <> RETURNDATACOPY /\ opc <> INVOKE ==> !st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_abi_decode_complex_elems dst src opc base_op hi_op elems ao vo st)))) /\
  (!dst src opc base_op hi_op info asz msz ip cnt.
    opc <> RETURNDATACOPY /\ opc <> INVOKE ==> !st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_abi_decode_dyn_loop dst src opc base_op hi_op info asz msz ip cnt st))))
Proof
  ho_match_mp_tac compile_abi_decode_to_buf_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >>
  simp[Once compile_abi_decode_to_buf_def, compile_abi_decode_static_def] >>
  rpt (FIRST [disch_then (CONJUNCTS_THEN assume_tac),
    IF_CASES_TAC >> gvs[],
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_emit_op, call_free_emit_void,
      call_free_emit_inst, every_state_insts_new_block,
      every_state_insts_fresh_label, call_free_alloc_buffer,
      call_free_abi_dec_addr, call_free_abi_range_check,
      call_free_abi_clamp, call_free_abi_element_ptr_opcode,
      every_state_insts_return])]) >>
  Cases_on `opc` >> gvs[call_free_emit_void]
QED

Theorem call_free_abi_decode_memory:
  (!dst src opc base_op hi_op info.
    opc = MLOAD ==> !st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_abi_decode_to_buf dst src opc base_op hi_op info st)))) /\
  (!dst src opc base_op hi_op elems ao vo.
    opc = MLOAD ==> !st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_abi_decode_complex_elems dst src opc base_op hi_op elems ao vo st)))) /\
  (!dst src opc base_op hi_op info asz msz ip cnt.
    opc = MLOAD ==> !st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_abi_decode_dyn_loop dst src opc base_op hi_op info asz msz ip cnt st))))
Proof
  rpt conj_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  simp[call_free_abi_decode_opcode]
QED

(* Opcode preservation for ABI encoding. *)
Theory ctorCallFreeABIEncode
Ancestors
  list compileEnv venomInst loweringShapeDefs emitHelper context abiEncoder
  ctorCallFreeRules ctorCallFreeValues

Theorem call_free_abi_encode_static[local]:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_abi_encode_static dst src st)))
Proof
  qid_spec_tac `st` >> simp[compile_abi_encode_static_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_emit_op, call_free_emit_void,
      every_state_insts_return])])
QED

Theorem call_free_abi_encode_static_info[local]:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_abi_encode_static_info dst src info st)))
Proof
  Cases_on `info` >> simp[compile_abi_encode_static_info_def,
    call_free_abi_encode_static, every_state_insts_ignore_bind,
    call_free_emit_void, every_state_insts_return]
QED

Theorem call_free_abi_encode_dyn_static_loop[local]:
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
    (state_insts (SND (compile_abi_encode_dyn_static_loop dst src info asz msz len_op st)))
Proof
  qid_spec_tac `st` >> simp[compile_abi_encode_dyn_static_loop_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_emit_op, call_free_emit_void,
      call_free_emit_inst, every_state_insts_new_block,
      every_state_insts_fresh_label, call_free_alloc_buffer,
      call_free_abi_encode_static_info, every_state_insts_return])])
QED

Theorem call_free_abi_encode:
  (!dst cp ci dyn off dp st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_abi_encode_child dst cp ci dyn off dp st)))) /\
  (!dst src info st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_abi_encode_to_buf dst src info st)))) /\
  (!dst src elems so ho dp st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_abi_encode_complex_elems dst src elems so ho dp st)))) /\
  (!dst src info asz msz len_op st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE)
      (state_insts (SND (compile_abi_encode_dyn_loop dst src info asz msz len_op st))))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >>
  simp[Once compile_abi_encode_child_def] >>
  rpt (FIRST [IF_CASES_TAC >> gvs[],
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_emit_op, call_free_emit_void,
      call_free_emit_inst, every_state_insts_new_block,
      every_state_insts_fresh_label, call_free_alloc_buffer,
      call_free_abi_encode_static, call_free_abi_encode_dyn_static_loop,
      every_state_insts_return])]) >>
  simp[every_state_insts_bind, every_state_insts_ignore_bind,
    call_free_emit_op, call_free_emit_void, call_free_emit_inst,
    every_state_insts_new_block, every_state_insts_fresh_label,
    call_free_alloc_buffer, every_state_insts_return] >>
  pop_assum mp_tac >> qid_spec_tac `st` >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[call_free_emit_op, call_free_emit_void,
      every_state_insts_return])])
QED

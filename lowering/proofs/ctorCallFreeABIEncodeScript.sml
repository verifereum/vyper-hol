(* Opcode preservation for ABI encoding. *)
Theory ctorCallFreeABIEncode
Ancestors
  list compileEnv venomInst loweringShapeDefs emitHelper context abiEncoder
  ctorCallFreeRules ctorCallFreeValues

Theorem opcode_every_abi_encode_static[local]:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_abi_encode_static dst src st)))
  )
Proof
  strip_tac >>
  qid_spec_tac `st` >> simp[compile_abi_encode_static_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void,
      every_state_insts_return])])
QED

Theorem opcode_every_abi_encode_static_info[local]:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_abi_encode_static_info dst src info st)))
  )
Proof
  strip_tac >>
  Cases_on `info` >> simp[compile_abi_encode_static_info_def,
    (UNDISCH opcode_every_abi_encode_static), every_state_insts_ignore_bind,
    opcode_every_emit_void, every_state_insts_return]
QED

Theorem opcode_every_abi_encode_dyn_static_loop[local]:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_abi_encode_dyn_static_loop dst src info asz msz len_op st)))
  )
Proof
  strip_tac >>
  qid_spec_tac `st` >> simp[compile_abi_encode_dyn_static_loop_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void,
      opcode_every_emit_inst, every_state_insts_new_block,
      every_state_insts_fresh_label, (UNDISCH opcode_every_alloc_buffer),
      (UNDISCH opcode_every_abi_encode_static_info), every_state_insts_return])])
QED

Theorem opcode_every_abi_encode:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!dst cp ci dyn off dp st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_abi_encode_child dst cp ci dyn off dp st)))) /\
  (!dst src info st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_abi_encode_to_buf dst src info st)))) /\
  (!dst src elems so ho dp st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_abi_encode_complex_elems dst src elems so ho dp st)))) /\
  (!dst src info asz msz len_op st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_abi_encode_dyn_loop dst src info asz msz len_op st))))
  )
Proof
  strip_tac >>
  ho_match_mp_tac compile_abi_encode_child_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >>
  simp[Once compile_abi_encode_child_def] >>
  rpt (FIRST [IF_CASES_TAC >> gvs[],
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void,
      opcode_every_emit_inst, every_state_insts_new_block,
      every_state_insts_fresh_label, (UNDISCH opcode_every_alloc_buffer),
      (UNDISCH opcode_every_abi_encode_static), (UNDISCH opcode_every_abi_encode_dyn_static_loop),
      every_state_insts_return])]) >>
  simp[every_state_insts_bind, every_state_insts_ignore_bind,
    opcode_every_emit_op, opcode_every_emit_void, opcode_every_emit_inst,
    every_state_insts_new_block, every_state_insts_fresh_label,
    (UNDISCH opcode_every_alloc_buffer), every_state_insts_return] >>
  pop_assum mp_tac >> qid_spec_tac `st` >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void,
      every_state_insts_return])])
QED

Theorem call_free_abi_encode:
  (!dst cp ci dyn off dp st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_abi_encode_child dst cp ci dyn off dp st)))) /\
  (!dst src info st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_abi_encode_to_buf dst src info st)))) /\
  (!dst src elems so ho dp st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_abi_encode_complex_elems dst src elems so ho dp st)))) /\
  (!dst src info asz msz len_op st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_abi_encode_dyn_loop dst src info asz msz len_op st))))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_abi_encode) >> simp[]
QED

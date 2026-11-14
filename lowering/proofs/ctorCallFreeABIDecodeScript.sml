(* The memory-source decoder used by abi_decode. *)
Theory ctorCallFreeABIDecode
Ancestors
  list compileEnv venomInst loweringShapeDefs emitHelper context abiEncoder
  ctorCallFreeRules ctorCallFreeValues

Theorem opcode_every_abi_clamp:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  !cl val_op st.
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_abi_clamp_basetype val_op cl st)))
  )
Proof
  strip_tac >>
  Cases >> rpt gen_tac >> qid_spec_tac `st` >>
  simp[compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
    compile_abi_bytes_clamp_def] >>
  rpt (FIRST [IF_CASES_TAC >> gvs[],
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void,
      every_state_insts_return])])
QED

Theorem call_free_abi_clamp:
  !cl val_op st.
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
  EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
    (state_insts (SND (compile_abi_clamp_basetype val_op cl st)))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_abi_clamp) >> simp[]
QED

Theorem opcode_every_abi_dec_addr[local]:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_abi_dec_addr base_op pos_op st)))
  )
Proof
  strip_tac >>
  simp[compile_abi_dec_addr_def] >> IF_CASES_TAC >>
  simp[opcode_every_emit_op, every_state_insts_return]
QED

Theorem opcode_every_abi_range_check[local]:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_abi_decode_range_check lo_op end_op hi_op st)))
  )
Proof
  strip_tac >>
  qid_spec_tac `st` >> simp[compile_abi_decode_range_check_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void])])
QED

Theorem opcode_every_abi_element_ptr_opcode:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!src dyn off opc base_op hi_op st.
    P opc /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_getelemptr_abi src dyn off opc base_op hi_op st)))) /\
  (!opc base_op elem_src src_data hi_op asz st.
    P opc /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_abi_decode_dyn_elem_ptr opc base_op elem_src src_data hi_op asz st))))
  )
Proof
  strip_tac >>
  conj_tac >> rpt gen_tac >> strip_tac >> qpat_x_assum `EVERY _ _` mp_tac >>
  qid_spec_tac `st` >>
  simp[compile_getelemptr_abi_def, compile_abi_decode_dyn_elem_ptr_def] >>
  rpt (FIRST [IF_CASES_TAC >> gvs[],
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void,
      (UNDISCH opcode_every_abi_dec_addr), (UNDISCH opcode_every_abi_range_check),
      every_state_insts_return])])
QED

Theorem call_free_abi_element_ptr_opcode:
  (!src dyn off opc base_op hi_op st.
    opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2 /\
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_getelemptr_abi src dyn off opc base_op hi_op st)))) /\
  (!opc base_op elem_src src_data hi_op asz st.
    opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2 /\
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_abi_decode_dyn_elem_ptr opc base_op elem_src src_data hi_op asz st))))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_abi_element_ptr_opcode) >> simp[]
QED

Theorem opcode_every_abi_copy[local]:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  !opc ops st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND
      ((case opc of CALLDATALOAD => emit_void CALLDATACOPY ops
        | DLOAD => emit_void DLOADBYTES ops
        | _ => emit_void MCOPY ops) st)))
Proof
  strip_tac >> Cases >> simp[opcode_every_emit_void]
QED

Theorem opcode_every_abi_decode_opcode:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!dst src opc base_op hi_op info.
    P opc ==> !st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_abi_decode_to_buf dst src opc base_op hi_op info st)))) /\
  (!dst src opc base_op hi_op elems ao vo.
    P opc ==> !st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_abi_decode_complex_elems dst src opc base_op hi_op elems ao vo st)))) /\
  (!dst src opc base_op hi_op info asz msz ip cnt.
    P opc ==> !st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_abi_decode_dyn_loop dst src opc base_op hi_op info asz msz ip cnt st))))
  )
Proof
  strip_tac >>
  ho_match_mp_tac compile_abi_decode_to_buf_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >>
  simp[Once compile_abi_decode_to_buf_def, compile_abi_decode_static_def] >>
  rpt (FIRST [disch_then (CONJUNCTS_THEN assume_tac),
    IF_CASES_TAC >> gvs[],
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void,
      opcode_every_emit_inst, every_state_insts_new_block,
      every_state_insts_fresh_label, (UNDISCH opcode_every_alloc_buffer),
      (UNDISCH opcode_every_abi_dec_addr), (UNDISCH opcode_every_abi_range_check),
      (UNDISCH opcode_every_abi_clamp), (UNDISCH opcode_every_abi_element_ptr_opcode),
      UNDISCH opcode_every_abi_copy, every_state_insts_return]), disch_tac]) >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem call_free_abi_decode_opcode:
  (!dst src opc base_op hi_op info.
    opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2 ==> !st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_abi_decode_to_buf dst src opc base_op hi_op info st)))) /\
  (!dst src opc base_op hi_op elems ao vo.
    opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2 ==> !st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_abi_decode_complex_elems dst src opc base_op hi_op elems ao vo st)))) /\
  (!dst src opc base_op hi_op info asz msz ip cnt.
    opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2 ==> !st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_abi_decode_dyn_loop dst src opc base_op hi_op info asz msz ip cnt st))))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_abi_decode_opcode) >> simp[]
QED

Theorem opcode_every_abi_decode_memory:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!dst src opc base_op hi_op info.
    opc = MLOAD ==> !st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_abi_decode_to_buf dst src opc base_op hi_op info st)))) /\
  (!dst src opc base_op hi_op elems ao vo.
    opc = MLOAD ==> !st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_abi_decode_complex_elems dst src opc base_op hi_op elems ao vo st)))) /\
  (!dst src opc base_op hi_op info asz msz ip cnt.
    opc = MLOAD ==> !st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_abi_decode_dyn_loop dst src opc base_op hi_op info asz msz ip cnt st))))
  )
Proof
  strip_tac >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  simp[(UNDISCH opcode_every_abi_decode_opcode)]
QED

Theorem call_free_abi_decode_memory:
  (!dst src opc base_op hi_op info.
    opc = MLOAD ==> !st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_abi_decode_to_buf dst src opc base_op hi_op info st)))) /\
  (!dst src opc base_op hi_op elems ao vo.
    opc = MLOAD ==> !st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_abi_decode_complex_elems dst src opc base_op hi_op elems ao vo st)))) /\
  (!dst src opc base_op hi_op info asz msz ip cnt.
    opc = MLOAD ==> !st.
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2) (state_insts st) ==>
    EVERY (\i. i.inst_opcode <> RETURNDATACOPY /\ i.inst_opcode <> INVOKE /\ i.inst_opcode <> CREATE /\ i.inst_opcode <> CREATE2)
      (state_insts (SND (compile_abi_decode_dyn_loop dst src opc base_op hi_op info asz msz ip cnt st))))
Proof
  mp_tac (Q.INST [`P` |-> `\opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\ opc <> CREATE /\ opc <> CREATE2`] opcode_every_abi_decode_memory) >> simp[]
QED

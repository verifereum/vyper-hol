(* The memory-source decoder used by abi_decode. *)
Theory ctorCallFreeABIDecode
Ancestors
  list compileEnv venomInst loweringShapeDefs emitHelper context abiEncoder
  ctorCallFreeRules ctorCallFreeValues

Theorem outcomes_free_abi_clamp:
  P SIGNEXTEND /\ P EQ /\ P SHR /\ P SHL /\ P ISZERO /\ P ASSERT /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_abi_clamp_basetype v ci s)))
Proof
  strip_tac >> Cases_on `ci` >>
  simp[compile_abi_clamp_basetype_def, compile_abi_int_clamp_def,
       compile_abi_bytes_clamp_def] >>
  rpt (FIRST [CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void,
      every_state_insts_return]),
    gen_tac, strip_tac, irule every_state_insts_bind, IF_CASES_TAC])
QED

Theorem outcomes_free_abi_dec_addr:
  P ADD /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_abi_dec_addr b p s)))
Proof
  strip_tac >> simp[compile_abi_dec_addr_def] >> IF_CASES_TAC >>
  simp[every_state_insts_return, opcode_every_emit_op]
QED

Theorem outcomes_free_abi_range_check:
  P LT /\ P GT /\ P AND /\ P ISZERO /\ P ASSERT /\
  EVERY (\i. P i.inst_opcode) (state_insts s) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_abi_decode_range_check a b hi s)))
Proof
  strip_tac >> simp[compile_abi_decode_range_check_def] >>
  rpt (FIRST [CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void]),
    gen_tac, strip_tac, irule every_state_insts_bind])
QED

Theorem outcomes_free_abi_element_ptr:
  P ADD /\ P LT /\ P GT /\ P AND /\ P ISZERO /\ P ASSERT ==>
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
Proof
  strip_tac >>
  simp[compile_getelemptr_abi_def, compile_abi_decode_dyn_elem_ptr_def] >>
  rpt (FIRST [CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void,
      every_state_insts_return, outcomes_free_abi_dec_addr,
      outcomes_free_abi_range_check]),
    gen_tac, strip_tac, irule every_state_insts_bind,
    irule every_state_insts_ignore_bind, conj_tac, IF_CASES_TAC])
QED

Theorem outcomes_free_abi_copy[local]:
  (opc = CALLDATALOAD ==> P CALLDATACOPY) /\ (opc = DLOAD ==> P DLOADBYTES) /\
  P MCOPY /\
  EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode) (state_insts (SND
    ((case opc of CALLDATALOAD => emit_void CALLDATACOPY ops
      | DLOAD => emit_void DLOADBYTES ops
      | _ => emit_void MCOPY ops) st)))
Proof
  Cases_on `opc` >> simp[opcode_every_emit_void]
QED

Theorem outcomes_free_abi_decode:
  (!opc. MEM opc [ADD; MUL; LT; GT; EQ; AND; NOT; ISZERO; SHR; SHL;
     SIGNEXTEND; ASSERT; MLOAD; MSTORE; MCOPY; ALLOCA; JMP; JNZ] ==> P opc) ==>
  (
  (!dst src opc base_op hi_op info.
    P opc /\ (opc = CALLDATALOAD ==> P CALLDATACOPY) /\
    (opc = DLOAD ==> P DLOADBYTES) ==> !st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_abi_decode_to_buf dst src opc base_op hi_op info st)))) /\
  (!dst src opc base_op hi_op elems ao vo.
    P opc /\ (opc = CALLDATALOAD ==> P CALLDATACOPY) /\
    (opc = DLOAD ==> P DLOADBYTES) ==> !st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_abi_decode_complex_elems dst src opc base_op hi_op elems ao vo st)))) /\
  (!dst src opc base_op hi_op info asz msz ip cnt.
    P opc /\ (opc = CALLDATALOAD ==> P CALLDATACOPY) /\
    (opc = DLOAD ==> P DLOADBYTES) ==> !st.
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_abi_decode_dyn_loop dst src opc base_op hi_op info asz msz ip cnt st))))
  )
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  ho_match_mp_tac compile_abi_decode_to_buf_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >>
  simp[Once compile_abi_decode_to_buf_def, compile_abi_decode_static_def] >>
  rpt (FIRST [disch_then (CONJUNCTS_THEN assume_tac),
    IF_CASES_TAC >> gvs[],
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, CHANGED_TAC (simp[opcode_every_emit_op, opcode_every_emit_void,
      opcode_every_emit_inst, every_state_insts_new_block,
      every_state_insts_fresh_label, outcomes_free_alloc_buffer,
      outcomes_free_abi_dec_addr, outcomes_free_abi_range_check,
      outcomes_free_abi_clamp, outcomes_free_abi_element_ptr,
      outcomes_free_abi_copy, every_state_insts_return]), disch_tac]) >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

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
  rpt strip_tac >> irule outcomes_free_abi_clamp >> simp[]
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
  strip_tac >> match_mp_tac outcomes_free_abi_element_ptr >> simp[]
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
  strip_tac >> mp_tac outcomes_free_abi_decode >>
  impl_tac >- simp[DISJ_IMP_THM] >> simp[]
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

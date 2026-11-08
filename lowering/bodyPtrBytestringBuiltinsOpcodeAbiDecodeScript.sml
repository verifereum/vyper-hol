Theory bodyPtrBytestringBuiltinsOpcodeAbiDecode
Ancestors bodyPtrBytestringBuiltinsOpcodeAbiEncode
          bodyPtrBytestringBuiltinsOpcodeValues
          bodyPtrBytestringBuiltinsOpcodeState abiEncoder

Theorem no_extcode_get_element_ptr:
  !p off s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_get_element_ptr p off s))
Proof
  simp[compile_get_element_ptr_def, no_extcode_emit_op]
QED

Theorem no_extcode_get_dynarray_elem_ptr:
  !p idx sz s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_get_dynarray_elem_ptr p idx sz s))
Proof
  rpt strip_tac >> simp[compile_get_dynarray_elem_ptr_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_emit_op, no_extcode_fresh_ops])
QED

Theorem no_extcode_getelemptr_abi:
  !p dyn off opc hi s. opc <> EXTCODECOPY /\ compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_getelemptr_abi p dyn off opc hi s))
Proof
  rpt strip_tac >> simp[compile_getelemptr_abi_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, IF_CASES_TAC] >>
    simp[no_extcode_emit_op, no_extcode_emit_void, no_extcode_fresh_ops])
QED

Theorem no_extcode_abi_decode_dyn_elem_ptr:
  !opc elem src hi sz s. opc <> EXTCODECOPY /\ compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_abi_decode_dyn_elem_ptr opc elem src hi sz s))
Proof
  rpt strip_tac >> simp[compile_abi_decode_dyn_elem_ptr_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, IF_CASES_TAC] >>
    simp[no_extcode_emit_op, no_extcode_emit_void, no_extcode_fresh_ops])
QED

Theorem no_extcode_abi_decode_static:
  !src dst opc clamp s.
    opc <> EXTCODECOPY /\ compiler_no_extcode s /\
    (!v st. compiler_no_extcode st ==> compiler_no_extcode (SND (clamp v st))) ==>
    compiler_no_extcode (SND (compile_abi_decode_static src dst opc clamp s))
Proof
  rpt strip_tac >> simp[compile_abi_decode_static_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_emit_op, no_extcode_emit_void, no_extcode_fresh_ops])
QED

Theorem no_extcode_abi_decode:
  (!dst src opc hi info s. opc <> EXTCODECOPY /\ compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_abi_decode_to_buf dst src opc hi info s))) /\
  (!dst src opc hi elems ao vo s. opc <> EXTCODECOPY /\ compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_abi_decode_complex_elems dst src opc hi elems ao vo s))) /\
  (!dst src opc hi info az mz ip cnt s. opc <> EXTCODECOPY /\ compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_abi_decode_dyn_loop dst src opc hi info az mz ip cnt s)))
Proof
  ho_match_mp_tac compile_abi_decode_to_buf_ind >> rpt strip_tac >>
  simp[Once compile_abi_decode_to_buf_def, no_extcode_fresh_ops,
       no_extcode_abi_decode_static, no_extcode_abi_clamp_basetype] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, IF_CASES_TAC] >>
    simp[no_extcode_emit_op, no_extcode_emit_void, no_extcode_emit_inst,
         no_extcode_fresh_ops, no_extcode_alloc_buffer, no_extcode_new_block,
         no_extcode_getelemptr_abi, no_extcode_abi_decode_dyn_elem_ptr]) >>
  gvs[] >> Cases_on `opc` >> simp[no_extcode_emit_void]
QED

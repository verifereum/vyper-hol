Theory bodyPtrBytestringBuiltinsOpcodeAbiEncode
Ancestors bodyPtrBytestringBuiltinsOpcodeValues
          bodyPtrBytestringBuiltinsOpcodeState abiEncoder

Theorem no_extcode_abi_int_clamp:
  !v bits signed s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_abi_int_clamp v bits signed s))
Proof
  rpt gen_tac >> Cases_on `signed` >> strip_tac >> simp[compile_abi_int_clamp_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_emit_op, no_extcode_emit_void, no_extcode_fresh_ops])
QED

Theorem no_extcode_abi_bytes_clamp:
  !v m s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_abi_bytes_clamp v m s))
Proof
  rpt strip_tac >> simp[compile_abi_bytes_clamp_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_emit_op, no_extcode_emit_void, no_extcode_fresh_ops])
QED

Theorem no_extcode_abi_clamp_basetype:
  !v c s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_abi_clamp_basetype v c s))
Proof
  rpt gen_tac >> Cases_on `c` >> strip_tac >>
  simp[compile_abi_clamp_basetype_def, no_extcode_abi_int_clamp,
       no_extcode_abi_bytes_clamp, no_extcode_fresh_ops] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_emit_op, no_extcode_emit_void, no_extcode_fresh_ops])
QED

Theorem no_extcode_abi_zero_pad:
  !p n c s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_abi_zero_pad p n c s))
Proof
  rpt strip_tac >> simp[compile_abi_zero_pad_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_emit_op, no_extcode_emit_void, no_extcode_fresh_ops])
QED

Theorem no_extcode_abi_encode_static:
  !dst src s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_abi_encode_static dst src s))
Proof
  rpt strip_tac >> simp[compile_abi_encode_static_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_emit_op, no_extcode_emit_void, no_extcode_fresh_ops])
QED

Theorem no_extcode_abi_encode_static_info:
  !dst src info s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_abi_encode_static_info dst src info s))
Proof
  rpt gen_tac >> Cases_on `info` >> strip_tac >>
  simp[compile_abi_encode_static_info_def, no_extcode_abi_encode_static,
       no_extcode_fresh_ops] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_emit_op, no_extcode_emit_void, no_extcode_fresh_ops])
QED

Theorem no_extcode_abi_encode_dyn_static_loop:
  !dst src info az mz len s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_abi_encode_dyn_static_loop dst src info az mz len s))
Proof
  rpt strip_tac >> simp[compile_abi_encode_dyn_static_loop_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_emit_op, no_extcode_emit_void, no_extcode_emit_inst,
         no_extcode_fresh_ops, no_extcode_alloc_buffer, no_extcode_new_block,
         no_extcode_abi_encode_static_info])
QED

Theorem no_extcode_abi_encode:
  (!dst cp ci dyn off dp s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_abi_encode_child dst cp ci dyn off dp s))) /\
  (!dst src info s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_abi_encode_to_buf dst src info s))) /\
  (!dst src elems so ho dp s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_abi_encode_complex_elems dst src elems so ho dp s))) /\
  (!dst src info az mz len s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_abi_encode_dyn_loop dst src info az mz len s)))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >> rpt strip_tac >>
  simp[Once compile_abi_encode_child_def, no_extcode_fresh_ops,
       no_extcode_abi_encode_static, no_extcode_abi_encode_dyn_static_loop] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, IF_CASES_TAC] >>
    simp[no_extcode_emit_op, no_extcode_emit_void, no_extcode_emit_inst,
         no_extcode_fresh_ops, no_extcode_alloc_buffer, no_extcode_new_block,
         no_extcode_abi_zero_pad, no_extcode_abi_encode_static,
         no_extcode_abi_encode_dyn_static_loop]) >> gvs[]
QED

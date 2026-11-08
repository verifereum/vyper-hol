Theory bodyPtrBytestringBuiltinsOpcodeCalldata
Ancestors bodyPtrBytestringBuiltinsOpcodeValues
          bodyPtrBytestringBuiltinsOpcodeState builtinBytes

Theorem no_extcode_assert_slice_bounds:
  !a b c s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_assert_slice_bounds a b c s))
Proof
  rpt strip_tac >> simp[compile_assert_slice_bounds_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_emit_op, no_extcode_emit_void])
QED

Theorem no_extcode_slice_out_buf:
  !sz s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_slice_out_buf sz s))
Proof
  rpt strip_tac >> simp[compile_slice_out_buf_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_alloc_buffer, no_extcode_emit_op, no_extcode_fresh_ops])
QED

Theorem no_extcode_slice_calldata:
  !a n sz s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_slice_calldata a n sz s))
Proof
  rpt strip_tac >> simp[compile_slice_calldata_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, pairarg_tac] >>
    simp[no_extcode_slice_out_buf, no_extcode_assert_slice_bounds,
      no_extcode_emit_op, no_extcode_emit_void, no_extcode_fresh_ops])
QED

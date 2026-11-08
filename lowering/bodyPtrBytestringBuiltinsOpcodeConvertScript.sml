Theory bodyPtrBytestringBuiltinsOpcodeConvert
Ancestors bodyPtrBytestringBuiltinsOpcodeValues
          bodyPtrBytestringBuiltinsOpcodeMemory
          bodyPtrBytestringBuiltinsOpcodeState exprLowering builtinSimple

Theorem no_extcode_load_bytestring_as_word:
  !v opc s. opc <> EXTCODECOPY /\ compiler_no_extcode s ==>
    compiler_no_extcode (SND (load_bytestring_as_word v opc s))
Proof
  rpt strip_tac >> simp[load_bytestring_as_word_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, IF_CASES_TAC] >>
    simp[no_extcode_emit_op, no_extcode_fresh_ops])
QED

Theorem no_extcode_int_clamp:
  !b n v s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_int_clamp b n v s))
Proof
  rpt strip_tac >> simp[compile_int_clamp_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, IF_CASES_TAC] >>
    simp[no_extcode_emit_op, no_extcode_emit_void, no_extcode_fresh_ops])
QED

Theorem no_extcode_type_convert:
  !v conv s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_type_convert v conv s))
Proof
  rpt gen_tac >> Cases_on `conv` >> strip_tac >>
  simp[compile_type_convert_def, no_extcode_fresh_ops, no_extcode_emit_op] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, IF_CASES_TAC,
    pairarg_tac] >>
    simp[no_extcode_emit_op, no_extcode_emit_void, no_extcode_fresh_ops,
         no_extcode_int_clamp, no_extcode_load_bytestring_as_word])
QED

Theorem no_extcode_bytestring_widen_copy:
  !dst v src s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_bytestring_widen_copy dst v src s))
Proof
  rpt strip_tac >> simp[compile_bytestring_widen_copy_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_alloc_buffer, no_extcode_copy_memory, no_extcode_fresh_ops])
QED

Theorem no_extcode_zero_words:
  !p n s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_zero_words p n s))
Proof
  gen_tac >> Induct >> simp[compile_zero_words_def, no_extcode_fresh_ops] >>
  rpt strip_tac >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_emit_op, no_extcode_emit_void, no_extcode_fresh_ops])
QED

Theorem no_extcode_builtin_empty_complex:
  !sz b s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_builtin_empty_complex sz b s))
Proof
  rpt strip_tac >> simp[compile_builtin_empty_complex_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, IF_CASES_TAC] >>
    simp[no_extcode_alloc_buffer, no_extcode_zero_words,
         no_extcode_emit_void, no_extcode_fresh_ops])
QED

Theory bodyPtrBytestringBuiltinsOpcodeExternal
Ancestors bodyPtrBytestringBuiltinsOpcodeArithmetic
          bodyPtrBytestringBuiltinsOpcodeCallStaging
          bodyPtrBytestringBuiltinsOpcodeAbiEncode
          bodyPtrBytestringBuiltinsOpcodeAbiDecode
          bodyPtrBytestringBuiltinsOpcodeValues
          bodyPtrBytestringBuiltinsOpcodeMemory
          bodyPtrBytestringBuiltinsOpcodeState exprLowering

Theorem no_extcode_extcodesize_check:
  !a s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_extcodesize_check a s))
Proof
  rpt strip_tac >> simp[compile_extcodesize_check_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_emit_op, no_extcode_emit_void, no_extcode_emit_inst,
         no_extcode_fresh_ops, no_extcode_new_block, no_extcode_select])
QED

Theorem no_extcode_return_value_decode:
  !b lo hi s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_return_value_decode b lo hi s))
Proof
  rpt strip_tac >> simp[compile_return_value_decode_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_emit_op, no_extcode_emit_void, no_extcode_emit_inst,
         no_extcode_fresh_ops, no_extcode_new_block, no_extcode_select])
QED

Theorem no_extcode_default_return_path:
  !ce rt dt buf result def addr skip minsz maxsz info s.
    compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_default_return_path ce rt dt buf result def addr skip minsz maxsz info s))
Proof
  rpt strip_tac >> simp[compile_default_return_path_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, IF_CASES_TAC] >>
    simp[no_extcode_emit_op, no_extcode_emit_void, no_extcode_emit_inst,
         no_extcode_fresh_ops, no_extcode_new_block,
         no_extcode_store_memory, no_extcode_extcodesize_check,
         no_extcode_return_value_decode, cj 1 no_extcode_abi_decode])
QED

Theorem no_extcode_external_call_kwargs:
  !ce addr vals tys memsz abisz mid retsz minsz retmem static value gas skip hasdef def rt dt enc dec s.
    compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_external_call_kwargs ce addr vals tys memsz abisz mid retsz minsz retmem static value gas skip hasdef def rt dt enc dec s))
Proof
  rpt strip_tac >> simp[compile_external_call_kwargs_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, IF_CASES_TAC] >>
    simp[no_extcode_emit_op, no_extcode_emit_void, no_extcode_emit_inst,
         no_extcode_fresh_ops, no_extcode_new_block, no_extcode_alloc_buffer,
         no_extcode_extcall_store_values, cj 2 no_extcode_abi_encode,
         cj 1 no_extcode_abi_decode, no_extcode_default_return_path,
         no_extcode_extcodesize_check, no_extcode_return_value_decode])
QED

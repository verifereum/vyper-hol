Theory bodyPtrBytestringBuiltinsOpcodeAbi
Ancestors bodyPtrBytestringBuiltinsOpcodeAbiEncode
          bodyPtrBytestringBuiltinsOpcodeAbiDecode
          bodyPtrBytestringBuiltinsOpcodeValues
          bodyPtrBytestringBuiltinsOpcodeState builtinAbi

Theorem no_extcode_lower_abi_encode:
  !ensure mid src info maxlen s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (lower_abi_encode ensure mid src info maxlen s))
Proof
  rpt gen_tac >> Cases_on `mid` >> strip_tac >> simp[lower_abi_encode_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind] >>
    simp[no_extcode_emit_op, no_extcode_emit_void, no_extcode_fresh_ops,
         no_extcode_alloc_buffer, cj 2 no_extcode_abi_encode])
QED

Theorem no_extcode_lower_abi_decode:
  !data info minsz maxsz outsz s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (lower_abi_decode data info minsz maxsz outsz s))
Proof
  rpt strip_tac >> simp[lower_abi_decode_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_bind, irule no_extcode_ignore_bind, IF_CASES_TAC] >>
    simp[no_extcode_emit_op, no_extcode_emit_void, no_extcode_fresh_ops,
         no_extcode_alloc_buffer, cj 1 no_extcode_abi_decode])
QED

Theory bodyPtrBytestringBuiltinsOpcodeTypeBody
Ancestors bodyPtrBytestringBuiltinsOpcodeConvert
          bodyPtrBytestringBuiltinsOpcodeAbi
          bodyPtrBytestringBuiltinsOpcodeAggregates
          bodyPtrBytestringBuiltinsOpcodeCallStaging
          bodyPtrBytestringBuiltinsOpcodeValues
          bodyPtrBytestringBuiltinsOpcodeState supportedExprForms exprLowering

Theorem no_extcode_value_wrappers[simp]:
  (!ty p. compiler_no_extcode (SND (as_stack_val ty p)) = compiler_no_extcode (SND p)) /\
  (!ty loc p. compiler_no_extcode (SND (as_ptr_val ty loc p)) = compiler_no_extcode (SND p))
Proof
  conj_tac >> rpt gen_tac >> PairCases_on `p` >>
  simp[as_stack_val_def, as_ptr_val_def]
QED

Theorem no_extcode_type_body_supported:
  !tops cfn ce vt ty tb rt es.
    supported_type_builtin_form tops vt tb rt es /\
    (!e et s. MEM e es /\ compiler_no_extcode s ==>
      compiler_no_extcode (SND (cfn ce et e s))) ==>
    !s. compiler_no_extcode s ==>
      compiler_no_extcode (SND (compile_type_builtin_dispatch_body cfn ce vt ty tb rt es s))
Proof
  rpt gen_tac >> Cases_on `es` >>
  TRY (rename1 `h::t` >> Cases_on `t`) >> Cases_on `tb` >>
  simp[supported_type_builtin_form_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  gvs[] >> simp[compile_type_builtin_dispatch_body_def, as_stack_val_def, as_ptr_val_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_pair, IF_CASES_TAC] >>
    simp[as_stack_val_def, as_ptr_val_def,
         no_extcode_lower_value, no_extcode_unwrap_value,
         no_extcode_alloc_buffer, no_extcode_emit_void,
         no_extcode_lower_abi_encode, no_extcode_lower_abi_decode,
         no_extcode_multi_exprs, no_extcode_store_abi_tuple,
         no_extcode_type_convert, no_extcode_bytestring_widen_copy,
         no_extcode_builtin_empty_complex]) >>
  Cases_on `type_bounds rt` >> simp[] >>
  Cases_on `rt` >> simp[no_extcode_type_convert]
QED

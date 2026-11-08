Theory bodyPtrBytestringBuiltinsOpcodeBuiltinBody
Ancestors bodyPtrBytestringBuiltinsOpcodeBuiltins
          bodyPtrBytestringBuiltinsOpcodeSimple
          bodyPtrBytestringBuiltinsOpcodeTypeBody
          bodyPtrBytestringBuiltinsOpcodeCallStaging
          bodyPtrBytestringBuiltinsOpcodeValues
          bodyPtrBytestringBuiltinsOpcodeState
          bodyPtrBytestringBuiltinsOpcodeArithmetic
          bodyPtrBytestringBuiltinsOpcodeScalars
          bodyPtrBytestringBuiltinsOpcodeCalldata
          bodyPtrBytestringBuiltinsOpcodeAggregates
          supportedExprForms exprLowering

Theorem no_extcode_builtin_body_supported:
  !tops cfn ce rt ty bi es.
    supported_builtin_form tops rt bi es /\
    (!e et s. MEM e es /\ compiler_no_extcode s ==>
      compiler_no_extcode (SND (cfn ce et e s))) ==>
    !s. compiler_no_extcode s ==>
      compiler_no_extcode (SND (compile_builtin_dispatch_body cfn ce rt ty bi es s))
Proof
  rpt gen_tac >> Cases_on `es` >>
  TRY (rename1 `a::xs` >> Cases_on `xs` >>
    TRY (rename1 `a::b::ys` >> Cases_on `ys` >>
      TRY (rename1 `a::b::c::zs` >> Cases_on `zs` >>
        TRY (rename1 `a::b::c::d::ws` >> Cases_on `ws`)))) >>
  Cases_on `bi` >>
  simp[supported_builtin_form_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  TRY (rename1 `MakeArray eo bnd` >> Cases_on `eo` >> gvs[]) >>
  TRY (drule supported_binop_scalar_paths >> strip_tac) >>
  simp[compile_builtin_dispatch_body_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_pair, irule no_extcode_make_array,
    irule no_extcode_make_tuple, irule no_extcode_acc, IF_CASES_TAC] >>
    simp[no_extcode_lower_value, no_extcode_unwrap_value,
      no_extcode_alloc_buffer, no_extcode_emit_op,
      no_extcode_builtin_abs, no_extcode_env_var, no_extcode_acc,
      no_extcode_binop, no_extcode_invert, no_extcode_neg, no_extcode_blockhash,
      no_extcode_blobhash, no_extcode_addmod, no_extcode_mulmod,
      no_extcode_pow_mod256, no_extcode_ecrecover,
      no_extcode_ecadd_points, no_extcode_ecmul_point,
      no_extcode_uint2str, no_extcode_as_wei_value_int,
      no_extcode_as_wei_value_decimal, no_extcode_slice_calldata,
      no_extcode_make_tuple, no_extcode_make_array]) >>
  simp[no_extcode_env_var] >> metis_tac[]
QED

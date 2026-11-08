Theory bodyPtrBytestringBuiltinsOpcodeBodies
Ancestors bodyPtrBytestringBuiltinsOpcodeExprBuiltin
          bodyPtrBytestringBuiltinsOpcodeBuiltinBody
          bodyPtrBytestringBuiltinsOpcodeTypeBody
          bodyPtrBytestringBuiltinsOpcodeSubscript
          bodyPtrBytestringBuiltinsOpcodeCalls
          bodyPtrBytestringBuiltinsOpcodeCallStaging
          bodyPtrBytestringBuiltinsOpcodeScalars
          bodyPtrBytestringBuiltinsOpcodeAggregates
          bodyPtrBytestringBuiltinsOpcodeMemory
          bodyPtrBytestringBuiltinsOpcodeValues
          bodyPtrBytestringBuiltinsOpcodeState
          supportedExprs exprLowering vyperAST list

Theorem no_extcode_expr_toplevel:
  !cfn bfn tfn ce ty rt id s. compiler_no_extcode s ==>
    compiler_no_extcode
      (SND (compile_expr_body cfn bfn tfn ce ty (TopLevelName rt id) s))
Proof
  rpt strip_tac >> simp[compile_expr_body_def, expr_type_def] >>
  namedCases_on `FLOOKUP ce.ce_module_vars id` ["", "binding"] >>
  simp[] >> TRY (Cases_on `binding` >> simp[]) >>
  irule no_extcode_pair >> simp[no_extcode_emit_inst]
QED

Theorem no_extcode_expr_body_supported:
  !tops cfn bfn tfn ce ty e.
    (supported_pure_expr tops e \/ supported_place_expr tops e \/
     supported_effect_expr tops e \/ supported_effect_place_expr tops e) /\
    (!a et s. (supported_pure_expr tops a \/ supported_place_expr tops a \/
               supported_effect_expr tops a \/ supported_effect_place_expr tops a) /\
       compiler_no_extcode s ==> compiler_no_extcode (SND (cfn ce et a s))) /\
    (!rt et bi es s. supported_builtin_form tops rt bi es /\
       supported_pure_exprs tops es /\ compiler_no_extcode s ==>
       compiler_no_extcode (SND (bfn ce rt et bi es s))) /\
    (!vt et tb rt es s. supported_type_builtin_form tops vt tb rt es /\
       supported_pure_exprs tops es /\ compiler_no_extcode s ==>
       compiler_no_extcode (SND (tfn ce vt et tb rt es s))) ==>
    !s. compiler_no_extcode s ==>
      compiler_no_extcode (SND (compile_expr_body cfn bfn tfn ce ty e s))
Proof
  rpt gen_tac >> Cases_on `e` >>
  simp[supported_pure_expr_def, supported_effect_expr_def] >>
  rpt strip_tac
  >~ [`compile_expr_body _ _ _ _ _ (Builtin _ _ _) _`] >-
    (irule no_extcode_expr_builtin >> simp[]) >>
  simp[no_extcode_expr_toplevel] >>
  TRY (rename1 `supported_effect_expr _ (Pop pty targ)` >>
    Cases_on `targ` >> gvs[supported_effect_expr_def]) >>
  simp[compile_expr_body_def, expr_type_def]
  >~ [`compile_call cfn ce rt ty ct args df`] >-
    (irule no_extcode_call_supported >> simp[] >>
     reverse conj_tac >- (qexists_tac `tops` >> simp[]) >>
     Cases_on `ct` >> Cases_on `df` >>
     TRY (PairCases_on `p`) >> TRY (Cases_on `b`) >>
     gvs[supported_effect_expr_def, supported_pure_exprs_every,
         EVERY_MEM, AllCaseEqs()] >>
     TRY (rename1 `supported_effect_expr _ (Call rt (Send _) args _)` >>
       Cases_on `rt` >> Cases_on `args` >>
       TRY (rename1 `arg0::args1` >> Cases_on `args1` >>
         TRY (rename1 `arg0::arg1::args2` >> Cases_on `args2` >>
           TRY (rename1 `arg0::arg1::arg2::args3` >> Cases_on `args3`)))) >>
     gvs[supported_effect_expr_def] >> metis_tac[]) >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_pair, irule no_extcode_attribute,
    irule no_extcode_subscript, irule no_extcode_struct_lit, IF_CASES_TAC] >>
    simp[no_extcode_lower_value, no_extcode_alloc_buffer,
      no_extcode_emit_inst, no_extcode_new_block, no_extcode_fresh_ops,
      no_extcode_ifexp_arm, no_extcode_dynarray_pop,
      no_extcode_toplevel_target])
  >~ [`compile_dynarray_pop`] >-
    (rpt gen_tac >> strip_tac >> pairarg_tac >> gvs[] >>
     irule no_extcode_pair >> simp[no_extcode_dynarray_pop])
  >> simp[no_extcode_literal_vv, no_extcode_name_vv] >>
  gvs[supported_pure_fields_every, EVERY_MEM] >> metis_tac[pairTheory.SND]
QED

Theory bodyPtrBytestringBuiltinsOpcodeCalls
Ancestors bodyPtrBytestringBuiltinsOpcodeCallStaging
          bodyPtrBytestringBuiltinsOpcodeExternal
          bodyPtrBytestringBuiltinsOpcodeValues
          bodyPtrBytestringBuiltinsOpcodeState exprLowering supportedExprs

Theorem no_extcode_call_internal:
  !cfn ce rt ty id args def.
  (!e et s. MEM e args /\ compiler_no_extcode s ==>
    compiler_no_extcode (SND (cfn ce et e s))) ==>
  !s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_call cfn ce rt ty (IntCall id) args def s))
Proof
  rpt strip_tac >> simp[compile_call_def] >> pairarg_tac >> simp[] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_pair, IF_CASES_TAC] >>
    simp[no_extcode_multi_vvs, no_extcode_alloc_buffer,
         no_extcode_stage_intcall_args, no_extcode_emit_multi_op,
         no_extcode_store_multi_results, no_extcode_emit_op, no_extcode_emit_void]) >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_pair, IF_CASES_TAC] >>
    simp[no_extcode_emit_multi_op, no_extcode_store_multi_results,
         no_extcode_emit_op, no_extcode_emit_void])
QED

Theorem no_extcode_call_external:
  !cfn ce rt ty static skip info opts args def.
  (!e et s. MEM e args /\ compiler_no_extcode s ==>
    compiler_no_extcode (SND (cfn ce et e s))) ==>
  !s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_call cfn ce rt ty (ExtCall static skip info opts) args def s))
Proof
  rpt strip_tac >> PairCases_on `info` >> Cases_on `args` >>
  simp[compile_call_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_pair, IF_CASES_TAC] >>
    simp[no_extcode_emit_inst, no_extcode_lower_value,
         no_extcode_multi_vvs, no_extcode_ext_call_kwargs])
  >~ [`SND (compile_multi_vvs _ _ _ _)`] >-
    (irule no_extcode_multi_vvs >> simp[] >> rpt strip_tac >>
     first_x_assum irule >> simp[] >> metis_tac[rich_listTheory.MEM_TAKE])
  >~ [`SND (compile_ext_call_kwargs _ _ _ _ _ _)`] >-
    (irule no_extcode_ext_call_kwargs >> simp[] >> rpt strip_tac >>
     first_x_assum irule >> simp[] >> metis_tac[rich_listTheory.MEM_DROP_IMP]) >>
  rpt gen_tac >> PairCases_on `v''` >> simp[] >>
  Cases_on `v''2` >> simp[] >>
  TRY (PairCases_on `x` >> simp[]) >>
  Cases_on `v''1` >> simp[] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_pair, IF_CASES_TAC] >>
    simp[no_extcode_emit_op, no_extcode_external_call_kwargs])
QED

Theorem no_extcode_call_send:
  !cfn ce rt ty gas args def.
  (!e et s. MEM e args /\ compiler_no_extcode s ==>
    compiler_no_extcode (SND (cfn ce et e s))) ==>
  !s. compiler_no_extcode s ==>
    compiler_no_extcode (SND (compile_call cfn ce rt ty (Send gas) args def s))
Proof
  rpt strip_tac >> Cases_on `args` >>
  TRY (rename1 `h::t` >> Cases_on `t`) >>
  simp[compile_call_def] >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_pair, IF_CASES_TAC] >>
    simp[no_extcode_emit_inst, no_extcode_lower_value,
         no_extcode_emit_op, no_extcode_emit_void]) >>
  Cases_on `t'` >> simp[] >>
  TRY (rename1 `h'::t` >> Cases_on `t` >> simp[]) >>
  rpt (rpt gen_tac >> rpt disch_tac >> FIRST [conj_tac,
    irule no_extcode_pair] >>
    simp[no_extcode_lower_value, no_extcode_emit_op, no_extcode_emit_void]) >>
  BasicProvers.TOP_CASE_TAC >> simp[no_extcode_lower_value]
QED

Theorem no_extcode_call_supported:
  !tops cfn ce rt ty target args def.
    supported_effect_expr tops (Call rt target args def) /\
    (!e et s. MEM e args /\ compiler_no_extcode s ==>
      compiler_no_extcode (SND (cfn ce et e s))) ==>
    !s. compiler_no_extcode s ==>
      compiler_no_extcode (SND (compile_call cfn ce rt ty target args def s))
Proof
  rpt gen_tac >> Cases_on `target` >> Cases_on `def` >>
  simp[supported_effect_expr_def, no_extcode_call_internal,
       no_extcode_call_external, no_extcode_call_send] >>
  rpt strip_tac
QED

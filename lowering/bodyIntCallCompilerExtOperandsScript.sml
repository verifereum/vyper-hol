Theory bodyIntCallCompilerExtOperands
Ancestors
  bodyIntCallCompilerAggregate bodyIntCallCompilerUniversalAggregate bodyIntCallCompilerAbiWrappers
  bodyIntCallCompilerContext bodyIntCallCompilerFloor bodyIntCallCompilerEmit
  bodyIntCallCompilerUnwrap exprLowering compileEnv

Theorem intcall_interval_extcodesize_check:
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a (SND (compile_extcodesize_check addr a))
Proof
  strip_tac >> simp[compile_extcodesize_check_def, comp_ignore_bind_def] >>
  irule intcall_interval_bind_floor >>
  simp[intcall_interval_emit_op, intcall_interval_emit_void]
QED

Theorem intcall_interval_extcall_store_values:
  !vs off a. k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_extcall_store_values cenv vs buf off a))
Proof
  Induct >> simp[compile_extcall_store_values_def, intcall_interval_return] >>
  rpt gen_tac >> PairCases_on `h` >> strip_tac >>
  Cases_on `is_word_type h1` >> Cases_on `is_bytestring_type h1` >>
  simp[compile_extcall_store_values_def, comp_ignore_bind_def] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_emit_op, intcall_interval_emit_void,
            intcall_interval_unwrap_value, intcall_interval_store_bytestring])
QED

Theorem intcall_interval_ext_call_kwarg:
  (!ce ty e a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) ==>
  !cenv rt kw e a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a
      (SND (compile_ext_call_kwarg cfn cenv rt kw e a))
Proof
  rpt strip_tac >> simp[compile_ext_call_kwarg_def] >>
  IF_CASES_TAC >> simp[] >>
  rpt (rpt strip_tac >> simp[] >> irule intcall_interval_bind_floor >>
       simp[intcall_interval_materialize_vv, intcall_interval_lower_value,
            intcall_interval_return])
QED

Theorem intcall_interval_ext_call_kwargs:
  (!ce ty e a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) ==>
  !ks es a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a
      (SND (compile_ext_call_kwargs cfn cenv rt ks es a))
Proof
  strip_tac >> Induct >> Cases_on `es` >>
  simp[compile_ext_call_kwargs_def, intcall_interval_return] >>
  rpt strip_tac >> irule intcall_interval_bind_floor >>
  simp[intcall_interval_ext_call_kwarg, pairTheory.FORALL_PROD] >>
  rpt strip_tac >> irule intcall_interval_bind_floor >>
  simp[pairTheory.FORALL_PROD, intcall_interval_return]
QED

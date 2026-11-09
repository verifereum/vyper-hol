Theory bodyIntCallCompilerBuiltin
Ancestors
  bodyIntCallCompilerUniversalAggregate bodyIntCallCompilerMembership
  bodyIntCallCompilerScalar bodyIntCallCompilerRead bodyIntCallCompilerHash
  bodyIntCallCompilerSlice bodyIntCallCompilerLiteral
  bodyIntCallCompilerUnwrap bodyIntCallCompilerAggregate
  bodyIntCallCompilerFloor bodyIntCallCompilerEmit bodyIntCallCompilerInterval
  exprBopLowering exprLowering compileEnv

Theorem intcall_interval_membership_callback[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) /\
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND ((\(vv,b). as_stack_val rt
      (compile_var_array_membership ce needle vv rhs_ty is_in b))
      (cfn ce rhs_ty e a)))
Proof
  strip_tac >> ho_match_mp_tac intcall_interval_pair_bind_floor >>
  simp[exprBopLoweringTheory.as_stack_val_pair, intcall_interval_var_membership]
QED

Theorem intcall_interval_membership_list_callback[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) /\
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND ((\(ops,b). if is_in then
      as_stack_val rt (compile_list_membership_in needle ops b) else
      as_stack_val rt (compile_list_membership_notin needle ops b))
      (compile_multi_exprs cfn ce es a)))
Proof
  strip_tac >> ho_match_mp_tac intcall_interval_pair_bind_floor >>
  simp[intcall_interval_multi_exprs_floor] >> rpt strip_tac >>
  IF_CASES_TAC >> simp[exprBopLoweringTheory.as_stack_val_pair,
    intcall_interval_membership_in, intcall_interval_membership_notin]
QED


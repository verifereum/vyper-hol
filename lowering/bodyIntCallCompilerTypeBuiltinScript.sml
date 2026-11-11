Theory bodyIntCallCompilerTypeBuiltin
Ancestors
  bodyIntCallCompilerAbiWrappers bodyIntCallCompilerUniversalAggregate
  bodyIntCallCompilerConvert bodyIntCallCompilerSlice
  bodyIntCallCompilerContext bodyIntCallCompilerUnwrap bodyIntCallCompilerAggregate
  bodyIntCallCompilerFloor bodyIntCallCompilerEmit bodyIntCallCompilerInterval
  exprBopLowering exprLowering compileEnv

Theorem intcall_interval_type_convert_branch[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) /\
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_type_builtin_dispatch_body cfn ce vt ty Convert rt es a))
Proof
  strip_tac >> simp[compile_type_builtin_dispatch_body_def] >>
  ho_match_mp_tac intcall_interval_pair_bind_floor >>
  simp[intcall_interval_lower_value] >> rpt strip_tac >>
  rpt IF_CASES_TAC >>
  simp[intcall_compiler_interval_refl, exprBopLoweringTheory.as_stack_val_pair,
       intcall_interval_bytestring_widen_copy] >>
  Cases_on `rt` >>
  simp[exprBopLoweringTheory.as_stack_val_pair, intcall_interval_type_convert]
QED

Theorem intcall_interval_type_extract_branch[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) /\
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_type_builtin_dispatch_body cfn ce vt ty Extract32 rt es a))
Proof
  strip_tac >> simp[compile_type_builtin_dispatch_body_def] >>
  rpt (ho_match_mp_tac intcall_interval_pair_bind_floor >>
       simp[intcall_interval_lower_value, intcall_interval_bytestring_src,
            intcall_interval_extract32_load, intcall_interval_clamp_basetype,
            exprBopLoweringTheory.as_stack_val_pair, pairTheory.FORALL_PROD] >>
       rpt strip_tac) >>
  simp[intcall_interval_lower_value, intcall_interval_bytestring_src,
       intcall_interval_extract32_load, intcall_interval_clamp_basetype]
QED

Theorem intcall_interval_type_encode_branch[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) /\
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_type_builtin_dispatch_body cfn ce vt ty (AbiEncode ensure mid) rt es a))
Proof
  strip_tac >> simp[compile_type_builtin_dispatch_body_def] >>
  rpt IF_CASES_TAC >>
  pure_rewrite_tac[oneline as_ptr_val_def, pairTheory.pair_CASE_UNCURRY,
                   combinTheory.C_DEF] >>
  rpt (ho_match_mp_tac intcall_interval_pair_bind_floor >>
       simp[intcall_interval_lower_value, intcall_interval_unwrap_value,
            intcall_interval_alloc_buffer, intcall_interval_emit_void,
            intcall_interval_abi_encode_args_all, intcall_interval_store_abi_tuple,
            intcall_interval_lower_abi_encode, intcall_compiler_interval_refl] >>
       rpt strip_tac) >>
  simp[intcall_interval_lower_value, intcall_interval_abi_encode_args_all,
       intcall_compiler_interval_refl]
QED

Theorem intcall_interval_type_decode_branch[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) /\
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_type_builtin_dispatch_body cfn ce vt ty (AbiDecode uw) rt es a))
Proof
  strip_tac >> simp[compile_type_builtin_dispatch_body_def] >>
  pure_rewrite_tac[oneline as_ptr_val_def, pairTheory.pair_CASE_UNCURRY,
                   combinTheory.C_DEF] >>
  rpt (ho_match_mp_tac intcall_interval_pair_bind_floor >>
       simp[intcall_interval_unwrap_value, intcall_interval_lower_abi_decode,
            intcall_compiler_interval_refl] >> rpt strip_tac) >>
  simp[intcall_compiler_interval_refl]
QED

Theorem intcall_interval_type_builtin_body:
  (!ce ty e a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) ==>
  !ce vt ty tb rt es a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a
      (SND (compile_type_builtin_dispatch_body cfn ce vt ty tb rt es a))
Proof
  strip_tac >> rpt gen_tac >> Cases_on `tb` >>
  simp[intcall_interval_type_convert_branch, intcall_interval_type_extract_branch,
       intcall_interval_type_encode_branch, intcall_interval_type_decode_branch] >>
  simp[compile_type_builtin_dispatch_body_def, intcall_compiler_interval_refl] >>
  strip_tac >> rpt IF_CASES_TAC >>
  simp[pairTheory.ELIM_UNCURRY, intcall_interval_builtin_empty_complex,
       intcall_compiler_interval_refl]
QED

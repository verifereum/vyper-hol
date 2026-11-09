Theory bodyIntCallCompilerBuiltin
Ancestors
  bodyIntCallCompilerUniversalAggregate bodyIntCallCompilerMembership
  bodyIntCallCompilerScalar bodyIntCallCompilerRead bodyIntCallCompilerHash
  bodyIntCallCompilerSlice bodyIntCallCompilerLiteral bodyIntCallCompilerContext
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

Theorem intcall_make_array_case_pred[local]:
  !P ordinary special e.
    P ordinary /\
    (!ann et bnd elems. e = Builtin ann (MakeArray et bnd) elems ==>
      P (special elems)) ==>
    P (case e of Builtin _ (MakeArray _ _) elems => special elems
       | _ => ordinary)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `e` >> simp[] >>
  rename1 `Builtin ann bi es` >> Cases_on `bi` >> simp[]
QED

Theorem intcall_interval_builtin_bop[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) /\
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_builtin_dispatch_body cfn ce rt ty (Bop bop) es a))
Proof
  strip_tac >> simp[compile_builtin_dispatch_body_def] >>
  rpt IF_CASES_TAC >>
  rpt (ho_match_mp_tac intcall_interval_pair_bind_floor >>
       simp[intcall_interval_lower_value, intcall_interval_bytestring_hash,
            intcall_interval_emit_op, intcall_interval_binop] >> rpt strip_tac)
  >- (rename1 `intcall_compiler_interval k mid (SND _)` >>
      ho_match_mp_tac (BETA_RULE (Q.ISPEC `\p. intcall_compiler_interval k mid (SND p)`
               intcall_make_array_case_pred)) >>
      conj_tac
      >- (irule intcall_interval_membership_callback >> simp[]) >>
      rpt strip_tac >> irule intcall_interval_membership_list_callback >> simp[]) >>
  simp[exprBopLoweringTheory.as_stack_val_pair, intcall_interval_binop,
       intcall_interval_emit_op] >>
  IF_CASES_TAC >> simp[intcall_interval_emit_op] >>
  ho_match_mp_tac intcall_interval_pair_bind_floor >>
  simp[intcall_interval_emit_op]
QED

Theorem intcall_interval_builtin_slice[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) /\
  k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_builtin_dispatch_body cfn ce rt ty (Slice n) es a))
Proof
  strip_tac >> simp[compile_builtin_dispatch_body_def] >>
  rpt IF_CASES_TAC >>
  pure_rewrite_tac[oneline as_ptr_val_def, pairTheory.pair_CASE_UNCURRY,
                   combinTheory.C_DEF] >>
  rpt (ho_match_mp_tac intcall_interval_pair_bind_floor >>
       simp[intcall_interval_lower_value, intcall_interval_bytestring_src,
            intcall_interval_slice_calldata, intcall_interval_slice_code,
            intcall_interval_slice_extcode, intcall_interval_slice_data,
            intcall_interval_slice_out_buf, intcall_interval_alloc_buffer,
            intcall_interval_emit_void, pairTheory.FORALL_PROD,
            intcall_compiler_interval_refl] >> rpt strip_tac) >>
  simp[intcall_interval_slice_calldata, intcall_interval_slice_code,
       intcall_interval_slice_extcode, intcall_interval_slice_data,
       intcall_compiler_interval_refl] >>
  IF_CASES_TAC >>
  rpt (ho_match_mp_tac intcall_interval_pair_bind_floor >>
       simp[intcall_interval_lower_value, intcall_interval_bytestring_src,
            intcall_interval_alloc_buffer, intcall_interval_emit_void,
            pairTheory.FORALL_PROD] >> rpt strip_tac) >>
  simp[intcall_interval_slice_data, intcall_compiler_interval_refl]
QED

Theory bodyIntCallCompilerBuiltin
Ancestors
  bodyIntCallCompilerUniversalAggregate bodyIntCallCompilerMembership
  bodyIntCallCompilerScalar bodyIntCallCompilerRead bodyIntCallCompilerHash
  bodyIntCallCompilerSlice bodyIntCallCompilerLiteral bodyIntCallCompilerContext
  bodyIntCallCompilerUnwrap bodyIntCallCompilerAggregate
  bodyIntCallCompilerFloor bodyIntCallCompilerEmit bodyIntCallCompilerInterval
  exprBopLowering exprLowering compileEnv
Libs
  BasicProvers

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

Theorem intcall_fixed_bytes_case_pred[local]:
  !P ordinary special ty.
    P ordinary /\ (!m. P (special m)) ==>
    P (case ty of BaseT (BytesT (Fixed m)) => special m | _ => ordinary)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `ty` >> simp[] >>
  TOP_CASE_TAC >> simp[] >> TOP_CASE_TAC >> simp[]
QED

Theorem intcall_interval_builtin_hash[local]:
  (!ce ty e a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) /\
  (bi = Keccak256 \/ bi = Sha256) /\ k <= a.cs_next_var ==>
  intcall_compiler_interval k a
    (SND (compile_builtin_dispatch_body cfn ce rt ty bi es a))
Proof
  strip_tac >> gvs[compile_builtin_dispatch_body_def] >>
  (IF_CASES_TAC
   >- (simp[exprBopLoweringTheory.as_stack_val_pair] >>
       ho_match_mp_tac intcall_interval_pair_bind_floor >>
       simp[intcall_interval_lower_value, intcall_interval_keccak256_bytes,
            intcall_interval_sha256_bytes])) >>
  ho_match_mp_tac (BETA_RULE (Q.ISPEC
    `\p. intcall_compiler_interval k a (SND p)`
    intcall_fixed_bytes_case_pred)) >> conj_tac >> rpt gen_tac >>
  simp[exprBopLoweringTheory.as_stack_val_pair] >>
  ho_match_mp_tac intcall_interval_pair_bind_floor >>
  simp[intcall_interval_lower_value, intcall_interval_keccak256_bytes,
       intcall_interval_keccak256_word, intcall_interval_keccak256_bytesm,
       intcall_interval_sha256_bytes, intcall_interval_sha256_word,
       intcall_interval_sha256_bytesm]
QED

Theorem intcall_interval_builtin_body:
  (!ce ty e a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a (SND (cfn ce ty e a))) ==>
  !ce rt ty bi es a. k <= a.cs_next_var ==>
    intcall_compiler_interval k a
      (SND (compile_builtin_dispatch_body cfn ce rt ty bi es a))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >> Cases_on `bi` >>
  simp[intcall_interval_builtin_bop, intcall_interval_builtin_slice,
       intcall_interval_builtin_hash] >>
  simp[compile_builtin_dispatch_body_def,
       exprBopLoweringTheory.as_stack_val_pair] >>
  pure_rewrite_tac[oneline as_ptr_val_def, pairTheory.pair_CASE_UNCURRY,
                   combinTheory.C_DEF] >>
  rpt (ho_match_mp_tac intcall_interval_pair_bind_floor >>
       simp[intcall_interval_lower_value, intcall_interval_unwrap_value,
            intcall_interval_alloc_buffer, intcall_interval_emit_op,
            intcall_interval_emit_void, intcall_interval_concat_all,
            intcall_interval_acc_all, intcall_interval_env_var,
            intcall_interval_neg, intcall_interval_abs,
            intcall_interval_builtin_calldatasize, intcall_interval_builtin_len,
            intcall_interval_slice_calldata, intcall_interval_blockhash,
            intcall_interval_blobhash, intcall_interval_addmod,
            intcall_interval_mulmod, intcall_interval_ceil, intcall_interval_floor,
            intcall_interval_pow_mod256, intcall_interval_ecrecover,
            intcall_interval_ecadd_points, intcall_interval_ecmul_point,
            intcall_interval_uint2str, pairTheory.FORALL_PROD] >> rpt strip_tac) >>
  simp[intcall_interval_builtin_calldatasize, intcall_compiler_interval_refl]
  >- (IF_CASES_TAC >> simp[intcall_interval_emit_op, intcall_interval_invert])
  >- (IF_CASES_TAC >> simp[intcall_interval_wei_int, intcall_interval_wei_decimal])
  >- (TOP_CASE_TAC >> simp[] >>
      ho_match_mp_tac intcall_interval_pair_bind_floor >>
      simp[intcall_interval_alloc_buffer] >> rpt strip_tac >>
      simp[pairTheory.ELIM_UNCURRY, intcall_interval_make_tuple_all,
           intcall_interval_make_array_all]) >>
  simp[intcall_interval_env_var, intcall_interval_acc_all] >>
  Cases_on `method_id_literal (HD es)` >> simp[intcall_interval_literal_vv] >>
  ho_match_mp_tac intcall_interval_pair_bind_floor >>
  simp[intcall_interval_lower_value] >> rpt strip_tac >>
  IF_CASES_TAC >> simp[pairTheory.ELIM_UNCURRY, intcall_interval_method_id_runtime]
QED

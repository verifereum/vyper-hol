(* Non-allocating operations used by the expression dispatchers. *)
Theory runtimePeakMemoryBuiltins
Ancestors
  runtimePeakMemoryCode builtinSimple builtinMath builtinBytes builtinSystem
  builtinMisc builtinHashing builtinStrings exprLowering compileEnv context
  emitHelper venomInst list

fun windows_tac thms =
  rpt (FIRST [
    CHANGED_TAC (simp(thms @ [LET_THM, pairTheory.FORALL_PROD, pairTheory.UNCURRY_DEF,
      dalloca_windows_emit_helpers, dalloca_windows_new_block,
      dalloca_windows_fresh, dalloca_windows_return, dalloca_windows_select,
      dalloca_windows_alloc_buffer])),
    gen_tac, irule dalloca_windows_bind >> conj_tac,
    irule dalloca_windows_ignore_bind >> conj_tac,
    COND_CASES_TAC, BasicProvers.TOP_CASE_TAC]);

Theorem dalloca_windows_clamp:
  preserves_dalloca_windows window (compile_clamp v ty) /\
  preserves_dalloca_windows window (compile_int_clamp signed bits v)
Proof
  Cases_on `type_bounds ty` >>
  simp[compile_clamp_def, compile_int_clamp_def] >> conj_tac >> windows_tac []
QED

Theorem dalloca_windows_clamp_and_return[local]:
  preserves_dalloca_windows window (clamp_and_return v ty)
Proof
  simp[clamp_and_return_def] >> windows_tac [dalloca_windows_clamp]
QED

Theorem dalloca_windows_clamp_basetype:
  preserves_dalloca_windows window (compile_clamp_basetype v ty)
Proof
  Cases_on `ty` >>
  TRY (rename1 `BaseT b` >> Cases_on `b` >>
       TRY (rename1 `BytesT m` >> Cases_on `m`)) >>
  simp[compile_clamp_basetype_def] >> windows_tac [dalloca_windows_clamp_and_return]
QED

Theorem dalloca_windows_arithmetic[local]:
  preserves_dalloca_windows window (compile_safe_add x y ty) /\
  preserves_dalloca_windows window (compile_safe_sub x y ty) /\
  preserves_dalloca_windows window (compile_safe_mul x y ty) /\
  preserves_dalloca_windows window (compile_safe_div x y ty) /\
  preserves_dalloca_windows window (compile_safe_decimal_div x y divisor ty) /\
  preserves_dalloca_windows window (compile_safe_mod x y ty) /\
  preserves_dalloca_windows window (compile_safe_pow x y ty base_lit exp_lit) /\
  preserves_dalloca_windows window (wrap_truncate x ty)
Proof
  Cases_on `base_lit` >> Cases_on `exp_lit` >>
  simp[compile_safe_add_def, compile_safe_sub_def, compile_safe_mul_def,
       compile_safe_div_def, compile_safe_decimal_div_def, compile_safe_mod_def,
       compile_safe_pow_def, wrap_truncate_def] >> rpt conj_tac >>
  windows_tac [dalloca_windows_clamp, dalloca_windows_clamp_and_return,
               compile_mul_overflow_check_def]
QED

Theorem dalloca_windows_compare[local]:
  preserves_dalloca_windows window (compile_compare bop x y ty)
Proof
  Cases_on `bop` >> simp[compile_compare_def] >> windows_tac []
QED

Theorem dalloca_windows_binop:
  preserves_dalloca_windows window (compile_binop bop x y ty base_lit exp_lit)
Proof
  Cases_on `bop` >> simp[compile_binop_def] >>
  windows_tac [dalloca_windows_arithmetic, dalloca_windows_compare]
QED

Theorem dalloca_windows_hashing[local]:
  preserves_dalloca_windows window (compile_keccak256_word opnd) /\
  preserves_dalloca_windows window (compile_keccak256_bytes opnd) /\
  preserves_dalloca_windows window (compile_keccak256_bytesm opnd n) /\
  preserves_dalloca_windows window (compile_sha256_word opnd) /\
  preserves_dalloca_windows window (compile_sha256_bytes opnd) /\
  preserves_dalloca_windows window (compile_sha256_bytesm opnd n)
Proof
  simp[compile_keccak256_word_def, compile_keccak256_bytes_def, compile_keccak256_bytesm_def,
       compile_sha256_word_def, compile_sha256_bytes_def, compile_sha256_bytesm_def] >>
  rpt conj_tac >> windows_tac []
QED

Theorem dalloca_windows_method_id[local]:
  preserves_dalloca_windows window (compile_method_id_hash ty v) /\
  preserves_dalloca_windows window (compile_method_id_runtime ty v bytes4)
Proof
  `preserves_dalloca_windows window (compile_method_id_hash ty v)` by
    (Cases_on `ty` >>
     TRY (rename1 `BaseT b` >> Cases_on `b` >>
          TRY (rename1 `BytesT m` >> Cases_on `m`)) >>
     simp[compile_method_id_hash_def, dalloca_windows_hashing]) >>
  simp[compile_method_id_runtime_def] >> windows_tac []
QED

Theorem dalloca_windows_base_operations:
  preserves_dalloca_windows window (compile_env_var item) /\
  preserves_dalloca_windows window (compile_neg v ty) /\
  preserves_dalloca_windows window (compile_invert v ty cenv) /\
  preserves_dalloca_windows window (compile_builtin_abs v) /\
  preserves_dalloca_windows window (compile_builtin_calldatasize) /\
  preserves_dalloca_windows window (compile_blockhash v) /\
  preserves_dalloca_windows window (compile_blobhash v) /\
  preserves_dalloca_windows window (compile_addmod v x y) /\
  preserves_dalloca_windows window (compile_mulmod v x y) /\
  preserves_dalloca_windows window (compile_pow_mod256 x y) /\
  preserves_dalloca_windows window (compile_ceil v divisor) /\
  preserves_dalloca_windows window (compile_floor v divisor) /\
  preserves_dalloca_windows window (compile_ecrecover v x y z) /\
  preserves_dalloca_windows window (compile_ecadd_points x y) /\
  preserves_dalloca_windows window (compile_ecmul_point x y) /\
  preserves_dalloca_windows window (compile_as_wei_value_decimal v factor divisor) /\
  preserves_dalloca_windows window (compile_as_wei_value_int v factor signed) /\
  preserves_dalloca_windows window (compile_bytestring_hash v) /\
  preserves_dalloca_windows window (compile_bytestring_src v) /\
  preserves_dalloca_windows window (compile_extract32_load v x y)
Proof
  rpt conj_tac >>
  TRY (Cases_on `item` >> simp[compile_env_var_def] >> windows_tac [] >> NO_TAC) >>
  TRY (Cases_on `ty` >> simp[compile_invert_def] >> windows_tac [] >> NO_TAC) >>
  simp[compile_neg_def, compile_builtin_abs_def, compile_builtin_calldatasize_def,
       compile_blockhash_def, compile_blobhash_def, compile_addmod_def, compile_mulmod_def,
       compile_pow_mod256_def, compile_ceil_def, compile_floor_def, compile_ecrecover_def,
       compile_ecadd_points_def, compile_ecmul_point_def, compile_as_wei_value_decimal_def,
       compile_as_wei_value_int_def, compile_bytestring_hash_def, compile_bytestring_src_def,
       compile_extract32_load_def] >>
  windows_tac [compile_assert_slice_bounds_def] >>
  Cases_on `type_bounds ty` >> windows_tac []
QED

Theorem dalloca_windows_hash_ops:
  preserves_dalloca_windows window (compile_keccak256_word opnd) /\
  preserves_dalloca_windows window (compile_keccak256_bytes opnd) /\
  preserves_dalloca_windows window (compile_keccak256_bytesm opnd n) /\
  preserves_dalloca_windows window (compile_sha256_word opnd) /\
  preserves_dalloca_windows window (compile_sha256_bytes opnd) /\
  preserves_dalloca_windows window (compile_sha256_bytesm opnd n) /\
  preserves_dalloca_windows window (compile_method_id_runtime ty opnd bytes4)
Proof
  simp[dalloca_windows_hashing, dalloca_windows_method_id]
QED

Theorem dalloca_windows_load_bytestring_as_word[local]:
  opc <> DALLOCA ==>
  preserves_dalloca_windows window (load_bytestring_as_word v opc)
Proof
  strip_tac >> simp[load_bytestring_as_word_def] >> windows_tac []
QED

Theorem dalloca_windows_convert:
  preserves_dalloca_windows window (compile_type_convert v conv)
Proof
  Cases_on `conv` >> simp[compile_type_convert_def] >>
  windows_tac [dalloca_windows_clamp, dalloca_windows_load_bytestring_as_word]
QED

Theorem dalloca_windows_zero_words:
  !n. preserves_dalloca_windows window (compile_zero_words buf n)
Proof
  Induct >> simp[compile_zero_words_def, dalloca_windows_return] >> windows_tac []
QED

Theorem dalloca_windows_bytes_ops:
  preserves_dalloca_windows window (compile_slice_calldata start len sz) /\
  preserves_dalloca_windows window (compile_slice_data src_len src start len sz) /\
  preserves_dalloca_windows window (compile_slice_code start len sz) /\
  preserves_dalloca_windows window (compile_slice_extcode addr start len sz) /\
  preserves_dalloca_windows window (compile_builtin_empty_complex sz zero_len) /\
  preserves_dalloca_windows window (compile_uint2str v maxlen sz)
Proof
  simp[compile_slice_calldata_def, compile_slice_data_def, compile_slice_code_def,
       compile_slice_extcode_def, compile_builtin_empty_complex_def, compile_uint2str_def] >>
  rpt conj_tac >>
  windows_tac [compile_assert_slice_bounds_def, compile_slice_out_buf_def,
               compile_copy_memory_dynamic_def, dalloca_windows_zero_words]
QED

Theorem dalloca_windows_membership_folds[local]:
  !vals. (!acc. preserves_dalloca_windows window (fold_membership_or acc vals)) /\
         (!acc. preserves_dalloca_windows window (fold_membership_and acc vals)) /\
         (!val_op. preserves_dalloca_windows window (emit_membership_eqs val_op vals))
Proof
  Induct >> simp[fold_membership_or_def, fold_membership_and_def, emit_membership_eqs_def,
                 dalloca_windows_return] >>
  rpt strip_tac >> windows_tac []
QED

Theorem dalloca_windows_list_membership:
  preserves_dalloca_windows window (compile_list_membership_in needle elems) /\
  preserves_dalloca_windows window (compile_list_membership_notin needle elems)
Proof
  simp[compile_list_membership_in_def, compile_list_membership_notin_def] >>
  conj_tac >> windows_tac [dalloca_windows_membership_folds]
QED

Theorem dalloca_windows_array_membership_loop:
  (!addr. preserves_dalloca_windows window (loader addr)) ==>
  preserves_dalloca_windows window
    (compile_array_membership_loop needle arr len sz off loader bound is_in)
Proof
  strip_tac >> simp[compile_array_membership_loop_def] >> windows_tac []
QED

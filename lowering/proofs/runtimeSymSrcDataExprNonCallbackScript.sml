Theory runtimeSymSrcDataExprNonCallback
Ancestors
  runtimeSymSrcDataFrame exprLowering compileEnv

fun frame_tac g = (simp[comp_ignore_bind_def] >> rpt (match_mp_tac runtime_data_frame_bind >> conj_tac
  >- (simp[] >> frame_tac) >> gen_tac >> BETA_TAC) >> simp[]) g;

Theorem runtime_data_frame_compile_clamp[simp]:
  runtime_data_frame (compile_clamp v ty)
Proof
  simp[compile_clamp_def] >> pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[] >> frame_tac
QED

Theorem runtime_data_frame_clamp_and_return[simp]:
  runtime_data_frame (clamp_and_return v ty)
Proof
  simp[clamp_and_return_def]
QED

Theorem runtime_data_frame_clamp_basetype[simp]:
  runtime_data_frame (compile_clamp_basetype v ty)
Proof
  Cases_on `ty` >> simp[compile_clamp_basetype_def] >>
  rename1 `BaseT b` >> Cases_on `b` >> simp[compile_clamp_basetype_def] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  TRY (rename1 `BytesT bd` >> Cases_on `bd` >> simp[compile_clamp_basetype_def]) >>
  rpt (IF_CASES_TAC >> simp[]) >> frame_tac
QED

Theorem runtime_data_frame_safe_add[simp]:
  runtime_data_frame (compile_safe_add x y ty)
Proof
  simp[compile_safe_add_def] >> irule runtime_data_frame_bind >> simp[] >>
  gen_tac >> rpt (IF_CASES_TAC >> simp[])
QED

Theorem runtime_data_frame_safe_sub[simp]:
  runtime_data_frame (compile_safe_sub x y ty)
Proof
  simp[compile_safe_sub_def] >> irule runtime_data_frame_bind >> simp[] >>
  gen_tac >> rpt (IF_CASES_TAC >> simp[])
QED

Theorem runtime_data_frame_mul_overflow[simp]:
  runtime_data_frame (compile_mul_overflow_check x y res sg bits)
Proof
  simp[compile_mul_overflow_check_def] >>
  Cases_on `sg /\ bits = 256` >> simp[] >> frame_tac
QED

Theorem runtime_data_frame_safe_mul[simp]:
  runtime_data_frame (compile_safe_mul x y ty)
Proof
  simp[compile_safe_mul_def] >>
  Cases_on `type_bits ty > 128` >>
  Cases_on `is_decimal_type ty` >>
  Cases_on `type_bits ty < 256` >> simp[]
QED

Theorem runtime_data_frame_safe_div[simp]:
  runtime_data_frame (compile_safe_div x y ty)
Proof
  Cases_on `is_signed_type ty` >> Cases_on `type_bits ty = 256` >>
  Cases_on `type_bits ty < 256` >> simp[compile_safe_div_def] >> frame_tac
QED

Theorem runtime_data_frame_safe_decimal_div[simp]:
  runtime_data_frame (compile_safe_decimal_div x y divisor ty)
Proof
  simp[compile_safe_decimal_div_def] >> frame_tac
QED

Theorem runtime_data_frame_safe_mod[simp]:
  runtime_data_frame (compile_safe_mod x y ty)
Proof
  Cases_on `is_signed_type ty` >> simp[compile_safe_mod_def]
QED

Theorem runtime_data_frame_safe_pow[simp]:
  runtime_data_frame (compile_safe_pow x y ty bl el)
Proof
  Cases_on `bl` >> Cases_on `el` >> simp[compile_safe_pow_def] >>
  rpt (IF_CASES_TAC >> simp[]) >> frame_tac
QED

Theorem runtime_data_frame_compare[simp]:
  runtime_data_frame (compile_compare op x y ty)
Proof
  Cases_on `op` >> simp[compile_compare_def] >>
  rpt (IF_CASES_TAC >> simp[]) >> frame_tac
QED

Theorem runtime_data_frame_wrap_truncate[simp]:
  runtime_data_frame (wrap_truncate v ty)
Proof
  simp[wrap_truncate_def] >> rpt (IF_CASES_TAC >> simp[])
QED

Theorem runtime_data_frame_binop:
  (!c x y. runtime_data_frame (compile_select c x y)) ==>
  runtime_data_frame (compile_binop op x y ty bl el)
Proof
  strip_tac >> Cases_on `op` >> simp[compile_binop_def] >>
  rpt (IF_CASES_TAC >> simp[]) >> frame_tac
QED

Theorem runtime_data_frame_bytestring_hash[simp]:
  runtime_data_frame (compile_bytestring_hash p)
Proof simp[compile_bytestring_hash_def] >> frame_tac
QED

Theorem runtime_data_frame_membership_eqs[simp]:
  !es n. runtime_data_frame (emit_membership_eqs n es)
Proof Induct >> simp[emit_membership_eqs_def] >> frame_tac
QED

Theorem runtime_data_frame_membership_or[simp]:
  !es acc. runtime_data_frame (fold_membership_or acc es)
Proof Induct >> simp[fold_membership_or_def] >> frame_tac
QED

Theorem runtime_data_frame_membership_and[simp]:
  !es acc. runtime_data_frame (fold_membership_and acc es)
Proof Induct >> simp[fold_membership_and_def] >> frame_tac
QED

Theorem runtime_data_frame_list_membership_in[simp]:
  runtime_data_frame (compile_list_membership_in n es)
Proof
  simp[compile_list_membership_in_def] >>
  match_mp_tac runtime_data_frame_bind >> simp[] >> Cases >> simp[]
QED

Theorem runtime_data_frame_list_membership_notin[simp]:
  runtime_data_frame (compile_list_membership_notin n es)
Proof
  simp[compile_list_membership_notin_def] >>
  match_mp_tac runtime_data_frame_bind >> simp[] >> Cases >> simp[] >> frame_tac
QED

Theorem runtime_data_frame_array_membership_loop:
  (!p. runtime_data_frame (loader p)) ==>
  runtime_data_frame (compile_array_membership_loop n arr len sz off loader bd isin)
Proof
  strip_tac >> Cases_on `bd` >> Cases_on `off > 0` >> Cases_on `isin` >>
  simp[compile_array_membership_loop_def] >> frame_tac
QED

Theorem runtime_data_frame_var_array_membership:
  (!ctor imm loc off. runtime_data_frame (compile_ptr_load ctor imm loc off)) ==>
  runtime_data_frame (compile_var_array_membership cenv n vv ty isin)
Proof
  strip_tac >> Cases_on `ty` >>
  TRY (rename1 `ArrayT t bd` >> Cases_on `bd`) >>
  simp[compile_var_array_membership_def] >>
  simp[runtime_data_frame_array_membership_loop] >>
  frame_tac >> irule runtime_data_frame_array_membership_loop >> simp[]
QED

Theorem runtime_data_frame_mapping_subscript:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_mapping_subscript slot key)
Proof strip_tac >> simp[compile_mapping_subscript_def] >> frame_tac
QED

Theorem runtime_data_frame_keccak256_key:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_keccak256_key key bs32)
Proof strip_tac >> Cases_on `bs32` >> simp[compile_keccak256_key_def] >> frame_tac
QED

Theorem runtime_data_frame_extcodesize_check[simp]:
  runtime_data_frame (compile_extcodesize_check addr)
Proof simp[compile_extcodesize_check_def] >> frame_tac
QED

Theorem runtime_data_frame_return_value_decode:
  (!c x y. runtime_data_frame (compile_select c x y)) ==>
  runtime_data_frame (compile_return_value_decode lo hi)
Proof strip_tac >> simp[compile_return_value_decode_def] >> frame_tac
QED

Theorem runtime_data_frame_unwrap_value:
  (!ctor imm loc off. runtime_data_frame (compile_ptr_load ctor imm loc off)) /\
  (!p loc bytes words ctor imm.
    runtime_data_frame (compile_ensure_in_memory p loc bytes words ctor imm)) ==>
  runtime_data_frame (unwrap_value cenv vv)
Proof
  strip_tac >> Cases_on `vv` >> simp[unwrap_value_def] >>
  IF_CASES_TAC >> simp[] >> Cases_on `p.ptr_location` >> simp[]
QED

Theorem runtime_data_frame_multi_vvs:
  !es. (!e. MEM e es ==> runtime_data_frame (cfn cenv (expr_type e) e)) ==>
  runtime_data_frame (compile_multi_vvs cfn cenv es)
Proof Induct >> simp[compile_multi_vvs_def] >> strip_tac >> frame_tac
QED

Theorem runtime_data_frame_extcall_store_values:
  (!vv. runtime_data_frame (unwrap_value cenv vv)) /\
  (!v dst. runtime_data_frame (compile_store_bytestring v dst)) ==>
  !vs buf off. runtime_data_frame (compile_extcall_store_values cenv vs buf off)
Proof
  strip_tac >> Induct >> simp[compile_extcall_store_values_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >> simp[compile_extcall_store_values_def] >>
  Cases_on `is_word_type h1` >> Cases_on `is_bytestring_type h1` >> simp[] >> frame_tac
QED

Theorem runtime_data_frame_default_return_path:
  (!v dst dt st. runtime_data_frame (compile_store_memory cenv v dst dt st)) /\
  (!lo hi. runtime_data_frame (compile_return_value_decode lo hi)) /\
  (!dst src opc lo hi info. runtime_data_frame (compile_abi_decode_to_buf dst src opc lo hi info)) ==>
  runtime_data_frame (compile_default_return_path cenv rt dt buf res dop addr skip lo hi info)
Proof
  strip_tac >> Cases_on `skip` >> simp[compile_default_return_path_def] >> frame_tac
QED

Theorem runtime_data_frame_external_call_kwargs:
  (!n. runtime_data_frame (compile_alloc_buffer n)) /\
  (!vs buf off. runtime_data_frame (compile_extcall_store_values cenv vs buf off)) /\
  (!dst src info. runtime_data_frame (compile_abi_encode_to_buf dst src info)) /\
  (!rt dt buf res dop addr skip lo hi info.
     runtime_data_frame (compile_default_return_path cenv rt dt buf res dop addr skip lo hi info)) /\
  (!lo hi. runtime_data_frame (compile_return_value_decode lo hi)) /\
  (!dst src opc lo hi info. runtime_data_frame (compile_abi_decode_to_buf dst src opc lo hi info)) ==>
  runtime_data_frame (compile_external_call_kwargs cenv addr vals tys mem abi mid rabi lo rmem static value gas skip has_default dop rt dt einfo dinfo)
Proof
  strip_tac >> simp[compile_external_call_kwargs_def] >>
  frame_tac >> rpt (IF_CASES_TAC >> simp[] >> frame_tac)
QED

Theorem runtime_data_frame_dynarray_append:
  (!v dst dt st. runtime_data_frame (compile_store_memory cenv v dst dt st)) /\
  (!src dst n sl dl imm. runtime_data_frame (compile_word_copy_loop src dst n sl dl imm)) ==>
  runtime_data_frame (compile_dynarray_append cenv arr v ws sz dt st cap prim ld sd)
Proof
  strip_tac >> simp[compile_dynarray_append_def] >>
  frame_tac >> rpt (IF_CASES_TAC >> simp[] >> frame_tac)
QED

Theorem runtime_data_frame_dynarray_pop:
  (!ctor imm loc off. runtime_data_frame (compile_ptr_load ctor imm loc off)) /\
  (!ctor imm loc off v. runtime_data_frame (compile_ptr_store ctor imm loc off v)) ==>
  runtime_data_frame (compile_dynarray_pop arr ws sz ctor imm loc)
Proof
  strip_tac >> simp[compile_dynarray_pop_def] >> frame_tac
QED

Theorem runtime_data_frame_stage_intcall_args:
  (!vv. runtime_data_frame (unwrap_value cenv vv)) /\
  (!n. runtime_data_frame (compile_alloc_buffer n)) /\
  (!v dst. runtime_data_frame (compile_store_bytestring v dst)) /\
  (!v dst dt st. runtime_data_frame (compile_store_memory cenv v dst dt st)) ==>
  !vs flags tys. runtime_data_frame (compile_stage_intcall_args cenv vs flags tys)
Proof
  strip_tac >> Induct >> simp[compile_stage_intcall_args_def] >>
  rpt gen_tac >> Cases_on `flags` >> Cases_on `tys` >>
  simp[compile_stage_intcall_args_def] >>
  TRY (Cases_on `h'` >> simp[compile_stage_intcall_args_def]) >>
  frame_tac >> rpt (IF_CASES_TAC >> simp[] >> frame_tac)
QED

Theorem runtime_data_frame_store_multi_results[simp]:
  !vs buf off. runtime_data_frame (store_multi_results buf vs off)
Proof
  Induct >> simp[store_multi_results_def] >> rpt gen_tac >> frame_tac
QED

Theorem runtime_data_frame_array_subscript:
  (!p. runtime_data_frame (loader p)) ==>
  runtime_data_frame (compile_array_subscript arr idx dyn cnt ws sz sg loader)
Proof
  strip_tac >> Cases_on `dyn` >> Cases_on `sg` >>
  simp[compile_array_subscript_def] >> frame_tac
QED

Theorem runtime_data_frame_tuple_subscript[simp]:
  runtime_data_frame (compile_tuple_subscript arr off)
Proof
  simp[compile_tuple_subscript_def]
QED

Theorem runtime_data_frame_store_byte_chunks[simp]:
  !p bs off. runtime_data_frame (compile_store_byte_chunks p bs off)
Proof
  recInduct compile_store_byte_chunks_ind >> rpt strip_tac >>
  simp[Once compile_store_byte_chunks_def] >> frame_tac >>
  gvs[]
QED

Theorem runtime_data_frame_bytelike_literal:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_bytelike_literal bs maxlen)
Proof
  strip_tac >> simp[compile_bytelike_literal_def] >> frame_tac
QED

Theorem runtime_data_frame_literal_vv:
  (!bs n. runtime_data_frame (compile_bytelike_literal bs n)) ==>
  runtime_data_frame (compile_literal_vv ty lit)
Proof
  strip_tac >> Cases_on `lit` >> simp[compile_literal_vv_def] >>
  TRY (rename1 `BoolL b` >> Cases_on `b` >> simp[compile_literal_vv_def]) >>
  Cases_on `ty` >> simp[compile_literal_vv_def] >>
  TRY (rename1 `BaseT b` >> Cases_on `b` >> simp[compile_literal_vv_def]) >>
  TRY (rename1 `BytesT bd` >> Cases_on `bd` >> simp[compile_literal_vv_def]) >> frame_tac
QED

Theorem runtime_data_frame_name_vv[simp]:
  runtime_data_frame (compile_name_vv cenv ty id)
Proof
  simp[compile_name_vv_def] >> Cases_on `FLOOKUP cenv.ce_vars id` >> simp[] >>
  Cases_on `x` >> simp[] >> frame_tac
QED

Theorem runtime_data_frame_env_var[simp]:
  runtime_data_frame (compile_env_var item)
Proof
  Cases_on `item` >> simp[compile_env_var_def] >> frame_tac
QED

Theorem runtime_data_frame_load_bytestring_as_word[simp]:
  runtime_data_frame (load_bytestring_as_word v opc)
Proof
  Cases_on `opc = SAR` >> simp[load_bytestring_as_word_def] >> frame_tac
QED

Theorem runtime_data_frame_int_clamp[simp]:
  runtime_data_frame (compile_int_clamp sg bits v)
Proof
  Cases_on `sg` >> simp[compile_int_clamp_def] >> frame_tac
QED

Theorem runtime_data_frame_type_convert[simp]:
  runtime_data_frame (compile_type_convert v conv)
Proof
  Cases_on `conv` >> simp[compile_type_convert_def] >>
  rpt (IF_CASES_TAC >> simp[]) >> frame_tac >>
  rpt (IF_CASES_TAC >> simp[] >> frame_tac) >>
  pairarg_tac >> simp[] >> frame_tac >>
  rpt (IF_CASES_TAC >> simp[] >> frame_tac)
QED

Theorem runtime_data_frame_bytestring_widen_copy:
  (!n. runtime_data_frame (compile_alloc_buffer n)) /\
  (!dst src sz. runtime_data_frame (compile_copy_memory dst src sz)) ==>
  runtime_data_frame (compile_bytestring_widen_copy dstsz v srcsz)
Proof
  strip_tac >> simp[compile_bytestring_widen_copy_def] >> frame_tac
QED

Theorem runtime_data_frame_neg[simp]:
  runtime_data_frame (compile_neg v ty)
Proof
  simp[compile_neg_def] >> pairarg_tac >> simp[] >> frame_tac
QED

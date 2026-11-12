Theory runtimeSymSrcDataBuiltins
Ancestors
  compileEnv runtimeSymSrcDataFrame builtinAbi builtinBytes builtinCreate
  builtinHashing builtinMath builtinMisc builtinSimple builtinStrings builtinSystem

(* External allocation and ABI operations are kept as uniform frame premises;
   their proofs belong to the Context and ABI libraries. *)
Theorem runtime_data_frame_select[simp]:
  runtime_data_frame (compile_select c a b)
Proof
  simp[compile_select_def]
QED

Theorem runtime_data_frame_zero_words[simp]:
  !n b. runtime_data_frame (compile_zero_words b n)
Proof
  Induct >> simp[compile_zero_words_def]
QED

Theorem runtime_data_frame_builtin_len:
  (!c i l p. runtime_data_frame (compile_ptr_load c i l p)) ==>
  runtime_data_frame (compile_builtin_len c i p l)
Proof
  simp[compile_builtin_len_def]
QED

Theorem runtime_data_frame_builtin_calldatasize[simp]:
  runtime_data_frame compile_builtin_calldatasize
Proof
  simp[compile_builtin_calldatasize_def]
QED

Theorem runtime_data_frame_builtin_empty_prim[simp]:
  runtime_data_frame compile_builtin_empty_prim
Proof
  simp[compile_builtin_empty_prim_def]
QED

Theorem runtime_data_frame_builtin_empty_complex:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_builtin_empty_complex n b)
Proof
  simp[compile_builtin_empty_complex_def, COND_RAND]
QED

Theorem runtime_data_frame_builtin_min[simp]:
  runtime_data_frame (compile_builtin_min a b u)
Proof
  Cases_on `u` >> simp[compile_builtin_min_def]
QED

Theorem runtime_data_frame_builtin_max[simp]:
  runtime_data_frame (compile_builtin_max a b u)
Proof
  Cases_on `u` >> simp[compile_builtin_max_def]
QED

Theorem runtime_data_frame_builtin_abs[simp]:
  runtime_data_frame (compile_builtin_abs a)
Proof
  simp[compile_builtin_abs_def] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem runtime_data_frame_unsafe_binop[simp]:
  runtime_data_frame (compile_unsafe_binop op x y bits s)
Proof
  simp[compile_unsafe_binop_def, COND_RAND]
QED

Theorem runtime_data_frame_unsafe_add[simp]:
  runtime_data_frame (compile_unsafe_add x y bits s)
Proof
  simp[compile_unsafe_add_def]
QED

Theorem runtime_data_frame_unsafe_sub[simp]:
  runtime_data_frame (compile_unsafe_sub x y bits s)
Proof
  simp[compile_unsafe_sub_def]
QED

Theorem runtime_data_frame_unsafe_mul[simp]:
  runtime_data_frame (compile_unsafe_mul x y bits s)
Proof
  simp[compile_unsafe_mul_def]
QED

Theorem runtime_data_frame_unsafe_div[simp]:
  runtime_data_frame (compile_unsafe_div x y bits s)
Proof
  simp[compile_unsafe_div_def]
QED

Theorem runtime_data_frame_pow_mod256[simp]:
  runtime_data_frame (compile_pow_mod256 x y)
Proof
  simp[compile_pow_mod256_def]
QED

Theorem runtime_data_frame_addmod[simp]:
  runtime_data_frame (compile_addmod x y z)
Proof
  simp[compile_addmod_def]
QED

Theorem runtime_data_frame_mulmod[simp]:
  runtime_data_frame (compile_mulmod x y z)
Proof
  simp[compile_mulmod_def]
QED

Theorem runtime_data_frame_shift[simp]:
  runtime_data_frame (compile_shift x y s)
Proof
  Cases_on `s` >> simp[compile_shift_def]
QED

Theorem runtime_data_frame_assert_slice_bounds[simp]:
  runtime_data_frame (compile_assert_slice_bounds s n l)
Proof
  simp[compile_assert_slice_bounds_def] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem runtime_data_frame_bytestring_src[simp]:
  runtime_data_frame (compile_bytestring_src p)
Proof
  simp[compile_bytestring_src_def]
QED

Theorem runtime_data_frame_slice_data:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_slice_data l p s n out)
Proof
  strip_tac >> simp[compile_slice_data_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem runtime_data_frame_slice_out_buf:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_slice_out_buf out)
Proof
  simp[compile_slice_out_buf_def]
QED

Theorem runtime_data_frame_slice_calldata:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_slice_calldata s n out)
Proof
  strip_tac >> simp[compile_slice_calldata_def] >>
  match_mp_tac runtime_data_frame_bind >> conj_tac
  >- simp[runtime_data_frame_slice_out_buf]
  >> simp[pairTheory.FORALL_PROD, comp_ignore_bind_def]
QED

Theorem runtime_data_frame_slice_code:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_slice_code s n out)
Proof
  strip_tac >> simp[compile_slice_code_def] >>
  match_mp_tac runtime_data_frame_bind >> conj_tac
  >- simp[runtime_data_frame_slice_out_buf]
  >> simp[pairTheory.FORALL_PROD, comp_ignore_bind_def]
QED

Theorem runtime_data_frame_slice_extcode[simp]:
  runtime_data_frame (compile_slice_extcode a s n b d)
Proof
  simp[compile_slice_extcode_def]
QED

Theorem runtime_data_frame_extract32_load[simp]:
  runtime_data_frame (compile_extract32_load l p s)
Proof
  simp[compile_extract32_load_def]
QED

Theorem runtime_data_frame_keccak256_word:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_keccak256_word v)
Proof
  simp[compile_keccak256_word_def]
QED

Theorem runtime_data_frame_keccak256_bytes[simp]:
  runtime_data_frame (compile_keccak256_bytes p)
Proof
  simp[compile_keccak256_bytes_def]
QED

Theorem runtime_data_frame_keccak256_bytesm:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_keccak256_bytesm v m)
Proof
  simp[compile_keccak256_bytesm_def]
QED

Theorem runtime_data_frame_method_id_hash:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_method_id_hash ty v)
Proof
  strip_tac >> Cases_on `ty` >> simp[compile_method_id_hash_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> simp[compile_method_id_hash_def] >>
  rename1 `BytesT sz` >> Cases_on `sz` >>
  simp[compile_method_id_hash_def, runtime_data_frame_keccak256_bytesm]
QED

Theorem runtime_data_frame_method_id_runtime:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_method_id_runtime ty v b)
Proof
  strip_tac >> Cases_on `b` >>
  simp[compile_method_id_runtime_def, runtime_data_frame_method_id_hash] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac
       >- simp[runtime_data_frame_method_id_hash] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem runtime_data_frame_sha256_word:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_sha256_word v)
Proof
  strip_tac >> simp[compile_sha256_word_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem runtime_data_frame_sha256_bytes:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_sha256_bytes v)
Proof
  strip_tac >> simp[compile_sha256_bytes_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem runtime_data_frame_sha256_bytesm:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_sha256_bytesm v m)
Proof
  strip_tac >> simp[compile_sha256_bytesm_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem runtime_data_frame_ecrecover:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_ecrecover h v r s)
Proof
  strip_tac >> simp[compile_ecrecover_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem runtime_data_frame_ecadd_points:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_ecadd_points p q)
Proof
  strip_tac >> simp[compile_ecadd_points_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem runtime_data_frame_ecmul_point:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_ecmul_point p s)
Proof
  strip_tac >> simp[compile_ecmul_point_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem runtime_data_frame_blockhash[simp]:
  runtime_data_frame (compile_blockhash n)
Proof
  simp[compile_blockhash_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem runtime_data_frame_blobhash[simp]:
  runtime_data_frame (compile_blobhash n)
Proof
  simp[compile_blobhash_def]
QED

Theorem runtime_data_frame_floor[simp]:
  runtime_data_frame (compile_floor v d)
Proof
  simp[compile_floor_def]
QED

Theorem runtime_data_frame_ceil[simp]:
  runtime_data_frame (compile_ceil v d)
Proof
  simp[compile_ceil_def]
QED

Theorem runtime_data_frame_as_wei_value_int[simp]:
  runtime_data_frame (compile_as_wei_value_int v scale s)
Proof
  Cases_on `scale = 1` >> Cases_on `s` >>
  simp[compile_as_wei_value_int_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem runtime_data_frame_as_wei_value_decimal[simp]:
  runtime_data_frame (compile_as_wei_value_decimal v scale d)
Proof
  Cases_on `scale = 1` >> simp[compile_as_wei_value_decimal_def]
QED

Theorem runtime_data_frame_uint2str:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_uint2str v digits sz)
Proof
  strip_tac >> simp[compile_uint2str_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem runtime_data_frame_check_create_result:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_check_create_result v b)
Proof
  strip_tac >> Cases_on `b` >>
  simp[compile_check_create_result_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem runtime_data_frame_create_dispatch:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_create_dispatch p n v salt b)
Proof
  strip_tac >> Cases_on `salt` >>
  simp[compile_create_dispatch_def, runtime_data_frame_check_create_result]
QED

Theorem runtime_data_frame_create_proxy_buf:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_create_proxy_buf v)
Proof
  strip_tac >> simp[compile_create_proxy_buf_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem runtime_data_frame_create_proxy:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_create_proxy v value salt b)
Proof
  simp[compile_create_proxy_def, runtime_data_frame_create_proxy_buf,
       runtime_data_frame_create_dispatch]
QED

Theorem runtime_data_frame_create_copy:
  (!n. runtime_data_frame (compile_alloc_buffer n)) /\
  (!n. runtime_data_frame (compile_alloc_dynamic n)) ==>
  runtime_data_frame (compile_create_copy v value salt b)
Proof
  strip_tac >> Cases_on `salt` >>
  simp[compile_create_copy_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- simp[] >> gen_tac >> BETA_TAC) >>
  simp[runtime_data_frame_check_create_result]
QED

Theorem runtime_data_frame_create_blueprint_check[simp]:
  runtime_data_frame (compile_create_blueprint_check v off)
Proof
  simp[compile_create_blueprint_check_def]
QED

Theorem runtime_data_frame_create_blueprint_append:
  (!n. runtime_data_frame (compile_alloc_buffer n)) /\
  (!n. runtime_data_frame (compile_alloc_dynamic n)) /\
  (!d s n. runtime_data_frame (compile_copy_memory_dynamic d s n)) ==>
  runtime_data_frame (compile_create_blueprint_append v value salt off n p len b)
Proof
  strip_tac >> Cases_on `salt` >> Cases_on `len = Lit 0w` >>
  simp[compile_create_blueprint_append_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- simp[] >> gen_tac >> BETA_TAC) >>
  simp[runtime_data_frame_check_create_result]
QED

Theorem runtime_data_frame_create_blueprint:
  (!n. runtime_data_frame (compile_alloc_buffer n)) /\
  (!n. runtime_data_frame (compile_alloc_dynamic n)) /\
  (!d s n. runtime_data_frame (compile_copy_memory_dynamic d s n)) ==>
  runtime_data_frame (compile_create_blueprint v value salt off args b)
Proof
  strip_tac >> Cases_on `args` >>
  simp[compile_create_blueprint_def, runtime_data_frame_create_blueprint_append,
       pairTheory.FORALL_PROD] >>
  PairCases_on `x` >>
  simp[compile_create_blueprint_def, runtime_data_frame_create_blueprint_append]
QED

Theorem runtime_data_frame_msg_data_to_memory:
  (!n. runtime_data_frame (compile_alloc_dynamic n)) ==>
  runtime_data_frame compile_msg_data_to_memory
Proof
  simp[compile_msg_data_to_memory_def]
QED

Theorem runtime_data_frame_raw_call_outbuf:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_raw_call_outbuf n)
Proof
  simp[compile_raw_call_outbuf_def, COND_RAND]
QED

Theorem runtime_data_frame_raw_call_finish:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_raw_call_finish to_op p len gas v ct n b out outp)
Proof
  strip_tac >> Cases_on `ct` >> Cases_on `b` >> Cases_on `n > 0` >>
  simp[compile_raw_call_finish_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem runtime_data_frame_send[simp]:
  runtime_data_frame (compile_send to_op v gas)
Proof
  simp[compile_send_def]
QED

Theorem runtime_data_frame_raw_revert[simp]:
  runtime_data_frame (compile_raw_revert p)
Proof
  simp[compile_raw_revert_def]
QED

Theorem runtime_data_frame_selfdestruct[simp]:
  runtime_data_frame (compile_selfdestruct to_op)
Proof
  simp[compile_selfdestruct_def]
QED

Theorem runtime_data_frame_lower_abi_encode:
  (!n. runtime_data_frame (compile_alloc_buffer n)) /\
  (!p s i. runtime_data_frame (compile_abi_encode_to_buf p s i)) ==>
  runtime_data_frame (lower_abi_encode tuple mid src info maxlen)
Proof
  strip_tac >> Cases_on `mid` >>
  simp[lower_abi_encode_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem runtime_data_frame_lower_abi_decode:
  (!n. runtime_data_frame (compile_alloc_buffer n)) /\
  (!d off op p n i. runtime_data_frame (compile_abi_decode_to_buf d off op p n i)) ==>
  runtime_data_frame (lower_abi_decode src info minsz maxsz outsz)
Proof
  strip_tac >> Cases_on `minsz = maxsz` >>
  simp[lower_abi_decode_def, comp_ignore_bind_def, comp_bind_assoc] >>
  rpt (match_mp_tac runtime_data_frame_bind >> conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

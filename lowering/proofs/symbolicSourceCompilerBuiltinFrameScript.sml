Theory symbolicSourceCompilerBuiltinFrame
Ancestors
  symbolicSourceCompilerFrame compileEnv builtinAbi builtinBytes builtinCreate
  builtinHashing builtinMath builtinMisc builtinSimple builtinStrings builtinSystem
Libs symbolicSourceCompilerFrameLib

open symbolicSourceCompilerFrameLib

val _ = augment_srw_ss [rewrites [symbolic_frame_bind, symbolic_frame_ignore_bind, symbolic_frame_cond]];

Theorem symbolic_frame_select[simp]:
  (!opc args. symbolic_frame R (emit_op opc args)) ==>
  symbolic_frame R (compile_select c a b)
Proof
  strip_tac >> simp[compile_select_def]
QED

Theorem symbolic_frame_assert_slice_bounds[simp]:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) ==>
  symbolic_frame R (compile_assert_slice_bounds s n l)
Proof
  strip_tac >> simp[compile_assert_slice_bounds_def] >>
  rpt (match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem symbolic_frame_slice_data:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!n. symbolic_frame R (compile_alloc_buffer n)) ==>
  symbolic_frame R (compile_slice_data l p s n out)
Proof
  strip_tac >> simp[compile_slice_data_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem symbolic_frame_slice_out_buf:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!n. symbolic_frame R (compile_alloc_buffer n)) ==>
  symbolic_frame R (compile_slice_out_buf out)
Proof
  simp[compile_slice_out_buf_def]
QED

Theorem symbolic_frame_slice_calldata:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!n. symbolic_frame R (compile_alloc_buffer n)) ==>
  symbolic_frame R (compile_slice_calldata s n out)
Proof
  strip_tac >> simp[compile_slice_calldata_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac symbolic_frame_bind >> conj_tac
    >- simp[symbolic_frame_slice_out_buf] >> gen_tac >> BETA_TAC) >>
  PairCases_on `x` >> simp[comp_ignore_bind_def]
QED

Theorem symbolic_frame_slice_code:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!n. symbolic_frame R (compile_alloc_buffer n)) ==>
  symbolic_frame R (compile_slice_code s n out)
Proof
  strip_tac >> simp[compile_slice_code_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac symbolic_frame_bind >> conj_tac
    >- simp[symbolic_frame_slice_out_buf] >> gen_tac >> BETA_TAC) >>
  PairCases_on `x` >> simp[comp_ignore_bind_def]
QED

Theorem symbolic_frame_slice_extcode:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!n. symbolic_frame R (compile_alloc_buffer n)) ==>
  symbolic_frame R (compile_slice_extcode a s n b)
Proof
  strip_tac >> simp[compile_slice_extcode_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac symbolic_frame_bind >> conj_tac
    >- simp[symbolic_frame_slice_out_buf] >> gen_tac >> BETA_TAC) >>
  PairCases_on `x` >> simp[comp_ignore_bind_def]
QED

Theorem symbolic_frame_keccak256_word:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!n. symbolic_frame R (compile_alloc_buffer n)) ==>
  symbolic_frame R (compile_keccak256_word v)
Proof
  simp[compile_keccak256_word_def]
QED

Theorem symbolic_frame_keccak256_bytes[simp]:
  (!opc args. symbolic_frame R (emit_op opc args)) ==>
  symbolic_frame R (compile_keccak256_bytes p)
Proof
  strip_tac >> simp[compile_keccak256_bytes_def]
QED

Theorem symbolic_frame_keccak256_bytesm:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!n. symbolic_frame R (compile_alloc_buffer n)) ==>
  symbolic_frame R (compile_keccak256_bytesm v m)
Proof
  simp[compile_keccak256_bytesm_def]
QED

Theorem symbolic_frame_method_id_hash:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!n. symbolic_frame R (compile_alloc_buffer n)) ==>
  symbolic_frame R (compile_method_id_hash ty v)
Proof
  strip_tac >> Cases_on `ty` >> simp[compile_method_id_hash_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> simp[compile_method_id_hash_def] >>
  rename1 `BytesT sz` >> Cases_on `sz` >>
  simp[compile_method_id_hash_def, symbolic_frame_keccak256_bytesm]
QED

Theorem symbolic_frame_method_id_runtime:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!n. symbolic_frame R (compile_alloc_buffer n)) ==>
  symbolic_frame R (compile_method_id_runtime ty v b)
Proof
  strip_tac >> Cases_on `b` >>
  simp[compile_method_id_runtime_def, symbolic_frame_method_id_hash] >>
  rpt (match_mp_tac symbolic_frame_bind >> conj_tac
       >- simp[symbolic_frame_method_id_hash] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem symbolic_frame_sha256_word:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!n. symbolic_frame R (compile_alloc_buffer n)) ==>
  symbolic_frame R (compile_sha256_word v)
Proof
  strip_tac >> simp[compile_sha256_word_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem symbolic_frame_sha256_bytes:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!n. symbolic_frame R (compile_alloc_buffer n)) ==>
  symbolic_frame R (compile_sha256_bytes v)
Proof
  strip_tac >> simp[compile_sha256_bytes_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem symbolic_frame_sha256_bytesm:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!n. symbolic_frame R (compile_alloc_buffer n)) ==>
  symbolic_frame R (compile_sha256_bytesm v m)
Proof
  strip_tac >> simp[compile_sha256_bytesm_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem symbolic_frame_ecrecover:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!n. symbolic_frame R (compile_alloc_buffer n)) ==>
  symbolic_frame R (compile_ecrecover h v r s)
Proof
  strip_tac >> simp[compile_ecrecover_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem symbolic_frame_ecadd_points:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!n. symbolic_frame R (compile_alloc_buffer n)) ==>
  symbolic_frame R (compile_ecadd_points p q)
Proof
  strip_tac >> simp[compile_ecadd_points_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem symbolic_frame_ecmul_point:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!n. symbolic_frame R (compile_alloc_buffer n)) ==>
  symbolic_frame R (compile_ecmul_point p s)
Proof
  strip_tac >> simp[compile_ecmul_point_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem symbolic_frame_blockhash:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) ==>
  symbolic_frame R (compile_blockhash n)
Proof
  strip_tac >> simp[compile_blockhash_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem symbolic_frame_as_wei_value_int:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) ==>
  symbolic_frame R (compile_as_wei_value_int v scale s)
Proof
  strip_tac >> Cases_on `scale = 1` >> Cases_on `s` >>
  simp[compile_as_wei_value_int_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem symbolic_frame_as_wei_value_decimal:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) ==>
  symbolic_frame R (compile_as_wei_value_decimal v scale d)
Proof
  strip_tac >> Cases_on `scale = 1` >> simp[compile_as_wei_value_decimal_def]
QED

Theorem symbolic_frame_uint2str:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!opc args outs. symbolic_frame R (emit_inst opc args outs)) /\
  (!s. symbolic_frame R (fresh_label s)) /\
  (!s. symbolic_frame R (new_block s)) /\
  (symbolic_frame R fresh_var) /\
  (!n. symbolic_frame R (compile_alloc_buffer n)) ==>
  symbolic_frame R (compile_uint2str v digits sz)
Proof
  strip_tac >> simp[compile_uint2str_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem symbolic_frame_check_create_result:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!opc args outs. symbolic_frame R (emit_inst opc args outs)) /\
  (!s. symbolic_frame R (fresh_label s)) /\
  (!s. symbolic_frame R (new_block s)) /\
  (!n. symbolic_frame R (compile_alloc_buffer n)) ==>
  symbolic_frame R (compile_check_create_result v b)
Proof
  strip_tac >> Cases_on `b` >>
  simp[compile_check_create_result_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem symbolic_frame_create_dispatch:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!opc args outs. symbolic_frame R (emit_inst opc args outs)) /\
  (!s. symbolic_frame R (fresh_label s)) /\
  (!s. symbolic_frame R (new_block s)) /\
  (!n. symbolic_frame R (compile_alloc_buffer n)) ==>
  symbolic_frame R (compile_create_dispatch p n v salt b)
Proof
  strip_tac >> Cases_on `salt` >>
  simp[compile_create_dispatch_def, symbolic_frame_check_create_result]
QED

Theorem symbolic_frame_create_proxy_buf:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!n. symbolic_frame R (compile_alloc_buffer n)) ==>
  symbolic_frame R (compile_create_proxy_buf v)
Proof
  strip_tac >> simp[compile_create_proxy_buf_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem symbolic_frame_create_proxy:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!opc args outs. symbolic_frame R (emit_inst opc args outs)) /\
  (!s. symbolic_frame R (fresh_label s)) /\
  (!s. symbolic_frame R (new_block s)) /\
  (!n. symbolic_frame R (compile_alloc_buffer n)) ==>
  symbolic_frame R (compile_create_proxy v value salt b)
Proof
  simp[compile_create_proxy_def, symbolic_frame_create_proxy_buf,
       symbolic_frame_create_dispatch]
QED

Theorem symbolic_frame_create_copy:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!opc args outs. symbolic_frame R (emit_inst opc args outs)) /\
  (!s. symbolic_frame R (fresh_label s)) /\
  (!s. symbolic_frame R (new_block s)) /\
  (!n. symbolic_frame R (compile_alloc_buffer n)) /\
  (!n. symbolic_frame R (compile_alloc_dynamic n)) ==>
  symbolic_frame R (compile_create_copy v value salt b)
Proof
  strip_tac >> Cases_on `salt` >>
  simp[compile_create_copy_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >> gen_tac >> BETA_TAC) >>
  simp[symbolic_frame_check_create_result]
QED

Theorem symbolic_frame_create_blueprint_check[simp]:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) ==>
  symbolic_frame R (compile_create_blueprint_check is_lit v off)
Proof
  strip_tac >> Cases_on `is_lit` >> simp[compile_create_blueprint_check_def]
QED

Theorem symbolic_frame_create_blueprint_append:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!opc args outs. symbolic_frame R (emit_inst opc args outs)) /\
  (!s. symbolic_frame R (fresh_label s)) /\
  (!s. symbolic_frame R (new_block s)) /\
  (!n. symbolic_frame R (compile_alloc_buffer n)) /\
  (!n. symbolic_frame R (compile_alloc_dynamic n)) /\
  (!d s n. symbolic_frame R (compile_copy_memory_dynamic d s n)) ==>
  symbolic_frame R (compile_create_blueprint_append v value salt off n p len b)
Proof
  strip_tac >> Cases_on `salt` >> Cases_on `len = Lit 0w` >>
  simp[compile_create_blueprint_append_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >> gen_tac >> BETA_TAC) >>
  simp[symbolic_frame_check_create_result]
QED

Theorem symbolic_frame_create_blueprint:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!opc args outs. symbolic_frame R (emit_inst opc args outs)) /\
  (!s. symbolic_frame R (fresh_label s)) /\
  (!s. symbolic_frame R (new_block s)) /\
  (!n. symbolic_frame R (compile_alloc_buffer n)) /\
  (!n. symbolic_frame R (compile_alloc_dynamic n)) /\
  (!d s n. symbolic_frame R (compile_copy_memory_dynamic d s n)) ==>
  symbolic_frame R (compile_create_blueprint is_lit v value salt off args b)
Proof
  strip_tac >> Cases_on `args` >>
  simp[compile_create_blueprint_def, symbolic_frame_create_blueprint_append,
       pairTheory.FORALL_PROD] >>
  PairCases_on `x` >>
  simp[compile_create_blueprint_def, symbolic_frame_create_blueprint_append]
QED

Theorem symbolic_frame_raw_call_finish:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!opc args outs. symbolic_frame R (emit_inst opc args outs)) /\
  (!s. symbolic_frame R (fresh_label s)) /\
  (!s. symbolic_frame R (new_block s)) /\
  (!n. symbolic_frame R (compile_alloc_buffer n)) ==>
  symbolic_frame R (compile_raw_call_finish to_op p len gas v ct n b out outp)
Proof
  strip_tac >> Cases_on `ct` >> Cases_on `b` >> Cases_on `n > 0` >>
  simp[compile_raw_call_finish_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem symbolic_frame_lower_abi_encode:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!n. symbolic_frame R (compile_alloc_buffer n)) /\
  (!p s i. symbolic_frame R (compile_abi_encode_to_buf p s i)) ==>
  symbolic_frame R (lower_abi_encode tuple mid src info maxlen)
Proof
  strip_tac >> Cases_on `mid` >>
  simp[lower_abi_encode_def, comp_ignore_bind_def] >>
  rpt (match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem symbolic_frame_lower_abi_decode:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!n. symbolic_frame R (compile_alloc_buffer n)) /\
  (!d off op p n i. symbolic_frame R (compile_abi_decode_to_buf d off op p n i)) ==>
  symbolic_frame R (lower_abi_decode src info minsz maxsz outsz)
Proof
  strip_tac >> Cases_on `minsz = maxsz` >>
  simp[lower_abi_decode_def, comp_ignore_bind_def, comp_bind_assoc] >>
  rpt (match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem symbolic_frame_zero_words[simp]:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) ==>
  !n b. symbolic_frame R (compile_zero_words b n)
Proof
  strip_tac >> Induct >> simp[compile_zero_words_def]
QED

Theorem symbolic_frame_builtin_len:
  (!c i l p. symbolic_frame R (compile_ptr_load c i l p)) ==>
  symbolic_frame R (compile_builtin_len c i p l)
Proof
  simp[compile_builtin_len_def]
QED

Theorem symbolic_frame_builtin_calldatasize:
  (!opc args. symbolic_frame R (emit_op opc args)) ==>
  symbolic_frame R compile_builtin_calldatasize
Proof
  strip_tac >> simp[compile_builtin_calldatasize_def]
QED

Theorem symbolic_frame_builtin_empty_prim:
  symbolic_frame R compile_builtin_empty_prim
Proof
  simp[compile_builtin_empty_prim_def]
QED

Theorem symbolic_frame_builtin_min:
  (!opc args. symbolic_frame R (emit_op opc args)) ==>
  symbolic_frame R (compile_builtin_min a b u)
Proof
  strip_tac >> Cases_on `u` >> simp[compile_builtin_min_def]
QED

Theorem symbolic_frame_builtin_max:
  (!opc args. symbolic_frame R (emit_op opc args)) ==>
  symbolic_frame R (compile_builtin_max a b u)
Proof
  strip_tac >> Cases_on `u` >> simp[compile_builtin_max_def]
QED

Theorem symbolic_frame_builtin_abs:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) ==>
  symbolic_frame R (compile_builtin_abs a)
Proof
  strip_tac >> simp[compile_builtin_abs_def] >>
  rpt (match_mp_tac symbolic_frame_bind >> conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem symbolic_frame_unsafe_binop[simp]:
  (!opc args. symbolic_frame R (emit_op opc args)) ==>
  symbolic_frame R (compile_unsafe_binop op x y bits s)
Proof
  strip_tac >> simp[compile_unsafe_binop_def, COND_RAND]
QED

Theorem symbolic_frame_unsafe_add:
  (!opc args. symbolic_frame R (emit_op opc args)) ==>
  symbolic_frame R (compile_unsafe_add x y bits s)
Proof
  strip_tac >> simp[compile_unsafe_add_def]
QED

Theorem symbolic_frame_unsafe_sub:
  (!opc args. symbolic_frame R (emit_op opc args)) ==>
  symbolic_frame R (compile_unsafe_sub x y bits s)
Proof
  strip_tac >> simp[compile_unsafe_sub_def]
QED

Theorem symbolic_frame_unsafe_mul:
  (!opc args. symbolic_frame R (emit_op opc args)) ==>
  symbolic_frame R (compile_unsafe_mul x y bits s)
Proof
  strip_tac >> simp[compile_unsafe_mul_def]
QED

Theorem symbolic_frame_unsafe_div:
  (!opc args. symbolic_frame R (emit_op opc args)) ==>
  symbolic_frame R (compile_unsafe_div x y bits s)
Proof
  strip_tac >> simp[compile_unsafe_div_def]
QED

Theorem symbolic_frame_pow_mod256:
  (!opc args. symbolic_frame R (emit_op opc args)) ==>
  symbolic_frame R (compile_pow_mod256 x y)
Proof
  strip_tac >> simp[compile_pow_mod256_def]
QED

Theorem symbolic_frame_addmod:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) ==>
  symbolic_frame R (compile_addmod x y z)
Proof
  strip_tac >> simp[compile_addmod_def]
QED

Theorem symbolic_frame_mulmod:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) ==>
  symbolic_frame R (compile_mulmod x y z)
Proof
  strip_tac >> simp[compile_mulmod_def]
QED

Theorem symbolic_frame_shift:
  (!opc args. symbolic_frame R (emit_op opc args)) ==>
  symbolic_frame R (compile_shift x y s)
Proof
  strip_tac >> Cases_on `s` >> simp[compile_shift_def] >> frame_tac
QED

Theorem symbolic_frame_bytestring_src:
  (!opc args. symbolic_frame R (emit_op opc args)) ==>
  symbolic_frame R (compile_bytestring_src p)
Proof
  strip_tac >> simp[compile_bytestring_src_def]
QED

Theorem symbolic_frame_extract32_load:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) ==>
  symbolic_frame R (compile_extract32_load l p s)
Proof
  strip_tac >> simp[compile_extract32_load_def]
QED

Theorem symbolic_frame_blobhash:
  (!opc args. symbolic_frame R (emit_op opc args)) ==>
  symbolic_frame R (compile_blobhash n)
Proof
  strip_tac >> simp[compile_blobhash_def]
QED

Theorem symbolic_frame_floor:
  (!opc args. symbolic_frame R (emit_op opc args)) ==>
  symbolic_frame R (compile_floor v d)
Proof
  strip_tac >> simp[compile_floor_def]
QED

Theorem symbolic_frame_ceil:
  (!opc args. symbolic_frame R (emit_op opc args)) ==>
  symbolic_frame R (compile_ceil v d)
Proof
  strip_tac >> simp[compile_ceil_def]
QED

Theorem symbolic_frame_msg_data_to_memory:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) /\
  (!n. symbolic_frame R (compile_alloc_dynamic n)) ==>
  symbolic_frame R compile_msg_data_to_memory
Proof
  simp[compile_msg_data_to_memory_def]
QED

Theorem symbolic_frame_send:
  (!opc args. symbolic_frame R (emit_op opc args)) /\
  (!opc args. symbolic_frame R (emit_void opc args)) ==>
  symbolic_frame R (compile_send to_op v gas)
Proof
  strip_tac >> simp[compile_send_def]
QED

Theorem symbolic_frame_raw_revert:
  (!opc args outs. symbolic_frame R (emit_inst opc args outs)) /\
  (!opc args. symbolic_frame R (emit_op opc args)) ==>
  symbolic_frame R (compile_raw_revert p)
Proof
  strip_tac >> simp[compile_raw_revert_def]
QED

Theorem symbolic_frame_selfdestruct:
  (!opc args. symbolic_frame R (emit_void opc args)) ==>
  symbolic_frame R (compile_selfdestruct to_op)
Proof
  strip_tac >> simp[compile_selfdestruct_def]
QED

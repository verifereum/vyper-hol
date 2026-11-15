Theory deploySymSrcFrameABI
Ancestors
  deploySymSrcBlockFrame abiEncoder compileEnv emitHelper
  builtinAbi builtinBytes builtinCreate builtinHashing builtinMath builtinMisc
  builtinSimple builtinStrings builtinSystem

val _ = augment_srw_ss [rewrites [deploy_blocks_frame_bind,
                                deploy_blocks_frame_ignore_bind]];

Theorem deploy_blocks_frame_abi_int_clamp[simp]:
  deploy_blocks_frame (compile_abi_int_clamp v bits signed)
Proof Cases_on `signed` >> simp[compile_abi_int_clamp_def]
QED

Theorem deploy_blocks_frame_abi_bytes_clamp[simp]:
  deploy_blocks_frame (compile_abi_bytes_clamp v n)
Proof simp[compile_abi_bytes_clamp_def]
QED

Theorem deploy_blocks_frame_abi_clamp_basetype[simp]:
  deploy_blocks_frame (compile_abi_clamp_basetype v c)
Proof Cases_on `c` >> simp[compile_abi_clamp_basetype_def]
QED

Theorem deploy_blocks_frame_abi_zero_pad[simp]:
  deploy_blocks_frame (compile_abi_zero_pad p n c)
Proof simp[compile_abi_zero_pad_def]
QED

Theorem deploy_blocks_frame_get_element_ptr[simp]:
  deploy_blocks_frame (compile_get_element_ptr p n)
Proof simp[compile_get_element_ptr_def]
QED

Theorem deploy_blocks_frame_get_dynarray_elem_ptr[simp]:
  deploy_blocks_frame (compile_get_dynarray_elem_ptr p i n)
Proof simp[compile_get_dynarray_elem_ptr_def]
QED

Theorem deploy_blocks_frame_abi_encode_static[simp]:
  deploy_blocks_frame (compile_abi_encode_static dst src)
Proof simp[compile_abi_encode_static_def]
QED

Theorem deploy_blocks_frame_abi_decode_static:
  (!v. deploy_blocks_frame (clamp v)) ==>
  deploy_blocks_frame (compile_abi_decode_static src dst opc clamp)
Proof simp[compile_abi_decode_static_def]
QED

Theorem deploy_blocks_frame_abi_encode_static_info[simp]:
  deploy_blocks_frame (compile_abi_encode_static_info dst src info)
Proof Cases_on `info` >> simp[compile_abi_encode_static_info_def]
QED

Theorem deploy_blocks_frame_abi_encode_dyn_static_loop[simp]:
  deploy_blocks_frame
    (compile_abi_encode_dyn_static_loop dst src info asz msz len)
Proof
  simp[compile_abi_encode_dyn_static_loop_def, comp_ignore_bind_def] >>
  rpt (irule deploy_blocks_frame_bind >>
       reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem deploy_blocks_frame_abi_encode_mutual:
  (!dst childp ci dyn off dp.
    deploy_blocks_frame (compile_abi_encode_child dst childp ci dyn off dp)) /\
  (!dst src info.
    deploy_blocks_frame (compile_abi_encode_to_buf dst src info)) /\
  (!dst src elems so ho dp.
    deploy_blocks_frame
      (compile_abi_encode_complex_elems dst src elems so ho dp)) /\
  (!dst src ei asz msz len.
    deploy_blocks_frame (compile_abi_encode_dyn_loop dst src ei asz msz len))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >> rpt strip_tac >>
  simp[Once compile_abi_encode_child_def, comp_ignore_bind_def] >>
  rpt (irule deploy_blocks_frame_bind >>
       reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >>
  rpt IF_CASES_TAC >>
  gvs[arithmeticTheory.ADD_COMM] >>
  rpt (irule deploy_blocks_frame_bind >>
       reverse conj_tac >- gvs[comp_ignore_bind_def] >>
       gen_tac >> BETA_TAC) >> gvs[comp_ignore_bind_def]
QED

Theorem deploy_blocks_frame_abi_encode_child[simp]:
  deploy_blocks_frame (compile_abi_encode_child dst childp ci dyn off dp)
Proof metis_tac[deploy_blocks_frame_abi_encode_mutual]
QED

Theorem deploy_blocks_frame_abi_encode_to_buf[simp]:
  deploy_blocks_frame (compile_abi_encode_to_buf dst src info)
Proof metis_tac[deploy_blocks_frame_abi_encode_mutual]
QED

Theorem deploy_blocks_frame_abi_encode_complex_elems[simp]:
  deploy_blocks_frame (compile_abi_encode_complex_elems dst src elems so ho dp)
Proof metis_tac[deploy_blocks_frame_abi_encode_mutual]
QED

Theorem deploy_blocks_frame_abi_encode_dyn_loop[simp]:
  deploy_blocks_frame (compile_abi_encode_dyn_loop dst src ei asz msz len)
Proof metis_tac[deploy_blocks_frame_abi_encode_mutual]
QED

Theorem deploy_blocks_frame_abi_dec_addr[simp]:
  deploy_blocks_frame (compile_abi_dec_addr bop pos)
Proof simp[compile_abi_dec_addr_def] >> IF_CASES_TAC >> simp[]
QED

Theorem deploy_blocks_frame_abi_decode_range_check[simp]:
  deploy_blocks_frame (compile_abi_decode_range_check start endop hi)
Proof
  simp[compile_abi_decode_range_check_def] >>
  rpt (irule deploy_blocks_frame_bind >>
       reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem deploy_blocks_frame_getelemptr_abi[simp]:
  deploy_blocks_frame (compile_getelemptr_abi src dyn off opc bop hi)
Proof
  simp[compile_getelemptr_abi_def, comp_ignore_bind_def] >>
  rpt (irule deploy_blocks_frame_bind >>
       reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >>
  rpt IF_CASES_TAC >> simp[comp_ignore_bind_def] >>
  rpt (irule deploy_blocks_frame_bind >>
       reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >>
  rpt IF_CASES_TAC >> simp[]
QED

Theorem deploy_blocks_frame_abi_decode_dyn_elem_ptr[simp]:
  deploy_blocks_frame (compile_abi_decode_dyn_elem_ptr opc bop elem src hi sz)
Proof
  simp[compile_abi_decode_dyn_elem_ptr_def, comp_ignore_bind_def] >>
  rpt (irule deploy_blocks_frame_bind >>
       reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >>
  rpt IF_CASES_TAC >> simp[comp_ignore_bind_def] >>
  rpt (irule deploy_blocks_frame_bind >>
       reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >>
  rpt IF_CASES_TAC >> simp[]
QED

Theorem deploy_blocks_frame_abi_copy_case[simp]:
  deploy_blocks_frame
    (case opc of CALLDATALOAD => emit_void CALLDATACOPY args
       | DLOAD => emit_void DLOADBYTES args | _ => emit_void MCOPY args)
Proof Cases_on `opc` >> simp[]
QED

Theorem deploy_blocks_frame_abi_decode_mutual:
  (!dst src opc bop hi info.
    deploy_blocks_frame (compile_abi_decode_to_buf dst src opc bop hi info)) /\
  (!dst src opc bop hi elems ao vo.
    deploy_blocks_frame
      (compile_abi_decode_complex_elems dst src opc bop hi elems ao vo)) /\
  (!dst src opc bop hi ei asz msz ip cnt.
    deploy_blocks_frame
      (compile_abi_decode_dyn_loop dst src opc bop hi ei asz msz ip cnt))
Proof
  ho_match_mp_tac compile_abi_decode_to_buf_ind >> rpt strip_tac >>
  simp[Once compile_abi_decode_to_buf_def, comp_ignore_bind_def,
       deploy_blocks_frame_abi_decode_static] >>
  rpt (irule deploy_blocks_frame_bind >>
       reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >>
  rpt IF_CASES_TAC >>
  rpt (FIRST
    [irule deploy_blocks_frame_bind >>
       reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC,
     CHANGED_TAC (pure_asm_rewrite_tac [COND_CLAUSES, comp_ignore_bind_def]),
     IF_CASES_TAC]) >> gvs[arithmeticTheory.ADD_COMM]
QED

Theorem deploy_blocks_frame_abi_decode_to_buf[simp]:
  deploy_blocks_frame (compile_abi_decode_to_buf dst src opc bop hi info)
Proof metis_tac[deploy_blocks_frame_abi_decode_mutual]
QED

Theorem deploy_blocks_frame_abi_decode_complex_elems[simp]:
  deploy_blocks_frame (compile_abi_decode_complex_elems dst src opc bop hi elems ao vo)
Proof metis_tac[deploy_blocks_frame_abi_decode_mutual]
QED

Theorem deploy_blocks_frame_abi_decode_dyn_loop[simp]:
  deploy_blocks_frame (compile_abi_decode_dyn_loop dst src opc bop hi ei asz msz ip cnt)
Proof metis_tac[deploy_blocks_frame_abi_decode_mutual]
QED

Theorem deploy_blocks_frame_select[simp]:
  deploy_blocks_frame (compile_select c a b)
Proof simp[compile_select_def]
QED

Theorem deploy_blocks_frame_zero_words[simp]:
  !n b. deploy_blocks_frame (compile_zero_words b n)
Proof Induct >> simp[compile_zero_words_def]
QED

Theorem deploy_blocks_frame_builtin_len:
  (!c i l p. deploy_blocks_frame (compile_ptr_load c i l p)) ==>
  deploy_blocks_frame (compile_builtin_len c i p l)
Proof simp[compile_builtin_len_def]
QED

Theorem deploy_blocks_frame_builtin_calldatasize[simp]:
  deploy_blocks_frame compile_builtin_calldatasize
Proof simp[compile_builtin_calldatasize_def]
QED

Theorem deploy_blocks_frame_builtin_empty_prim[simp]:
  deploy_blocks_frame compile_builtin_empty_prim
Proof simp[compile_builtin_empty_prim_def]
QED

Theorem deploy_blocks_frame_builtin_empty_complex[simp]:
  deploy_blocks_frame (compile_builtin_empty_complex n b)
Proof simp[compile_builtin_empty_complex_def, COND_RAND]
QED

Theorem deploy_blocks_frame_builtin_min[simp]:
  deploy_blocks_frame (compile_builtin_min a b u)
Proof Cases_on `u` >> simp[compile_builtin_min_def]
QED

Theorem deploy_blocks_frame_builtin_max[simp]:
  deploy_blocks_frame (compile_builtin_max a b u)
Proof Cases_on `u` >> simp[compile_builtin_max_def]
QED

Theorem deploy_blocks_frame_builtin_abs[simp]:
  deploy_blocks_frame (compile_builtin_abs a)
Proof
  simp[compile_builtin_abs_def, comp_ignore_bind_def] >>
  rpt (irule deploy_blocks_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem deploy_blocks_frame_unsafe_binop[simp]:
  deploy_blocks_frame (compile_unsafe_binop op x y bits s)
Proof simp[compile_unsafe_binop_def, COND_RAND]
QED

Theorem deploy_blocks_frame_unsafe_add[simp]:
  deploy_blocks_frame (compile_unsafe_add x y bits s)
Proof simp[compile_unsafe_add_def]
QED

Theorem deploy_blocks_frame_unsafe_sub[simp]:
  deploy_blocks_frame (compile_unsafe_sub x y bits s)
Proof simp[compile_unsafe_sub_def]
QED

Theorem deploy_blocks_frame_unsafe_mul[simp]:
  deploy_blocks_frame (compile_unsafe_mul x y bits s)
Proof simp[compile_unsafe_mul_def]
QED

Theorem deploy_blocks_frame_unsafe_div[simp]:
  deploy_blocks_frame (compile_unsafe_div x y bits s)
Proof simp[compile_unsafe_div_def]
QED

Theorem deploy_blocks_frame_pow_mod256[simp]:
  deploy_blocks_frame (compile_pow_mod256 x y)
Proof simp[compile_pow_mod256_def]
QED

Theorem deploy_blocks_frame_addmod[simp]:
  deploy_blocks_frame (compile_addmod x y z)
Proof simp[compile_addmod_def]
QED

Theorem deploy_blocks_frame_mulmod[simp]:
  deploy_blocks_frame (compile_mulmod x y z)
Proof simp[compile_mulmod_def]
QED

Theorem deploy_blocks_frame_shift[simp]:
  deploy_blocks_frame (compile_shift x y s)
Proof Cases_on `s` >> simp[compile_shift_def]
QED

Theorem deploy_blocks_frame_assert_slice_bounds[simp]:
  deploy_blocks_frame (compile_assert_slice_bounds s n l)
Proof
  simp[compile_assert_slice_bounds_def] >>
  rpt (irule deploy_blocks_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem deploy_blocks_frame_bytestring_src[simp]:
  deploy_blocks_frame (compile_bytestring_src p)
Proof simp[compile_bytestring_src_def]
QED

Theorem deploy_blocks_frame_slice_data[simp]:
  deploy_blocks_frame (compile_slice_data l p s n out)
Proof
  simp[compile_slice_data_def, comp_ignore_bind_def] >>
  rpt (irule deploy_blocks_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem deploy_blocks_frame_slice_out_buf[simp]:
  deploy_blocks_frame (compile_slice_out_buf out)
Proof simp[compile_slice_out_buf_def]
QED

Theorem deploy_blocks_frame_slice_calldata[simp]:
  deploy_blocks_frame (compile_slice_calldata s n out)
Proof
  simp[compile_slice_calldata_def, comp_ignore_bind_def] >>
  rpt (irule deploy_blocks_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >>
  PairCases_on `x` >> simp[comp_ignore_bind_def]
QED

Theorem deploy_blocks_frame_slice_code[simp]:
  deploy_blocks_frame (compile_slice_code s n out)
Proof
  simp[compile_slice_code_def, comp_ignore_bind_def] >>
  rpt (irule deploy_blocks_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >>
  PairCases_on `x` >> simp[comp_ignore_bind_def]
QED

Theorem deploy_blocks_frame_slice_extcode[simp]:
  deploy_blocks_frame (compile_slice_extcode a s n b)
Proof
  simp[compile_slice_extcode_def, comp_ignore_bind_def] >>
  rpt (irule deploy_blocks_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >>
  PairCases_on `x` >> simp[comp_ignore_bind_def]
QED

Theorem deploy_blocks_frame_extract32_load[simp]:
  deploy_blocks_frame (compile_extract32_load l p s)
Proof simp[compile_extract32_load_def]
QED

Theorem deploy_blocks_frame_keccak256_word[simp]:
  deploy_blocks_frame (compile_keccak256_word v)
Proof simp[compile_keccak256_word_def]
QED

Theorem deploy_blocks_frame_keccak256_bytes[simp]:
  deploy_blocks_frame (compile_keccak256_bytes p)
Proof simp[compile_keccak256_bytes_def]
QED

Theorem deploy_blocks_frame_keccak256_bytesm[simp]:
  deploy_blocks_frame (compile_keccak256_bytesm v m)
Proof simp[compile_keccak256_bytesm_def]
QED

Theorem deploy_blocks_frame_method_id_hash[simp]:
  deploy_blocks_frame (compile_method_id_hash ty v)
Proof
  Cases_on `ty` >> simp[compile_method_id_hash_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> simp[compile_method_id_hash_def] >>
  rename1 `BytesT sz` >> Cases_on `sz` >> simp[compile_method_id_hash_def]
QED

Theorem deploy_blocks_frame_method_id_runtime[simp]:
  deploy_blocks_frame (compile_method_id_runtime ty v b)
Proof
  Cases_on `b` >> simp[compile_method_id_runtime_def] >>
  rpt (irule deploy_blocks_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem deploy_blocks_frame_sha256_word[simp]:
  deploy_blocks_frame (compile_sha256_word v)
Proof
  simp[compile_sha256_word_def, comp_ignore_bind_def] >>
  rpt (irule deploy_blocks_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem deploy_blocks_frame_sha256_bytes[simp]:
  deploy_blocks_frame (compile_sha256_bytes v)
Proof
  simp[compile_sha256_bytes_def, comp_ignore_bind_def] >>
  rpt (irule deploy_blocks_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem deploy_blocks_frame_sha256_bytesm[simp]:
  deploy_blocks_frame (compile_sha256_bytesm v m)
Proof
  simp[compile_sha256_bytesm_def, comp_ignore_bind_def] >>
  rpt (irule deploy_blocks_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem deploy_blocks_frame_ecrecover[simp]:
  deploy_blocks_frame (compile_ecrecover h v r s)
Proof
  simp[compile_ecrecover_def, comp_ignore_bind_def] >>
  rpt (irule deploy_blocks_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem deploy_blocks_frame_ecadd_points[simp]:
  deploy_blocks_frame (compile_ecadd_points p q)
Proof
  simp[compile_ecadd_points_def, comp_ignore_bind_def] >>
  rpt (irule deploy_blocks_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem deploy_blocks_frame_ecmul_point[simp]:
  deploy_blocks_frame (compile_ecmul_point p s)
Proof
  simp[compile_ecmul_point_def, comp_ignore_bind_def] >>
  rpt (irule deploy_blocks_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem deploy_blocks_frame_blockhash[simp]:
  deploy_blocks_frame (compile_blockhash n)
Proof
  simp[compile_blockhash_def, comp_ignore_bind_def] >>
  rpt (irule deploy_blocks_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem deploy_blocks_frame_blobhash[simp]:
  deploy_blocks_frame (compile_blobhash n)
Proof simp[compile_blobhash_def]
QED

Theorem deploy_blocks_frame_floor[simp]:
  deploy_blocks_frame (compile_floor v d)
Proof simp[compile_floor_def]
QED

Theorem deploy_blocks_frame_ceil[simp]:
  deploy_blocks_frame (compile_ceil v d)
Proof simp[compile_ceil_def]
QED

Theorem deploy_blocks_frame_as_wei_value_int[simp]:
  deploy_blocks_frame (compile_as_wei_value_int v scale s)
Proof
  Cases_on `scale = 1` >> Cases_on `s` >>
  simp[compile_as_wei_value_int_def, comp_ignore_bind_def] >>
  rpt (irule deploy_blocks_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem deploy_blocks_frame_as_wei_value_decimal[simp]:
  deploy_blocks_frame (compile_as_wei_value_decimal v scale d)
Proof Cases_on `scale = 1` >> simp[compile_as_wei_value_decimal_def]
QED

Theorem deploy_blocks_frame_uint2str[simp]:
  deploy_blocks_frame (compile_uint2str v digits sz)
Proof
  simp[compile_uint2str_def, comp_ignore_bind_def] >>
  rpt (irule deploy_blocks_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem deploy_blocks_frame_check_create_result[simp]:
  deploy_blocks_frame (compile_check_create_result v b)
Proof
  Cases_on `b` >> simp[compile_check_create_result_def, comp_ignore_bind_def] >>
  rpt (irule deploy_blocks_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem deploy_blocks_frame_create_dispatch[simp]:
  deploy_blocks_frame (compile_create_dispatch p n v salt b)
Proof Cases_on `salt` >> simp[compile_create_dispatch_def]
QED

Theorem deploy_blocks_frame_create_proxy_buf[simp]:
  deploy_blocks_frame (compile_create_proxy_buf v)
Proof
  simp[compile_create_proxy_buf_def, comp_ignore_bind_def] >>
  rpt (irule deploy_blocks_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem deploy_blocks_frame_create_proxy[simp]:
  deploy_blocks_frame (compile_create_proxy v value salt b)
Proof simp[compile_create_proxy_def]
QED

Theorem deploy_blocks_frame_create_copy:
  (!n. deploy_blocks_frame (compile_alloc_dynamic n)) ==>
  deploy_blocks_frame (compile_create_copy v value salt b)
Proof
  strip_tac >> Cases_on `salt` >>
  simp[compile_create_copy_def, comp_ignore_bind_def] >>
  rpt (irule deploy_blocks_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem deploy_blocks_frame_create_blueprint_check[simp]:
  deploy_blocks_frame (compile_create_blueprint_check v off)
Proof simp[compile_create_blueprint_check_def]
QED

Theorem deploy_blocks_frame_create_blueprint_append:
  (!n. deploy_blocks_frame (compile_alloc_dynamic n)) /\
  (!d s n. deploy_blocks_frame (compile_copy_memory_dynamic d s n)) ==>
  deploy_blocks_frame (compile_create_blueprint_append v value salt off n p len b)
Proof
  strip_tac >> Cases_on `salt` >> Cases_on `len = Lit 0w` >>
  simp[compile_create_blueprint_append_def, comp_ignore_bind_def] >>
  rpt (irule deploy_blocks_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem deploy_blocks_frame_create_blueprint:
  (!n. deploy_blocks_frame (compile_alloc_dynamic n)) /\
  (!d s n. deploy_blocks_frame (compile_copy_memory_dynamic d s n)) ==>
  deploy_blocks_frame (compile_create_blueprint v value salt off args b)
Proof
  strip_tac >> Cases_on `args` >>
  simp[compile_create_blueprint_def, deploy_blocks_frame_create_blueprint_append,
       pairTheory.FORALL_PROD] >>
  PairCases_on `x` >>
  simp[compile_create_blueprint_def, deploy_blocks_frame_create_blueprint_append]
QED

Theorem deploy_blocks_frame_msg_data_to_memory:
  (!n. deploy_blocks_frame (compile_alloc_dynamic n)) ==>
  deploy_blocks_frame compile_msg_data_to_memory
Proof simp[compile_msg_data_to_memory_def]
QED

Theorem deploy_blocks_frame_raw_call_outbuf[simp]:
  deploy_blocks_frame (compile_raw_call_outbuf n)
Proof simp[compile_raw_call_outbuf_def, COND_RAND]
QED

Theorem deploy_blocks_frame_raw_call_finish[simp]:
  deploy_blocks_frame (compile_raw_call_finish to_op p len gas v ct n b out outp)
Proof
  Cases_on `ct` >> Cases_on `b` >> Cases_on `n > 0` >>
  simp[compile_raw_call_finish_def, comp_ignore_bind_def] >>
  rpt (irule deploy_blocks_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem deploy_blocks_frame_send[simp]:
  deploy_blocks_frame (compile_send to_op v gas)
Proof simp[compile_send_def]
QED

Theorem deploy_blocks_frame_raw_revert[simp]:
  deploy_blocks_frame (compile_raw_revert p)
Proof simp[compile_raw_revert_def]
QED

Theorem deploy_blocks_frame_selfdestruct[simp]:
  deploy_blocks_frame (compile_selfdestruct to_op)
Proof simp[compile_selfdestruct_def]
QED

Theorem deploy_blocks_frame_lower_abi_encode[simp]:
  deploy_blocks_frame (lower_abi_encode tuple mid src info maxlen)
Proof
  Cases_on `mid` >> simp[lower_abi_encode_def, comp_ignore_bind_def] >>
  rpt (irule deploy_blocks_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

Theorem deploy_blocks_frame_lower_abi_decode[simp]:
  deploy_blocks_frame (lower_abi_decode src info minsz maxsz outsz)
Proof
  Cases_on `minsz = maxsz` >>
  simp[lower_abi_decode_def, comp_ignore_bind_def, comp_bind_assoc] >>
  rpt (irule deploy_blocks_frame_bind >> reverse conj_tac >- simp[] >> gen_tac >> BETA_TAC) >> simp[]
QED

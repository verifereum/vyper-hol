Theory deploySymSrcFrameABI
Ancestors
  symbolicSourceCompilerBuiltinFrame
  symbolicSourceCompilerAbiFrame
  deploySymSrcBlockFrame symbolicSourceCompilerFrame abiEncoder compileEnv emitHelper
  builtinAbi builtinBytes builtinCreate builtinHashing builtinMath builtinMisc
  builtinSimple builtinStrings builtinSystem

val _ = augment_srw_ss [rewrites [deploy_blocks_frame_bind,
                                deploy_blocks_frame_ignore_bind]];

fun specialize_frame theorem =
  REWRITE_RULE [symbolic_frame_deploy]
    (Q.ISPEC `\blocks (s:compile_state) t. t = s with cs_blocks := s.cs_blocks ++ blocks`
      (Q.GEN `R` theorem))

fun apply_symbolic_frame theorem = match_mp_tac (specialize_frame theorem)

Theorem deploy_blocks_frame_abi_int_clamp[simp]:
  deploy_blocks_frame (compile_abi_int_clamp v bits signed)
Proof
  apply_symbolic_frame symbolic_frame_abi_int_clamp >> simp[]
QED

Theorem deploy_blocks_frame_abi_bytes_clamp[simp]:
  deploy_blocks_frame (compile_abi_bytes_clamp v n)
Proof
  apply_symbolic_frame symbolic_frame_abi_bytes_clamp >> simp[]
QED

Theorem deploy_blocks_frame_abi_clamp_basetype[simp]:
  deploy_blocks_frame (compile_abi_clamp_basetype v c)
Proof
  apply_symbolic_frame symbolic_frame_abi_clamp_basetype >> simp[]
QED

Theorem deploy_blocks_frame_abi_zero_pad[simp]:
  deploy_blocks_frame (compile_abi_zero_pad p n c)
Proof
  apply_symbolic_frame symbolic_frame_abi_zero_pad >> simp[]
QED

Theorem deploy_blocks_frame_get_element_ptr[simp]:
  deploy_blocks_frame (compile_get_element_ptr p n)
Proof
  apply_symbolic_frame symbolic_frame_get_element_ptr >> simp[]
QED

Theorem deploy_blocks_frame_get_dynarray_elem_ptr[simp]:
  deploy_blocks_frame (compile_get_dynarray_elem_ptr p i n)
Proof
  apply_symbolic_frame symbolic_frame_get_dynarray_elem_ptr >> simp[]
QED

Theorem deploy_blocks_frame_abi_encode_static[simp]:
  deploy_blocks_frame (compile_abi_encode_static dst src)
Proof
  apply_symbolic_frame symbolic_frame_abi_encode_static >> simp[]
QED

Theorem deploy_blocks_frame_abi_decode_static:
  (!v. deploy_blocks_frame (clamp v)) ==>
  deploy_blocks_frame (compile_abi_decode_static src dst opc clamp)
Proof
  strip_tac >>
  apply_symbolic_frame symbolic_frame_abi_decode_static >> simp[]
QED

Theorem deploy_blocks_frame_abi_encode_static_info[simp]:
  deploy_blocks_frame (compile_abi_encode_static_info dst src info)
Proof
  apply_symbolic_frame symbolic_frame_abi_encode_static_info >> simp[]
QED

Theorem deploy_blocks_frame_abi_encode_dyn_static_loop[simp]:
  deploy_blocks_frame
    (compile_abi_encode_dyn_static_loop dst src info asz msz len)
Proof
  apply_symbolic_frame symbolic_frame_abi_encode_dyn_static_loop >> simp[]
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
  match_mp_tac (REWRITE_RULE [symbolic_frame_deploy]
    (Q.ISPEC `\blocks (s:compile_state) t. t = s with cs_blocks := s.cs_blocks ++ blocks`
      (Q.GEN `R` symbolic_frame_abi_encode))) >>
  simp[deploy_blocks_frame_abi_encode_dyn_static_loop]
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
Proof
  apply_symbolic_frame symbolic_frame_abi_dec_addr >> simp[]
QED

Theorem deploy_blocks_frame_abi_decode_range_check[simp]:
  deploy_blocks_frame (compile_abi_decode_range_check start endop hi)
Proof
  apply_symbolic_frame symbolic_frame_abi_decode_range_check >> simp[]
QED

Theorem deploy_blocks_frame_getelemptr_abi[simp]:
  deploy_blocks_frame (compile_getelemptr_abi src dyn off opc bop hi)
Proof
  apply_symbolic_frame symbolic_frame_getelemptr_abi >> simp[]
QED

Theorem deploy_blocks_frame_abi_decode_dyn_elem_ptr[simp]:
  deploy_blocks_frame (compile_abi_decode_dyn_elem_ptr opc bop elem src hi sz)
Proof
  apply_symbolic_frame symbolic_frame_abi_decode_dyn_elem_ptr >> simp[]
QED

Theorem deploy_blocks_frame_abi_copy_case[simp]:
  deploy_blocks_frame
    (case opc of CALLDATALOAD => emit_void CALLDATACOPY args
       | DLOAD => emit_void DLOADBYTES args | _ => emit_void MCOPY args)
Proof
  apply_symbolic_frame symbolic_frame_abi_copy_case >> simp[]
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
  match_mp_tac (REWRITE_RULE [symbolic_frame_deploy]
    (Q.ISPEC `\blocks (s:compile_state) t. t = s with cs_blocks := s.cs_blocks ++ blocks`
      (Q.GEN `R` symbolic_frame_abi_decode))) >>
  simp[deploy_blocks_frame_abi_decode_static]
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
Proof
  apply_symbolic_frame symbolic_frame_select >> simp[]
QED

Theorem deploy_blocks_frame_zero_words[simp]:
  !n b. deploy_blocks_frame (compile_zero_words b n)
Proof
  apply_symbolic_frame symbolic_frame_zero_words >> simp[]
QED

Theorem deploy_blocks_frame_builtin_len:
  (!c i l p. deploy_blocks_frame (compile_ptr_load c i l p)) ==>
  deploy_blocks_frame (compile_builtin_len c i p l)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_builtin_len >> simp[]
QED

Theorem deploy_blocks_frame_builtin_calldatasize[simp]:
  deploy_blocks_frame compile_builtin_calldatasize
Proof
  apply_symbolic_frame symbolic_frame_builtin_calldatasize >> simp[]
QED

Theorem deploy_blocks_frame_builtin_empty_prim[simp]:
  deploy_blocks_frame compile_builtin_empty_prim
Proof
  MATCH_ACCEPT_TAC (specialize_frame symbolic_frame_builtin_empty_prim)
QED

Theorem deploy_blocks_frame_builtin_empty_complex[simp]:
  deploy_blocks_frame (compile_builtin_empty_complex n b)
Proof simp[compile_builtin_empty_complex_def, COND_RAND]
QED

Theorem deploy_blocks_frame_builtin_min[simp]:
  deploy_blocks_frame (compile_builtin_min a b u)
Proof
  apply_symbolic_frame symbolic_frame_builtin_min >> simp[]
QED

Theorem deploy_blocks_frame_builtin_max[simp]:
  deploy_blocks_frame (compile_builtin_max a b u)
Proof
  apply_symbolic_frame symbolic_frame_builtin_max >> simp[]
QED

Theorem deploy_blocks_frame_builtin_abs[simp]:
  deploy_blocks_frame (compile_builtin_abs a)
Proof
  apply_symbolic_frame symbolic_frame_builtin_abs >> simp[]
QED

Theorem deploy_blocks_frame_unsafe_binop[simp]:
  deploy_blocks_frame (compile_unsafe_binop op x y bits s)
Proof
  apply_symbolic_frame symbolic_frame_unsafe_binop >> simp[]
QED

Theorem deploy_blocks_frame_unsafe_add[simp]:
  deploy_blocks_frame (compile_unsafe_add x y bits s)
Proof
  apply_symbolic_frame symbolic_frame_unsafe_add >> simp[]
QED

Theorem deploy_blocks_frame_unsafe_sub[simp]:
  deploy_blocks_frame (compile_unsafe_sub x y bits s)
Proof
  apply_symbolic_frame symbolic_frame_unsafe_sub >> simp[]
QED

Theorem deploy_blocks_frame_unsafe_mul[simp]:
  deploy_blocks_frame (compile_unsafe_mul x y bits s)
Proof
  apply_symbolic_frame symbolic_frame_unsafe_mul >> simp[]
QED

Theorem deploy_blocks_frame_unsafe_div[simp]:
  deploy_blocks_frame (compile_unsafe_div x y bits s)
Proof
  apply_symbolic_frame symbolic_frame_unsafe_div >> simp[]
QED

Theorem deploy_blocks_frame_pow_mod256[simp]:
  deploy_blocks_frame (compile_pow_mod256 x y)
Proof
  apply_symbolic_frame symbolic_frame_pow_mod256 >> simp[]
QED

Theorem deploy_blocks_frame_addmod[simp]:
  deploy_blocks_frame (compile_addmod x y z)
Proof
  apply_symbolic_frame symbolic_frame_addmod >> simp[]
QED

Theorem deploy_blocks_frame_mulmod[simp]:
  deploy_blocks_frame (compile_mulmod x y z)
Proof
  apply_symbolic_frame symbolic_frame_mulmod >> simp[]
QED

Theorem deploy_blocks_frame_shift[simp]:
  deploy_blocks_frame (compile_shift x y s)
Proof
  apply_symbolic_frame symbolic_frame_shift >> simp[]
QED

Theorem deploy_blocks_frame_assert_slice_bounds[simp]:
  deploy_blocks_frame (compile_assert_slice_bounds s n l)
Proof
  apply_symbolic_frame symbolic_frame_assert_slice_bounds >> simp[]
QED

Theorem deploy_blocks_frame_bytestring_src[simp]:
  deploy_blocks_frame (compile_bytestring_src p)
Proof
  apply_symbolic_frame symbolic_frame_bytestring_src >> simp[]
QED

Theorem deploy_blocks_frame_slice_data[simp]:
  deploy_blocks_frame (compile_slice_data l p s n out)
Proof
  apply_symbolic_frame symbolic_frame_slice_data >> simp[]
QED

Theorem deploy_blocks_frame_slice_out_buf[simp]:
  deploy_blocks_frame (compile_slice_out_buf out)
Proof
  apply_symbolic_frame symbolic_frame_slice_out_buf >> simp[]
QED

Theorem deploy_blocks_frame_slice_calldata[simp]:
  deploy_blocks_frame (compile_slice_calldata s n out)
Proof
  apply_symbolic_frame symbolic_frame_slice_calldata >> simp[]
QED

Theorem deploy_blocks_frame_slice_code[simp]:
  deploy_blocks_frame (compile_slice_code s n out)
Proof
  apply_symbolic_frame symbolic_frame_slice_code >> simp[]
QED

Theorem deploy_blocks_frame_slice_extcode[simp]:
  deploy_blocks_frame (compile_slice_extcode a s n b)
Proof
  apply_symbolic_frame symbolic_frame_slice_extcode >> simp[]
QED

Theorem deploy_blocks_frame_extract32_load[simp]:
  deploy_blocks_frame (compile_extract32_load l p s)
Proof
  apply_symbolic_frame symbolic_frame_extract32_load >> simp[]
QED

Theorem deploy_blocks_frame_keccak256_word[simp]:
  deploy_blocks_frame (compile_keccak256_word v)
Proof
  apply_symbolic_frame symbolic_frame_keccak256_word >> simp[]
QED

Theorem deploy_blocks_frame_keccak256_bytes[simp]:
  deploy_blocks_frame (compile_keccak256_bytes p)
Proof
  apply_symbolic_frame symbolic_frame_keccak256_bytes >> simp[]
QED

Theorem deploy_blocks_frame_keccak256_bytesm[simp]:
  deploy_blocks_frame (compile_keccak256_bytesm v m)
Proof
  apply_symbolic_frame symbolic_frame_keccak256_bytesm >> simp[]
QED

Theorem deploy_blocks_frame_method_id_hash[simp]:
  deploy_blocks_frame (compile_method_id_hash ty v)
Proof
  apply_symbolic_frame symbolic_frame_method_id_hash >> simp[]
QED

Theorem deploy_blocks_frame_method_id_runtime[simp]:
  deploy_blocks_frame (compile_method_id_runtime ty v b)
Proof
  apply_symbolic_frame symbolic_frame_method_id_runtime >> simp[]
QED

Theorem deploy_blocks_frame_sha256_word[simp]:
  deploy_blocks_frame (compile_sha256_word v)
Proof
  apply_symbolic_frame symbolic_frame_sha256_word >> simp[]
QED

Theorem deploy_blocks_frame_sha256_bytes[simp]:
  deploy_blocks_frame (compile_sha256_bytes v)
Proof
  apply_symbolic_frame symbolic_frame_sha256_bytes >> simp[]
QED

Theorem deploy_blocks_frame_sha256_bytesm[simp]:
  deploy_blocks_frame (compile_sha256_bytesm v m)
Proof
  apply_symbolic_frame symbolic_frame_sha256_bytesm >> simp[]
QED

Theorem deploy_blocks_frame_ecrecover[simp]:
  deploy_blocks_frame (compile_ecrecover h v r s)
Proof
  apply_symbolic_frame symbolic_frame_ecrecover >> simp[]
QED

Theorem deploy_blocks_frame_ecadd_points[simp]:
  deploy_blocks_frame (compile_ecadd_points p q)
Proof
  apply_symbolic_frame symbolic_frame_ecadd_points >> simp[]
QED

Theorem deploy_blocks_frame_ecmul_point[simp]:
  deploy_blocks_frame (compile_ecmul_point p s)
Proof
  apply_symbolic_frame symbolic_frame_ecmul_point >> simp[]
QED

Theorem deploy_blocks_frame_blockhash[simp]:
  deploy_blocks_frame (compile_blockhash n)
Proof
  apply_symbolic_frame symbolic_frame_blockhash >> simp[]
QED

Theorem deploy_blocks_frame_blobhash[simp]:
  deploy_blocks_frame (compile_blobhash n)
Proof
  apply_symbolic_frame symbolic_frame_blobhash >> simp[]
QED

Theorem deploy_blocks_frame_floor[simp]:
  deploy_blocks_frame (compile_floor v d)
Proof
  apply_symbolic_frame symbolic_frame_floor >> simp[]
QED

Theorem deploy_blocks_frame_ceil[simp]:
  deploy_blocks_frame (compile_ceil v d)
Proof
  apply_symbolic_frame symbolic_frame_ceil >> simp[]
QED

Theorem deploy_blocks_frame_as_wei_value_int[simp]:
  deploy_blocks_frame (compile_as_wei_value_int v scale s)
Proof
  apply_symbolic_frame symbolic_frame_as_wei_value_int >> simp[]
QED

Theorem deploy_blocks_frame_as_wei_value_decimal[simp]:
  deploy_blocks_frame (compile_as_wei_value_decimal v scale d)
Proof
  apply_symbolic_frame symbolic_frame_as_wei_value_decimal >> simp[]
QED

Theorem deploy_blocks_frame_uint2str[simp]:
  deploy_blocks_frame (compile_uint2str v digits sz)
Proof
  apply_symbolic_frame symbolic_frame_uint2str >> simp[]
QED

Theorem deploy_blocks_frame_check_create_result[simp]:
  deploy_blocks_frame (compile_check_create_result v b)
Proof
  apply_symbolic_frame symbolic_frame_check_create_result >> simp[]
QED

Theorem deploy_blocks_frame_create_dispatch[simp]:
  deploy_blocks_frame (compile_create_dispatch p n v salt b)
Proof
  apply_symbolic_frame symbolic_frame_create_dispatch >> simp[]
QED

Theorem deploy_blocks_frame_create_proxy_buf[simp]:
  deploy_blocks_frame (compile_create_proxy_buf v)
Proof
  apply_symbolic_frame symbolic_frame_create_proxy_buf >> simp[]
QED

Theorem deploy_blocks_frame_create_proxy[simp]:
  deploy_blocks_frame (compile_create_proxy v value salt b)
Proof
  apply_symbolic_frame symbolic_frame_create_proxy >> simp[]
QED

Theorem deploy_blocks_frame_create_copy:
  (!n. deploy_blocks_frame (compile_alloc_dynamic n)) ==>
  deploy_blocks_frame (compile_create_copy v value salt b)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_create_copy >> simp[]
QED

Theorem deploy_blocks_frame_create_blueprint_check[simp]:
  deploy_blocks_frame (compile_create_blueprint_check is_lit v off)
Proof
  apply_symbolic_frame symbolic_frame_create_blueprint_check >> simp[]
QED

Theorem deploy_blocks_frame_create_blueprint_append:
  (!n. deploy_blocks_frame (compile_alloc_dynamic n)) /\
  (!d s n. deploy_blocks_frame (compile_copy_memory_dynamic d s n)) ==>
  deploy_blocks_frame (compile_create_blueprint_append v value salt off n p len b)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_create_blueprint_append >> simp[]
QED

Theorem deploy_blocks_frame_create_blueprint:
  (!n. deploy_blocks_frame (compile_alloc_dynamic n)) /\
  (!d s n. deploy_blocks_frame (compile_copy_memory_dynamic d s n)) ==>
  deploy_blocks_frame (compile_create_blueprint is_lit v value salt off args b)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_create_blueprint >> simp[]
QED

Theorem deploy_blocks_frame_msg_data_to_memory:
  (!n. deploy_blocks_frame (compile_alloc_dynamic n)) ==>
  deploy_blocks_frame compile_msg_data_to_memory
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_msg_data_to_memory >> simp[]
QED

Theorem deploy_blocks_frame_raw_call_outbuf[simp]:
  deploy_blocks_frame (compile_raw_call_outbuf n)
Proof simp[compile_raw_call_outbuf_def, COND_RAND]
QED

Theorem deploy_blocks_frame_raw_call_finish[simp]:
  deploy_blocks_frame (compile_raw_call_finish to_op p len gas v ct n b out outp)
Proof
  apply_symbolic_frame symbolic_frame_raw_call_finish >> simp[]
QED

Theorem deploy_blocks_frame_send[simp]:
  deploy_blocks_frame (compile_send to_op v gas)
Proof
  apply_symbolic_frame symbolic_frame_send >> simp[]
QED

Theorem deploy_blocks_frame_raw_revert[simp]:
  deploy_blocks_frame (compile_raw_revert p)
Proof
  apply_symbolic_frame symbolic_frame_raw_revert >> simp[]
QED

Theorem deploy_blocks_frame_selfdestruct[simp]:
  deploy_blocks_frame (compile_selfdestruct to_op)
Proof
  apply_symbolic_frame symbolic_frame_selfdestruct >> simp[]
QED

Theorem deploy_blocks_frame_lower_abi_encode[simp]:
  (!dst. deploy_blocks_frame (encode dst)) ==>
  deploy_blocks_frame (lower_abi_encode mid maxlen encode)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_lower_abi_encode >> simp[]
QED

Theorem deploy_blocks_frame_lower_abi_decode[simp]:
  deploy_blocks_frame (lower_abi_decode src info minsz maxsz outsz)
Proof
  apply_symbolic_frame symbolic_frame_lower_abi_decode >> simp[]
QED

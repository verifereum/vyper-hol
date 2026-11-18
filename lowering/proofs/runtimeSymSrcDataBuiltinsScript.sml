Theory runtimeSymSrcDataBuiltins
Ancestors
  symbolicSourceCompilerBuiltinFrame
  compileEnv runtimeSymSrcDataFrame builtinAbi builtinBytes builtinCreate
  builtinHashing builtinMath builtinMisc builtinSimple builtinStrings builtinSystem
  symbolicSourceCompilerFrame

fun specialize_frame theorem =
  REWRITE_RULE [symbolic_frame_runtime]
    (Q.ISPEC `\data (s:compile_state) t. s = t /\ s.cs_data_sections = data`
      (Q.GEN `R` theorem))

fun apply_symbolic_frame theorem = match_mp_tac (specialize_frame theorem)

(* External allocation and ABI operations are kept as uniform frame premises;
   their proofs belong to the Context and ABI libraries. *)
Theorem runtime_data_frame_select[simp]:
  runtime_data_frame (compile_select c a b)
Proof
  apply_symbolic_frame symbolic_frame_select >> simp[]
QED

Theorem runtime_data_frame_zero_words[simp]:
  !n b. runtime_data_frame (compile_zero_words b n)
Proof
  apply_symbolic_frame symbolic_frame_zero_words >> simp[]
QED

Theorem runtime_data_frame_builtin_len:
  (!c i l p. runtime_data_frame (compile_ptr_load c i l p)) ==>
  runtime_data_frame (compile_builtin_len c i p l)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_builtin_len >> simp[]
QED

Theorem runtime_data_frame_builtin_calldatasize[simp]:
  runtime_data_frame compile_builtin_calldatasize
Proof
  apply_symbolic_frame symbolic_frame_builtin_calldatasize >> simp[]
QED

Theorem runtime_data_frame_builtin_empty_prim[simp]:
  runtime_data_frame compile_builtin_empty_prim
Proof
  MATCH_ACCEPT_TAC (specialize_frame symbolic_frame_builtin_empty_prim)
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
  apply_symbolic_frame symbolic_frame_builtin_min >> simp[]
QED

Theorem runtime_data_frame_builtin_max[simp]:
  runtime_data_frame (compile_builtin_max a b u)
Proof
  apply_symbolic_frame symbolic_frame_builtin_max >> simp[]
QED

Theorem runtime_data_frame_builtin_abs[simp]:
  runtime_data_frame (compile_builtin_abs a)
Proof
  apply_symbolic_frame symbolic_frame_builtin_abs >> simp[]
QED

Theorem runtime_data_frame_unsafe_binop[simp]:
  runtime_data_frame (compile_unsafe_binop op x y bits s)
Proof
  apply_symbolic_frame symbolic_frame_unsafe_binop >> simp[]
QED

Theorem runtime_data_frame_unsafe_add[simp]:
  runtime_data_frame (compile_unsafe_add x y bits s)
Proof
  apply_symbolic_frame symbolic_frame_unsafe_add >> simp[]
QED

Theorem runtime_data_frame_unsafe_sub[simp]:
  runtime_data_frame (compile_unsafe_sub x y bits s)
Proof
  apply_symbolic_frame symbolic_frame_unsafe_sub >> simp[]
QED

Theorem runtime_data_frame_unsafe_mul[simp]:
  runtime_data_frame (compile_unsafe_mul x y bits s)
Proof
  apply_symbolic_frame symbolic_frame_unsafe_mul >> simp[]
QED

Theorem runtime_data_frame_unsafe_div[simp]:
  runtime_data_frame (compile_unsafe_div x y bits s)
Proof
  apply_symbolic_frame symbolic_frame_unsafe_div >> simp[]
QED

Theorem runtime_data_frame_pow_mod256[simp]:
  runtime_data_frame (compile_pow_mod256 x y)
Proof
  apply_symbolic_frame symbolic_frame_pow_mod256 >> simp[]
QED

Theorem runtime_data_frame_addmod[simp]:
  runtime_data_frame (compile_addmod x y z)
Proof
  apply_symbolic_frame symbolic_frame_addmod >> simp[]
QED

Theorem runtime_data_frame_mulmod[simp]:
  runtime_data_frame (compile_mulmod x y z)
Proof
  apply_symbolic_frame symbolic_frame_mulmod >> simp[]
QED

Theorem runtime_data_frame_shift[simp]:
  runtime_data_frame (compile_shift x y s)
Proof
  apply_symbolic_frame symbolic_frame_shift >> simp[]
QED

Theorem runtime_data_frame_assert_slice_bounds[simp]:
  runtime_data_frame (compile_assert_slice_bounds s n l)
Proof
  apply_symbolic_frame symbolic_frame_assert_slice_bounds >> simp[]
QED

Theorem runtime_data_frame_bytestring_src[simp]:
  runtime_data_frame (compile_bytestring_src p)
Proof
  apply_symbolic_frame symbolic_frame_bytestring_src >> simp[]
QED

Theorem runtime_data_frame_slice_data:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_slice_data l p s n out)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_slice_data >> simp[]
QED

Theorem runtime_data_frame_slice_out_buf:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_slice_out_buf out)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_slice_out_buf >> simp[]
QED

Theorem runtime_data_frame_slice_calldata:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_slice_calldata s n out)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_slice_calldata >> simp[]
QED

Theorem runtime_data_frame_slice_code:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_slice_code s n out)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_slice_code >> simp[]
QED

Theorem runtime_data_frame_slice_extcode:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_slice_extcode a s n b)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_slice_extcode >> simp[]
QED

Theorem runtime_data_frame_extract32_load[simp]:
  runtime_data_frame (compile_extract32_load l p s)
Proof
  apply_symbolic_frame symbolic_frame_extract32_load >> simp[]
QED

Theorem runtime_data_frame_keccak256_word:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_keccak256_word v)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_keccak256_word >> simp[]
QED

Theorem runtime_data_frame_keccak256_bytes[simp]:
  runtime_data_frame (compile_keccak256_bytes p)
Proof
  apply_symbolic_frame symbolic_frame_keccak256_bytes >> simp[]
QED

Theorem runtime_data_frame_keccak256_bytesm:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_keccak256_bytesm v m)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_keccak256_bytesm >> simp[]
QED

Theorem runtime_data_frame_method_id_hash:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_method_id_hash ty v)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_method_id_hash >> simp[]
QED

Theorem runtime_data_frame_method_id_runtime:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_method_id_runtime ty v b)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_method_id_runtime >> simp[]
QED

Theorem runtime_data_frame_sha256_word:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_sha256_word v)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_sha256_word >> simp[]
QED

Theorem runtime_data_frame_sha256_bytes:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_sha256_bytes v)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_sha256_bytes >> simp[]
QED

Theorem runtime_data_frame_sha256_bytesm:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_sha256_bytesm v m)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_sha256_bytesm >> simp[]
QED

Theorem runtime_data_frame_ecrecover:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_ecrecover h v r s)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_ecrecover >> simp[]
QED

Theorem runtime_data_frame_ecadd_points:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_ecadd_points p q)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_ecadd_points >> simp[]
QED

Theorem runtime_data_frame_ecmul_point:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_ecmul_point p s)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_ecmul_point >> simp[]
QED

Theorem runtime_data_frame_blockhash[simp]:
  runtime_data_frame (compile_blockhash n)
Proof
  apply_symbolic_frame symbolic_frame_blockhash >> simp[]
QED

Theorem runtime_data_frame_blobhash[simp]:
  runtime_data_frame (compile_blobhash n)
Proof
  apply_symbolic_frame symbolic_frame_blobhash >> simp[]
QED

Theorem runtime_data_frame_floor[simp]:
  runtime_data_frame (compile_floor v d)
Proof
  apply_symbolic_frame symbolic_frame_floor >> simp[]
QED

Theorem runtime_data_frame_ceil[simp]:
  runtime_data_frame (compile_ceil v d)
Proof
  apply_symbolic_frame symbolic_frame_ceil >> simp[]
QED

Theorem runtime_data_frame_as_wei_value_int[simp]:
  runtime_data_frame (compile_as_wei_value_int v scale s)
Proof
  apply_symbolic_frame symbolic_frame_as_wei_value_int >> simp[]
QED

Theorem runtime_data_frame_as_wei_value_decimal[simp]:
  runtime_data_frame (compile_as_wei_value_decimal v scale d)
Proof
  apply_symbolic_frame symbolic_frame_as_wei_value_decimal >> simp[]
QED

Theorem runtime_data_frame_uint2str:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_uint2str v digits sz)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_uint2str >> simp[]
QED

Theorem runtime_data_frame_check_create_result:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_check_create_result v b)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_check_create_result >> simp[]
QED

Theorem runtime_data_frame_create_dispatch:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_create_dispatch p n v salt b)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_create_dispatch >> simp[]
QED

Theorem runtime_data_frame_create_proxy_buf:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_create_proxy_buf v)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_create_proxy_buf >> simp[]
QED

Theorem runtime_data_frame_create_proxy:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_create_proxy v value salt b)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_create_proxy >> simp[]
QED

Theorem runtime_data_frame_create_copy:
  (!n. runtime_data_frame (compile_alloc_buffer n)) /\
  (!n. runtime_data_frame (compile_alloc_dynamic n)) ==>
  runtime_data_frame (compile_create_copy v value salt b)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_create_copy >> simp[]
QED

Theorem runtime_data_frame_create_blueprint_check[simp]:
  runtime_data_frame (compile_create_blueprint_check is_lit v off)
Proof
  apply_symbolic_frame symbolic_frame_create_blueprint_check >> simp[]
QED

Theorem runtime_data_frame_create_blueprint_append:
  (!n. runtime_data_frame (compile_alloc_buffer n)) /\
  (!n. runtime_data_frame (compile_alloc_dynamic n)) /\
  (!d s n. runtime_data_frame (compile_copy_memory_dynamic d s n)) ==>
  runtime_data_frame (compile_create_blueprint_append v value salt off n p len b)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_create_blueprint_append >> simp[]
QED

Theorem runtime_data_frame_create_blueprint:
  (!n. runtime_data_frame (compile_alloc_buffer n)) /\
  (!n. runtime_data_frame (compile_alloc_dynamic n)) /\
  (!d s n. runtime_data_frame (compile_copy_memory_dynamic d s n)) ==>
  runtime_data_frame (compile_create_blueprint is_lit v value salt off args b)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_create_blueprint >> simp[]
QED

Theorem runtime_data_frame_msg_data_to_memory:
  (!n. runtime_data_frame (compile_alloc_dynamic n)) ==>
  runtime_data_frame compile_msg_data_to_memory
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_msg_data_to_memory >> simp[]
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
  strip_tac >> apply_symbolic_frame symbolic_frame_raw_call_finish >> simp[]
QED

Theorem runtime_data_frame_send[simp]:
  runtime_data_frame (compile_send to_op v gas)
Proof
  apply_symbolic_frame symbolic_frame_send >> simp[]
QED

Theorem runtime_data_frame_raw_revert[simp]:
  runtime_data_frame (compile_raw_revert p)
Proof
  apply_symbolic_frame symbolic_frame_raw_revert >> simp[]
QED

Theorem runtime_data_frame_selfdestruct[simp]:
  runtime_data_frame (compile_selfdestruct to_op)
Proof
  apply_symbolic_frame symbolic_frame_selfdestruct >> simp[]
QED

Theorem runtime_data_frame_lower_abi_encode:
  (!n. runtime_data_frame (compile_alloc_buffer n)) /\
  (!p s i. runtime_data_frame (compile_abi_encode_to_buf p s i)) ==>
  runtime_data_frame (lower_abi_encode tuple mid src info maxlen)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_lower_abi_encode >> simp[]
QED

Theorem runtime_data_frame_lower_abi_decode:
  (!n. runtime_data_frame (compile_alloc_buffer n)) /\
  (!d off op p n i. runtime_data_frame (compile_abi_decode_to_buf d off op p n i)) ==>
  runtime_data_frame (lower_abi_decode src info minsz maxsz outsz)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_lower_abi_decode >> simp[]
QED

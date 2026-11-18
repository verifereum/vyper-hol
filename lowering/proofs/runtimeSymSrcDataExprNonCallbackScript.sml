Theory runtimeSymSrcDataExprNonCallback
Ancestors
  symbolicSourceCompilerCallFrame
  symbolicSourceCompilerExprFrame
  runtimeSymSrcDataFrame runtimeSymSrcDataContext exprLowering compileEnv

(* Keep compiler conditionals intact for the structural frame proofs. *)
val _ = temp_delsimps ["runtime_data_frame_cond"];

fun frame_tac g = (simp[comp_ignore_bind_def] >> rpt (match_mp_tac runtime_data_frame_bind >> conj_tac
  >- (simp[] >> frame_tac) >> gen_tac >> BETA_TAC) >> simp[]) g;

fun specialize_frame theorem =
  REWRITE_RULE [symbolic_frame_runtime]
    (Q.ISPEC `\data (s:compile_state) t. s = t /\ s.cs_data_sections = data`
      (Q.GEN `R` theorem))

fun apply_symbolic_frame theorem = match_mp_tac (specialize_frame theorem)

Theorem runtime_data_frame_compile_clamp[simp]:
  runtime_data_frame (compile_clamp v ty)
Proof
  apply_symbolic_frame symbolic_frame_compile_clamp >> simp[]
QED

Theorem runtime_data_frame_clamp_and_return[simp]:
  runtime_data_frame (clamp_and_return v ty)
Proof
  apply_symbolic_frame symbolic_frame_clamp_and_return >> simp[]
QED

Theorem runtime_data_frame_clamp_basetype[simp]:
  runtime_data_frame (compile_clamp_basetype v ty)
Proof
  apply_symbolic_frame symbolic_frame_clamp_basetype >> simp[]
QED

Theorem runtime_data_frame_safe_add[simp]:
  runtime_data_frame (compile_safe_add x y ty)
Proof
  apply_symbolic_frame symbolic_frame_safe_add >> simp[]
QED

Theorem runtime_data_frame_safe_sub[simp]:
  runtime_data_frame (compile_safe_sub x y ty)
Proof
  apply_symbolic_frame symbolic_frame_safe_sub >> simp[]
QED

Theorem runtime_data_frame_mul_overflow[simp]:
  runtime_data_frame (compile_mul_overflow_check x y res sg bits)
Proof
  apply_symbolic_frame symbolic_frame_mul_overflow >> simp[]
QED

Theorem runtime_data_frame_safe_mul[simp]:
  runtime_data_frame (compile_safe_mul x y ty)
Proof
  apply_symbolic_frame symbolic_frame_safe_mul >> simp[]
QED

Theorem runtime_data_frame_safe_div[simp]:
  runtime_data_frame (compile_safe_div x y ty)
Proof
  apply_symbolic_frame symbolic_frame_safe_div >> simp[]
QED

Theorem runtime_data_frame_safe_decimal_div[simp]:
  runtime_data_frame (compile_safe_decimal_div x y divisor ty)
Proof
  apply_symbolic_frame symbolic_frame_safe_decimal_div >> simp[]
QED

Theorem runtime_data_frame_safe_mod[simp]:
  runtime_data_frame (compile_safe_mod x y ty)
Proof
  apply_symbolic_frame symbolic_frame_safe_mod >> simp[]
QED

Theorem runtime_data_frame_safe_pow[simp]:
  runtime_data_frame (compile_safe_pow x y ty bl el)
Proof
  apply_symbolic_frame symbolic_frame_safe_pow >> simp[]
QED

Theorem runtime_data_frame_compare[simp]:
  runtime_data_frame (compile_compare op x y ty)
Proof
  apply_symbolic_frame symbolic_frame_compare >> simp[]
QED

Theorem runtime_data_frame_wrap_truncate[simp]:
  runtime_data_frame (wrap_truncate v ty)
Proof
  apply_symbolic_frame symbolic_frame_wrap_truncate >> simp[]
QED

Theorem runtime_data_frame_binop:
  (!c x y. runtime_data_frame (compile_select c x y)) ==>
  runtime_data_frame (compile_binop op x y ty bl el)
Proof
  strip_tac >>
  apply_symbolic_frame symbolic_frame_binop >> simp[]
QED

Theorem runtime_data_frame_bytestring_hash[simp]:
  runtime_data_frame (compile_bytestring_hash p)
Proof
  apply_symbolic_frame symbolic_frame_bytestring_hash >> simp[]
QED

Theorem runtime_data_frame_membership_eqs[simp]:
  !es n. runtime_data_frame (emit_membership_eqs n es)
Proof
  apply_symbolic_frame symbolic_frame_membership_eqs >> simp[]
QED

Theorem runtime_data_frame_membership_or[simp]:
  !es acc. runtime_data_frame (fold_membership_or acc es)
Proof
  apply_symbolic_frame symbolic_frame_membership_or >> simp[]
QED

Theorem runtime_data_frame_membership_and[simp]:
  !es acc. runtime_data_frame (fold_membership_and acc es)
Proof
  apply_symbolic_frame symbolic_frame_membership_and >> simp[]
QED

Theorem runtime_data_frame_list_membership_in[simp]:
  runtime_data_frame (compile_list_membership_in n es)
Proof
  apply_symbolic_frame symbolic_frame_list_membership_in >> simp[]
QED

Theorem runtime_data_frame_list_membership_notin[simp]:
  runtime_data_frame (compile_list_membership_notin n es)
Proof
  apply_symbolic_frame symbolic_frame_list_membership_notin >> simp[]
QED

Theorem runtime_data_frame_array_membership_loop:
  (!p. runtime_data_frame (loader p)) ==>
  runtime_data_frame (compile_array_membership_loop n arr len sz off loader bd isin)
Proof
  strip_tac >>
  apply_symbolic_frame symbolic_frame_array_membership_loop >> simp[]
QED

Theorem runtime_data_frame_var_array_membership:
  (!ctor imm loc off. runtime_data_frame (compile_ptr_load ctor imm loc off)) ==>
  runtime_data_frame (compile_var_array_membership cenv n vv ty isin)
Proof
  strip_tac >>
  apply_symbolic_frame symbolic_frame_var_array_membership >> simp[]
QED

Theorem runtime_data_frame_mapping_subscript:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_mapping_subscript slot key)
Proof
  strip_tac >>
  apply_symbolic_frame symbolic_frame_mapping_subscript >> simp[]
QED

Theorem runtime_data_frame_keccak256_key:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_keccak256_key key bs32)
Proof
  strip_tac >>
  apply_symbolic_frame symbolic_frame_keccak256_key >> simp[]
QED

Theorem runtime_data_frame_extcodesize_check[simp]:
  runtime_data_frame (compile_extcodesize_check addr)
Proof
  apply_symbolic_frame symbolic_frame_extcodesize_check >> simp[]
QED

Theorem runtime_data_frame_return_value_decode:
  (!c x y. runtime_data_frame (compile_select c x y)) ==>
  runtime_data_frame (compile_return_value_decode lo hi)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_return_value_decode >> simp[]
QED

Theorem runtime_data_frame_unwrap_value:
  (!ctor imm loc off. runtime_data_frame (compile_ptr_load ctor imm loc off)) /\
  (!p loc bytes words ctor imm.
    runtime_data_frame (compile_ensure_in_memory p loc bytes words ctor imm)) ==>
  runtime_data_frame (unwrap_value cenv vv)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_unwrap_value >> simp[]
QED

Theorem runtime_data_frame_multi_vvs:
  !es. (!e. MEM e es ==> runtime_data_frame (cfn cenv (expr_type e) e)) ==>
  runtime_data_frame (compile_multi_vvs cfn cenv es)
Proof
  MATCH_ACCEPT_TAC (specialize_frame symbolic_frame_multi_vvs)
QED

Theorem runtime_data_frame_extcall_store_values:
  (!vv. runtime_data_frame (unwrap_value cenv vv)) /\
  (!v dst. runtime_data_frame (compile_store_bytestring v dst)) ==>
  !vs buf off. runtime_data_frame (compile_extcall_store_values cenv vs buf off)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_extcall_store_values >> simp[]
QED

Theorem runtime_data_frame_default_return_path:
  (!v dst dt st. runtime_data_frame (compile_store_memory cenv v dst dt st)) /\
  (!lo hi. runtime_data_frame (compile_return_value_decode lo hi)) /\
  (!dst src opc lo hi info. runtime_data_frame (compile_abi_decode_to_buf dst src opc lo hi info)) ==>
  runtime_data_frame (compile_default_return_path cenv rt dt buf res dop addr skip lo hi info)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_default_return_path >> simp[]
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
  strip_tac >> apply_symbolic_frame symbolic_frame_external_call_kwargs >> simp[]
QED

Theorem runtime_data_frame_dynarray_append:
  (!v dst dt st. runtime_data_frame (compile_store_memory cenv v dst dt st)) /\
  (!src dst n sl dl imm. runtime_data_frame (compile_word_copy_loop src dst n sl dl imm)) /\
  (!src slot ty trans. runtime_data_frame (compile_store_slots cenv src slot ty trans)) ==>
  runtime_data_frame (compile_dynarray_append cenv arr v ws sz dt st cap prim loc)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_dynarray_append >> simp[]
QED

Theorem runtime_data_frame_dynarray_pop:
  (!ctor imm loc off. runtime_data_frame (compile_ptr_load ctor imm loc off)) /\
  (!ctor imm loc off v. runtime_data_frame (compile_ptr_store ctor imm loc off v)) ==>
  runtime_data_frame (compile_dynarray_pop arr ws sz ctor imm loc)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_dynarray_pop >> simp[]
QED

Theorem runtime_data_frame_stage_intcall_args:
  (!vv. runtime_data_frame (unwrap_value cenv vv)) /\
  (!n. runtime_data_frame (compile_alloc_buffer n)) /\
  (!v dst. runtime_data_frame (compile_store_bytestring v dst)) /\
  (!v dst dt st. runtime_data_frame (compile_store_memory cenv v dst dt st)) ==>
  !vs flags tys.
    (!e. MEM e vs ==> runtime_data_frame (cfn cenv (expr_type e) e)) ==>
    runtime_data_frame (compile_stage_intcall_args cfn cenv vs flags tys)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_stage_intcall_args >> simp[]
QED

Theorem runtime_data_frame_store_multi_results[simp]:
  !vs buf off. runtime_data_frame (store_multi_results buf vs off)
Proof
  apply_symbolic_frame symbolic_frame_store_multi_results >> simp[]
QED

Theorem runtime_data_frame_array_subscript:
  (!p. runtime_data_frame (loader p)) ==>
  runtime_data_frame (compile_array_subscript arr idx dyn cnt ws sz sg loader)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_array_subscript >> simp[]
QED

Theorem runtime_data_frame_tuple_subscript[simp]:
  runtime_data_frame (compile_tuple_subscript arr off)
Proof
  apply_symbolic_frame symbolic_frame_tuple_subscript >> simp[]
QED

Theorem runtime_data_frame_store_byte_chunks[simp]:
  !p bs off. runtime_data_frame (compile_store_byte_chunks p bs off)
Proof
  apply_symbolic_frame symbolic_frame_store_byte_chunks >> simp[]
QED

Theorem runtime_data_frame_bytelike_literal:
  (!n. runtime_data_frame (compile_alloc_buffer n)) ==>
  runtime_data_frame (compile_bytelike_literal bs maxlen)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_bytelike_literal >> simp[]
QED

Theorem runtime_data_frame_literal_vv:
  (!bs n. runtime_data_frame (compile_bytelike_literal bs n)) ==>
  runtime_data_frame (compile_literal_vv ty lit)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_literal_vv >> simp[]
QED

Theorem runtime_data_frame_name_vv[simp]:
  runtime_data_frame (compile_name_vv cenv ty id)
Proof
  apply_symbolic_frame symbolic_frame_name_vv >> simp[]
QED

Theorem runtime_data_frame_env_var[simp]:
  runtime_data_frame (compile_env_var item)
Proof
  apply_symbolic_frame symbolic_frame_env_var >> simp[]
QED

Theorem runtime_data_frame_load_bytestring_as_word[simp]:
  runtime_data_frame (load_bytestring_as_word v opc)
Proof
  apply_symbolic_frame symbolic_frame_load_bytestring_as_word >> simp[]
QED

Theorem runtime_data_frame_int_clamp[simp]:
  runtime_data_frame (compile_int_clamp sg bits v)
Proof
  apply_symbolic_frame symbolic_frame_int_clamp >> simp[]
QED

Theorem runtime_data_frame_type_convert[simp]:
  runtime_data_frame (compile_type_convert v conv)
Proof
  apply_symbolic_frame symbolic_frame_type_convert >> simp[]
QED

Theorem runtime_data_frame_bytestring_widen_copy:
  (!n. runtime_data_frame (compile_alloc_buffer n)) /\
  (!dst src sz. runtime_data_frame (compile_copy_memory dst src sz)) ==>
  runtime_data_frame (compile_bytestring_widen_copy dstsz v srcsz)
Proof
  strip_tac >> apply_symbolic_frame symbolic_frame_bytestring_widen_copy >> simp[]
QED

Theorem runtime_data_frame_neg[simp]:
  runtime_data_frame (compile_neg v ty)
Proof
  apply_symbolic_frame symbolic_frame_neg >> simp[]
QED

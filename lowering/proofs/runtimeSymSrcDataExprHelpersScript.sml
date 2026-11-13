Theory runtimeSymSrcDataExprHelpers
Ancestors
  runtimeSymSrcDataExprNonCallback runtimeSymSrcDataExprCallbacksAll
  runtimeSymSrcDataExprBodies runtimeSymSrcDataExprCallbacks
  runtimeSymSrcDataExprCalls runtimeSymSrcDataExprAddressing
  runtimeSymSrcDataContext runtimeSymSrcDataABI
  runtimeSymSrcDataBuiltins

(* Join the implementation libraries at their frame boundary.  These rules
   discharge only local helper premises; no compiler body is unfolded here. *)
Theorem runtime_data_frame_unwrap_closed[simp]:
  runtime_data_frame (unwrap_value cenv vv)
Proof
  irule runtime_data_frame_unwrap_value >> simp[]
QED

Theorem runtime_data_frame_literal_closed[simp]:
  runtime_data_frame (compile_literal_vv ty lit)
Proof
  simp[runtime_data_frame_literal_vv, runtime_data_frame_bytelike_literal]
QED

Theorem runtime_data_frame_materialize_closed[simp]:
  runtime_data_frame (compile_materialize_vv cenv ty vv)
Proof
  simp[runtime_data_frame_materialize_vv]
QED

Theorem runtime_data_frame_abi_encode_closed[simp]:
  runtime_data_frame (compile_abi_encode_to_buf dst src info)
Proof
  simp[runtime_data_frame_abi_encode_to_buf]
QED

Theorem runtime_data_frame_abi_decode_closed[simp]:
  runtime_data_frame (compile_abi_decode_to_buf dst src opc bop hi info)
Proof
  simp[runtime_data_frame_abi_decode_to_buf]
QED

Theorem runtime_data_frame_external_call_closed[simp]:
  runtime_data_frame (compile_external_call_kwargs cenv addr vals tys mem abi mid rabi lo rmem static value gas skip has_default dop rt dt einfo dinfo)
Proof
  irule runtime_data_frame_external_call_kwargs >>
  simp[runtime_data_frame_extcall_store_values,
       runtime_data_frame_default_return_path, runtime_data_frame_return_value_decode]
QED

Theorem runtime_data_frame_call_closed:
  (!e ty. MEM e args ==> runtime_data_frame (cfn cenv ty e)) /\
  (!topics data e. target = RawLog /\ args = [topics; data] /\
    MEM e (raw_log_topic_exprs topics) ==>
    runtime_data_frame (cfn cenv (expr_type e) e)) ==>
  runtime_data_frame (compile_call cfn cenv rt ty target args dr)
Proof
  strip_tac >> irule runtime_data_frame_call_composed >>
  simp[runtime_data_frame_multi_vvs, runtime_data_frame_stage_intcall_args,
       runtime_data_frame_extcall_store_values, runtime_data_frame_raw_call_outbuf,
       runtime_data_frame_raw_call_finish, runtime_data_frame_msg_data_to_memory,
       runtime_data_frame_create_proxy_buf, runtime_data_frame_create_dispatch,
       runtime_data_frame_create_copy, runtime_data_frame_create_blueprint_append]
QED

Theorem runtime_data_frame_expr_body_assembled:
  (!t e. runtime_data_frame (cfn cenv t e)) /\
  (!t ty bi args. runtime_data_frame (bfn cenv t ty bi args)) /\
  (!t ty tb rt args. runtime_data_frame (tfn cenv t ty tb rt args)) ==>
  runtime_data_frame (compile_expr_body cfn bfn tfn cenv ty e)
Proof
  strip_tac >> irule runtime_data_frame_expr_body >>
  simp[runtime_data_frame_lower_value, runtime_data_frame_ifexp_arm,
       runtime_data_frame_addmod_names, runtime_data_frame_mulmod_names,
       runtime_data_frame_powmod256_names, runtime_data_frame_subscript,
       runtime_data_frame_attribute, runtime_data_frame_struct_lit,
       runtime_data_frame_call_closed, runtime_data_frame_get_target_ptr,
       runtime_data_frame_keccak256_key, runtime_data_frame_mapping_subscript,
       runtime_data_frame_array_subscript, runtime_data_frame_dynarray_pop]
QED

Theorem runtime_data_frame_type_body_assembled:
  (!t e. runtime_data_frame (cfn cenv t e)) ==>
  runtime_data_frame (compile_type_builtin_dispatch_body cfn cenv vt ty tb rt args)
Proof
  strip_tac >> irule runtime_data_frame_type_builtin_dispatch_body >>
  simp[runtime_data_frame_lower_value, runtime_data_frame_bytestring_widen_copy,
       runtime_data_frame_builtin_empty_complex, runtime_data_frame_lower_abi_encode,
       runtime_data_frame_lower_abi_decode, runtime_data_frame_abi_encode_args,
       runtime_data_frame_store_abi_tuple]
QED

Theorem runtime_data_frame_builtin_body_assembled:
  (!t e. runtime_data_frame (cfn cenv t e)) ==>
  runtime_data_frame (compile_builtin_dispatch_body cfn cenv rt ty bi args)
Proof
  strip_tac >> irule runtime_data_frame_builtin_dispatch_body >>
  simp[runtime_data_frame_lower_value, runtime_data_frame_multi_exprs,
       runtime_data_frame_var_array_membership, runtime_data_frame_binop,
       runtime_data_frame_invert, runtime_data_frame_acc,
       runtime_data_frame_keccak256_word, runtime_data_frame_keccak256_bytesm,
       runtime_data_frame_sha256_word, runtime_data_frame_sha256_bytes,
       runtime_data_frame_sha256_bytesm, runtime_data_frame_slice_calldata,
       runtime_data_frame_builtin_len, runtime_data_frame_ecrecover,
       runtime_data_frame_ecadd_points, runtime_data_frame_ecmul_point,
       runtime_data_frame_concat, runtime_data_frame_slice_code,
       runtime_data_frame_slice_out_buf, runtime_data_frame_slice_data,
       runtime_data_frame_uint2str, runtime_data_frame_method_id_runtime,
       runtime_data_frame_method_id_hash, runtime_data_frame_make_tuple,
       runtime_data_frame_make_array]
QED

(* Preserve the precise target-index callback scope for statement consumers. *)
Theorem runtime_data_frame_target_assembled:
  (!e. MEM e (target_indices target) ==>
    runtime_data_frame (cfn cenv (expr_type e) e)) ==>
  runtime_data_frame (compile_get_target_ptr cfn cenv target)
Proof
  strip_tac >> irule runtime_data_frame_get_target_ptr >>
  simp[runtime_data_frame_keccak256_key, runtime_data_frame_mapping_subscript,
       runtime_data_frame_array_subscript]
QED

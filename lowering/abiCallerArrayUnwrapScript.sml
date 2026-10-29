(* Checked compiler environments establish array coherence for both actual
   unwrap choices. Numeric allocation/history resources remain explicit. *)
Theory abiCallerArrayUnwrap
Ancestors
  abiCallerCoherence abiValidArrayUnwrap abiBuiltinSource abiBuiltinDecodeEffect
  abiDecoderCoherence abiDecoderContract abiDecoderLoop abiDecoderReentry compileVyper
  compileEnv vyperTypeSystem vyperValue vyperContext vyperABI contractABI valueEncoding
  abiEncoder builtinAbi fragExec venomState words list

Theorem lower_abi_decode_checked_array_unwrap:
  let ce = build_compile_env tops vis mut func_name fargs ret_type (code_stmts:stmt list) use_trans;
      ty = ArrayT elem_ty (Dynamic maxn);
      wrapped_ty = if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty in
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\ get_tenv cx = type_env tops /\
  assignable_type (type_env tops) ty /\
  evaluate_type (type_env tops) ty = SOME (ArrayTV elem_tv (Dynamic maxn)) /\
  ~is_dynamic (vyper_to_abi_type (get_tenv cx) elem_ty) /\
  evaluate_type_builtin cx (AbiDecode unwrap) ty arg_tys [vyperValue$BytesV bs] = INL v /\
  lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce wrapped_ty) min_size max_size
    (type_memory_bytes ce wrapped_ty) start = (out,final) /\ fn_has_code start final func /\
  (start.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  val_in_memory (BaseTV (BytesT (Dynamic input_bound))) (vyperValue$BytesV bs) p initial.vs_memory /\
  eval_operand data initial = SOME (n2w p) /\ abi_decoder_operand_live start.cs_next_var data /\
  abi_builtin_decode_resources start first last min_size max_size (type_memory_bytes ce ty)
    (LENGTH bs) p d b cap initial /\ final.cs_next_id <= last /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. eval_operand out actual = SOME (n2w d) /\
    val_in_memory (ArrayTV elem_tv (Dynamic maxn)) v d actual.vs_memory /\
    abi_builtin_decode_effect first last start final limit_st d (type_memory_bytes ce ty)
      b cap initial actual /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_coherent
    (build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans)
    (get_tenv cx)
    (build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans).ce_struct_fields
    (ArrayT elem_ty (Dynamic maxn)) (ArrayTV elem_tv (Dynamic maxn))` by
    (asm_simp_tac bool_ss [] >> irule abi_caller_coherent >> asm_simp_tac bool_ss [] >>
     qexists_tac `in_deploy` >> asm_simp_tac bool_ss []) >>
  drule_all (SIMP_RULE bool_ss [LET_THM] lower_abi_decode_valid_array_unwrap) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

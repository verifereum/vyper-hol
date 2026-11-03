(* Both unwrap_tuple choices use actual source-valid static-element array bytes. *)
Theory abiValidArrayUnwrap
Ancestors
  abiBuiltinWrapped abiBuiltinPrefixSource abiValidBytesUnwrap abiBuiltinSource
  abiBuiltinDecodeEffect abiDecoderCoherence abiDecoderReentry abiDecoderContract abiDecoderLoop
  abiEncoder builtinAbi fragExec compileEnv valueEncoding vyperABI vyperContext vyperValue
  contractABI venomState words list

val unwrapped_array_rule = SIMP_RULE (srw_ss()) [vyper_to_abi_type_def]
  (Q.INST [`ty` |-> `ArrayT ty (Dynamic maxn)`, `tv` |-> `ArrayTV tv (Dynamic maxn)`]
    lower_abi_decode_valid_prefix_source);

Theorem lower_abi_decode_valid_array_unwrap:
  let ty = ArrayT elem_ty (Dynamic maxn);
      wrapped_ty = if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty in
  abi_decoder_coherent ce (get_tenv cx) sf ty (ArrayTV elem_tv (Dynamic maxn)) /\
  ~is_dynamic (vyper_to_abi_type (get_tenv cx) elem_ty) /\
  evaluate_type_builtin cx (AbiDecode unwrap) ty arg_tys [vyperValue$BytesV bs] = INL v /\
  lower_abi_decode data (type_to_abi_dec_info sf ce wrapped_ty) min_size max_size
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
  `type_memory_bytes ce (TupleT [ArrayT elem_ty (Dynamic maxn)]) =
    type_memory_bytes ce (ArrayT elem_ty (Dynamic maxn))` by
    simp[Once type_memory_bytes_def] >>
  qpat_x_assum `evaluate_type_builtin _ _ _ _ _ = _`
    (assume_tac o PURE_REWRITE_RULE [abi_source_decode_wrapping_iff]) >>
  Cases_on `unwrap` >> RULE_ASSUM_TAC (SIMP_RULE bool_ss [needs_external_call_wrap_def]) >>
  qpat_assum `type_memory_bytes ce (TupleT [ArrayT elem_ty (Dynamic maxn)]) = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  FIRST [drule_all lower_abi_decode_valid_wrapped_array >>
           disch_then (qspec_then `ctx` strip_assume_tac),
         drule_all unwrapped_array_rule >> disch_then (qspec_then `ctx` strip_assume_tac)] >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

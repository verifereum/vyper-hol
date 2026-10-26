(* Full source-valid builtin decoding for both unwrap_tuple choices. *)
Theory abiBuiltinValidUnwrap
Ancestors
  abiBuiltinValidSource abiDecoderValidWrapping abiValidBytesUnwrap abiBoundaryChecks abiDecodeUnwrapCase
  abiBuiltinSourceInput abiBuiltinDecodeEffect abiDecoderCoherence abiDecoderReadableTypes
  abiDecoderContract abiDecoderLoop abiDecoderReentry abiEncoder builtinAbi fragExec
  compileEnv valueEncoding vyperABI vyperContext vyperValue venomState words list

Theorem lower_abi_decode_valid_unwrap:
  let wrapped = (unwrap /\ needs_external_call_wrap ty) in
  let wrapped_ty = if wrapped then TupleT [ty] else ty in
  abi_decoder_coherent ce (get_tenv cx) sf ty tv /\
  evaluate_type_builtin cx (AbiDecode unwrap) ty [vyperValue$BytesV bs] = INL v /\
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
  ?actual. eval_operand out actual = SOME (n2w d) /\ val_in_memory tv v d actual.vs_memory /\
    abi_builtin_decode_effect first last start final limit_st d (type_memory_bytes ce ty)
      b cap initial actual /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `evaluate_type_builtin _ _ _ _ = _`
    (assume_tac o PURE_REWRITE_RULE [abi_source_decode_wrapping_iff]) >>
  mp_tac (Q.INST [`env` |-> `get_tenv cx`,
    `wrapped` |-> `unwrap /\ needs_external_call_wrap ty`]
    abi_decoder_valid_wrapping) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [abi_decode_output_size]) >>
  mp_tac (SIMP_RULE bool_ss [abi_decode_output_size] (Q.INST
    [`env` |-> `get_tenv cx`, `src_base` |-> `p:num`,
     `ty` |-> `if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty`,
     `tv` |-> `if unwrap /\ needs_external_call_wrap ty then TupleTV [tv] else tv`,
     `v` |-> `if unwrap /\ needs_external_call_wrap ty then ArrayV (TupleV [v]) else v`]
    lower_abi_decode_valid_source)) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `actual` >>
  Cases_on `unwrap /\ needs_external_call_wrap ty` >>
  gvs[val_in_memory_singleton_tuple, Excl "dec_def", Excl "valid_enc_def"]
QED

Theorem lower_abi_decode_valid_unwrap_true =
  SIMP_RULE bool_ss [LET_THM] (Q.INST [`unwrap` |-> `T`] lower_abi_decode_valid_unwrap);

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_VALID_UNWRAP_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI actual-source builtin unwrap not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinValidUnwrap");

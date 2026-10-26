(* Whole builtin execution from a source Bytes value already in memory. *)
Theory abiBuiltinSourceCorrect
Ancestors
  abiBuiltinSourceInput abiBuiltinUnwrapCorrect abiBuiltinDecodeEffect
  abiDecoderCoherence abiDecoderContract abiDecoderLoop
  builtinAbi fragExec compileEnv valueEncoding vyperABI vyperContext
  contractABI venomState venomExecSemantics words list

Theorem lower_abi_decode_source_canonical:
  let wrapped = (unwrap /\ needs_external_call_wrap ty) in
  let wrapped_ty = if wrapped then TupleT [ty] else ty in
  let wrapped_tv = if wrapped then TupleTV [tv] else tv in
  let wrapped_v = if wrapped then ArrayV (TupleV [v]) else v in
  lower_abi_decode data (type_to_abi_dec_info sf ce wrapped_ty) min_size max_size
    (type_memory_bytes ce wrapped_ty) start = (out,final) /\ fn_has_code start final func /\
  (start.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_coherent ce (get_tenv cx) sf wrapped_ty wrapped_tv /\
  evaluate_abi_decode (get_tenv cx) wrapped_ty bs = INL wrapped_v /\
  bs = enc (vyper_to_abi_type (get_tenv cx) wrapped_ty)
    (dec (vyper_to_abi_type (get_tenv cx) wrapped_ty) bs) /\
  val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV bs) src_base initial.vs_memory /\
  eval_operand data initial = SOME (n2w src_base) /\
  abi_decoder_operand_live start.cs_next_var data /\
  abi_builtin_decode_resources start first last min_size max_size (type_memory_bytes ce wrapped_ty)
    (LENGTH bs) src_base d b cap initial /\
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\ initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. evaluate_type_builtin cx (AbiDecode unwrap) ty [BytesV bs] = INL v /\
    eval_operand out actual = SOME (n2w d) /\ val_in_memory tv v d actual.vs_memory /\
    abi_builtin_decode_effect first last start final limit_st d (type_memory_bytes ce ty)
      b cap initial actual /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_builtin_canonical_pre_from_source >> strip_tac >>
  mp_tac (Q.INST [`av` |->
    `dec (vyper_to_abi_type (get_tenv cx)
      (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty)) bs`]
    lower_abi_decode_unwrap_canonical) >>
  asm_simp_tac bool_ss [LET_THM]
QED

Theorem lower_abi_decode_source_unwrap_true_canonical =
  SIMP_RULE bool_ss [LET_THM] (Q.INST [`unwrap` |-> `T`] lower_abi_decode_source_canonical);

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_SOURCE_CORRECT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI builtin source correctness not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinSourceCorrect");

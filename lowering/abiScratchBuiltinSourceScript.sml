(* Source-level result of the complete physical lower_abi_encode action.
   TOP-LEVEL: lower_abi_encode_scratch_source covers singleton unwrapping,
   tuple payloads and either method ID while preserving complete source data. *)
Theory abiScratchBuiltinSource
Ancestors
  abiScratchBuiltinRun abiScratchBuiltinPre abiScratchBuiltinEffect
  abiBuiltinEncodeSourceModel abiBuiltinEncodeSourcePrefix abiBuiltinEncodeRun
  abiEncoderInput abiDecoderContract abiDecoderLoop fragExec builtinAbi exprLowering
  compileEnv valueEncoding vyperContext vyperABI vyperAST vyperTypeSystem contractABI
  venomState words list

Theorem lower_abi_encode_scratch_source:
  let enc_ty = abi_builtin_encode_type ensure tys in
  let bytes = abi_encode_method_id_bytes method_id ++ enc (vyper_to_abi_type (get_tenv cx) enc_ty) av in
  well_typed_type_builtin_args (AbiEncode ensure method_id) (TupleT tys) tys /\
  LENGTH vs = LENGTH tys /\
  vyper_to_abi (get_tenv cx) enc_ty (abi_builtin_encode_value ensure tys vs) = SOME av /\
  lower_abi_encode ensure (OPTION_MAP bytes_method_id_word method_id) src
    (type_to_abi_enc_info ce.ce_struct_fields ce enc_ty) maxlen start = (out,final) /\
  fn_has_code start final func /\
  (start.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_builtin_pre (type_to_abi_enc_info ce.ce_struct_fields ce enc_ty)
    (vyper_to_abi_type (get_tenv cx) enc_ty) av start (OPTION_MAP bytes_method_id_word method_id)
    src sb source_cap p maxlen first last b cap initial /\
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. evaluate_type_builtin cx (AbiEncode ensure method_id) (TupleT tys) vs = INL (BytesV bytes) /\
    eval_operand out actual = SOME (n2w p) /\ mload p actual = n2w (LENGTH bytes) /\
    mem_bytes_at (p+32) (LENGTH bytes) actual.vs_memory = bytes /\
    val_in_memory (BaseTV (BytesT (Dynamic (maxlen+LENGTH (abi_encode_method_id_bytes method_id)))))
      (BytesV bytes) p actual.vs_memory /\
    abi_encoder_input (type_to_abi_enc_info ce.ce_struct_fields ce enc_ty)
      (vyper_to_abi_type (get_tenv cx) enc_ty) av sb source_cap actual.vs_memory /\
    abi_scratch_builtin_effect first last start final limit_st p
      (maxlen+32+LENGTH (abi_encode_method_id_bytes method_id))
      (case method_id of NONE => 0 | SOME _ => 32) b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_encode_checked_prefix >> strip_tac >>
  qpat_assum `well_typed_type_builtin_args _ _ _`
    (assume_tac o CONJUNCT1 o SIMP_RULE (srw_ss()) [well_typed_type_builtin_args_def]) >>
  drule_all abi_builtin_encode_source_result >> disch_then (qspec_then `method_id` assume_tac) >>
  drule_all lower_abi_encode_scratch >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  qpat_assum `abi_builtin_encode_prefix _ = _` (fn prefix =>
    let val size = REWRITE_RULE [abi_scratch_builtin_prefix_length]
          (AP_TERM ``LENGTH:word8 list -> num`` prefix) in
      RULE_ASSUM_TAC (PURE_REWRITE_RULE [prefix, size, abi_builtin_encode_store_case]) end) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [abi_scratch_builtin_prefix_length]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_BUILTIN_SOURCE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch source builtin result not kernel closed: " ^ n)
  end) (DB.thms "abiScratchBuiltinSource");

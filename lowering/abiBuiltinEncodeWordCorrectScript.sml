(* Source semantics of the actual singleton word AbiEncode dispatcher path.
   Its source memory is established by executing allocation and MSTORE. *)
Theory abiBuiltinEncodeWordCorrect
Ancestors
  abiBuiltinEncodeDispatchCode abiBuiltinEncodeWordContext abiBuiltinEncodeWordPrepare
  abiBuiltinEncodeSourceCorrect abiBuiltinEncodeSourceModel abiBuiltinEncodeStagedEffect
  abiBuiltinEncodeResources abiBuiltinAllocationState abiDecoderContract abiDecoderLoop
  exprLowering builtinAbi fragExec compileEnv context valueEncoding
  vyperABI vyperContext vyperAST vyperTypeSystem contractABI venomState venomExecSemantics
  finite_map words byte list arithmetic

Theorem compile_abi_encode_word_source:
  let src_ty = expr_type e in
  let maxlen = abi_size_bound ce.ce_struct_fields src_ty in
  let at = vyper_to_abi_type (get_tenv cx) src_ty in
  let bytes = abi_encode_method_id_bytes method_id ++ enc at av in
  is_word_type src_ty /\ lower_value cfn ce src_ty e origin = (value_op,arg_st) /\
  compile_type_builtin_dispatch_body cfn ce vv_ty ty (AbiEncode F method_id) ret_ty [e] origin =
    (vv,final) /\ fn_has_code arg_st final func /\
  (arg_st.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  well_typed_type_builtin_args (AbiEncode F method_id) (TupleT [src_ty]) [src_ty] /\
  vyper_to_abi (get_tenv cx) src_ty v = SOME av /\
  has_type at av /\ ~is_dynamic at /\ static_length at = 32 /\
  word_to_bytes w T = enc at av /\ LENGTH (enc at av) <= maxlen /\
  eval_operand value_op prepared = SOME w /\ abi_decoder_operand_live arg_st.cs_next_var value_op /\
  ((FLOOKUP prepared.vs_allocas arg_st.cs_next_id = NONE /\ sb = prepared.vs_alloca_next) \/
    FLOOKUP prepared.vs_allocas arg_st.cs_next_id = SOME (sb,32)) /\
  abi_builtin_encode_resources (arg_st with cs_next_id := arg_st.cs_next_id+2)
    (OPTION_MAP bytes_method_id_word method_id) sb 32 p maxlen first last b cap
    (abi_builtin_allocate_state arg_st.cs_next_id 32 prepared) /\
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st prepared /\ ~prepared.vs_halted /\
  prepared.vs_current_bb = arg_st.cs_current_bb /\ prepared.vs_inst_idx = LENGTH arg_st.cs_current_insts /\
  abi_decode_sim ctx func initial prepared ==>
  ?actual. evaluate_type_builtin cx (AbiEncode F method_id) (TupleT [src_ty]) [v] = INL (BytesV bytes) /\
    vv_location vv = SOME LocMemory /\ eval_operand (vv_operand vv) actual = SOME (n2w p) /\
    mload p actual = n2w (LENGTH bytes) /\ mem_bytes_at (p+32) (LENGTH bytes) actual.vs_memory = bytes /\
    val_in_memory (BaseTV (BytesT (Dynamic (maxlen+LENGTH (abi_encode_method_id_bytes method_id)))))
      (BytesV bytes) p actual.vs_memory /\
    abi_builtin_encode_staged_effect first last arg_st final limit_st sb 32 p
      (maxlen+32+LENGTH (abi_encode_method_id_bytes method_id))
      (case method_id of NONE => 0 | SOME _ => 32) b cap prepared actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all compile_abi_encode_word_trace >> strip_tac >>
  drule_all abi_builtin_encode_word_context >> strip_tac >>
  `staged.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`st` |-> `arg_st`, `initial` |-> `prepared:venom_state`,
    `ty` |-> `expr_type e`, `at` |-> `vyper_to_abi_type (get_tenv cx) (expr_type e)`,
    `method_id_opt` |-> `OPTION_MAP bytes_method_id_word method_id`,
    `maxlen` |-> `abi_size_bound ce.ce_struct_fields (expr_type e)`]
    (Q.ISPEC `ce.ce_struct_fields` (Q.GEN `sf` abi_builtin_encode_word_prepare))) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func prepared staged_state` >>
  mp_tac (SIMP_RULE (srw_ss()) [LET_THM, abi_builtin_encode_type_def, abi_builtin_encode_value_def]
    (Q.INST [`ensure` |-> `F`, `tys` |-> `[expr_type e]`, `vs` |-> `[v]`,
      `src` |-> `buf.buf_operand`, `start` |-> `staged`, `initial` |-> `staged_state:venom_state`,
      `source_cap` |-> `32:num`,
      `maxlen` |-> `abi_size_bound ce.ce_struct_fields (expr_type e)`, `ctx` |-> `ctx`]
      lower_abi_encode_source)) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func staged_state actual` >>
  `abi_builtin_encode_staged_effect first last arg_st final limit_st sb 32 p
    (abi_size_bound ce.ce_struct_fields (expr_type e)+32+LENGTH (abi_encode_method_id_bytes method_id))
    (case method_id of NONE => 0 | SOME _ => 32) b cap prepared actual` by
    (irule abi_builtin_encode_producer_compose >>
     qexistsl_tac [`staged_state`, `staged`] >> asm_simp_tac bool_ss [] >> decide_tac) >>
  `abi_decode_sim ctx func prepared actual` by
    (irule abi_decode_sim_trans >> qexists_tac `staged_state` >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) [vv_location_def, vv_operand_def, mk_ptr_def] >>
  irule abi_decode_sim_trans >> qexists_tac `prepared` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_ENCODE_WORD_CORRECT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI builtin word dispatcher correctness not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinEncodeWordCorrect");

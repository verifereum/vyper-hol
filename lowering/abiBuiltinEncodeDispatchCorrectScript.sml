(* Compose argument evaluation with the actual singleton memory AbiEncode path.
   Source conversion and complete memory/resource predicates are explicit. *)
Theory abiBuiltinEncodeDispatchCorrect
Ancestors
  abiBuiltinEncodeDispatchCode abiBuiltinEncodeSourceCorrect abiBuiltinEncodeSourceModel
  abiBuiltinEncodeInput abiBuiltinEncodeEffect abiDecoderContract abiDecoderLoop
  exprLowering builtinAbi fragExec compileEnv context valueEncoding
  vyperABI vyperContext vyperAST vyperTypeSystem contractABI venomState venomExecSemantics words list

Theorem compile_abi_encode_memory_source:
  let src_ty = expr_type e in
  let maxlen = abi_size_bound ce.ce_struct_fields src_ty in
  let bytes = abi_encode_method_id_bytes method_id ++ enc (vyper_to_abi_type (get_tenv cx) src_ty) av in
  ~is_word_type src_ty /\
  cfn ce src_ty e origin = (LocatedValue src_ty srcptr,ready) /\ srcptr.ptr_location = LocMemory /\
  compile_type_builtin_dispatch_body cfn ce vv_ty ty (AbiEncode F method_id) ret_ty [e] origin =
    (vv,final) /\ fn_has_code ready final func /\
  (ready.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  well_typed_type_builtin_args (AbiEncode F method_id) (TupleT [src_ty]) [src_ty] /\
  vyper_to_abi (get_tenv cx) src_ty v = SOME av /\
  abi_builtin_encode_pre (type_to_abi_enc_info ce.ce_struct_fields ce src_ty)
    (vyper_to_abi_type (get_tenv cx) src_ty) av ready (OPTION_MAP bytes_method_id_word method_id)
    srcptr.ptr_operand sb source_cap p maxlen first last b cap prepared /\
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st prepared /\ ~prepared.vs_halted /\
  prepared.vs_current_bb = ready.cs_current_bb /\ prepared.vs_inst_idx = LENGTH ready.cs_current_insts /\
  abi_decode_sim ctx func initial prepared ==>
  ?actual. evaluate_type_builtin cx (AbiEncode F method_id) (TupleT [src_ty]) [v] = INL (BytesV bytes) /\
    vv_location vv = SOME LocMemory /\ eval_operand (vv_operand vv) actual = SOME (n2w p) /\
    val_in_memory (BaseTV (BytesT (Dynamic (maxlen+LENGTH (abi_encode_method_id_bytes method_id)))))
      (BytesV bytes) p actual.vs_memory /\
    abi_builtin_encode_effect first last ready final limit_st p
      (maxlen+32+LENGTH (abi_encode_method_id_bytes method_id))
      (case method_id of NONE => 0 | SOME _ => 32) b cap prepared actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all compile_abi_encode_memory_trace >> strip_tac >>
  mp_tac (SIMP_RULE (srw_ss()) [LET_THM, abi_builtin_encode_type_def, abi_builtin_encode_value_def]
    (Q.INST [`ensure` |-> `F`, `tys` |-> `[expr_type e]`, `vs` |-> `[v]`,
      `src` |-> `srcptr.ptr_operand`, `start` |-> `ready`, `initial` |-> `prepared:venom_state`,
      `maxlen` |-> `abi_size_bound ce.ce_struct_fields (expr_type e)`, `ctx` |-> `ctx`]
      lower_abi_encode_source)) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func prepared actual` >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) [vv_location_def, vv_operand_def, mk_ptr_def] >>
  irule abi_decode_sim_trans >> qexists_tac `prepared` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_ENCODE_DISPATCH_CORRECT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI builtin encode dispatch correctness not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinEncodeDispatchCorrect");

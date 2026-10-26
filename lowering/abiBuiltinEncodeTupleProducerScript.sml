(* Actual multi-argument AbiEncode results are live, owned tuple inputs.
   Separation follows from allocation credit, without a final-layout premise. *)
Theory abiBuiltinEncodeTupleProducer
Ancestors
  abiBuiltinEncodeProducer abiBuiltinEncodeTupleCorrect abiBuiltinEncodeDispatchCode
  abiBuiltinEncodeSourcePrefix abiBuiltinEncodeStagedEffect abiBuiltinEncodeResources
  abiBuiltinAllocationState abiTupleEncodeOwnedBytes abiTupleEncodeInput abiTupleEncodeLayout
  abiTupleProps abiDecoderReentry abiDecoderContract abiDecoderLoop abiDecoderFootprint
  compileEnv context exprLowering exprLoweringProps valueEncoding vyperABI
  vyperContext vyperAST vyperTypeSystem contractABI venomMemDefs
  venomState venomExecSemantics finite_map words list arithmetic

Theorem compile_abi_encode_tuple_output_live:
  ~(LENGTH args = 1 /\ ~ensure) /\ compile_multi_exprs cfn ce args origin = (ops,arg_st) /\
  compile_type_builtin_dispatch_body cfn ce vv_ty ty (AbiEncode ensure method_id) ret_ty args origin =
    (vv,final) ==>
  abi_decoder_operand_live final.cs_next_var (vv_operand vv)
Proof
  strip_tac >> drule_all compile_abi_encode_tuple_trace >> strip_tac >>
  drule abi_builtin_encode_output_live >> strip_tac >>
  gvs[vv_operand_def, mk_ptr_def]
QED

Theorem compile_abi_encode_tuple_producer:
  let tys = MAP expr_type args in
  let xs = ZIP (ops,tys) in
  let ats = vyper_to_abi_types (get_tenv cx) tys in
  let source_size = type_memory_bytes ce (TupleT tys) in
  let maxlen = abi_size_bound ce.ce_struct_fields (TupleT tys) in
  let n = maxlen+LENGTH (abi_encode_method_id_bytes method_id) in
  let bytes = abi_encode_method_id_bytes method_id ++ enc (Tuple ats) (ListV avs) in
  ~(LENGTH args = 1 /\ ~ensure) /\ compile_multi_exprs cfn ce args origin = (ops,arg_st) /\
  compile_type_builtin_dispatch_body cfn ce vv_ty ty (AbiEncode ensure method_id) ret_ty args origin =
    (vv,final) /\ fn_has_code arg_st final func /\
  (arg_st.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  well_typed_type_builtin_args (AbiEncode ensure method_id) (TupleT tys) tys /\ LENGTH vs = LENGTH args /\
  vyper_to_abi (get_tenv cx) (TupleT tys) (ArrayV (TupleV vs)) = SOME (ListV avs) /\
  has_type (Tuple ats) (ListV avs) /\ LENGTH (enc (Tuple ats) (ListV avs)) <= maxlen /\
  abi_tuple_encode_layout ce xs ats /\
  abi_tuple_encode_inputs ce.ce_struct_fields ce xs ats avs arg_st.cs_next_var sb (sb+source_size) prepared /\
  ((FLOOKUP prepared.vs_allocas arg_st.cs_next_id = NONE /\ sb = prepared.vs_alloca_next) \/
    FLOOKUP prepared.vs_allocas arg_st.cs_next_id = SOME (sb,source_size)) /\
  abi_builtin_encode_resources
    (arg_st with cs_next_id := arg_st.cs_next_id+1+abi_tuple_encode_inst_count ce tys)
    (OPTION_MAP bytes_method_id_word method_id) sb source_size p maxlen first last b cap
    (abi_builtin_allocate_state arg_st.cs_next_id source_size prepared) /\
  alloca_next_valid prepared /\ type_memory_bytes ce (BaseT (BytesT (Dynamic n))) < dimword (:256) /\
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st prepared /\
  ~prepared.vs_halted /\ prepared.vs_current_bb = arg_st.cs_current_bb /\
  prepared.vs_inst_idx = LENGTH arg_st.cs_current_insts /\ abi_decode_sim ctx func initial prepared ==>
  ?actual. evaluate_type_builtin cx (AbiEncode ensure method_id) (TupleT tys) vs = INL (BytesV bytes) /\
    vv_location vv = SOME LocMemory /\ eval_operand (vv_operand vv) actual = SOME (n2w p) /\
    mload p actual = n2w (LENGTH bytes) /\ mem_bytes_at (p+32) (LENGTH bytes) actual.vs_memory = bytes /\
    val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bytes) p actual.vs_memory /\
    FLOOKUP actual.vs_allocas (arg_st.cs_next_id+1+abi_tuple_encode_inst_count ce tys) =
      SOME (p,maxlen+32+LENGTH (abi_encode_method_id_bytes method_id)) /\
    abi_builtin_encode_staged_effect first last arg_st final limit_st sb source_size p
      (maxlen+32+LENGTH (abi_encode_method_id_bytes method_id))
      (case method_id of NONE => 0 | SOME _ => 32) b cap prepared actual /\
    (!hi. abi_tuple_encode_input consumer_sf ce (BaseT (BytesT (Dynamic n)))
      (vyper_to_abi_type env (BaseT (BytesT (Dynamic n)))) (contractABI$BytesV bytes)
      (vv_operand vv) final.cs_next_var actual.vs_alloca_next hi actual) /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all (SIMP_RULE bool_ss [LET_THM] compile_abi_encode_tuple_source) >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  drule_all (SIMP_RULE bool_ss [] compile_abi_encode_tuple_output_live) >> strip_tac >>
  `alloca_next_valid (abi_builtin_allocate_state arg_st.cs_next_id
     (type_memory_bytes ce (TupleT (MAP expr_type args))) prepared)` by
    (irule abi_builtin_allocate_next_valid >> simp[]) >>
  drule_all abi_builtin_encode_output_before_scratch >> strip_tac >>
  drule_all abi_builtin_encode_output_bounds >> strip_tac >>
  drule_all abi_builtin_encode_checked_prefix >> strip_tac >>
  qpat_x_assum `abi_builtin_encode_prefix (OPTION_MAP bytes_method_id_word method_id) = _`
    (fn eq => RULE_ASSUM_TAC (PURE_REWRITE_RULE [eq])) >>
  `b <= actual.vs_alloca_next` by
    (qpat_assum `abi_builtin_encode_staged_effect _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (MP_TAC o CONJUNCT2 o PURE_REWRITE_RULE [abi_builtin_encode_staged_effect_def]) >>
     strip_tac >> drule abi_decoder_budget_frontier >> simp[]) >>
  qexists_tac `actual` >> asm_rewrite_tac[] >> gen_tac >>
  irule abi_tuple_encode_owned_bytes_source_input >> asm_rewrite_tac[] >>
  qexists_tac `n2w p:bytes32` >> fs[w2n_n2w, LENGTH_APPEND] >> decide_tac
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_ENCODE_TUPLE_PRODUCER_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI tuple dispatcher producer not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinEncodeTupleProducer");

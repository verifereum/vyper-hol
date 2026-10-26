(* The actual multi-argument/ensure-tuple AbiEncode dispatcher, from argument
   evaluation through staging and complete source-correct ABI encoding. *)
Theory abiBuiltinEncodeTupleCorrect
Ancestors
  abiBuiltinEncodeDispatchCode abiBuiltinEncodeTupleRun abiTupleEncodeEntryResources
  abiTupleEncodeInput abiTupleEncodeLayout abiTupleEncodeMemory abiTupleEncodeCounters abiTupleProps
  abiBuiltinEncodeStagedEffect abiBuiltinEncodeResources abiBuiltinAllocationState
  abiDecoderContract abiDecoderLoop exprLowering exprLoweringProps builtinAbi
  fragExec compileEnv context valueEncoding vyperABI vyperContext vyperAST vyperTypeSystem
  contractABI venomState venomExecSemantics finite_map words list arithmetic

Theorem compile_abi_encode_tuple_source:
  let tys = MAP expr_type args in
  let xs = ZIP (ops,tys) in
  let ats = vyper_to_abi_types (get_tenv cx) tys in
  let source_size = type_memory_bytes ce (TupleT tys) in
  let maxlen = abi_size_bound ce.ce_struct_fields (TupleT tys) in
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
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st prepared /\
  ~prepared.vs_halted /\ prepared.vs_current_bb = arg_st.cs_current_bb /\
  prepared.vs_inst_idx = LENGTH arg_st.cs_current_insts /\ abi_decode_sim ctx func initial prepared ==>
  ?actual. evaluate_type_builtin cx (AbiEncode ensure method_id) (TupleT tys) vs = INL (BytesV bytes) /\
    vv_location vv = SOME LocMemory /\ eval_operand (vv_operand vv) actual = SOME (n2w p) /\
    mload p actual = n2w (LENGTH bytes) /\ mem_bytes_at (p+32) (LENGTH bytes) actual.vs_memory = bytes /\
    val_in_memory (BaseTV (BytesT (Dynamic (maxlen+LENGTH (abi_encode_method_id_bytes method_id)))))
      (BytesV bytes) p actual.vs_memory /\
    FLOOKUP actual.vs_allocas (arg_st.cs_next_id+1+abi_tuple_encode_inst_count ce tys) =
      SOME (p,maxlen+32+LENGTH (abi_encode_method_id_bytes method_id)) /\
    abi_builtin_encode_staged_effect first last arg_st final limit_st sb source_size p
      (maxlen+32+LENGTH (abi_encode_method_id_bytes method_id))
      (case method_id of NONE => 0 | SOME _ => 32) b cap prepared actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all (SIMP_RULE bool_ss [] compile_abi_encode_tuple_trace) >> strip_tac >>
  rename1 `compile_alloc_buffer _ arg_st = (source_buf,allocated)` >>
  rename1 `compile_store_abi_tuple _ _ _ _ allocated = ((),staged)` >>
  rename1 `lower_abi_encode _ _ _ _ _ staged = (out,final)` >>
  `LENGTH ops = LENGTH args` by
    (mp_tac (Q.SPECL [`args`, `cfn`, `ce`, `origin`] compile_multi_exprs_length) >> asm_simp_tac (srw_ss()) []) >>
  `MAP SND (ZIP (ops,MAP expr_type args)) = MAP expr_type args` by asm_simp_tac (srw_ss()) [MAP_ZIP] >>
  `abi_tuple_bytes ce (ZIP (ops,MAP expr_type args)) = type_memory_bytes ce (TupleT (MAP expr_type args))` by
    (mp_tac (Q.ISPECL [`ops:operand list`, `MAP expr_type args`] abi_tuple_encode_bytes_zip) >>
     impl_tac >- asm_simp_tac (srw_ss()) [] >> simp[]) >>
  `LENGTH (ZIP (ops,MAP expr_type args)) = LENGTH args` by asm_simp_tac (srw_ss()) [] >>
  `abi_builtin_encode_resources staged (OPTION_MAP bytes_method_id_word method_id)
    sb (type_memory_bytes ce (TupleT (MAP expr_type args))) p
    (abi_size_bound ce.ce_struct_fields (TupleT (MAP expr_type args))) first last b cap
    (abi_builtin_allocate_state arg_st.cs_next_id (type_memory_bytes ce (TupleT (MAP expr_type args))) prepared)` by
    (drule_all abi_tuple_encode_resources_site >> disch_then (fn th => rewrite_tac [th]) >>
     asm_simp_tac (srw_ss()) []) >>
  qpat_assum `MAP SND (ZIP (ops,MAP expr_type args)) = _` (fn tys_eq =>
    qpat_assum `abi_tuple_bytes ce (ZIP (ops,MAP expr_type args)) = _` (fn size_eq =>
      qpat_assum `LENGTH (ZIP (ops,MAP expr_type args)) = _` (fn len_eq =>
        mp_tac (SIMP_RULE bool_ss [LET_THM, tys_eq, size_eq, len_eq]
          (Q.INST [`xs` |-> `ZIP (ops,MAP expr_type args)`, `st` |-> `arg_st`,
            `initial` |-> `prepared:venom_state`,
            `maxlen` |-> `abi_size_bound ce.ce_struct_fields (TupleT (MAP expr_type args))`]
            lower_abi_encode_tuple_source))))) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  rename1 `abi_decode_sim ctx func prepared actual` >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) [vv_location_def, vv_operand_def, mk_ptr_def] >>
  irule abi_decode_sim_trans >> qexists_tac `prepared` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_ENCODE_TUPLE_CORRECT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI builtin tuple dispatcher correctness not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinEncodeTupleCorrect");

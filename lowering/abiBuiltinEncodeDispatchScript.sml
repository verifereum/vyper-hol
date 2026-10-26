Theory abiBuiltinEncodeDispatch
Ancestors
  abiBuiltinDispatchCorrect exprLowering builtinAbi compileEnv context words list arithmetic
  abiBuiltinEncodeSource abiBuiltinEncodeInput abiBuiltinEncodeEffect abiDecoderContract
  abiDecoderLoop fragExec valueEncoding vyperABI vyperContext vyperAST vyperTypeSystem
  contractABI venomState venomExecSemantics

(* ===== Code ===== *)

(* Exact compiler traces for all three AbiEncode dispatcher paths. *)

Theorem compile_abi_encode_memory_trace:
  ~is_word_type (expr_type e) /\
  cfn ce (expr_type e) e origin = (LocatedValue (expr_type e) srcptr,ready) /\
  srcptr.ptr_location = LocMemory /\
  compile_type_builtin_dispatch_body cfn ce vv_ty ty (AbiEncode F method_id) ret_ty [e] origin =
    (vv,final) ==>
  ?out. lower_abi_encode F (OPTION_MAP bytes_method_id_word method_id) srcptr.ptr_operand
      (type_to_abi_enc_info ce.ce_struct_fields ce (expr_type e))
      (abi_size_bound ce.ce_struct_fields (expr_type e)) ready = (out,final) /\
    vv = LocatedValue vv_ty (mk_ptr out LocMemory)
Proof
  strip_tac >>
  gvs[compile_type_builtin_dispatch_body_def, unwrap_value_def, comp_return_def, LET_THM] >>
  drule as_ptr_val_result >> simp[]
QED

Theorem compile_abi_encode_word_trace:
  is_word_type (expr_type e) /\
  lower_value cfn ce (expr_type e) e origin = (value_op,arg_st) /\
  compile_type_builtin_dispatch_body cfn ce vv_ty ty (AbiEncode F method_id) ret_ty [e] origin =
    (vv,final) ==>
  ?buf allocated staged out.
    compile_alloc_buffer 32 arg_st = (buf,allocated) /\
    emit_void MSTORE [buf.buf_operand;value_op] allocated = ((),staged) /\
    lower_abi_encode F (OPTION_MAP bytes_method_id_word method_id) buf.buf_operand
      (type_to_abi_enc_info ce.ce_struct_fields ce (expr_type e))
      (abi_size_bound ce.ce_struct_fields (expr_type e)) staged = (out,final) /\
    vv = LocatedValue vv_ty (mk_ptr out LocMemory)
Proof
  strip_tac >>
  gvs[compile_type_builtin_dispatch_body_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `compile_alloc_buffer 32 arg_st = (buf,allocated)` >>
  rename1 `emit_void MSTORE [buf.buf_operand;value_op] allocated = ((),staged)` >>
  drule as_ptr_val_result >> strip_tac >>
  rename1 `lower_abi_encode _ _ _ _ _ staged = (out,final)` >>
  qexists_tac `out` >> simp[]
QED

Theorem compile_abi_encode_tuple_trace:
  ~(LENGTH args = 1 /\ ~ensure) /\
  compile_multi_exprs cfn ce args origin = (ops,arg_st) /\
  compile_type_builtin_dispatch_body cfn ce vv_ty ty (AbiEncode ensure method_id) ret_ty args origin =
    (vv,final) ==>
  ?buf allocated staged out.
    compile_alloc_buffer (type_memory_bytes ce (TupleT (MAP expr_type args))) arg_st = (buf,allocated) /\
    compile_store_abi_tuple ce buf.buf_operand 0 (ZIP (ops,MAP expr_type args)) allocated = ((),staged) /\
    lower_abi_encode ensure (OPTION_MAP bytes_method_id_word method_id) buf.buf_operand
      (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP expr_type args)))
      (abi_size_bound ce.ce_struct_fields (TupleT (MAP expr_type args))) staged = (out,final) /\
    vv = LocatedValue vv_ty (mk_ptr out LocMemory)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `compile_type_builtin_dispatch_body _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [compile_type_builtin_dispatch_body_def, LET_THM] >> strip_tac >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `compile_alloc_buffer _ arg_st = (buf,allocated)` >>
  rename1 `compile_store_abi_tuple _ _ _ _ allocated = ((),staged)` >>
  drule as_ptr_val_result >> strip_tac >>
  rename1 `lower_abi_encode _ _ _ _ _ staged = (out,final)` >>
  qexists_tac `out` >> simp[]
QED

(* ===== Correct ===== *)

(* Compose argument evaluation with the actual singleton memory AbiEncode path.
   Source conversion and complete memory/resource predicates are explicit. *)

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

(* Source semantics of tuple allocation, all staging writes and full ABI
   encoding. Preconditions describe evaluated arguments and pure resources. *)
Theory abiBuiltinEncodeTupleRun
Ancestors
  abiTupleEncodePrepare abiTupleEncodeContext abiTupleEncodeInput abiTupleEncodeLayout abiTupleProps
  abiBuiltinEncodeSourceCorrect abiBuiltinEncodeSourceModel abiBuiltinEncodeStagedEffect
  abiBuiltinEncodeResources abiBuiltinAllocationState abiDecoderReentry abiDecoderContract abiDecoderLoop
  builtinAbi exprLowering fragExec compileEnv valueEncoding vyperABI vyperContext
  vyperAST vyperTypeSystem contractABI venomState venomExecSemantics finite_map words list arithmetic

Theorem lower_abi_encode_tuple_source:
  let tys = MAP SND xs in
  let ats = vyper_to_abi_types (get_tenv cx) tys in
  let bytes = abi_encode_method_id_bytes method_id ++ enc (Tuple ats) (ListV avs) in
  ~(LENGTH xs = 1 /\ ~ensure) /\
  compile_alloc_buffer (abi_tuple_bytes ce xs) st = (source_buf,allocated) /\
  compile_store_abi_tuple ce source_buf.buf_operand 0 xs allocated = ((),staged) /\
  lower_abi_encode ensure (OPTION_MAP bytes_method_id_word method_id) source_buf.buf_operand
    (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT tys)) maxlen staged = (out,final) /\
  fn_has_code st final func /\
  (st.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  well_typed_type_builtin_args (AbiEncode ensure method_id) (TupleT tys) tys /\ LENGTH vs = LENGTH xs /\
  vyper_to_abi (get_tenv cx) (TupleT tys) (ArrayV (TupleV vs)) = SOME (ListV avs) /\
  has_type (Tuple ats) (ListV avs) /\ LENGTH (enc (Tuple ats) (ListV avs)) <= maxlen /\
  abi_tuple_encode_layout ce xs ats /\
  abi_tuple_encode_inputs ce.ce_struct_fields ce xs ats avs st.cs_next_var sb (sb+abi_tuple_bytes ce xs) initial /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ sb = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (sb,abi_tuple_bytes ce xs)) /\
  abi_builtin_encode_resources staged (OPTION_MAP bytes_method_id_word method_id)
    sb (abi_tuple_bytes ce xs) p maxlen first last b cap
    (abi_builtin_allocate_state st.cs_next_id (abi_tuple_bytes ce xs) initial) /\
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. evaluate_type_builtin cx (AbiEncode ensure method_id) (TupleT tys) vs = INL (BytesV bytes) /\
    eval_operand out actual = SOME (n2w p) /\ mload p actual = n2w (LENGTH bytes) /\
    mem_bytes_at (p+32) (LENGTH bytes) actual.vs_memory = bytes /\
    val_in_memory (BaseTV (BytesT (Dynamic (maxlen+LENGTH (abi_encode_method_id_bytes method_id)))))
      (BytesV bytes) p actual.vs_memory /\
    FLOOKUP actual.vs_allocas (st.cs_next_id+1+abi_tuple_encode_inst_count ce tys) =
      SOME (p,maxlen+32+LENGTH (abi_encode_method_id_bytes method_id)) /\
    abi_builtin_encode_staged_effect first last st final limit_st sb (abi_tuple_bytes ce xs) p
      (maxlen+32+LENGTH (abi_encode_method_id_bytes method_id))
      (case method_id of NONE => 0 | SOME _ => 32) b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_tuple_encode_context >> strip_tac >>
  `staged.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all abi_tuple_encode_prepare >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial staged_state` >>
  `abi_builtin_encode_type ensure (MAP SND xs) = TupleT (MAP SND xs) /\
   abi_builtin_encode_value ensure (MAP SND xs) vs = ArrayV (TupleV vs)` by
    (Cases_on `LENGTH xs = 1` >> gvs[abi_builtin_encode_type_def, abi_builtin_encode_value_def]) >>
  qpat_assum `abi_builtin_encode_type _ _ = _` (fn ty_eq =>
    qpat_assum `abi_builtin_encode_value _ _ _ = _` (fn value_eq =>
      mp_tac (SIMP_RULE bool_ss [LET_THM, ty_eq, value_eq, vyper_to_abi_type_def, LENGTH_MAP]
        (Q.INST [`tys` |-> `MAP SND (xs:(operand # type) list)`, `av` |-> `ListV avs`,
          `src` |-> `source_buf.buf_operand`, `start` |-> `staged`, `initial` |-> `staged_state:venom_state`,
          `source_cap` |-> `abi_tuple_bytes ce (xs:(operand # type) list)`] lower_abi_encode_source)))) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, asm_simp_tac bool_ss []]) >>
  strip_tac >> rename1 `abi_decode_sim ctx func staged_state actual` >>
  `abi_builtin_encode_staged_effect first last st final limit_st sb (abi_tuple_bytes ce xs) p
    (maxlen+32+LENGTH (abi_encode_method_id_bytes method_id))
    (case method_id of NONE => 0 | SOME _ => 32) b cap initial actual` by
    (irule abi_builtin_encode_producer_compose >> qexistsl_tac [`staged_state`, `staged`] >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  qpat_assum `staged.cs_next_id = _` (fn site_eq =>
    qpat_assum `FLOOKUP actual.vs_allocas staged.cs_next_id = _`
      (assume_tac o PURE_REWRITE_RULE [site_eq])) >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) [] >>
  irule abi_decode_sim_trans >> qexists_tac `staged_state` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_ENCODE_TUPLE_RUN_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI builtin tuple encoding not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinEncodeTupleRun");

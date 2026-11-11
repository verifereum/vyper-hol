(* Dispatcher tuple staging: the source and memory continuation share an endpoint. *)
Theory bodyAbiEncodeTupleMemory
Ancestors
  abiBuiltinEncodeWord abiTupleEncodeMemoryChecks abiTupleEncodeMemoryReach
  abiTupleEncodePrepare abiTupleEncodeLayout abiTupleEncodeMemory fragExec compileEnv exprLoweringProps
  abiBuiltinAllocation abiDecoderContract abiDecoderReentry memContinuation
  abiEncoderWindow valueEncoding contractABI words list arithmetic

Theorem abi_encode_tuple_source_window_mem:
  let xs = ZIP (ops,MAP expr_type args) in
  let n = abi_tuple_bytes ce xs in
  ~(LENGTH args = 1 /\ ~ensure) /\
  compile_abi_encode_args cfn ce args origin = (ops,arg_st) /\
  compile_type_builtin_dispatch_body cfn ce vv_ty ty (AbiEncode ensure method_id) ret_ty args origin =
    (vv,final) /\ fn_has_code arg_st final func /\
  abi_tuple_encode_layout ce xs ats /\ has_type (Tuple ats) (ListV avs) /\
  abi_tuple_encode_inputs ce.ce_struct_fields ce xs ats avs arg_st.cs_next_var sb (sb+n) initial /\
  ((FLOOKUP initial.vs_allocas arg_st.cs_next_id = NONE /\ sb = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas arg_st.cs_next_id = SOME (sb,n)) /\
  sb+n < dimword (:256) /\ alloca_next_valid initial /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  EVERY (\(op,ty). ~is_word_type ty ==> ?p. eval_operand op initial = SOME (n2w p) /\
    p < dimword (:256) /\ p+type_memory_bytes ce ty <= initial.vs_alloca_next) xs /\
  ~initial.vs_halted /\ initial.vs_current_bb = arg_st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH arg_st.cs_current_insts ==>
  ?buf allocated staged out actual.
    compile_alloc_buffer n arg_st = (buf,allocated) /\
    compile_store_abi_tuple ce buf.buf_operand 0 xs allocated = ((),staged) /\
    lower_abi_encode ensure (OPTION_MAP bytes_method_id_word method_id) buf.buf_operand
      (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP expr_type args)))
      (abi_size_bound ce.ce_struct_fields (TupleT (MAP expr_type args))) staged = (out,final) /\
    vv = LocatedValue vv_ty (mk_ptr out LocMemory) /\
    fn_has_code arg_st staged func /\ fn_has_code staged final func /\
    staged.cs_next_var <= final.cs_next_var /\ staged.cs_next_id <= final.cs_next_id /\
    eval_operand buf.buf_operand actual = SOME (n2w sb) /\
    abi_decoder_operand_live staged.cs_next_var buf.buf_operand /\
    abi_encoder_window_input (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP SND xs)))
      (Tuple ats) (ListV avs) sb n actual.vs_memory /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame sb n initial actual /\
    actual.vs_allocas = (abi_builtin_allocate_state arg_st.cs_next_id n initial).vs_allocas /\
    actual.vs_alloca_next = (abi_builtin_allocate_state arg_st.cs_next_id n initial).vs_alloca_next /\
    (!op w. abi_decoder_operand_live arg_st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_current_bb = staged.cs_current_bb /\ actual.vs_inst_idx = LENGTH staged.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual /\ mem_cont_sim ctx func initial actual
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all (SIMP_RULE bool_ss [] compile_abi_encode_tuple_trace) >> strip_tac >>
  rename1 `compile_alloc_buffer _ arg_st = (buf,allocated)` >>
  rename1 `compile_store_abi_tuple _ _ _ _ allocated = ((),staged)` >>
  `LENGTH ops = LENGTH args` by
    (qspecl_then [`args`, `cfn`, `ce`, `origin`] mp_tac compile_abi_encode_args_length >> simp[]) >>
  `abi_tuple_bytes ce (ZIP (ops,MAP expr_type args)) = type_memory_bytes ce (TupleT (MAP expr_type args))` by
    (irule abi_tuple_encode_bytes_zip >> simp[]) >>
  drule_all abi_tuple_encode_stage_shape >> strip_tac >>
  drule lower_abi_encode_extends >> strip_tac >>
  `cs_extends arg_st staged` by (simp[cs_extends_def] >> metis_tac[]) >>
  drule_all fn_has_code_split >> strip_tac >>
  `staged.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  qpat_assum `abi_tuple_bytes ce _ = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM th])) >>
  drule_all abi_tuple_encode_stage_mem_ok >> strip_tac >>
  drule_all abi_tuple_encode_stage_reach_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all abi_tuple_encode_window_input >> strip_tac >>
  qexistsl_tac [`buf`, `allocated`, `staged`, `out`, `actual`] >> simp[]
QED

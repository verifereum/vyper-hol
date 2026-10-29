Theory abiBuiltinEncodeTuple
Ancestors
  abiTupleEncodePrepare abiTupleEncodeContext abiTupleEncodeInput abiTupleEncodeLayout
  abiTupleProps abiBuiltinEncodeSource abiBuiltinEncodeStagedEffect abiBuiltinEncodeResources
  abiBuiltinAllocation abiDecoderReentry abiDecoderContract abiDecoderLoop builtinAbi
  exprLowering fragExec compileEnv valueEncoding vyperABI vyperContext vyperAST vyperTypeSystem
  contractABI venomState venomExecSemantics finite_map words list arithmetic
  abiBuiltinEncodeDispatch abiTupleEncodeEntryResources abiTupleEncodeMemory
  abiTupleEncodeCounters exprLoweringProps context abiBuiltinEncodeProducer
  abiTupleEncodeOwnedBytes abiDecoderFootprint venomMemDefs

(* ===== Run ===== *)

(* Source semantics of tuple allocation, all staging writes and full ABI
   encoding. Preconditions describe evaluated arguments and pure resources. *)

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
  ?actual. evaluate_type_builtin cx (AbiEncode ensure method_id) (TupleT tys) arg_tys vs = INL (BytesV bytes) /\
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

(* ===== Correct ===== *)

(* The actual multi-argument/ensure-tuple AbiEncode dispatcher, from argument
   evaluation through staging and complete source-correct ABI encoding. *)

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
  ?actual. evaluate_type_builtin cx (AbiEncode ensure method_id) (TupleT tys) arg_tys vs = INL (BytesV bytes) /\
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

(* ===== Producer ===== *)

(* Actual multi-argument AbiEncode results are live, owned tuple inputs.
   Separation follows from allocation credit, without a final-layout premise. *)

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
  ?actual. evaluate_type_builtin cx (AbiEncode ensure method_id) (TupleT tys) arg_tys vs = INL (BytesV bytes) /\
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
  drule_all (SIMP_RULE bool_ss [LET_THM] compile_abi_encode_tuple_source) >>
  disch_then (qspec_then `arg_tys` strip_assume_tac) >>
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

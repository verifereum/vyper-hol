Theory exprSimAbiEncodeTupleCompletion
Ancestors
  exprSimAbiEncodeTupleResult exprSimAbiEncodeTupleExecution
  exprSimAbiEncodeTupleSuccess exprSimAbiEncodeProducerAssembly
  abiEncoderAdmissible abiEncoderCounters abiBuiltinEncodeCode
  abiBuiltinEncodeContext exprSimAbiEncodeTupleResources abiTupleEncodePrepare
  abiBuiltinEncodeSource exprSimHypsDefs vyperTypeSystem vyperAST
  fragGasMode loweringPosts exprSimProps compileEnv vyperState abiEncodeArgsSim
  localPtrsProps instIdxIndep exprLoweringProps
  exprSimAbiEncodeTupleCounted abiDecoderContract vyperABI pred_set
  abiDecoderMembers abiDecoderReentry exprSimAggregateChildren
  vyperTypeInvariants exprSimDefs vyperABIValid vyperContext
  exprSimAbiEncodeRuntimeInputs vyperTypeExprSoundness vyperTypeDefaults
  words list finite_map arithmetic

Theorem abi_encode_tuple_counted_success:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid0) target args) es /\
  ~(LENGTH args = 1 /\ ~ensure) /\ mid = OPTION_MAP bytes_method_id_word mid0 /\
  eval_exprs cx args es = (INL vs,es') /\
  evaluate_type_builtin cx (AbiEncode ensure mid0) target (MAP expr_type args) vs = INL result /\
  abi_args_post ctx func ce cx es origin st s0 es' args values vs initial /\
  EVERY (abi_decoder_operand_live st.cs_next_var) values /\
  compile_alloc_buffer (abi_tuple_bytes ce (ZIP (values,MAP expr_type args))) st = (buf,allocated) /\
  compile_store_abi_tuple ce buf.buf_operand 0 (ZIP (values,MAP expr_type args)) allocated = ((),staged) /\
  ei = type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP expr_type args)) /\
  lower_abi_encode ensure mid buf.buf_operand ei
    (abi_size_bound ce.ce_struct_fields (TupleT (MAP expr_type args))) staged = (out,final) /\
  fn_has_code st allocated func /\ fn_has_code st staged func /\
  fn_has_code staged final func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce origin /\ local_ptrs_reserved ce st /\
  origin.cs_next_var <= st.cs_next_var /\ origin.cs_next_id <= st.cs_next_id /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  fresh_vars_wrt final initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. gas_marked_path F ctx func initial 0 (OK actual) /\
    ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    vv_post ctx func ce cx (TypeBuiltin ann (AbiEncode ensure mid0) target args)
      es origin final s0 es' (Value result)
      (LocatedValue (expr_type (TypeBuiltin ann (AbiEncode ensure mid0) target args))
        <|ptr_operand := out; ptr_location := LocMemory|>) actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule lower_abi_encode_trace >> strip_tac >>
  drule_all abi_builtin_encode_code >> strip_tac >>
  drule_all abi_encode_args_tuple_allocation_resources >>
  simp_tac bool_ss [LET_THM] >>
  disch_then (qx_choose_then `sb` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  drule_all abi_tuple_encode_stage_shape >> strip_tac >>
  `staged.cs_next_var <= final.cs_next_var` by decide_tac >>
  drule_all abi_encode_args_staged_source >>
  disch_then (qx_choose_then `raw` (qx_choose_then `avs` (qx_choose_then `ct`
    (qx_choose_then `rv` (MAP_EVERY assume_tac o CONJUNCTS))))) >>
  drule_all abi_encode_tuple_staging_path >> strip_tac >>
  `stmt_state_rel ctx func ce cx es' initial /\
   wb_frame ce es origin s0 initial` by fs[abi_args_post_def] >>
  `abi_tuple_bytes ce (ZIP (values,MAP expr_type args)) < dimword (:256)` by decide_tac >>
  `FLOOKUP raw.vs_allocas st.cs_next_id =
    SOME (sb,abi_tuple_bytes ce (ZIP (values,MAP expr_type args)))` by metis_tac[] >>
  drule_all abi_encode_tuple_staging_cursor >> strip_tac >>
  qabbrev_tac `s = raw with vs_inst_idx := LENGTH staged.cs_current_insts` >>
  `local_ptrs_reserved ce staged` by
    (irule local_ptrs_reserved_next_var >> qexists `st` >> simp[]) >>
  `s.vs_allocas = raw.vs_allocas /\ s.vs_alloca_next = raw.vs_alloca_next /\
   s.vs_memory = raw.vs_memory /\ fresh_vars_wrt final s /\
   eval_operand buf.buf_operand s = SOME (n2w sb) /\
   ~s.vs_halted /\ s.vs_current_bb = staged.cs_current_bb /\
   s.vs_inst_idx = LENGTH staged.cs_current_insts` by
    (simp[Abbr `s`, eval_op_inst_idx] >>
     qpat_assum `fresh_vars_wrt final raw` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[fresh_vars_wrt_def]) >>
  `abi_encoder_open_input ei ct rv sb (abi_tuple_bytes ce (ZIP (values,MAP expr_type args)))
     s.vs_memory` by metis_tac[] >>
  `enc ct rv = enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP expr_type args))) (ListV avs)` by
    asm_rewrite_tac [vyper_to_abi_types_MAP, MAP_MAP_o] >>
  `abi_encoder_admissible ei` by metis_tac[abi_encoder_translation_admissible] >>
  drule_all buffer_alloc_provenance >> strip_tac >>
  `(!l. buf.buf_operand <> Label l)` by simp[] >>
  `(!x. buf.buf_operand = Var x ==> not_fresh_at staged x)` by
    (qpat_assum `abi_decoder_operand_live staged.cs_next_var buf.buf_operand` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `buf.buf_operand` >>
     simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def, IN_DEF]) >>
  `stmt_state_rel ctx func ce cx es' s /\ wb_frame ce es origin s0 s` by
    (simp_tac bool_ss [Abbr `s`] >> asm_rewrite_tac []) >>
  `s.vs_allocas = (abi_builtin_allocate_state st.cs_next_id
     (abi_tuple_bytes ce (ZIP (values,MAP expr_type args))) initial).vs_allocas /\
   s.vs_alloca_next = (abi_builtin_allocate_state st.cs_next_id
     (abi_tuple_bytes ce (ZIP (values,MAP expr_type args))) initial).vs_alloca_next /\
   FLOOKUP s.vs_allocas st.cs_next_id = SOME(sb,abi_tuple_bytes ce (ZIP (values,MAP expr_type args)))` by
    metis_tac[] >>
  drule_all abi_encode_tuple_counted_encoder >>
  disch_then (qx_choose_then `p` (qx_choose_then `actual` (MAP_EVERY assume_tac o CONJUNCTS))) >>
  suspend "result"
QED

Resume abi_encode_tuple_counted_success[result]:
  `?N. expr_type (TypeBuiltin ann (AbiEncode ensure mid0) target args) = BaseT (BytesT (Dynamic N)) /\
    target = TupleT (MAP expr_type args) /\
    vyper_abi_size_bound (get_tenv cx) (TupleT (MAP expr_type args)) + abi_encode_method_id_size mid0 <= N` by
    (qpat_assum `expr_body_pre _ _ _ _ _` mp_tac >>
     qpat_assum `~(LENGTH args = 1 /\ ~ensure)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[expr_body_pre_def, well_typed_expr_def, type_builtin_result_ok_def, abi_encode_size_ok_def] >>
     strip_tac >> strip_tac >>
     `env.type_defs = get_tenv cx` by
       fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
     Cases_on `args` >> gvs[expr_type_def] >>
     Cases_on `t` >> gvs[expr_type_def]) >>
  `LENGTH (enc ct rv) <= vyper_abi_size_bound (get_tenv cx) (TupleT (MAP expr_type args))` by
    (drule_all abi_encode_body_args_runtime_typed >>
     simp_tac (srw_ss()) [exprs_runtime_typed_def] >> strip_tac >>
     `LIST_REL (\ty tv. evaluate_type (get_tenv cx) ty = SOME tv)
        (MAP expr_type args) tvs` by gvs[LIST_REL_MAP1, combinTheory.o_DEF] >>
     `values_have_types tvs vs` by simp[values_have_types_LIST_REL] >>
     drule_all (cj 2 vyper_to_abi_enc_le_size_bound) >>
     qpat_assum `enc ct rv = enc (Tuple (vyper_to_abi_types _ _)) _`
       (fn th => rewrite_tac[th]) >> simp[]) >>
  `LENGTH (abi_encode_method_id_bytes mid0 ++ enc ct rv) <= N` by
    (qpat_assum `LENGTH (enc ct rv) <= _` mp_tac >>
     qpat_assum `vyper_abi_size_bound _ _ + _ <= N` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[abi_encode_method_id_size_def] >> decide_tac) >>
  `result = BytesV (abi_encode_method_id_bytes mid0 ++ enc ct rv)` by
    (qpat_assum `evaluate_type_builtin _ _ _ _ _ = _` mp_tac >>
     qpat_assum `vyper_to_abi_list _ _ _ = _` mp_tac >>
     qpat_assum `enc ct rv = enc (Tuple (vyper_to_abi_types _ _)) _` mp_tac >>
     qpat_assum `target = TupleT _` mp_tac >>
     qpat_assum `~(LENGTH args = 1 /\ ~ensure)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[evaluate_type_builtin_def, needs_external_call_wrap_def,
       evaluate_abi_encode_bytes_def, vyper_to_abi_def] >>
     Cases_on `args` >- (Cases_on `ensure` >> simp[]) >>
     simp[] >> Cases_on `t` >> simp[]) >>
  `origin.cs_next_var <= staged.cs_next_var /\ origin.cs_next_id <= staged.cs_next_id` by decide_tac >>
  drule_all abi_encode_tuple_observation_vv_post >> disch_tac >>
  qexists `actual` >>
  reverse conj_tac >- metis_tac[] >>
  `gas_marked_path F ctx func initial 0 (OK s)` by
    (simp_tac bool_ss [Abbr `s`] >> asm_rewrite_tac []) >>
  `0 = 0 + 0` by simp[] >> pop_assum (fn th => once_rewrite_tac[th]) >>
  irule gas_marked_path_then >> qexists `s` >> asm_rewrite_tac []
QED

Finalise abi_encode_tuple_counted_success

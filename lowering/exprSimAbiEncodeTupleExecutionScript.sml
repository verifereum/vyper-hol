Theory exprSimAbiEncodeTupleExecution
Ancestors
  exprSimAbiEncodeTupleResources exprSimAbiEncodeExecution exprSimAbiEncodeProducerAssembly
  exprSimAbiEncodeProducerExecution abiTupleEncodePrepare abiEncoderSequence
  abiEncoderAdmissible abiEncoderCounters abiBuiltinEncodeCode abiDecoderContract
  abiDecoderReentry abiBuiltinEncodeContext exprLoweringProps instIdxIndep venomState venomInst
  exprSimAbiEncodeWindowRoom abiDecoderLoop
  compileEnv vyperABI abiDecoderMembers words finite_map list arithmetic

Theorem abi_encode_args_producer_phases:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid0) target args) es /\
  ~(LENGTH args = 1 /\ ~ensure) /\ mid = OPTION_MAP bytes_method_id_word mid0 /\
  eval_exprs cx args es = (INL vs,es') /\
  evaluate_type_builtin cx (AbiEncode ensure mid0) target (MAP expr_type args) vs = INL result /\
  abi_args_post ctx func ce cx es origin st s0 es' args values vs initial /\
  EVERY (abi_decoder_operand_live st.cs_next_var) values /\
  compile_alloc_buffer (abi_tuple_bytes ce (ZIP (values,MAP (lowered_value_type ce) args))) st = (buf,allocated) /\
  compile_store_abi_tuple ce buf.buf_operand 0 (ZIP (values,MAP (lowered_value_type ce) args)) allocated = ((),staged) /\
  ei = type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP (lowered_value_type ce) args)) /\
  abi_builtin_encode_setup mid (abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args)))
    staged = (ops,ready) /\
  compile_abi_encode_to_buf (SND ops) buf.buf_operand ei ready = (len,body_end) /\
  abi_builtin_encode_finish (FST ops) len (case mid of NONE => 0 | SOME _ => 4) body_end = ((),final) /\
  fn_has_code st allocated func /\ fn_has_code staged ready func /\
  fn_has_code st staged obs /\ fn_has_code staged ready obs /\
  fn_has_code ready body_end obs /\ fn_has_code body_end final obs /\
  fn_inst_ids_distinct obs /\ fn_inst_ids_distinct func /\ obs.fn_name = func.fn_name /\
  (!j. MEM j (fn_insts obs) /\ j.inst_opcode <> STOP /\ j.inst_opcode <> NOP ==>
    MEM j (fn_insts func)) /\
  (!j. MEM j (fn_insts obs) ==> j.inst_opcode <> INVOKE) /\ local_ptrs_reserved ce st ==>
  !limit_st. staged.cs_next_var <= limit_st.cs_next_var /\
    ready.cs_next_var <= limit_st.cs_next_var /\ body_end.cs_next_var <= limit_st.cs_next_var /\
    final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
    ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
    initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?avs p actual.
    vyper_to_abi_list (get_tenv cx) (MAP expr_type args) vs = SOME avs /\
    let bytes = enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP expr_type args))) (ListV avs) in
    let m = case mid of NONE => 0 | SOME _ => 4 in
    eval_operand (FST ops) actual = SOME (n2w p) /\
    mload p actual = n2w (LENGTH bytes+m) /\
    mem_bytes_at (p+32+m) (LENGTH bytes) actual.vs_memory = bytes /\
    (case mid of NONE => T | SOME selector =>
      mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes selector) /\
    ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\ abi_decode_sim ctx obs initial actual
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all abi_encode_args_tuple_allocation_resources >>
  simp_tac bool_ss [LET_THM] >>
  disch_then (qx_choose_then `sb` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  drule_all abi_encode_args_staged_source >>
  disch_then (qx_choose_then `raw` (qx_choose_then `avs` (qx_choose_then `ct`
    (qx_choose_then `rv` (MAP_EVERY assume_tac o CONJUNCTS))))) >>
  drule_all abi_tuple_encode_stage_shape >> strip_tac >>
  drule_all abi_encoder_run_sequence_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `~t.vs_halted /\ fresh_vars_wrt limit_st t /\
   eval_operand buf.buf_operand t = SOME (n2w sb) /\
   t.vs_allocas = raw.vs_allocas /\ t.vs_alloca_next = raw.vs_alloca_next /\
   t.vs_memory = raw.vs_memory` by
    (qpat_assum `t = _` (fn th => pure_rewrite_tac [th]) >>
     simp_tac (srw_ss()) [eval_op_inst_idx] >>
     asm_rewrite_tac [] >>
     qpat_assum `fresh_vars_wrt limit_st raw` mp_tac >>
     simp_tac (srw_ss()) [fresh_vars_wrt_def]) >>
  `FLOOKUP t.vs_allocas st.cs_next_id =
    SOME (sb,abi_tuple_bytes ce (ZIP (values,MAP (lowered_value_type ce) args)))` by metis_tac[] >>
  `abi_encoder_open_input ei ct rv sb (abi_tuple_bytes ce (ZIP (values,MAP (lowered_value_type ce) args)))
     t.vs_memory` by metis_tac[] >>
  `enc ct rv = enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP expr_type args))) (ListV avs)` by
    (asm_rewrite_tac [vyper_to_abi_types_MAP, MAP_MAP_o]) >>
  drule_at (Pat `abi_encoder_open_input _ _ _ _ _ _`) abi_encode_args_phase_resources >>
  disch_then (drule_at (Pat `abi_args_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `compile_abi_encode_to_buf _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `expr_body_pre _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `abi_builtin_encode_setup _ _ _ = _`)) >>
  disch_then (drule_at (Pat `fn_has_code ready body_end _`)) >>
  disch_then (drule_at (Pat `vyper_to_abi_list _ _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  (impl_tac >- (asm_rewrite_tac [] >> metis_tac[])) >>
  simp_tac bool_ss [LET_THM] >>
  disch_then (qx_choose_then `p` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `abi_encoder_admissible ei` by metis_tac[abi_encoder_translation_admissible] >>
  drule abi_builtin_encode_setup_live >> strip_tac >>
  drule abi_builtin_encode_setup_shape >> strip_tac >>
  drule abi_encoder_counters >> strip_tac >>
  `abi_decoder_operand_live ready.cs_next_var buf.buf_operand` by
    (irule abi_decoder_operand_live_mono >> qexists `staged.cs_next_var` >>
     conj_tac >- (qpat_assum `ready.cs_next_var = _` (fn th => rewrite_tac[th]) >>
       Cases_on `mid` >> simp_tac (srw_ss()) []) >> first_assum ACCEPT_TAC) >>
  `(!x. buf.buf_operand = Var x \/ SND ops = Var x ==> not_fresh_at ready x) /\
   (!x. FST ops = Var x ==> not_fresh_at ready x) /\
   abi_decoder_operand_live body_end.cs_next_var (FST ops)` by
    suspend "live" >>
  suspend "phases"
QED

Resume abi_encode_args_producer_phases[live]:
  conj_tac
  >- (rpt strip_tac
      >- (qpat_assum `abi_decoder_operand_live ready.cs_next_var buf.buf_operand` mp_tac >>
          qpat_assum `buf.buf_operand = Var x` (fn th => rewrite_tac[th]) >>
          simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
      qpat_assum `abi_decoder_operand_live ready.cs_next_var (SND ops)` mp_tac >>
      qpat_assum `SND ops = Var x` (fn th => rewrite_tac[th]) >>
      simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `abi_decoder_operand_live ready.cs_next_var (FST ops)` mp_tac >>
      qpat_assum `FST ops = Var x` (fn th => rewrite_tac[th]) >>
      simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
  irule abi_decoder_operand_live_mono >> qexists `ready.cs_next_var` >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Resume abi_encode_args_producer_phases[phases]:
  drule_at (Pat `abi_builtin_encode_setup _ _ _ = _`) abi_encode_bridge_bytes_phases_open >>
  disch_then (drule_at (Pat `compile_abi_encode_to_buf _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `abi_encoder_window_input _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `alloca_room ctx func _`)) >>
  disch_then (drule_at (Pat `fn_has_code body_end final _`)) >>
  disch_then (drule_at (Pat `fresh_vars_wrt limit_st t`)) >>
  disch_then (drule_at (Pat `enc _ _ = _`)) >>
  disch_then (qspecl_then [`case mid of NONE => 0 | SOME _ => 32`, `p`,
    `case mid of NONE => 0 | SOME _ => 4`, `p+32+(case mid of NONE => 0 | SOME _ => 4)`] mp_tac) >>
  (impl_tac >-
    (asm_rewrite_tac [] >> conj_tac >- (rpt strip_tac >> first_assum ACCEPT_TAC) >>
     qpat_assum `enc ct rv = enc (Tuple (vyper_to_abi_types _ _)) _`
       (fn th => pure_rewrite_tac [GSYM th]) >>
     qpat_assum `mid = OPTION_MAP _ _` (fn th => pure_rewrite_tac [GSYM th]) >>
     qpat_assum `t = _` (fn th => pure_rewrite_tac [GSYM th]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  `abi_decode_sim ctx obs t actual` by
    (irule abi_decode_sim_ctx_no_invoke >> conj_tac >- first_assum ACCEPT_TAC >>
     qexists `ctx with ctx_functions := [obs]` >> first_assum ACCEPT_TAC) >>
  qexistsl [`avs`, `p`, `actual`] >> asm_rewrite_tac [] >>
  irule abi_decode_sim_trans >> qexists `t` >> conj_tac >> first_assum ACCEPT_TAC
QED

Finalise abi_encode_args_producer_phases

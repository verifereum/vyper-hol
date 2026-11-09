Theory exprSimAbiEncodeTupleSourceFresh
Ancestors
  exprSimAbiEncodeTupleFresh exprSimAbiEncodeTupleStagingProbe
  exprSimAbiEncodeProducerAssembly abiTupleEncodePrepare
  exprSimAbiEncodeObservationExtension abiDecoderVarExtend abiDecoderReentry
  abiBuiltinAllocation abiEncoderOpenInput varsExt freshWrites pred_set compileEnv venomState
  abiEncodeArgsSim exprSimAbiEncodeExtension abiEncoderExtendSim
  abiDecoderContract list finite_map words

Theorem abi_encode_args_staged_source_fresh_free:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) target args) es /\
  eval_exprs cx args es = (INL vs,es') /\
  evaluate_type_builtin cx (AbiEncode ensure mid) target (MAP expr_type args) vs = INL out /\
  abi_args_post ctx func ce cx es sa st s0 es' args ops vs initial /\
  EVERY (abi_decoder_operand_live st.cs_next_var) ops /\
  (!k tv w. k < LENGTH args /\
    evaluate_type (get_tenv cx) (expr_type (EL k args)) = SOME tv /\
    ~is_word_type (expr_type (EL k args)) /\ eval_operand (EL k ops) initial = SOME w ==>
    venomMemDefs$regions_disjoint (w2n w,val_footprint tv (EL k vs))
      (sb,abi_tuple_bytes ce (ZIP (ops,MAP expr_type args)))) /\
  compile_alloc_buffer (abi_tuple_bytes ce (ZIP (ops,MAP expr_type args))) st = (source_buf,allocated) /\
  compile_store_abi_tuple ce source_buf.buf_operand 0 (ZIP (ops,MAP expr_type args)) allocated = ((),staged) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ sb = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id =
      SOME (sb,abi_tuple_bytes ce (ZIP (ops,MAP expr_type args)))) /\
  sb+abi_tuple_bytes ce (ZIP (ops,MAP expr_type args)) < dimword (:256) /\
  local_ptrs_reserved ce st /\ sa.cs_next_var <= st.cs_next_var /\ fn_has_code st staged func ==>
  ?actual avs ct rv.
    vyper_to_abi_list (get_tenv cx) (MAP expr_type args) vs = SOME avs /\
    run_inst_seq (emitted_insts st staged) initial = OK actual /\ inst_extends st staged /\
    eval_operand source_buf.buf_operand actual = SOME (n2w sb) /\
    abi_encoder_open_input
      (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP expr_type args))) ct rv sb
      (abi_tuple_bytes ce (ZIP (ops,MAP expr_type args))) actual.vs_memory /\
    enc ct rv = enc (Tuple (MAP (vyper_to_abi_type (get_tenv cx) o expr_type) args)) (ListV avs) /\
    abi_decode_frame sb (abi_tuple_bytes ce (ZIP (ops,MAP expr_type args))) initial actual /\
    actual.vs_allocas = (abi_builtin_allocate_state st.cs_next_id
      (abi_tuple_bytes ce (ZIP (ops,MAP expr_type args))) initial).vs_allocas /\
    actual.vs_alloca_next = (abi_builtin_allocate_state st.cs_next_id
      (abi_tuple_bytes ce (ZIP (ops,MAP expr_type args))) initial).vs_alloca_next /\
    actual.vs_halted = initial.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_tuple_encode_stage_shape >> strip_tac >>
  `abi_args_post ctx func ce cx es sa st s0 es' args ops vs (drop_fresh st initial)` by
    (irule abi_encode_args_post_drop_fresh >> asm_rewrite_tac []) >>
  `fresh_vars_wrt staged (drop_fresh st initial)` by
    (irule abi_encode_drop_final_fresh >> decide_tac) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op (drop_fresh st initial) = eval_operand op initial` by
    (rpt strip_tac >> irule eval_operand_drop_fresh >>
     Cases_on `op` >> fs[abi_decoder_operand_live_def,
       abi_decoder_older_vars_def, not_fresh_at_def, IN_DEF]) >>
  `?clean avs ct rv.
    vyper_to_abi_list (get_tenv cx) (MAP expr_type args) vs = SOME avs /\
    run_inst_seq (emitted_insts st staged) (drop_fresh st initial) = OK clean /\ inst_extends st staged /\
    eval_operand source_buf.buf_operand clean = SOME (n2w sb) /\
    abi_encoder_open_input
      (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP expr_type args))) ct rv sb
      (abi_tuple_bytes ce (ZIP (ops,MAP expr_type args))) clean.vs_memory /\
    enc ct rv = enc (Tuple (MAP (vyper_to_abi_type (get_tenv cx) o expr_type) args)) (ListV avs) /\
    fresh_vars_wrt staged clean /\
    abi_decode_frame sb (abi_tuple_bytes ce (ZIP (ops,MAP expr_type args))) (drop_fresh st initial) clean /\
    clean.vs_allocas = (abi_builtin_allocate_state st.cs_next_id
      (abi_tuple_bytes ce (ZIP (ops,MAP expr_type args))) initial).vs_allocas /\
    clean.vs_alloca_next = (abi_builtin_allocate_state st.cs_next_id
      (abi_tuple_bytes ce (ZIP (ops,MAP expr_type args))) initial).vs_alloca_next /\
    clean.vs_halted = initial.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op clean = SOME w)` by
    (drule_at (Pat `abi_args_post _ _ _ _ _ _ _ _ _ _ _ _ _`)
       abi_encode_args_staged_source >>
     disch_then (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
     disch_then (drule_at (Pat `compile_store_abi_tuple _ _ _ _ _ = _`)) >>
     disch_then (drule_at (Pat `expr_body_pre _ _ _ _ _`)) >>
     disch_then (drule_at (Pat `evaluate_type_builtin _ _ _ _ _ = _`)) >>
     disch_then (qspecl_then [`sb`, `staged`] mp_tac) >>
     (impl_tac >-
       (asm_rewrite_tac [] >> conj_tac >-
         (rpt gen_tac >> strip_tac >>
          `k < LENGTH ops` by (drule abi_args_post_lengths >> simp[] >> decide_tac) >>
          `abi_decoder_operand_live st.cs_next_var (EL k ops)` by fs[EVERY_EL] >>
          metis_tac[]) >>
        simp_tac (srw_ss()) [drop_fresh_def] >> asm_rewrite_tac [])) >>
     strip_tac >> qexistsl [`actual`, `avs`, `ct`, `rv`] >>
     asm_rewrite_tac [] >>
     conj_tac >-
       (Cases_on `FLOOKUP initial.vs_allocas st.cs_next_id = NONE` >>
        simp[abi_builtin_allocate_state_def, drop_fresh_def]) >>
     conj_tac >-
       (Cases_on `FLOOKUP initial.vs_allocas st.cs_next_id = NONE` >>
        simp[abi_builtin_allocate_state_def, drop_fresh_def]) >>
     conj_tac >- simp[drop_fresh_def] >>
     rpt strip_tac >> first_x_assum irule >> asm_rewrite_tac [] >>
     metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE) (emitted_insts st staged)` by
    (fs[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `abi_decoder_vars_extend initial.vs_vars (drop_fresh st initial) initial` by
    simp[abi_encode_drop_fresh_bounded_extension] >>
  drule_all abi_encoder_sequence_extend >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st staged) initial = OK actual` >>
  drule abi_decoder_vars_extend_observations >> strip_tac >>
  qexistsl [`actual`, `avs`, `ct`, `rv`] >>
  asm_rewrite_tac [] >>
  conj_tac >- (irule abi_decoder_vars_extend_eval >> goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >-
    (qpat_x_assum `abi_decode_frame _ _ _ _` mp_tac >>
     simp[abi_decode_frame_def, drop_fresh_def] >> metis_tac[]) >>
  conj_tac >-
    (drule_at (Pat `abi_decoder_vars_extend _ clean actual`)
       abi_decoder_vars_extend_restore >>
     disch_then (fn th =>
       qpat_x_assum `clean.vs_halted = _` mp_tac >>
       once_rewrite_tac [GSYM th]) >> simp_tac (srw_ss()) []) >>
  rpt strip_tac >>
  `eval_operand op clean = SOME w` by
    (qpat_x_assum `!op w. _ ==> eval_operand op clean = SOME w` irule >>
     asm_rewrite_tac []) >>
  drule_at (Pat `abi_decoder_vars_extend _ clean actual`) abi_decoder_vars_extend_eval >>
  disch_then irule >> asm_rewrite_tac []
QED

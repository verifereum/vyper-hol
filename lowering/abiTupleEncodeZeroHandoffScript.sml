Theory abiTupleEncodeZeroHandoff
Ancestors
  abiTupleEncodeZeroPrepare abiTupleEncodeOpenDynamic abiTupleEncodeOpenStatic
  abiTupleEncodeOpenAssembly abiTupleEncodePrepare abiTupleEncodeOpenInput
  abiTupleEncodeLayout abiBuiltinEncodeResources abiBuiltinEncodeInput
  abiBuiltinAllocation abiEncoderOpenInput abiEncoderInput abiTupleProps
  abiDecoderReentry abiDecoderContract compileEnv exprLowering
  venomState venomExecSemantics words list arithmetic finite_map

Theorem abi_tuple_encode_resources_keep[local]:
  abi_builtin_encode_resources st method_id_opt sb source_cap p maxlen first last b cap s /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next ==>
  abi_builtin_encode_resources st method_id_opt sb source_cap p maxlen first last b cap t
Proof
  metis_tac[abi_builtin_encode_resources_transport]
QED

Theorem abi_tuple_encode_zero_dynamic_prepare:
  compile_alloc_buffer (abi_tuple_bytes ce xs) st = (source_buf,allocated) /\
  compile_store_abi_tuple ce source_buf.buf_operand 0 xs allocated = ((),staged) /\ fn_has_code st staged func /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ sb = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (sb,abi_tuple_bytes ce xs)) /\
  abi_tuple_encode_zero_inputs sf ce xs ats avs st.cs_next_var sb (sb+abi_tuple_bytes ce xs) initial /\
  abi_tuple_encode_layout ce xs ats /\ any_dynamic ats /\
  LENGTH (enc (Tuple ats) (ListV avs)) <= maxlen /\
  abi_builtin_encode_resources staged method_id_opt sb (abi_tuple_bytes ce xs) p maxlen first last b cap
    (abi_builtin_allocate_state st.cs_next_id (abi_tuple_bytes ce xs) initial) /\
  staged.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual.
    abi_encoder_open_input (type_to_abi_enc_info sf ce (TupleT (MAP SND xs)))
      (Tuple ats) (ListV avs) sb (abi_tuple_bytes ce xs) actual.vs_memory /\
    eval_operand source_buf.buf_operand actual = SOME (n2w sb) /\
    abi_decoder_operand_live staged.cs_next_var source_buf.buf_operand /\
    LENGTH (enc (Tuple ats) (ListV avs)) <= maxlen /\
    abi_builtin_encode_resources staged method_id_opt sb (abi_tuple_bytes ce xs) p maxlen first last b cap actual /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame sb (abi_tuple_bytes ce xs) initial actual /\
    actual.vs_allocas = (abi_builtin_allocate_state st.cs_next_id (abi_tuple_bytes ce xs) initial).vs_allocas /\
    actual.vs_alloca_next = (abi_builtin_allocate_state st.cs_next_id (abi_tuple_bytes ce xs) initial).vs_alloca_next /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_current_bb = staged.cs_current_bb /\ actual.vs_inst_idx = LENGTH staged.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_tuple_encode_stage_shape >> strip_tac >>
  qpat_assum `abi_builtin_encode_resources _ _ _ _ _ _ _ _ _ _ _`
    (assume_tac o CONJUNCT1 o SIMP_RULE (srw_ss()) [abi_builtin_encode_resources_def, LET_THM]) >>
  drule_all abi_tuple_encode_zero_stage_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  drule_all abi_tuple_encode_open_dynamic_input >> strip_tac >>
  `abi_builtin_encode_resources staged method_id_opt sb (abi_tuple_bytes ce xs) p maxlen first last b cap actual` by
    (irule abi_tuple_encode_resources_keep >> goal_assum (drule_at Any) >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >> first_assum ACCEPT_TAC
QED

Theorem abi_tuple_encode_zero_static_prepare:
  compile_alloc_buffer (abi_tuple_bytes ce xs) st = (source_buf,allocated) /\
  compile_store_abi_tuple ce source_buf.buf_operand 0 xs allocated = ((),staged) /\ fn_has_code st staged func /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ sb = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (sb,abi_tuple_bytes ce xs)) /\
  abi_tuple_encode_zero_inputs sf ce xs ats avs st.cs_next_var sb (sb+abi_tuple_bytes ce xs) initial /\
  abi_tuple_encode_layout ce xs ats /\ ~any_dynamic ats /\ abi_tuple_bytes ce xs MOD 32 = 0 /\
  LENGTH (enc (Tuple ats) (ListV avs)) <= maxlen /\
  abi_builtin_encode_resources staged method_id_opt sb (abi_tuple_bytes ce xs) p maxlen first last b cap
    (abi_builtin_allocate_state st.cs_next_id (abi_tuple_bytes ce xs) initial) /\
  staged.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual ct rv.
    has_type ct rv /\ ~is_dynamic ct /\ static_length ct = abi_tuple_bytes ce xs /\
    enc ct rv = enc (Tuple ats) (ListV avs) /\
    abi_encoder_open_input (AbiCopy (abi_tuple_bytes ce xs)) ct rv sb (abi_tuple_bytes ce xs) actual.vs_memory /\
    eval_operand source_buf.buf_operand actual = SOME (n2w sb) /\
    abi_decoder_operand_live staged.cs_next_var source_buf.buf_operand /\
    LENGTH (enc ct rv) <= maxlen /\
    abi_builtin_encode_resources staged method_id_opt sb (abi_tuple_bytes ce xs) p maxlen first last b cap actual /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame sb (abi_tuple_bytes ce xs) initial actual /\
    actual.vs_allocas = (abi_builtin_allocate_state st.cs_next_id (abi_tuple_bytes ce xs) initial).vs_allocas /\
    actual.vs_alloca_next = (abi_builtin_allocate_state st.cs_next_id (abi_tuple_bytes ce xs) initial).vs_alloca_next /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_current_bb = staged.cs_current_bb /\ actual.vs_inst_idx = LENGTH staged.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_tuple_encode_stage_shape >> strip_tac >>
  qpat_assum `abi_builtin_encode_resources _ _ _ _ _ _ _ _ _ _ _`
    (assume_tac o CONJUNCT1 o SIMP_RULE (srw_ss()) [abi_builtin_encode_resources_def, LET_THM]) >>
  drule_all abi_tuple_encode_zero_stage_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  drule_all abi_tuple_encode_open_static_representative >> strip_tac >>
  `abi_builtin_encode_resources staged method_id_opt sb (abi_tuple_bytes ce xs) p maxlen first last b cap actual` by
    (irule abi_tuple_encode_resources_keep >> goal_assum (drule_at Any) >> asm_simp_tac bool_ss []) >>
  qexistsl_tac [`actual`, `ct`, `rv`] >> asm_simp_tac bool_ss []
QED

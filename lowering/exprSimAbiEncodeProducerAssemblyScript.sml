Theory exprSimAbiEncodeProducerAssembly
Ancestors
  exprSimAbiEncodeSourceSupplier exprSimAbiEncodeRuntimeInputs
  exprSimAbiEncodeSourceSuccess exprSimAbiEncodeSourceMetadata
  exprSimAbiEncodeArgsSeparation exprSimAbiEncodeRegionStage
  exprSimAbiEncodeRegionInput exprSimAbiEncodeTupleProducer
  abiEncodeArgsSim abiEncoderSourcePrimitive abiTupleEncodeLayout
  abiTupleProps exprLowering
  exprSimHypsDefs exprSimDefs compileEnv vyperABI vyperABIRoundtrip
  vyperTypeSystem valueEncoding words list rich_list

Theorem abi_encode_args_region_inputs:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) target args) es /\
  eval_exprs cx args es = (INL vs,es') /\
  abi_args_post ctx func ce cx es sa st s0 es' args ops vs s /\
  vyper_to_abi_list (get_tenv cx) (MAP expr_type args) vs = SOME avs /\
  EVERY (abi_decoder_operand_live next) ops /\
  (!k tv w. k < LENGTH args /\
    evaluate_type (get_tenv cx) (lowered_value_type ce (EL k args)) = SOME tv /\
    ~is_word_type (lowered_value_type ce (EL k args)) /\ eval_operand (EL k ops) s = SOME w ==>
    venomMemDefs$regions_disjoint (w2n w,val_footprint tv (EL k vs)) (lo,hi-lo)) ==>
  ?cts rvs. abi_encode_region_inputs ce.ce_struct_fields ce (ZIP (ops,MAP (lowered_value_type ce) args))
      cts rvs next lo hi s /\
    abi_tuple_encode_layout ce (ZIP (ops,MAP (lowered_value_type ce) args)) cts /\
    enc (Tuple cts) (ListV rvs) =
      enc (Tuple (MAP (vyper_to_abi_type (get_tenv cx) o expr_type) args)) (ListV avs)
Proof
  strip_tac >> drule_all abi_encode_body_args_indexed_physical_types >> strip_tac >>
  drule abi_encode_body_args_physical_conversion >>
  disch_then drule >> strip_tac >>
  drule abi_args_post_lengths >> strip_tac >>
  `sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx)` by
    fs[expr_body_pre_def, expr_sim_inv_def] >>
  `!t v. evaluate_type (get_tenv cx) t = SOME v ==> type_memory_bytes ce t = type_memory_size v` by
    metis_tac[abi_encode_body_evaluated_metadata] >>
  `MAP (vyper_to_abi_type (get_tenv cx) o SND) (ZIP (ops,MAP (lowered_value_type ce) args)) =
   MAP (vyper_to_abi_type (get_tenv cx) o expr_type) args` by
    (simp[GSYM MAP_MAP_o, MAP_ZIP] >>
     irule LIST_EQ >> simp[EL_MAP]) >>
  pop_assum (SUBST1_TAC o SYM) >>
  irule abi_encode_region_list_supplier >> simp[] >>
  qexists `vs` >> simp[LIST_REL_EL_EQN, EL_ZIP, EL_MAP] >>
  drule vyper_to_abi_list_EL >> strip_tac >> gvs[] >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!k. _ ==> ?tv. evaluate_type _ _ = SOME tv /\ _`
    (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
  `type_memory_bytes ce (lowered_value_type ce (EL n args)) = type_memory_size tv` by metis_tac[] >>
  `type_memory_bytes ce (lowered_value_type ce (EL n args)) < dimword (:256)` by
    (Cases_on `is_word_type (expr_type (EL n args))`
     >- (`expr_body_pre ce cx env (EL n args) es` by
           (irule abi_encode_body_arg_pre >> goal_assum (drule_at Any) >> simp[EL_MEM]) >>
         drule exprSimHypsTheory.expr_body_pre_physical_type >> strip_tac >>
         `lowered_value_type ce (EL n args) = expr_type (EL n args)` by
           (Cases_on `lowered_value_type ce (EL n args)` >>
            Cases_on `expr_type (EL n args)` >>
            gvs[is_word_type_def, arg_type_fits_def] >>
            rename1 `arg_type_fits (BaseT bt1) (BaseT bt2)` >>
            Cases_on `bt1` >> Cases_on `bt2` >>
            gvs[is_word_type_def, arg_type_fits_def] >>
            rename1 `arg_type_fits (BaseT (BytesT bd1)) (BaseT (BytesT bd2))` >>
            Cases_on `bd1` >> Cases_on `bd2` >>
            gvs[is_word_type_def, arg_type_fits_def]) >>
         gvs[] >> drule_all abi_encoder_word_source_shape >> strip_tac >>
         `type_memory_bytes ce (expr_type (EL n args)) = type_memory_size tv` by metis_tac[] >>
         simp[dimword_def]) >>
     `n < LENGTH args` by simp[] >>
     drule_all abi_encode_body_arg_physical_copy_bound >>
     strip_tac >> gvs[] >>
     `type_memory_bytes ce (lowered_value_type ce (EL n args)) = type_memory_size tv` by metis_tac[] >>
     simp[dimword_def]) >>
  qexists `tv` >> simp[] >>
  gvs[abi_args_post_def, LIST_REL_EL_EQN, EVERY_EL, EL_ZIP, EL_MAP] >>
  metis_tac[]
QED

Theorem abi_encode_args_registered_inputs:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) target args) es /\
  eval_exprs cx args es = (INL vs,es') /\
  evaluate_type_builtin cx (AbiEncode ensure mid) target (MAP expr_type args) vs = INL out /\
  abi_args_post ctx func ce cx es sa st s0 es' args ops vs s /\
  EVERY (abi_decoder_operand_live next) ops /\ alloca_inv s /\
  fn_inst_ids_distinct func /\ local_ptrs_rel func ce es'.scopes s /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [q] /\
  not_local_ptr ce es'.scopes q /\ st.cs_next_id <= inst.inst_id /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (sb,sz) ==>
  ?avs cts rvs.
    vyper_to_abi_list (get_tenv cx) (MAP expr_type args) vs = SOME avs /\
    abi_encode_region_inputs ce.ce_struct_fields ce (ZIP (ops,MAP (lowered_value_type ce) args))
      cts rvs next sb (sb+sz) s /\
    abi_tuple_encode_layout ce (ZIP (ops,MAP (lowered_value_type ce) args)) cts /\
    enc (Tuple cts) (ListV rvs) =
      enc (Tuple (MAP (vyper_to_abi_type (get_tenv cx) o expr_type) args)) (ListV avs)
Proof
  strip_tac >>
  `target = TupleT (MAP expr_type args)` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_type_builtin_args_def] >>
  gvs[] >> drule_all abi_encode_source_success_list >> strip_tac >>
  `?cts rvs. abi_encode_region_inputs ce.ce_struct_fields ce (ZIP (ops,MAP (lowered_value_type ce) args))
      cts rvs next sb (sb+sz) s /\
    abi_tuple_encode_layout ce (ZIP (ops,MAP (lowered_value_type ce) args)) cts /\
    enc (Tuple cts) (ListV rvs) =
      enc (Tuple (MAP (vyper_to_abi_type (get_tenv cx) o expr_type) args)) (ListV avs)` by
    (irule abi_encode_args_region_inputs >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >> rpt strip_tac >>
     drule_all abi_encode_args_footprint_site_disjoint >> simp[]) >>
  qexistsl [`avs`, `cts`, `rvs`] >> fs[]
QED

Theorem abi_encode_staged_source_consumer:
  abi_tuple_encode_open_memory ce.ce_struct_fields ce xs ats avs d mem /\
  abi_tuple_encode_layout ce xs ats /\
  abi_tuple_bytes ce xs MOD 32 = 0 ==>
  ?ct rv. abi_encoder_open_input
    (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP SND xs)))
    ct rv d (abi_tuple_bytes ce xs) mem /\
    enc ct rv = enc (Tuple ats) (ListV avs)
Proof
  strip_tac >> Cases_on `any_dynamic ats`
  >- (qexistsl [`Tuple ats`, `ListV avs`] >>
      asm_simp_tac bool_ss [] >>
      irule abi_encode_tuple_dynamic_consumer >>
      asm_simp_tac bool_ss [abi_encode_tuple_open_memory_interface]) >>
  drule_all abi_tuple_encode_layout_dynamic >> strip_tac >>
  `type_memory_bytes ce (TupleT (MAP SND xs)) = abi_tuple_bytes ce xs` by
    simp[type_memory_bytes_def, abi_tuple_bytes_def, MAP_MAP_o, combinTheory.o_DEF] >>
  drule_all (PURE_REWRITE_RULE [abi_encode_tuple_open_memory_interface]
    abi_encode_tuple_static_consumer) >> strip_tac >>
  qexistsl [`ct`, `rv`] >>
  asm_simp_tac bool_ss [type_to_abi_enc_info_def]
QED

Theorem abi_encode_tuple_bytes_aligned:
  !xs. EVERY (\p. type_memory_bytes ce (SND p) MOD 32 = 0) xs ==>
    abi_tuple_bytes ce xs MOD 32 = 0
Proof
  Induct >> simp[abi_tuple_bytes_def] >>
  gvs[abi_tuple_bytes_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  once_rewrite_tac[GSYM arithmeticTheory.MOD_PLUS] >> simp[]
QED

Theorem abi_encode_args_bytes_aligned:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) target args) es /\
  eval_exprs cx args es = (INL vs,es') /\ LENGTH ops = LENGTH args ==>
  abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args)) MOD 32 = 0
Proof
  strip_tac >> irule abi_encode_tuple_bytes_aligned >>
  simp[EVERY_EL, EL_ZIP, EL_MAP] >> gen_tac >> strip_tac >>
  drule_all abi_encode_body_args_indexed_physical_types >> strip_tac >>
  `n < LENGTH args` by simp[] >>
  qpat_x_assum `!k. _ ==> ?tv. _` drule >> strip_tac >>
  drule_all abi_encode_body_evaluated_metadata >> simp[]
QED

Theorem abi_encode_args_staged_source:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) target args) es /\
  eval_exprs cx args es = (INL vs,es') /\
  evaluate_type_builtin cx (AbiEncode ensure mid) target (MAP expr_type args) vs = INL out /\
  abi_args_post ctx func ce cx es sa st s0 es' args ops vs initial /\
  EVERY (abi_decoder_operand_live st.cs_next_var) ops /\
  (!k tv w. k < LENGTH args /\
    evaluate_type (get_tenv cx) (lowered_value_type ce (EL k args)) = SOME tv /\
    ~is_word_type (lowered_value_type ce (EL k args)) /\ eval_operand (EL k ops) initial = SOME w ==>
    venomMemDefs$regions_disjoint (w2n w,val_footprint tv (EL k vs))
      (sb,abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args)))) /\
  compile_alloc_buffer (abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args))) st = (source_buf,allocated) /\
  compile_store_abi_tuple ce source_buf.buf_operand 0 (ZIP (ops,MAP (lowered_value_type ce) args)) allocated = ((),staged) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ sb = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id =
      SOME (sb,abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args)))) /\
  sb+abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args)) < dimword (:256) /\
  staged.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual avs ct rv.
    vyper_to_abi_list (get_tenv cx) (MAP expr_type args) vs = SOME avs /\
    run_inst_seq (emitted_insts st staged) initial = OK actual /\ inst_extends st staged /\
    eval_operand source_buf.buf_operand actual = SOME (n2w sb) /\
    abi_encoder_open_input
      (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP (lowered_value_type ce) args))) ct rv sb
      (abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args))) actual.vs_memory /\
    enc ct rv = enc (Tuple (MAP (vyper_to_abi_type (get_tenv cx) o expr_type) args)) (ListV avs) /\
    fresh_vars_wrt limit_st actual /\
    abi_decode_frame sb (abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args))) initial actual /\
    actual.vs_allocas = (abi_builtin_allocate_state st.cs_next_id
      (abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args))) initial).vs_allocas /\
    actual.vs_alloca_next = (abi_builtin_allocate_state st.cs_next_id
      (abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args))) initial).vs_alloca_next /\
    actual.vs_halted = initial.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w)
Proof
  strip_tac >>
  `target = TupleT (MAP expr_type args)` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_type_builtin_args_def] >>
  drule abi_args_post_lengths >> strip_tac >>
  `?avs. vyper_to_abi_list (get_tenv cx) (MAP expr_type args) vs = SOME avs` by
    (irule abi_encode_source_success_list >> metis_tac[]) >>
  `?cts rvs. abi_encode_region_inputs ce.ce_struct_fields ce (ZIP (ops,MAP (lowered_value_type ce) args))
      cts rvs st.cs_next_var sb (sb+abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args))) initial /\
    abi_tuple_encode_layout ce (ZIP (ops,MAP (lowered_value_type ce) args)) cts /\
    enc (Tuple cts) (ListV rvs) =
      enc (Tuple (MAP (vyper_to_abi_type (get_tenv cx) o expr_type) args)) (ListV avs)` by
    (irule abi_encode_args_region_inputs >> simp[] >> metis_tac[]) >>
  drule_at (Pat `abi_encode_region_inputs _ _ _ _ _ _ _ _ _`)
    abi_encode_region_stage_sequence >>
  disch_then (qspecl_then [`staged`, `source_buf`, `limit_st`, `allocated`] mp_tac) >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_tuple_bytes ce (ZIP (ops,MAP (lowered_value_type ce) args)) MOD 32 = 0` by
    (irule abi_encode_args_bytes_aligned >> metis_tac[]) >>
  drule_all abi_encode_staged_source_consumer >> strip_tac >>
  qexistsl [`actual`, `avs`, `ct`, `rv`] >>
  asm_simp_tac bool_ss [] >>
  `MAP SND (ZIP (ops,MAP (lowered_value_type ce) args)) = MAP (lowered_value_type ce) args` by simp[MAP_ZIP] >>
  metis_tac[]
QED

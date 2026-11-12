(* Dynamic-array counted physical decoder constructor. *)
Theory bodyIntCallDecoderCountedArray
Ancestors
  bodyIntCallDecoderCountedArrayInit bodyIntCallDecoderCountedLoopEntry
  bodyIntCallDecoderCountedContract abiScratchDecoderArray abiScratchDecoderContract
  abiScratchDecoderLoopInput abiScratchDecoderLoopContext abiScratchEncoderContract
  abiScratchEffect abiDecoderRecursiveArray abiDecoderArrayInit abiDecoderArrayInitExec abiDecoderAllocation
  abiDecoderContract abiDecoderLoop abiDecoderTypedContract abiDecoderCoherence
  abiDecoderCorrectPrimitiveArray abiScratchFootprint fragGasPath
  exprLowering compileEnv valueEncoding vyperABI vyperValue venomState words list arithmetic

Theorem intcall_scratch_decoder_array_execute:
  compile_abi_decode_to_buf dst src opc base_op hi_op
    (DecDynArray (type_to_abi_dec_info sf ce ty) (abi_embedded_static_size ce.ce_struct_fields ty)
      (type_memory_bytes ce ty) (is_abi_dynamic ce.ce_struct_fields ty) maxn)
    st = ((),final) /\
  (is_abi_dynamic ce.ce_struct_fields ty \/ dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)) /\
  intcall_scratch_decoder_counted ce env sf ty tv /\ (base_op = Lit 0w \/ opc = MLOAD) /\
  fn_has_code st final func /\
  (!bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_decoder_input ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    bs (ArrayV (DynArrayV vs)) st src dst opc base_op hi_op B sb d first last b cap initial /\
  (is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  abi_decoder_budget first last b cap initial /\ first <= abi_decoder_entry_floor st /\ final.cs_next_id <= last /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t n. val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
    abi_scratch_effect first last st.cs_next_id final.cs_next_id st.cs_next_var limit_st
      d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial t /\
    t.vs_current_bb = final.cs_current_bb /\ t.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~t.vs_halted /\ gas_path ctx func initial n (OK t)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode opc` by fs[abi_scratch_decoder_input_def, abi_scratch_decoder_ranges_def] >>
  drule_all abi_decoder_recursive_array_code >> strip_tac >>
  drule_all abi_decode_array_loop_init_allocation_floor >> strip_tac >>
  `loop_st.cs_next_var <= limit_st.cs_next_var /\ loop_st.cs_next_id <= last /\
    first <= loop_st.cs_next_id-2 /\ loop_st.cs_next_id-2 < last` by decide_tac >>
  drule_all intcall_scratch_decoder_array_initialize >>
  disch_then (qspec_then `ctx` (qx_choose_then `prepared`
    (qx_choose_then `slot` (qx_choose_then `ninit` (MAP_EVERY assume_tac o CONJUNCTS))))) >>
  `fresh_vars_wrt limit_st prepared /\ abi_decoder_budget first last b cap prepared`
    by fs[abi_scratch_effect_def] >>
  drule_at (Pat `FLOOKUP _ _ = _`) abi_scratch_decoder_loop_input >>
  simp_tac bool_ss [] >> disch_then drule_all >> strip_tac >>
  drule_at (Pat `abi_scratch_decoder_loop_data`) intcall_scratch_decoder_loop_from_state >>
  disch_then drule >>
  disch_then (qspecl_then [`loop_st.cs_next_id-2`, `loop_st.cs_next_id-2`,
    `limit_st`, `final.cs_next_id`] mp_tac) >>
  simp_tac bool_ss [LESS_EQ_REFL] >> disch_then drule_all >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `abi_scratch_effect first last st.cs_next_id final.cs_next_id st.cs_next_var limit_st
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial prepared` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `loop_st.cs_next_id`, `st.cs_next_id`,
       `st.cs_next_var`, `type_memory_bytes ce (ArrayT ty (Dynamic maxn))`] >>
     asm_simp_tac bool_ss [LESS_EQ_REFL]) >>
  `abi_scratch_effect first last st.cs_next_id final.cs_next_id st.cs_next_var limit_st
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial t` by
    (irule abi_scratch_effect_trans_tail >>
     qexistsl_tac [`prepared`, `final.cs_next_id`, `loop_st.cs_next_id-2`, `loop_st.cs_next_var`] >>
     asm_simp_tac bool_ss [LESS_EQ_REFL]) >>
  qexists_tac `t` >> asm_simp_tac bool_ss [] >> metis_tac[gas_path_then]
QED

Theorem intcall_scratch_decoder_array_loop:
  intcall_scratch_decoder_counted ce env sf ty tv /\
  (is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  (is_abi_dynamic ce.ce_struct_fields ty \/ dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)) ==>
  intcall_scratch_decoder_counted ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  simp_tac bool_ss [intcall_scratch_decoder_counted_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_scratch_decoder_input ce env sf (ArrayT ty (Dynamic maxn))
    (ArrayTV tv (Dynamic maxn)) bs v start src dst opc base_op hi B sb d first last b cap initial`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_input_def]) >>
  drule abi_decoder_dynarray_metadata_shape >> strip_tac >>
  full_simp_tac bool_ss [] >>
  (qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`
    (assume_tac o PURE_REWRITE_RULE [cj 3 type_to_abi_dec_info_def]) >>
  `abi_decode_source_opcode opc` by fs[abi_scratch_decoder_ranges_def] >>
  drule abi_decoder_recursive_array_adds_blocks >>
  disch_then (qspec_then `func` mp_tac) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  `!bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0` by metis_tac[] >>
  drule_at (Pat `abi_scratch_decoder_input`) intcall_scratch_decoder_array_execute >>
  disch_then (qspecl_then [`limit_st`, `func`, `end_st`, `ctx`] mp_tac) >>
  impl_tac >- asm_simp_tac bool_ss [] >> asm_simp_tac bool_ss [])
QED

Theorem intcall_scratch_decoder_array_copy:
  ~is_abi_dynamic ce.ce_struct_fields ty /\ ~dec_info_needs_clamp (type_to_abi_dec_info sf ce ty) ==>
  intcall_scratch_decoder_counted ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  simp_tac bool_ss [intcall_scratch_decoder_counted_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_scratch_decoder_input ce env sf (ArrayT ty (Dynamic maxn))
    (ArrayTV tv (Dynamic maxn)) bs v start src dst opc base_op hi B sb d first last b cap initial`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_input_def]) >>
  drule abi_decoder_dynarray_metadata_shape >> strip_tac >>
  full_simp_tac bool_ss [] >>
  (qpat_assum `~is_abi_dynamic ce.ce_struct_fields ty` (fn static =>
    qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`
      (assume_tac o SIMP_RULE bool_ss [Once type_to_abi_dec_info_def, static])) >>
  drule_at (Pat `abi_scratch_decoder_input`) intcall_scratch_decoder_array_bulk >>
  disch_then (qspecl_then [`limit_st`, `func`, `end_st`, `ctx`] mp_tac) >>
  impl_tac >- asm_simp_tac bool_ss [] >> asm_simp_tac bool_ss [])
QED

Theorem intcall_scratch_decoder_array:
  intcall_scratch_decoder_counted ce env sf ty tv /\
  (is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) ==>
  intcall_scratch_decoder_counted ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
  strip_tac >>
  Cases_on `is_abi_dynamic ce.ce_struct_fields ty \/ dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)`
  >- (irule intcall_scratch_decoder_array_loop >> asm_simp_tac bool_ss []) >>
  irule intcall_scratch_decoder_array_copy >> fs[]
QED

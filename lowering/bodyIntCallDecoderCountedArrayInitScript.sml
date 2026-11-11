(* Actual bulk-array execution and physical ncounter initialization. *)
Theory bodyIntCallDecoderCountedArrayInit
Ancestors
  bodyIntCallDecoderCountedPrimitive abiScratchDecoderArray abiDecoderBulkReentry
  abiDecoderBulk abiScratchLeafEffect abiScratchEncoderContract abiDecoderContract
  abiDecoderTypedContract abiDecoderCoherence abiDecoderReentry abiDecoderFrame
  abiDecoderLoop abiScratchDecoderContract abiScratchDecoderInitReentry abiDecoderArrayInit
  abiDecoderArrayInitExec abiDecoderArrayInitReentry abiDecoderAllocation abiScratchFootprint
  abiScratchEffect abiScratchDecoderTransport abiDecoderValidArrayMemory
  entrySinkExtraction instIdxIndep exprLoweringProps compileEnv venomState
  valueEncoding vyperABI abiDecoderCorrectPrimitiveArray exprLowering words list arithmetic

Theorem intcall_decoder_bulk_sequence_path:
  compile_abi_decode_to_buf dst src opc base_op hi (DecDynArray ei abi_sz mem_sz F maxn)
    st = ((),end_st) /\ ~dec_info_needs_clamp ei /\ fn_has_code st end_st func /\
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (DecDynArray ei abi_sz mem_sz F maxn) (ListV avs) (ArrayV (DynArrayV vs))
    st stop src dst opc base_op hi B sb d b cap (abi_decoder_prune_vars st.cs_next_var initial) /\
  abi_decoder_budget first last b0 cap0 initial /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual n. val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d actual.vs_memory /\
    abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var limit_st
      d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b0 cap0 initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    gas_path ctx func initial n (OK actual)
Proof
  strip_tac >>
  `abi_decode_source_opcode opc` by
    fs[abi_decoder_recursive_pre_def, abi_decoder_pre_def, abi_decoder_ranges_def] >>
  drule_all abi_decoder_bulk_shape >> strip_tac >>
  drule_all abi_decoder_bulk_reentry_sequence >> strip_tac >>
  drule_all intcall_same_block_seq_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  `abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var limit_st
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b0 cap0 initial actual` by
    (irule abi_scratch_leaf_effect >> asm_simp_tac bool_ss [] >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`actual with vs_inst_idx := LENGTH end_st.cs_current_insts`, `n`] >>
  gvs[abi_scratch_effect_def, fresh_vars_wrt_def, eval_op_inst_idx,
    abi_decode_frame_def, abi_decode_footprint_frame_def]
QED

Theorem intcall_scratch_decoder_array_bulk:
  compile_abi_decode_to_buf dst src opc base_op hi
    (DecDynArray (type_to_abi_dec_info sf ce ty) (abi_embedded_static_size ce.ce_struct_fields ty)
      (type_memory_bytes ce ty) F maxn) st = ((),end_st) /\
  ~is_abi_dynamic ce.ce_struct_fields ty /\ ~dec_info_needs_clamp (type_to_abi_dec_info sf ce ty) /\
  fn_has_code st end_st func /\
  abi_scratch_decoder_input ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    bs (ArrayV (DynArrayV vs)) st src dst opc base_op hi B sb d first last b cap initial /\
  abi_decoder_budget first last b cap initial /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual n. val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d actual.vs_memory /\
    abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var limit_st
      d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    gas_path ctx func initial n (OK actual)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_coherent ce env sf ty tv` by
    fs[abi_scratch_decoder_input_def, abi_decoder_coherent_array_iff] >>
  drule abi_decoder_coherent_header >> strip_tac >>
  `~is_dynamic (vyper_to_abi_type env ty)` by fs[abi_decoder_header_def] >>
  drule_all abi_scratch_decoder_static_array_pre >> strip_tac >>
  qhdtm_x_assum `abi_scratch_decoder_input`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_input_def]) >>
  RULE_ASSUM_TAC (SIMP_RULE bool_ss [Once vyper_to_abi_type_def]) >>
  drule abi_decoder_dynarray_metadata_shape >> strip_tac >>
  gvs[Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"] >>
  qpat_assum `~is_abi_dynamic ce.ce_struct_fields ty` (fn static =>
    qhdtm_assum `abi_decoder_recursive_pre`
      (assume_tac o SIMP_RULE bool_ss [Once type_to_abi_dec_info_def, static])) >>
  drule_all intcall_decoder_bulk_sequence_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexistsl_tac [`actual`, `n`] >> asm_simp_tac bool_ss []
QED

Theorem intcall_scratch_decoder_init_path:
  abi_decode_array_loop_init dst src opc base_op hi maxn abi_sz st = (setup,loop_st) /\
  abi_decode_source_opcode opc /\ eval_operand src initial = SOME (n2w sb) /\
  eval_operand dst initial = SOME (n2w d) /\ d < dimword (:256) /\
  eval_operand base_op initial = SOME (n2w B) /\
  abi_decode_load opc (n2w (B + sb):bytes32) initial = n2w ncount /\ ncount <= maxn /\ maxn < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb + 32 + ncount * abi_sz <= h /\ h < dimword (:256)) /\
  abi_decoder_budget first last b cap initial /\ first <= abi_decoder_entry_floor st /\ loop_st.cs_next_id <= last /\
  abi_footprint_disjoint d 32 (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\ abi_decoder_operand_live st.cs_next_var base_op /\
  loop_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st loop_st func /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual n. abi_decoder_array_init_post setup st.cs_next_var limit_st (loop_st.cs_next_id-2)
      first last b cap d ncount initial actual /\
    abi_scratch_effect first last st.cs_next_id loop_st.cs_next_id st.cs_next_var limit_st
      d 32 b cap initial actual /\
    inst_extends st loop_st /\ actual.vs_current_bb = loop_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH loop_st.cs_current_insts /\ ~actual.vs_halted /\
    gas_path ctx func initial n (OK actual)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decode_array_loop_init_shape >> strip_tac >>
  drule_all abi_decode_array_loop_init_site_bounds >> strip_tac >>
  drule_all abi_scratch_decoder_init_reentry >> strip_tac >>
  `abi_decoder_array_init_post setup st.cs_next_var limit_st (loop_st.cs_next_id-2)
    first last b cap d ncount initial actual` by
    (simp_tac bool_ss [abi_decoder_array_init_post_def] >> qexists_tac `slot` >>
     asm_simp_tac bool_ss []) >>
  `abi_scratch_effect first last st.cs_next_id loop_st.cs_next_id st.cs_next_var limit_st
    d 32 b cap initial actual` by
    (irule abi_scratch_decoder_init_effect >> conj_tac
     >- (goal_assum (drule_at Any)) >>
     qexistsl_tac [`ncount`, `setup`, `loop_st.cs_next_id-2`] >> asm_simp_tac bool_ss []) >>
  drule_all intcall_same_block_seq_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  qexistsl_tac [`actual with vs_inst_idx := LENGTH loop_st.cs_current_insts`, `n`] >>
  gvs[abi_scratch_effect_def, fresh_vars_wrt_def, eval_op_inst_idx,
    abi_decode_footprint_frame_def]
QED

Theorem intcall_decoder_init_footprint:
  abi_decode_footprint_frame [(d,32);(slot,32)] initial actual /\ 32 <= sz /\
  FLOOKUP actual.vs_allocas site = SOME (slot,32) /\ first <= site /\ site < last /\
  abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual ==>
  abi_decode_footprint_frame
    ((d,sz)::abi_decoder_child_scratch (abi_decoder_ids first last) b cap actual) initial actual /\
  abi_decode_footprint_frame
    ((d,sz)::abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) initial actual
Proof
  strip_tac >>
  `MEM (slot,32) (abi_decoder_child_scratch (abi_decoder_ids first last) b cap actual)` by
    (irule abi_scratch_registered_member >> conj_tac >- simp[] >>
     qexists_tac `site` >> simp[abi_decoder_ids_def]) >>
  conj_asm1_tac
  >- (irule abi_decode_footprint_frame_weaken >> qexists_tac `[(d,32);(slot,32)]` >>
      asm_simp_tac bool_ss [] >> simp_tac bool_ss [MEM, pairTheory.PAIR_EQ] >>
      rpt gen_tac >> strip_tac >> asm_rewrite_tac []
      >- (qexistsl_tac [`d`, `sz`] >> simp[]) >>
      qexistsl_tac [`slot`, `32`] >> simp[]) >>
  qpat_x_assum `abi_decode_footprint_frame (_::_) initial actual`
    (mp_tac o PURE_REWRITE_RULE [abi_decode_footprint_frame_def]) >>
  simp_tac bool_ss [abi_decode_footprint_frame_def] >> strip_tac >>
  asm_simp_tac bool_ss [] >> rpt gen_tac >> strip_tac >>
  first_x_assum irule >> gvs[abi_scratch_disjoint_cons] >>
  irule abi_scratch_disjoint_advance >> simp[] >> qexists_tac `initial` >> simp[]
QED

Theorem intcall_scratch_decoder_array_initialize:
  abi_decode_array_loop_init dst src opc base_op hi maxn (abi_embedded_static_size ce.ce_struct_fields ty)
    st = (setup,loop_st) /\
  abi_scratch_decoder_input ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    bs (ArrayV (DynArrayV vs)) st src dst opc base_op hi B sb d first last b cap initial /\
  abi_decoder_budget first last b cap initial /\ first <= abi_decoder_entry_floor st /\ loop_st.cs_next_id <= last /\
  loop_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st loop_st func /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual slot n.
    abi_scratch_decoder_input ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
      bs (ArrayV (DynArrayV vs)) loop_st src dst opc base_op hi B sb d first last b cap actual /\
    abi_decoder_valid_array_memory opc bs tv vs (B + sb) d 0 actual /\
    abi_scratch_effect first last st.cs_next_id loop_st.cs_next_id st.cs_next_var
      limit_st d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial actual /\
    abi_decode_footprint_frame
      ((d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)))::
        abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) initial actual /\
    FLOOKUP actual.vs_allocas (loop_st.cs_next_id-2) = SOME (slot,32) /\
    eval_operand (FST setup) actual = SOME (n2w slot) /\ mload slot actual = 0w /\
    eval_operand (SND setup) actual = SOME (n2w (LENGTH vs)) /\
    abi_decoder_operand_live loop_st.cs_next_var (FST setup) /\
    actual.vs_current_bb = loop_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH loop_st.cs_current_insts /\ ~actual.vs_halted /\
    gas_path ctx func initial n (OK actual)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_decoder_array_init_inputs >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decode_array_loop_init_shape >> strip_tac >>
  drule_all abi_decode_array_loop_init_site_bounds >> strip_tac >>
  drule_all abi_decode_array_loop_init_allocation_floor >> strip_tac >>
  drule_all intcall_scratch_decoder_init_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qhdtm_x_assum `abi_decoder_array_init_post`
    (mp_tac o PURE_REWRITE_RULE [abi_decoder_array_init_post_def]) >>
  disch_then (qx_choose_then `slot` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `32 <= type_memory_bytes ce (ArrayT ty (Dynamic maxn))` by simp[Once type_memory_bytes_def] >>
  `abi_scratch_effect first last st.cs_next_id loop_st.cs_next_id st.cs_next_var limit_st
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial actual` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `loop_st.cs_next_id`, `st.cs_next_id`, `st.cs_next_var`, `32`] >>
     asm_simp_tac arith_ss []) >>
  `abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual` by fs[abi_scratch_effect_def] >>
  `first <= loop_st.cs_next_id-2 /\ loop_st.cs_next_id-2 < last` by decide_tac >>
  drule_all intcall_decoder_init_footprint >> strip_tac >>
  `abi_scratch_decoder_input ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    bs (ArrayV (DynArrayV vs)) st src dst opc base_op hi B sb d first last b cap actual` by
    (irule abi_scratch_decoder_input_effect_frame >>
     qexistsl_tac [`loop_st.cs_next_id`, `initial`, `limit_st`, `st.cs_next_id`, `st.cs_next_var`] >> simp[]) >>
  `abi_scratch_decoder_input ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    bs (ArrayV (DynArrayV vs)) loop_st src dst opc base_op hi B sb d first last b cap actual` by
    (irule abi_scratch_decoder_input_mono >> qexists_tac `st` >> simp[]) >>
  `mem_bytes_at (B + sb) (LENGTH bs) (abi_decode_source opc actual) = bs` by fs[abi_scratch_decoder_input_def] >>
  `abi_decoder_valid_array_memory opc bs tv vs (B + sb) d 0 actual` by
    (irule abi_decoder_valid_array_memory_init >> asm_simp_tac bool_ss []) >>
  drule abi_decode_array_loop_index_live >> strip_tac >>
  qexistsl_tac [`actual`, `slot`, `n`] >> asm_simp_tac bool_ss []
QED

Theory abiScratchDecoderArray
Ancestors
  vyperABIValid abiScratchDecoderContract abiScratchDecoderRanges abiScratchEncoderContract
  abiScratchLeafEffect abiDecoderValidContract abiDecoderCorrectPrimitiveArray
  abiDecoderBulkReentry abiDecoderDynamic abiDecoderCoherence abiDecoderTypedContract
  abiDecoderContract abiDecoderReentry abiDecoderLoop abiDecoderFrame abiDecodeRanges
  abiValidStatic abiEncoder fragExec exprLowering compileEnv valueEncoding vyperABI vyperValue
  contractABI venomState venomExecSemantics words list arithmetic abiScratchDecoderInitReentry
  abiScratchDecoderTransport abiScratchEffect abiDecoderValidArray abiDecoderValidArrayMemory
  abiDecoderArrayInit abiDecoderArrayInitReentry abiDecoderAllocation abiEncoderArrayFrame
  abiScratchDecoderLoopInput abiScratchDecoderLoopEntry abiDecoderRecursiveArray
  abiScratchDecoderTuple abiDecoderValidFixed

(* Static-element bulk copying uses a validity-derived readable prefix and no scratch allocation. *)
Theorem abi_scratch_decoder_static_array_pre:
  abi_scratch_decoder_input ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    bs v st src dst opc hi sb d first last b cap s /\
  abi_decoder_budget first last b cap s /\ ~is_dynamic (vyper_to_abi_type env ty) ==>
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn)))
    (dec (Array NONE (vyper_to_abi_type env ty)) bs) v st st.cs_next_id src dst opc hi sb d
    s.vs_alloca_next 0 (abi_decoder_prune_vars st.cs_next_var s)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_decoder_input_point >> strip_tac >>
  `abi_decoder_reservation st.cs_next_id st.cs_next_id s.vs_alloca_next 0 s` by
    (mp_tac abi_scratch_decoder_point_reservation >> asm_simp_tac bool_ss []) >>
  `vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) bs` by
    fs[abi_scratch_decoder_input_def, Once vyper_to_abi_type_def,
      Excl "vyper_decode_valid_enc_def", Excl "dec_def", Excl "enc_def"] >>
  `valid_enc (Array NONE (vyper_to_abi_type env ty)) bs` by
    (qpat_x_assum `vyper_decode_valid_enc (Array NONE _) bs` mp_tac >>
     simp_tac bool_ss [Once vyper_decode_valid_enc_def, Once valid_enc_def, LET_THM] >>
     strip_tac >> gvs[] >>
     irule (cj 2 vyper_decode_valid_enc_static_mutual) >> simp[]) >>
  drule_all abi_valid_static_array_prefix >> strip_tac >>
  mp_tac (SIMP_RULE bool_ss [Once vyper_to_abi_type_def] (Q.INST
    [`ty` |-> `ArrayT ty (Dynamic maxn)`, `tv` |-> `ArrayTV tv (Dynamic maxn)`,
     `last` |-> `st.cs_next_id`, `b` |-> `s.vs_alloca_next`, `cap` |-> `0:num`]
    abi_decoder_valid_pre_prefix)) >> asm_simp_tac bool_ss [vyper_to_abi_type_def]
QED

Theorem abi_scratch_decoder_array_bulk:
  compile_abi_decode_to_buf dst src opc hi
    (DecDynArray (type_to_abi_dec_info sf ce ty) (abi_embedded_static_size ce.ce_struct_fields ty)
      (type_memory_bytes ce ty) F maxn) st = ((),end_st) /\
  ~is_abi_dynamic ce.ce_struct_fields ty /\ ~dec_info_needs_clamp (type_to_abi_dec_info sf ce ty) /\
  fn_has_code st end_st func /\
  abi_scratch_decoder_input ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    bs (ArrayV (DynArrayV vs)) st src dst opc hi sb d first last b cap initial /\
  abi_decoder_budget first last b cap initial /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d actual.vs_memory /\
    abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var limit_st
      d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
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
  (qpat_assum `~is_abi_dynamic ce.ce_struct_fields ty` (fn static =>
    qpat_assum `abi_decoder_recursive_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
      (assume_tac o SIMP_RULE bool_ss [Once type_to_abi_dec_info_def, static])) >>
  drule_all (Q.INST [`st'` |-> `end_st`, `b` |-> `initial.vs_alloca_next`, `cap` |-> `0:num`,
    `last` |-> `st.cs_next_id`] abi_decoder_bulk_reentry_from_state) >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var limit_st
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial actual` by
    (irule abi_scratch_leaf_effect >> asm_simp_tac bool_ss [] >> first_assum ACCEPT_TAC) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [])
QED

(* Actual source-valid array initialization with precise physical scratch effects. *)
Theorem abi_scratch_decoder_array_init_inputs:
  abi_scratch_decoder_input ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    bs (ArrayV (DynArrayV vs)) st src dst opc hi sb d first last b cap initial /\
  abi_decoder_budget first last b cap initial ==>
  abi_decode_source_opcode opc /\ eval_operand src initial = SOME (n2w sb) /\
  eval_operand dst initial = SOME (n2w d) /\ d < dimword (:256) /\
  abi_decode_load opc (n2w sb:bytes32) initial = n2w (LENGTH vs) /\
  LENGTH vs <= maxn /\ maxn < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb + 32 + LENGTH vs * abi_embedded_static_size ce.ce_struct_fields ty <= h /\ h < dimword (:256)) /\
  abi_footprint_disjoint d 32
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_decoder_input_point >> strip_tac >>
  drule abi_decoder_valid_array_pre_observations >>
    disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_valid_array_init_inputs >>
    disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_scratch_decoder_input ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    bs (ArrayV (DynArrayV vs)) st src dst opc hi sb d first last b cap initial`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_input_def]) >>
  qpat_assum `abi_scratch_decoder_ranges _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_ranges_def]) >>
  `32 <= type_memory_bytes ce (ArrayT ty (Dynamic maxn))` by simp[Once type_memory_bytes_def] >>
  `abi_footprint_disjoint d 32
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial)` by
    (irule abi_footprint_disjoint_subwindow >>
     qexistsl_tac [`d`, `type_memory_bytes ce (ArrayT ty (Dynamic maxn))`] >>
     asm_simp_tac (srw_ss()) []) >>
  asm_simp_tac bool_ss []
QED

Theorem abi_scratch_decoder_array_initialize:
  abi_decode_array_loop_init dst src opc hi maxn (abi_embedded_static_size ce.ce_struct_fields ty)
    st = (setup,loop_st) /\
  abi_scratch_decoder_input ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    bs (ArrayV (DynArrayV vs)) st src dst opc hi sb d first last b cap initial /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ loop_st.cs_next_id <= last /\
  loop_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st loop_st func /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual slot.
    abi_scratch_decoder_input ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
      bs (ArrayV (DynArrayV vs)) loop_st src dst opc hi sb d first last b cap actual /\
    abi_decoder_valid_array_memory opc bs tv vs sb d 0 actual /\
    abi_scratch_effect first last st.cs_next_id loop_st.cs_next_id st.cs_next_var
      limit_st d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial actual /\
    FLOOKUP actual.vs_allocas (loop_st.cs_next_id-2) = SOME (slot,32) /\
    eval_operand (FST setup) actual = SOME (n2w slot) /\ mload slot actual = 0w /\
    eval_operand (SND setup) actual = SOME (n2w (LENGTH vs)) /\
    abi_decoder_operand_live loop_st.cs_next_var (FST setup) /\
    actual.vs_current_bb = loop_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH loop_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_decoder_array_init_inputs >>
    disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decode_array_loop_init_shape >> strip_tac >>
  drule_all abi_scratch_decoder_init_from_state >>
    disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  qpat_assum `abi_decoder_array_init_post _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o PURE_REWRITE_RULE [abi_decoder_array_init_post_def]) >>
  disch_then (qx_choose_then `slot` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `32 <= type_memory_bytes ce (ArrayT ty (Dynamic maxn))` by simp[Once type_memory_bytes_def] >>
  `abi_scratch_effect first last st.cs_next_id loop_st.cs_next_id st.cs_next_var
    limit_st d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial actual` by
    (mp_tac (Q.INST [`child_lo` |-> `st.cs_next_id`, `child_hi` |-> `loop_st.cs_next_id`,
       `child_next` |-> `st.cs_next_var`, `child_d` |-> `d:num`, `child_sz` |-> `32:num`,
       `lo` |-> `st.cs_next_id`, `hi` |-> `loop_st.cs_next_id`, `next` |-> `st.cs_next_var`,
       `sz` |-> `type_memory_bytes ce (ArrayT ty (Dynamic maxn))`,
       `s` |-> `initial:venom_state`, `t` |-> `actual:venom_state`] abi_scratch_effect_widen) >>
     asm_simp_tac (srw_ss()) []) >>
  `abi_scratch_decoder_input ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    bs (ArrayV (DynArrayV vs)) st src dst opc hi sb d first last b cap actual` by
    (mp_tac (Q.INST [`ty` |-> `ArrayT ty (Dynamic maxn)`, `tv` |-> `ArrayTV tv (Dynamic maxn)`,
       `v` |-> `ArrayV (DynArrayV vs)`, `lo` |-> `st.cs_next_id`,
       `hi_id` |-> `loop_st.cs_next_id`, `next` |-> `st.cs_next_var`, `hi_op` |-> `hi:operand`]
       abi_scratch_decoder_input_effect) >> asm_simp_tac (srw_ss()) []) >>
  `abi_scratch_decoder_input ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    bs (ArrayV (DynArrayV vs)) loop_st src dst opc hi sb d first last b cap actual` by
    (irule abi_scratch_decoder_input_mono >> qexists_tac `st` >> asm_simp_tac bool_ss []) >>
  `mem_bytes_at sb (LENGTH bs) (abi_decode_source opc actual) = bs` by
    fs[abi_scratch_decoder_input_def] >>
  `abi_decoder_valid_array_memory opc bs tv vs sb d 0 actual` by
    (irule abi_decoder_valid_array_memory_init >> asm_simp_tac bool_ss []) >>
  drule abi_decode_array_loop_index_live >> strip_tac >>
  qexistsl_tac [`actual`, `slot`] >> asm_simp_tac bool_ss []
QED

(* The real array initializer and finite loop compose under physical ownership. *)
Theorem abi_scratch_decoder_array_execute:
  compile_abi_decode_to_buf dst src opc hi_op
    (DecDynArray (type_to_abi_dec_info sf ce ty) (abi_embedded_static_size ce.ce_struct_fields ty)
      (type_memory_bytes ce ty) (is_abi_dynamic ce.ce_struct_fields ty) maxn)
    st = ((),final) /\
  (is_abi_dynamic ce.ce_struct_fields ty \/ dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)) /\
  abi_scratch_decoder ce env sf ty tv /\ fn_has_code st final func /\
  (!bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_decoder_input ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    bs (ArrayV (DynArrayV vs)) st src dst opc hi_op sb d first last b cap initial /\
  (is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ final.cs_next_id <= last /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
    abi_scratch_effect first last st.cs_next_id final.cs_next_id st.cs_next_var limit_st
      d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial t /\
    t.vs_current_bb = final.cs_current_bb /\ t.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode opc` by fs[abi_scratch_decoder_input_def, abi_scratch_decoder_ranges_def] >>
  drule_all abi_decoder_recursive_array_code >> strip_tac >>
  `loop_st.cs_next_var <= limit_st.cs_next_var /\ loop_st.cs_next_id <= last /\
    first <= loop_st.cs_next_id-2 /\ loop_st.cs_next_id-2 < last` by decide_tac >>
  drule_all abi_scratch_decoder_array_initialize >>
  disch_then (qspec_then `ctx` (qx_choose_then `prepared`
    (qx_choose_then `slot` (MAP_EVERY assume_tac o CONJUNCTS)))) >>
  `fresh_vars_wrt limit_st prepared /\ abi_decoder_budget first last b cap prepared`
    by fs[abi_scratch_effect_def] >>
  mp_tac (Q.INST [`st` |-> `loop_st`, `initial` |-> `prepared:venom_state`,
    `site` |-> `loop_st.cs_next_id-2`, `ip` |-> `FST (setup:operand # operand)`,
    `hi` |-> `hi_op:operand`] abi_scratch_decoder_loop_input) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.INST [`lo` |-> `st.cs_next_id`, `hi` |-> `final.cs_next_id`,
    `ip` |-> `FST (setup:operand # operand)`, `cnt` |-> `SND (setup:operand # operand)`,
    `next` |-> `loop_st.cs_next_var`, `start` |-> `loop_st:compile_state`,
    `initial` |-> `prepared:venom_state`, `site` |-> `loop_st.cs_next_id-2`]
    abi_scratch_decoder_loop_from_state) >>
  impl_tac >- asm_simp_tac bool_ss [LESS_EQ_REFL] >> strip_tac >>
  `abi_scratch_effect first last st.cs_next_id final.cs_next_id st.cs_next_var limit_st
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap prepared t` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `final.cs_next_id`, `st.cs_next_id`,
       `loop_st.cs_next_var`, `type_memory_bytes ce (ArrayT ty (Dynamic maxn))`] >>
     asm_simp_tac bool_ss [LESS_EQ_REFL]) >>
  `abi_scratch_effect first last st.cs_next_id final.cs_next_id st.cs_next_var limit_st
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial prepared` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `loop_st.cs_next_id`, `st.cs_next_id`,
       `st.cs_next_var`, `type_memory_bytes ce (ArrayT ty (Dynamic maxn))`] >>
     asm_simp_tac bool_ss [LESS_EQ_REFL]) >>
  `abi_scratch_effect first last st.cs_next_id final.cs_next_id st.cs_next_var limit_st
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial t` by
    (drule_all abi_scratch_effect_trans >> simp[]) >>
  qexists_tac `t` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `prepared` >> asm_simp_tac bool_ss []
QED

(* Both emitted dynamic-array branches satisfy the physical decoder contract. *)
Theorem abi_scratch_decoder_array_loop:
  abi_scratch_decoder ce env sf ty tv /\
  (is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  (is_abi_dynamic ce.ce_struct_fields ty \/ dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)) ==>
  abi_scratch_decoder ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  simp_tac bool_ss [abi_scratch_decoder_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_scratch_decoder_input ce env sf (ArrayT ty (Dynamic maxn))
    (ArrayTV tv (Dynamic maxn)) bs v start src dst opc hi sb d first last b cap initial`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_input_def]) >>
  drule abi_decoder_dynarray_metadata_shape >> strip_tac >>
  gvs[Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  (qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _`
    (assume_tac o PURE_REWRITE_RULE [cj 3 type_to_abi_dec_info_def]) >>
  `abi_decode_source_opcode opc` by fs[abi_scratch_decoder_ranges_def] >>
  mp_tac (Q.INST [`st` |-> `start`, `final` |-> `end_st`,
    `ei` |-> `type_to_abi_dec_info (sf:string |-> (string # vyperAST$type # num) list) ce ty`,
    `asz` |-> `abi_embedded_static_size ce.ce_struct_fields ty`,
    `msz` |-> `type_memory_bytes ce ty`, `dyn` |-> `is_abi_dynamic ce.ce_struct_fields ty`]
    abi_decoder_recursive_array_adds_blocks) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  `!bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0` by metis_tac[] >>
  mp_tac (Q.INST [`st` |-> `start`, `final` |-> `end_st`, `hi_op` |-> `hi:operand`]
    abi_scratch_decoder_array_execute) >>
  impl_tac >- asm_simp_tac bool_ss [] >> asm_simp_tac bool_ss [])
QED

Theorem abi_scratch_decoder_array_copy:
  ~is_abi_dynamic ce.ce_struct_fields ty /\ ~dec_info_needs_clamp (type_to_abi_dec_info sf ce ty) ==>
  abi_scratch_decoder ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  simp_tac bool_ss [abi_scratch_decoder_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_scratch_decoder_input ce env sf (ArrayT ty (Dynamic maxn))
    (ArrayTV tv (Dynamic maxn)) bs v start src dst opc hi sb d first last b cap initial`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_input_def]) >>
  drule abi_decoder_dynarray_metadata_shape >> strip_tac >>
  gvs[Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  (qpat_assum `~is_abi_dynamic ce.ce_struct_fields ty` (fn static =>
    qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _`
      (assume_tac o SIMP_RULE bool_ss [Once type_to_abi_dec_info_def, static])) >>
  mp_tac (Q.INST [`st` |-> `start`] abi_scratch_decoder_array_bulk) >>
  impl_tac >- asm_simp_tac bool_ss [] >> asm_simp_tac bool_ss [])
QED

Theorem abi_scratch_decoder_array:
  abi_scratch_decoder ce env sf ty tv /\
  (is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) ==>
  abi_scratch_decoder ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
  strip_tac >>
  Cases_on `is_abi_dynamic ce.ce_struct_fields ty \/ dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)`
  >- (irule abi_scratch_decoder_array_loop >> asm_simp_tac bool_ss []) >>
  irule abi_scratch_decoder_array_copy >> fs[]
QED

Theorem abi_scratch_decoder_base_array:
  !bt. abi_scratch_decoder ce env sf
    (ArrayT (BaseT bt) (Dynamic maxn)) (ArrayTV (BaseTV bt) (Dynamic maxn))
Proof
  gen_tac >> irule abi_scratch_decoder_array >>
  metis_tac[abi_scratch_decoder_base, abi_decoder_valid_base_member_nonempty]
QED

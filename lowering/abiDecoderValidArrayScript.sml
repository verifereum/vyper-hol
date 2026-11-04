Theory abiDecoderValidArray
Ancestors
  abiDecoderValidContract abiDecoderValidArraySetupInputs abiDecoderRecursiveArray
  abiDecoderCoherence abiDecoderTypedContract abiDecoderContract abiDecoderReentry
  abiValidAggregateHeads abiValidMember abiCanonicalHeadSize abiDecodeRanges compileEnv
  valueEncoding vyperABI vyperValue contractABI venomState words list arithmetic
  abiDecoderValidLoopContext abiDecoderRecursiveArrayIteration abiDecoderValidArrayMemory
  abiDecoderArrayInitReentry abiDecoderArrayInit abiDecoderArrayInitExec
  abiDecoderArrayInvariant abiDecoderArrayLoopInit abiDecoderEffect abiDecoderReservation
  abiDecoderAllocation abiDecoderLoop fragExec exprLoweringProps emitHelperProps
  abiDecoderValidLoopEntry abiDecoderValidPrefix abiDecoderValidFixed
  abiDecoderCorrectPrimitiveArray abiEncoder exprLowering

(* Actual source observations justify the emitted array initializer. *)
Theorem abi_decoder_valid_array_pre_observations:
  abi_decoder_valid_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    bs (ArrayV (DynArrayV vs)) st src dst opc hi sb d b cap initial ==>
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Dynamic maxn)))
    (dec (Array NONE (vyper_to_abi_type env ty)) bs) (ArrayV (DynArrayV vs)) /\
  vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) bs /\
  abi_decoder_ranges opc hi src dst sb (LENGTH bs)
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc initial) = bs /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi
Proof
  simp_tac bool_ss [abi_decoder_valid_pre_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  RULE_ASSUM_TAC (SIMP_RULE bool_ss [Once vyper_to_abi_type_def]) >> asm_simp_tac bool_ss []
QED

Theorem abi_decoder_source_head_load:
  32 <= LENGTH bs /\ mem_bytes_at sb (LENGTH bs) (abi_decode_source opc s) = bs /\
  sb + LENGTH bs < dimword (:256) ==>
  abi_decode_load opc (n2w sb : bytes32) s = n2w (abi_head_word bs)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `sb < dimword (:256)` by decide_tac >>
  `mem_bytes_at sb 32 (abi_decode_source opc s) = TAKE 32 bs` by
    (mp_tac (SIMP_RULE bool_ss [ADD_CLAUSES, DROP_0]
      (Q.INST [`off` |-> `0:num`, `n` |-> `32:num`] abi_decode_source_window)) >>
     asm_simp_tac bool_ss []) >>
  asm_simp_tac bool_ss [abi_decode_load_bytes, abi_head_word_bytes]
QED

Theorem abi_decoder_valid_array_init_inputs:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (dec (Array NONE (vyper_to_abi_type env ty)) bs) (ArrayV (DynArrayV vs)) /\
  vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) bs /\
  abi_decoder_ranges opc hi src dst sb
    (LENGTH bs)
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial /\
  mem_bytes_at sb (LENGTH bs)
    (abi_decode_source opc initial) = bs ==>
  abi_decode_source_opcode opc /\ eval_operand src initial = SOME (n2w sb) /\
  eval_operand dst initial = SOME (n2w d) /\ d < dimword (:256) /\
  abi_decode_load opc (n2w sb:bytes32) initial = n2w (LENGTH vs) /\
  LENGTH vs <= maxn /\ maxn < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb + 32 + LENGTH vs * abi_embedded_static_size ce.ce_struct_fields ty <= h /\
    h < dimword (:256)) /\ (d + 32 <= b \/ b + cap <= d)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_valid_dynarray_values >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_valid_dynamic_array_view >> strip_tac >>
  drule abi_decoder_coherent_array_capacity >> strip_tac >>
  `abi_decoder_coherent ce env sf ty tv` by fs[abi_decoder_coherent_array_iff] >>
  `abi_embedded_static_size ce.ce_struct_fields ty = abi_member_head_size (vyper_to_abi_type env ty)`
    by metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  qpat_assum `abi_head_word bs = LENGTH vs`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> assume_tac th) >>
  `32 + LENGTH vs * abi_embedded_static_size ce.ce_struct_fields ty <=
    LENGTH bs` by
    (fs[LENGTH_DROP, Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >> decide_tac) >>
  qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_ranges_def]) >>
  drule_all abi_decoder_source_head_load >> strip_tac >>
  `d < dimword (:256)` by decide_tac >>
  SUBGOAL_THEN ``d + 32 <= b \/ b + cap <= d`` assume_tac
  >- (qpat_x_assum `d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= b \/ _` mp_tac >>
      simp_tac bool_ss [Once type_memory_bytes_def] >> strip_tac >> decide_tac) >>
  SUBGOAL_THEN ``hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb + 32 + LENGTH (vs:vyperValue$value list) * abi_embedded_static_size ce.ce_struct_fields ty <= h /\
    h < dimword (:256)`` assume_tac
  >- (Cases_on `hi = Lit 0w` >- simp[] >>
      qpat_x_assum `hi = Lit 0w \/ _` mp_tac >> asm_simp_tac bool_ss [] >> strip_tac >>
      qexists_tac `h` >> asm_simp_tac bool_ss [] >>
      qpat_x_assum `32 + LENGTH vs * abi_embedded_static_size ce.ce_struct_fields ty <= _` mp_tac >>
      asm_simp_tac bool_ss [] >> decide_tac) >>
  asm_simp_tac bool_ss [] >> metis_tac[]
QED

(* Execute generic dynamic-array initialization and establish recursive loop data. *)
Theorem abi_decoder_valid_init_data:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Dynamic maxn)))
    (dec (Array NONE (vyper_to_abi_type env ty)) bs) (ArrayV (DynArrayV vs)) /\
  vyper_decode_valid_enc (Array NONE (vyper_to_abi_type env ty)) bs /\
  is_dynamic (vyper_to_abi_type env ty) /\
  (!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  abi_decoder_ranges opc hi src dst sb
    (LENGTH bs)
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial /\
  mem_bytes_at sb (LENGTH bs)
    (abi_decode_source opc initial) = bs /\
  abi_decoder_effect first last lo hi_id next limit_st
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial prepared /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
  abi_decoder_operand_live next hi /\ next <= loop_next /\
  abi_decoder_operand_live loop_next ip /\ eval_operand ip prepared = SOME (n2w slot) /\
  slot < dimword (:256) /\ mem_word_at d prepared.vs_memory = n2w (LENGTH vs) ==>
  abi_decoder_valid_array_memory opc bs tv vs sb d 0 prepared /\
  abi_decoder_valid_loop_data ce env sf ty tv maxn bs vs opc hi ip src dst
    sb d slot b cap loop_next prepared
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_effect_ranges >> strip_tac >>
  `abi_decode_footprint_frame [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)));(b,cap)]
    initial prepared` by fs[abi_decoder_effect_def, Excl "enc_def"] >>
  drule_all abi_decoder_source_frame >> strip_tac >>
  `abi_decoder_valid_array_memory opc bs tv vs sb d 0 prepared` by
    (irule abi_decoder_valid_array_memory_init >> metis_tac[]) >>
  asm_simp_tac bool_ss [abi_decoder_valid_loop_data_def] >>
  metis_tac[abi_decoder_operand_live_mono]
QED

Theorem abi_decoder_valid_array_initialize:
  abi_decode_array_loop_init dst src opc hi maxn (abi_embedded_static_size ce.ce_struct_fields ty)
    st = (setup,loop_st) /\
  abi_decoder_valid_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    bs (ArrayV (DynArrayV vs)) st src dst opc hi sb d b cap initial /\
  is_dynamic (vyper_to_abi_type env ty) /\
  (!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\
  loop_st.cs_next_id <= owner_hi /\ owner_hi <= last /\
  loop_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st loop_st func /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?prepared slot.
    abi_decoder_valid_array_memory opc bs tv vs sb d 0 prepared /\
    abi_decoder_valid_loop_data ce env sf ty tv maxn bs vs opc hi (FST setup) src dst
      sb d slot b cap loop_st.cs_next_var prepared /\
    abi_decoder_effect first last st.cs_next_id owner_hi st.cs_next_var limit_st
      d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial prepared /\
    FLOOKUP prepared.vs_allocas (loop_st.cs_next_id-2) = SOME (slot,32) /\
    mload slot prepared = 0w /\ prepared.vs_current_bb = loop_st.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH loop_st.cs_current_insts /\ ~prepared.vs_halted /\
    abi_decode_sim ctx func initial prepared
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_valid_array_pre_observations >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_valid_array_init_inputs >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decode_array_loop_init_shape >> strip_tac >>
  drule_all abi_decode_array_loop_init_site_bounds >> strip_tac >>
  `loop_st.cs_next_id <= last` by decide_tac >>
  drule_all abi_decode_array_loop_init_reentry_from_state >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial prepared` >>
  qpat_assum `abi_decoder_array_init_post _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_decoder_array_init_post_def]) >>
  rename1 `mload slot prepared = 0w` >>
  `32 <= type_memory_bytes ce (ArrayT ty (Dynamic maxn))` by
    simp[Once type_memory_bytes_def] >>
  SUBGOAL_THEN ``d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= b \/ b + cap <= d`` assume_tac
  >- (qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
      simp_tac bool_ss [abi_decoder_ranges_def] >>
      disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> first_assum ACCEPT_TAC) >>
  `st.cs_next_id <= loop_st.cs_next_id-2 /\ loop_st.cs_next_id-2 < owner_hi` by decide_tac >>
  `abi_decoder_effect first last st.cs_next_id owner_hi st.cs_next_var limit_st
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial prepared` by
    (mp_tac (Q.INST [`lo` |-> `st.cs_next_id`, `hi` |-> `owner_hi:num`,
      `next` |-> `st.cs_next_var`, `site` |-> `loop_st.cs_next_id-2`,
      `n` |-> `LENGTH (vs:vyperValue$value list)`,
      `outsz` |-> `type_memory_bytes ce (ArrayT ty (Dynamic maxn))`]
      abi_decoder_recursive_init_effect) >> asm_simp_tac bool_ss []) >>
  `slot < dimword (:256)` by
    (qpat_assum `abi_decoder_budget _ _ _ _ prepared` mp_tac >>
     simp_tac bool_ss [abi_decoder_budget_def] >> strip_tac >> decide_tac) >>
  drule abi_decode_array_loop_index_live >> strip_tac >>
  drule_all abi_decoder_valid_init_data >> strip_tac >>
  qexistsl_tac [`prepared`, `slot`] >> asm_simp_tac bool_ss []
QED

(* Compose actual generic initialization with finite recursive array execution. *)
Theorem abi_decoder_valid_array_execute:
  compile_abi_decode_to_buf dst src opc hi_op
    (DecDynArray (type_to_abi_dec_info sf ce ty) (abi_embedded_static_size ce.ce_struct_fields ty)
      (type_memory_bytes ce ty) (is_abi_dynamic ce.ce_struct_fields ty) maxn)
    st = ((),final) /\
  (is_abi_dynamic ce.ce_struct_fields ty \/ dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)) /\
  abi_decoder_valid_correct ce env sf ty tv /\ fn_has_code st final func /\
  (!bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_valid_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    bs (ArrayV (DynArrayV vs)) st src dst opc hi_op sb d b cap initial /\
  is_dynamic (vyper_to_abi_type env ty) /\
  (!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ final.cs_next_id <= last /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
    abi_decoder_effect first last st.cs_next_id final.cs_next_id st.cs_next_var limit_st
      d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial t /\
    t.vs_current_bb = final.cs_current_bb /\ t.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_valid_array_pre_observations >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode opc` by fs[abi_decoder_ranges_def, Excl "enc_def"] >>
  drule_all abi_decoder_recursive_array_code >> strip_tac >>
  `loop_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all (Q.INST [`owner_hi` |-> `final.cs_next_id`] abi_decoder_valid_array_initialize) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `fresh_vars_wrt limit_st prepared /\ abi_decoder_budget first last b cap prepared`
    by fs[abi_decoder_effect_def, Excl "enc_def"] >>
  mp_tac (Q.INST [`lo` |-> `st.cs_next_id`, `hi` |-> `final.cs_next_id`,
    `ip` |-> `FST (setup:operand # operand)`,
    `cnt` |-> `SND (setup:operand # operand)`,
    `next` |-> `loop_st.cs_next_var`, `start` |-> `loop_st:compile_state`,
    `initial` |-> `prepared:venom_state`, `site` |-> `loop_st.cs_next_id-2`]
    abi_decoder_valid_loop_from_state) >>
  impl_tac >- asm_simp_tac bool_ss [LESS_EQ_REFL] >> strip_tac >>
  `abi_decoder_effect first last st.cs_next_id final.cs_next_id st.cs_next_var limit_st
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap prepared t` by
    (mp_tac (Q.INST [`s` |-> `prepared:venom_state`, `t` |-> `t:venom_state`,
      `lo` |-> `st.cs_next_id`, `hi` |-> `final.cs_next_id`, `next` |-> `st.cs_next_var`,
      `child_next` |-> `loop_st.cs_next_var`,
      `sz` |-> `type_memory_bytes ce (ArrayT ty (Dynamic maxn))`] abi_decoder_effect_lower_vars) >>
     asm_simp_tac bool_ss []) >>
  `abi_decoder_effect first last st.cs_next_id final.cs_next_id st.cs_next_var limit_st
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial t` by
    (drule_all abi_decoder_effect_trans >> simp[]) >>
  `abi_decode_sim ctx func initial t` by metis_tac[abi_decode_sim_trans] >>
  qexists_tac `t` >> asm_simp_tac bool_ss []
QED

(* Dynamic arrays close the actual-source decoder API for both emitted branches. *)
Theorem abi_decoder_valid_correct_dynamic_array:
  abi_decoder_valid_correct ce env sf ty tv /\ is_dynamic (vyper_to_abi_type env ty) /\
  (!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) ==>
  abi_decoder_valid_correct ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  simp_tac bool_ss [abi_decoder_valid_correct_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_decoder_valid_pre ce env sf (ArrayT ty (Dynamic maxn))
    (ArrayTV tv (Dynamic maxn)) bs v start src dst opc hi sb d b cap initial`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_valid_pre_def]) >>
  drule abi_decoder_dynarray_metadata_shape >> strip_tac >>
  gvs[Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"] >>
  `abi_decoder_coherent ce env sf ty tv` by fs[abi_decoder_coherent_array_iff] >>
  `is_abi_dynamic ce.ce_struct_fields ty` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [Once type_to_abi_dec_info_def] >> strip_tac >>
  `abi_decode_source_opcode opc` by fs[abi_decoder_ranges_def] >>
  qpat_assum `is_abi_dynamic ce.ce_struct_fields ty`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> assume_tac th) >>
  drule_all (SIMP_RULE bool_ss []
    (Q.INST [`dyn` |-> `T`] abi_decoder_recursive_array_adds_blocks)) >> disch_then assume_tac >>
  `!bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0` by metis_tac[] >>
  mp_tac (Q.INST [`st` |-> `start`, `final` |-> `end_st`, `hi_op` |-> `hi:operand`]
    abi_decoder_valid_array_execute) >>
  impl_tac >- asm_simp_tac bool_ss [] >> asm_simp_tac bool_ss []
QED

Theorem abi_decoder_valid_correct_array:
  abi_decoder_valid_correct ce env sf ty tv /\
  (is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem) ==>
  abi_decoder_valid_correct ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  Cases_on `is_dynamic (vyper_to_abi_type env ty)`
  >- (irule abi_decoder_valid_correct_dynamic_array >> asm_simp_tac bool_ss []) >>
  irule abi_decoder_valid_correct_static_array >>
  qexists_tac `vyper_to_abi_type env ty` >> asm_simp_tac bool_ss [Once vyper_to_abi_type_def]
QED

Theorem abi_decoder_valid_correct_base_array:
  !bt. abi_decoder_valid_correct ce env sf
    (ArrayT (BaseT bt) (Dynamic maxn)) (ArrayTV (BaseTV bt) (Dynamic maxn))
Proof
  gen_tac >> irule abi_decoder_valid_correct_array >>
  metis_tac[abi_decoder_valid_correct_base, abi_decoder_valid_base_member_nonempty]
QED

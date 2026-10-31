Theory abiDecoderRecursiveArray
Ancestors
  abiDecoderArrayInit abiDecoderArrayInitExec abiDecoderEffect abiDecoderProtectedScratch
  abiDecoderAllocation abiDecoderTypedContract abiDecoderContract abiDecoderFrame compileEnv
  venomState words arithmetic abiDecoderCoherence abiDecoderArrayInvariant abiDecoderReentry
  abiDecoderArrayInitReentry abiDecoderPrimitiveArrayReentry abiCanonicalHeadSize
  abiDecodeRanges valueEncoding vyperABI vyperTyping vyperValue contractABI list
  abiDecoderArrayLoopInit abiDecoderLoopEmit abiDecoderRecursiveLoopLayout
  abiDecoderArraySetupCode abiDecoderLoopCode abiDecoderAppend abiDecoderCode abiDecoderCounters
  fragExec exprLoweringProps emitHelperProps abiDecoderRecursiveLoopContext
  abiDecoderRecursiveArrayIteration abiDecoderReservation abiDecoderLoop
  abiDecoderRecursiveLoopEntry abiDecoderCorrect

(* An actual array initializer owns its slot and preserves surrounding scratch. *)
Theorem abi_decoder_recursive_init_effect:
  abi_decoder_array_init_post setup next limit_st site first last b cap d n initial prepared /\
  first <= lo /\ lo <= site /\ site < hi /\ hi <= last /\
  32 <= outsz /\ (d + outsz <= b \/ b + cap <= d) ==>
  abi_decoder_effect first last lo hi next limit_st d outsz b cap initial prepared
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_decoder_array_init_post _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_decoder_array_init_post_def]) >>
  rename1 `FLOOKUP prepared.vs_allocas site = SOME (slot,32)` >>
  `abi_decode_footprint_frame [(d,outsz);(b,cap)] initial prepared` by
    (mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `prepared:venom_state`,
       `b` |-> `b:num`, `cap` |-> `cap:num`] abi_decoder_array_init_frame_widen) >>
     asm_simp_tac bool_ss []) >>
  `abi_decode_footprint_frame [(d,outsz);(slot,32)] initial prepared` by
    (mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `prepared:venom_state`,
       `b` |-> `slot:num`, `cap` |-> `32:num`] abi_decoder_array_init_frame_widen) >>
     asm_simp_tac bool_ss []) >>
  mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `prepared:venom_state`,
    `child_first` |-> `lo:num`, `child_last` |-> `hi:num`] abi_decoder_child_scratch_preservation) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_then assume_tac >>
  asm_simp_tac bool_ss [abi_decoder_effect_def, abi_decoder_scratch_frame_def] >>
  conj_tac
  >- (rpt strip_tac >> `id <> site` by decide_tac >> metis_tac[]) >>
  rpt strip_tac >> `id IN abi_decoder_ids first last` by simp[abi_decoder_ids_def] >> metis_tac[]
QED

Theorem abi_decoder_effect_lower_vars:
  abi_decoder_effect first last lo hi child_next limit_st d sz b cap s t /\ next <= child_next ==>
  abi_decoder_effect first last lo hi next limit_st d sz b cap s t
Proof
  strip_tac >> mp_tac (Q.INST [`child_lo` |-> `lo:num`, `child_hi` |-> `hi:num`,
    `child_d` |-> `d:num`, `child_sz` |-> `sz:num`] abi_decoder_effect_widen) >>
  asm_simp_tac (srw_ss()) []
QED

(* Canonical and typed inputs for recursive array initialization. *)
Theorem abi_decoder_array_capacity_arithmetic:
  !n sz limit:num. 0 < sz /\ 1 + n * sz < limit ==> n < limit
Proof
  rpt strip_tac >> Cases_on `sz` >> gvs[MULT_CLAUSES] >> decide_tac
QED

Theorem abi_decoder_coherent_array_capacity:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) ==>
  maxn < dimword (:256)
Proof
  strip_tac >>
  `evaluate_type env (ArrayT ty (Dynamic maxn)) = SOME (ArrayTV tv (Dynamic maxn))` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  `0 < type_slot_size tv /\ type_slot_size (ArrayTV tv (Dynamic maxn)) < dimword (:256)` by
    (qpat_x_assum `evaluate_type env (ArrayT _ _) = _` mp_tac >>
     simp[Once evaluate_type_def, AllCaseEqs()]) >>
  irule abi_decoder_array_capacity_arithmetic >> qexists_tac `type_slot_size tv` >>
  fs[type_slot_size_def]
QED

Theorem abi_decoder_array_encoding_head_bound:
  has_type (Array NONE aty) (ListV avs) ==>
  32 + LENGTH avs * abi_member_head_size aty <= LENGTH (enc (Array NONE aty) (ListV avs))
Proof
  strip_tac >> drule canonical_array_length >> simp_tac bool_ss [] >> strip_tac >> decide_tac
QED

Theorem abi_decoder_array_pre_observations:
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    di (ListV avs) (ArrayV (DynArrayV vs)) st last src dst opc hi sb d b cap
    (abi_decoder_prune_vars st.cs_next_var initial) ==>
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Dynamic maxn)))
    (ListV avs) (ArrayV (DynArrayV vs)) /\
  abi_decoder_ranges opc hi src dst sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    (abi_decode_source opc initial) = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi
Proof
  strip_tac >> qpat_assum `abi_decoder_recursive_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_pre_def]) >>
  drule abi_decoder_pre_pruned_operands >> strip_tac >>
  qpat_assum `abi_decoder_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_pre_def]) >>
  `abi_decoder_ranges opc hi src dst sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial` by
    (qpat_x_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     asm_simp_tac bool_ss [abi_decoder_prune_ranges, Once vyper_to_abi_type_def]) >>
  asm_simp_tac bool_ss [] >>
  fs[abi_decoder_prune_source, Once vyper_to_abi_type_def, Excl "enc_def"]
QED

Theorem abi_decoder_recursive_array_init_inputs:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV avs) (ArrayV (DynArrayV vs)) /\
  abi_decoder_ranges opc hi src dst sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    (abi_decode_source opc initial) = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) ==>
  abi_decode_source_opcode opc /\ eval_operand src initial = SOME (n2w sb) /\
  eval_operand dst initial = SOME (n2w d) /\ d < dimword (:256) /\
  abi_decode_load opc (n2w sb:bytes32) initial = n2w (LENGTH vs) /\
  LENGTH vs <= maxn /\ maxn < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
    sb + 32 + LENGTH vs * abi_embedded_static_size ce.ce_struct_fields ty <= h /\
    h < dimword (:256)) /\ (d + 32 <= b \/ b + cap <= d)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_dynarray_values >> strip_tac >>
  drule abi_decoder_coherent_array_capacity >> strip_tac >>
  `abi_decoder_coherent ce env sf ty tv` by fs[abi_decoder_coherent_array_iff] >>
  `abi_embedded_static_size ce.ce_struct_fields ty = abi_member_head_size (vyper_to_abi_type env ty)`
    by metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  `32 + LENGTH vs * abi_embedded_static_size ce.ce_struct_fields ty <=
    LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs))` by
    (drule abi_decoder_array_encoding_head_bound >> asm_simp_tac bool_ss []) >>
  qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_ranges_def]) >>
  drule_all canonical_dynamic_array_count_load >> strip_tac >>
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

(* ===== Code ===== *)

(* Extract actual initializer and recursive loop code from array compilation. *)

Theorem abi_decoder_recursive_loop_end:
  compile_abi_decode_dyn_loop dst src opc hi ei asz msz ip cnt start = ((),final) /\
  abi_decode_source_opcode opc ==>
  start.cs_next_id <= final.cs_next_id /\ start.cs_next_var <= final.cs_next_var /\
  final.cs_current_insts = [] /\
  final.cs_current_bb = fresh_label_output "dec_dyn_exit" (start.cs_next_label+2) /\
  cs_extends start final
Proof
  strip_tac >> drule_all abi_decoder_dyn_loop_code >>
  simp_tac bool_ss [abi_decoder_code_def] >> strip_tac >>
  `start.cs_next_var <= final.cs_next_var` by
    metis_tac[cj 3 abi_decoder_vars_mono_mutual, abi_decoder_vars_mono_def, pairTheory.SND] >>
  `cs_extends start final` by metis_tac[cj 3 cs_appends_abi_decode_mutual, cs_appends_def] >>
  drule abi_decode_dyn_loop_trace >> strip_tac >>
  drule abi_decoder_array_setup_head >> strip_tac >>
  qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_decoder_loop_suffix_facts >> strip_tac >>
  qpat_x_assum `abi_decode_loop_prefix _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [abi_decode_loop_prefix_shape] >> strip_tac >> gvs[]
QED

Theorem abi_decoder_recursive_array_code:
  compile_abi_decode_to_buf dst src opc hi (DecDynArray ei asz msz dyn maxn) st = ((),final) /\
  (dyn \/ dec_info_needs_clamp ei) /\ abi_decode_source_opcode opc /\ fn_has_code st final func ==>
  ?setup loop_st.
    abi_decode_array_loop_init dst src opc hi maxn asz st = (setup,loop_st) /\
    compile_abi_decode_dyn_loop dst src opc hi ei asz msz (FST setup) (SND setup)
      loop_st = ((),final) /\
    fn_has_code st loop_st func /\ fn_has_code loop_st final func /\
    st.cs_next_var <= loop_st.cs_next_var /\
    loop_st.cs_next_id <= final.cs_next_id /\ loop_st.cs_next_var <= final.cs_next_var /\
    st.cs_next_id <= loop_st.cs_next_id-2 /\ loop_st.cs_next_id-2 < loop_st.cs_next_id /\
    final.cs_current_insts = [] /\
    final.cs_current_bb = fresh_label_output "dec_dyn_exit" (loop_st.cs_next_label+2)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decode_loop_array_trace >> strip_tac >>
  drule_all abi_decode_array_loop_init_shape >> strip_tac >>
  drule_all abi_decode_array_loop_init_site_bounds >> strip_tac >>
  drule_all abi_decoder_recursive_loop_end >> strip_tac >>
  `cs_extends st loop_st` by (irule cs_extends_same_block >> simp[]) >>
  mp_tac (Q.SPECL [`st`, `loop_st`, `final`, `func`] fn_has_code_split) >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  qexistsl_tac [`setup`, `loop_st`] >> simp[]
QED

Theorem abi_decoder_recursive_array_adds_blocks:
  compile_abi_decode_to_buf dst src opc hi (DecDynArray ei asz msz dyn maxn) st = ((),final) /\
  (dyn \/ dec_info_needs_clamp ei) /\ abi_decode_source_opcode opc /\ fn_has_code st final func ==>
  st.cs_blocks <> final.cs_blocks
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_recursive_array_code >> strip_tac >>
  drule_all abi_decode_array_loop_init_shape >> strip_tac >>
  drule abi_decode_dyn_loop_trace >> strip_tac >>
  rename1 `abi_decode_loop_prefix _ _ _ loop_st = (labels,body_st)` >>
  rename1 `abi_decode_loop_suffix _ _ _ _ child_end = ((),final)` >>
  drule_all abi_decoder_loop_phase_containment >> strip_tac >>
  drule abi_decoder_loop_prefix_facts >> strip_tac >>
  drule abi_decoder_array_setup_head >> strip_tac >>
  qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_decoder_loop_suffix_facts >> strip_tac >>
  `?children. child_end.cs_blocks = children ++ body_st.cs_blocks` by fs[cs_extends_def] >>
  `LENGTH st.cs_blocks < LENGTH final.cs_blocks` by
    (asm_simp_tac bool_ss [LENGTH_APPEND, LENGTH] >> decide_tac) >>
  strip_tac >> gvs[]
QED

(* ===== Init ===== *)

(* Execute generic dynamic-array initialization and establish recursive loop data. *)

Theorem abi_decoder_recursive_init_data:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Dynamic maxn)))
    (ListV avs) (ArrayV (DynArrayV vs)) /\
  abi_decoder_ranges opc hi src dst sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    (abi_decode_source opc initial) = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  abi_decoder_effect first last lo hi_id next limit_st
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial prepared /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
  abi_decoder_operand_live next hi /\ next <= loop_next /\
  abi_decoder_operand_live loop_next ip /\ eval_operand ip prepared = SOME (n2w slot) /\
  slot < dimword (:256) /\ mem_word_at d prepared.vs_memory = n2w (LENGTH vs) ==>
  abi_decoder_array_memory opc (vyper_to_abi_type env ty) avs tv vs sb d 0 prepared /\
  abi_decoder_recursive_loop_data ce env sf ty tv maxn avs vs opc hi ip src dst
    sb d slot b cap loop_next prepared
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_effect_ranges >> strip_tac >>
  `abi_decode_footprint_frame [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)));(b,cap)]
    initial prepared` by fs[abi_decoder_effect_def, Excl "enc_def"] >>
  drule_all abi_decoder_source_frame >> strip_tac >>
  `abi_decoder_array_memory opc (vyper_to_abi_type env ty) avs tv vs sb d 0 prepared` by
    (irule abi_decoder_array_memory_init >> metis_tac[]) >>
  asm_simp_tac bool_ss [abi_decoder_recursive_loop_data_def] >>
  metis_tac[abi_decoder_operand_live_mono]
QED

Theorem abi_decoder_recursive_array_initialize:
  abi_decode_array_loop_init dst src opc hi maxn (abi_embedded_static_size ce.ce_struct_fields ty)
    st = (setup,loop_st) /\
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    di (ListV avs) (ArrayV (DynArrayV vs)) st last src dst opc hi sb d b cap
    (abi_decoder_prune_vars st.cs_next_var initial) /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\
  loop_st.cs_next_id <= owner_hi /\ owner_hi <= last /\
  loop_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  fn_has_code st loop_st func /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?prepared slot.
    abi_decoder_array_memory opc (vyper_to_abi_type env ty) avs tv vs sb d 0 prepared /\
    abi_decoder_recursive_loop_data ce env sf ty tv maxn avs vs opc hi (FST setup) src dst
      sb d slot b cap loop_st.cs_next_var prepared /\
    abi_decoder_effect first last st.cs_next_id owner_hi st.cs_next_var limit_st
      d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial prepared /\
    FLOOKUP prepared.vs_allocas (loop_st.cs_next_id-2) = SOME (slot,32) /\
    mload slot prepared = 0w /\ prepared.vs_current_bb = loop_st.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH loop_st.cs_current_insts /\ ~prepared.vs_halted /\
    abi_decode_sim ctx func initial prepared
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_array_pre_observations >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_recursive_array_init_inputs >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
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
  drule_all abi_decoder_recursive_init_data >> strip_tac >>
  qexistsl_tac [`prepared`, `slot`] >> asm_simp_tac bool_ss []
QED

(* ===== Execute ===== *)

(* Compose actual generic initialization with finite recursive array execution. *)

Theorem abi_decoder_recursive_array_execute:
  compile_abi_decode_to_buf dst src opc hi_op
    (DecDynArray (type_to_abi_dec_info sf ce ty) (abi_embedded_static_size ce.ce_struct_fields ty)
      (type_memory_bytes ce ty) (is_abi_dynamic ce.ce_struct_fields ty) maxn)
    st = ((),final) /\
  (is_abi_dynamic ce.ce_struct_fields ty \/ dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)) /\
  abi_decoder_correct ce env sf ty tv /\ fn_has_code st final func /\
  (!bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    di (ListV avs) (ArrayV (DynArrayV vs)) st last src dst opc hi_op sb d b cap
    (abi_decoder_prune_vars st.cs_next_var initial) /\
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
  drule abi_decoder_array_pre_observations >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode opc` by fs[abi_decoder_ranges_def, Excl "enc_def"] >>
  drule_all abi_decoder_recursive_array_code >> strip_tac >>
  `loop_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all (Q.INST [`owner_hi` |-> `final.cs_next_id`] abi_decoder_recursive_array_initialize) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `fresh_vars_wrt limit_st prepared /\ abi_decoder_budget first last b cap prepared`
    by fs[abi_decoder_effect_def, Excl "enc_def"] >>
  mp_tac (Q.INST [`lo` |-> `st.cs_next_id`, `hi` |-> `final.cs_next_id`,
    `ip` |-> `FST (setup:operand # operand)`,
    `cnt` |-> `SND (setup:operand # operand)`,
    `next` |-> `loop_st.cs_next_var`, `start` |-> `loop_st:compile_state`,
    `initial` |-> `prepared:venom_state`, `site` |-> `loop_st.cs_next_id-2`]
    abi_decoder_recursive_loop_from_state) >>
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

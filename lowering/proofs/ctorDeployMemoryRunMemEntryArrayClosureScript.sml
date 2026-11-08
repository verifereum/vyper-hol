Theory ctorDeployMemoryRunMemEntryArrayClosure
Ancestors
  loweringStateRelDefs
 ctorDeployMemoryRunMemEntryComplex ctorDeployMemoryRunMemEntryArrayFinite
 ctorDeployMemoryRunMemEntryBulk ctorDeployMemoryRunMemEntryWord
 ctorAbiActualBulk abiDecoderBulkReentry abiDecoderBulkExecute abiDecoderBulk
 ctorAbiActualObservations venomState venomExecSemantics
 abiDecoderReentryPointer ctorAbiActualWorld instIdxIndep
 ctorAbiActualArrayClosure abiDecoderFixedInputs abiDecoderFixedMemory
 abiDecoderMemberInfos rich_list vyperABI vyperTypeABI compileEnv
 ctorAbiActualArrayInvariant ctorAbiActualArrayEntry ctorAbiActualArrayContext
 ctorDeployMemoryRunMemEntryCompositeEdges
 abiDecoderLoop arithmetic ctorAbiActualArrayRun ctorAbiActualArrayLayout
 ctorDeployMemoryRunMemEntryArraySteps abiDecoderRecursiveLoopContext
 abiDecoderLoopEmit abiDecoderArrayLoopInit abiDecoderIndexInit
 abiDecoderReentry allocaFrontierBound ctorAbiActualFrame exprLowering
 abiDecoderCode abiDecoderCounters abiDecoderArraySetupCode ctorAbiActualSites
 abiDecoderRecursiveLoopLayout abiDecoderCorrectPrimitiveArray
 abiDecoderRecursiveLoopEntry abiDecoderRecursiveArray
 abiCanonicalHeadSize abiDecoderTypedContract abiDecoderContract
 abiDecoderCoherence abiEncoderRegisteredEffect fragGasPathMem allocaHistory

val C = ``\ty tv.
 !dst src hi st st' ctx func site initial limit_st sb d D N ids av v root_di.
 compile_abi_decode_to_buf dst src DLOAD hi (type_to_abi_dec_info sf ce ty) st = ((),st') /\
 abi_decoder_coherent ce env sf ty tv /\
 abi_decoder_metadata ce env ty tv root_di av v /\
 eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
 sb + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
 sb + LENGTH (enc (vyper_to_abi_type env ty) av) <= LENGTH initial.vs_data_section /\
 mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av)) initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
 (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\ sb + LENGTH (enc (vyper_to_abi_type env ty) av) <= h /\ h < dimword (:256)) /\
 (!x. src = Var x \/ dst = Var x \/ hi = Var x ==> not_fresh_at st x) /\
 st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
 fn_has_code st st' func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = st'.cs_blocks \/ !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\ unit_alloca_budget ctx < dimword (:256) /\
 alloca_history func initial /\
 D <= d /\ d + type_memory_bytes ce ty <= D+N /\ D+N <= initial.vs_alloca_next /\
 frag_ids st st' SUBSET ids /\ ctor_actual_scratch func ids D N initial /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?actual. val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st')) [(d,type_memory_bytes ce ty)] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv ctx func site actual /\
 ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
 actual.vs_data_section = initial.vs_data_section /\ actual.vs_call_ctx = initial.vs_call_ctx /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==> lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\
 actual.vs_labels = initial.vs_labels /\
 gas_path_mem ctx func initial 0 (OK actual) /\ actual.vs_gas_readings = initial.vs_gas_readings /\
 alloca_history func actual``;

(* Fixed arrays use member decoding (including the zero-member case).
   Dynamic arrays split into recursive/clamped loops and bulk copies. *)
Theorem ctor_checked_fixed_array_run:
 (^C) ty tv ==> (^C) (ArrayT ty (Fixed n)) (ArrayTV tv (Fixed n))
Proof
 strip_tac >> simp_tac bool_ss [] >> rpt gen_tac >>
 disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 drule_all abi_decoder_fixed_array_values >> strip_tac >>
 gnvs[Once vyper_to_abi_type_def, canonical_array_tuple, Excl "enc_def"] >>
 qpat_assum `LENGTH vs = LENGTH avs`
   (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM th]) >> assume_tac th) >>
 `type_memory_bytes ce (ArrayT ty (Fixed (LENGTH vs))) =
   LENGTH vs * type_memory_bytes ce ty` by simp[Once type_memory_bytes_def] >>
 qpat_assum `type_memory_bytes ce (ArrayT ty (Fixed (LENGTH vs))) = _`
   (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
 `LIST_REL (^C) (REPLICATE (LENGTH vs) ty) (REPLICATE (LENGTH vs) tv)` by
   (simp_tac bool_ss [LIST_REL_REPLICATE_same] >> BETA_TAC >>
    strip_tac >> first_assum ACCEPT_TAC) >>
 qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _`
   (assume_tac o PURE_REWRITE_RULE [abi_decoder_fixed_array_infos]) >>
 drule_all (SIMP_RULE bool_ss [map_replicate, SUM_REPLICATE]
   (Q.INST [`tys` |-> `REPLICATE (LENGTH vs) ty`,
     `tvs` |-> `REPLICATE (LENGTH vs) tv`] (BETA_RULE ctor_checked_complex_execute))) >>
 disch_then (qx_choose_then `actual` (MAP_EVERY assume_tac o CONJUNCTS)) >>
 qexists `actual` >>
 qpat_x_assum `LENGTH vs = LENGTH avs` (fn th => rewrite_tac[GSYM th]) >>
 asm_simp_tac bool_ss [Once type_memory_bytes_def] >>
 irule abi_decoder_fixed_array_memory >> asm_simp_tac bool_ss []
QED

val P = ``
 abi_decoder_recursive_loop_compiled ce sf ty func st middle end_st ops ip src dst DLOAD hi
   hdr exit_lbl hid header_var first last lo hi_id next limit_st slot_id /\
 abi_decoder_recursive_loop_data ce env sf ty tv maxn avs vs DLOAD hi ip src dst
   sb d slot b cap next prepared /\
 fn_inst_ids_distinct func /\
 mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
   prepared.vs_data_section = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
 sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) <= LENGTH prepared.vs_data_section /\
 unit_alloca_budget ctx < dimword (:256) /\
 D <= d /\ d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= D+N /\
 frag_ids st end_st SUBSET ids /\ slot_id NOTIN frag_ids middle end_st /\
 slot_id IN ctor_actual_sites func ids /\
 venomMemDefs$regions_disjoint (slot,32) (d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)))``;

Theorem ctor_checked_array_prepared_run:
 (^C) ty tv /\ ^P /\
 ctor_actual_array_observation ctx func site ids D N d
   (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) earlier limit_st
   tv vs slot_id slot initial 0 0 prepared /\ earlier <= next /\
 lookup_block prepared.vs_current_bb func.fn_blocks = SOME bb /\
 bb.bb_instructions = prefix ++ [mk_inst id JMP [Label hdr] []] /\
 lookup_block hdr func.fn_blocks = SOME hdr_bb /\
 phi_prefix_length hdr_bb.bb_instructions = 0 /\
 ~prepared.vs_halted /\ prepared.vs_inst_idx = LENGTH prefix /\
 abi_decode_sim ctx func initial prepared /\
 gas_path_mem ctx func initial 0 (OK prepared) /\
 prepared.vs_gas_readings = initial.vs_gas_readings /\ alloca_history func prepared ==>
 ?actual.
   val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d actual.vs_memory /\
   ctor_actual_array_observation ctx func site ids D N d
     (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) earlier limit_st
     tv vs slot_id slot initial (LENGTH vs) (LENGTH vs) actual /\
   ~actual.vs_halted /\ actual.vs_current_bb = exit_lbl /\ actual.vs_inst_idx = 0 /\
   abi_decode_sim ctx func initial actual /\ gas_path_mem ctx func initial 0 (OK actual) /\
   actual.vs_gas_readings = initial.vs_gas_readings /\ alloca_history func actual
Proof
 disch_then (CONJUNCTS_THEN2 (mk_asm "child") (MAP_EVERY assume_tac o CONJUNCTS)) >>
 `ctor_actual_array_observation ctx func site ids D N d
   (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
   tv vs slot_id slot prepared 0 0 prepared` by
   (irule ctor_actual_array_observation_self >> goal_assum (drule_at Any)) >>
 drule_all ctor_checked_array_entry_jump >>
 disch_then (qx_choose_then `h` (MAP_EVERY assume_tac o CONJUNCTS)) >>
 asm "child" assume_tac >>
 drule_all ctor_checked_array_loop_finite >>
 disch_then (qx_choose_then `actual` (MAP_EVERY assume_tac o CONJUNCTS)) >>
 `ctor_actual_array_observation ctx func site ids D N d
   (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) earlier limit_st
   tv vs slot_id slot initial (LENGTH vs) (LENGTH vs) actual` by
   (irule ctor_actual_array_observation_compose >> goal_assum (drule_at Any) >> simp[]) >>
 qexists `actual` >> asm_simp_tac bool_ss [] >> conj_tac
 >- (irule ctor_actual_array_observation_exit >> goal_assum (drule_at Any)) >>
 conj_tac >- metis_tac[abi_decode_sim_trans] >>
 asm_x "child" kall_tac >> metis_tac[gas_path_mem_then, ADD_0]
QED

Theorem ctor_checked_dynamic_array_loop_run:
 (^C) ty tv /\
 (is_abi_dynamic ce.ce_struct_fields ty \/
   dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)) ==>
 (^C) (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
 qabbrev_tac `Child = (^C) ty tv` >>
 disch_then (CONJUNCTS_THEN2 (mk_asm "child") assume_tac) >>
 simp_tac bool_ss [] >> rpt gen_tac >>
 disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 drule abi_decoder_dynarray_metadata_shape >> strip_tac >> gnvs[Excl "enc_def"] >>
 `abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Dynamic maxn)))
    (ListV avs) (ArrayV (DynArrayV vs))` by fs[abi_decoder_metadata_def] >>
 `compile_abi_decode_to_buf dst src DLOAD hi
    (DecDynArray (type_to_abi_dec_info sf ce ty)
      (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty)
      (is_abi_dynamic ce.ce_struct_fields ty) maxn) st = ((),st')` by
    (qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
     simp_tac bool_ss [Once type_to_abi_dec_info_def]) >>
 drule_all ctor_actual_array_loop_layout >> strip_tac >>
 drule_all ctor_actual_array_prefix_inputs >>
 disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 `abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi` by
   (Cases_on `src` >> Cases_on `dst` >> Cases_on `hi` >>
    fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
 `loop_st.cs_next_var <= limit_st.cs_next_var` by
   fs[abi_decoder_recursive_loop_compiled_def] >>
 `32 <= type_memory_bytes ce (ArrayT ty (Dynamic maxn)) /\ d+32 <= D+N` by
   fs[Once type_memory_bytes_def] >>
 `d < dimword (:256)` by
   (drule_all alloca_frontier_inv_bound >> strip_tac >> decide_tac) >>
 `sb < dimword (:256) /\ sb+32 <= LENGTH initial.vs_data_section` by
   (`has_type (Array NONE (vyper_to_abi_type env ty)) (ListV avs)` by
      fs[abi_decoder_metadata_def, Once vyper_to_abi_type_def] >>
    drule abi_decoder_array_encoding_head_bound >> strip_tac >> decide_tac) >>
 `ctor_actual_scratch func (frag_ids st st') D N initial` by
   (irule ctor_actual_scratch_restrict >> goal_assum (drule_at Any) >> simp[]) >>
 `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts func))` by
   (irule ctor_actual_function_ids >> simp[]) >>
 drule_all ctor_checked_array_prefix_header_index_entry >>
 disch_then (qspec_then `tv`
   (qx_choose_then `prepared` (qx_choose_then `slot` (MAP_EVERY assume_tac o CONJUNCTS)))) >>
 `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
 `st.cs_next_var <= loop_st.cs_next_var` by
   (drule_all abi_decode_dynarray_prefix_shape >> strip_tac >>
    drule_all abi_decode_array_header_shape >> strip_tac >>
    drule abi_decode_index_init_shape >> strip_tac >> decide_tac) >>
 drule_all ctor_actual_array_setup_context >>
 disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 drule_all abi_decoder_loop_phase_entry >> disch_tac >>
 drule_all abi_decoder_recursive_compiled_facts >> strip_tac >>
 `?bb. lookup_block prepared.vs_current_bb func.fn_blocks = SOME bb /\
   bb.bb_instructions = loop_st.cs_current_insts ++
     [mk_inst loop_st.cs_next_id JMP [Label (FST labels)] []]` by simp[] >>
 pop_assum strip_assume_tac >>
 `sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) <=
   LENGTH prepared.vs_data_section` by
   fs[ctor_actual_array_observation_def, Once vyper_to_abi_type_def, Excl "enc_def"] >>
 asm_x "child" mp_tac >> simp_tac bool_ss [Abbr `Child`] >> disch_tac >>
 drule_all (BETA_RULE ctor_checked_array_prepared_run) >>
 disch_then (qx_choose_then `actual` (MAP_EVERY assume_tac o CONJUNCTS)) >>
 qpat_x_assum `ctor_actual_array_observation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ actual` mp_tac >>
 simp_tac bool_ss [ctor_actual_array_observation_def] >>
 disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 `ctor_actual_scratch func ids D N actual` by
   (simp_tac bool_ss [ctor_actual_scratch_def] >> rpt gen_tac >>
    disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
    Cases_on `inst.inst_id IN frag_ids st st'`
    >- (qpat_x_assum `ctor_actual_scratch func (frag_ids st st') _ _ actual` mp_tac >>
        simp_tac bool_ss [ctor_actual_scratch_def] >>
        disch_then (qspecl_then [`inst`, `b`, `sz`] mp_tac) >> asm_rewrite_tac[]) >>
    `inst.inst_id NOTIN ctor_actual_sites func (frag_ids st st')` by
      simp[ctor_actual_sites_def] >>
    qpat_x_assum `abi_encoder_registered_effect _ _ initial actual` mp_tac >>
    simp_tac bool_ss [abi_encoder_registered_effect_def] >> strip_tac >>
    `FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz)` by metis_tac[] >>
    qpat_x_assum `ctor_actual_scratch func ids _ _ initial` mp_tac >>
    simp_tac bool_ss [ctor_actual_scratch_def] >>
    disch_then (qspecl_then [`inst`, `b`, `sz`] mp_tac) >> asm_rewrite_tac[]) >>
 qexists `actual` >> asm_simp_tac bool_ss [] >>
 conj_tac
 >- (rpt strip_tac >> first_x_assum irule >>
     fs[abi_decoder_older_vars_def, not_fresh_at_def]) >>
 drule abi_decoder_array_setup_head >> strip_tac >>
 qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
 asm_rewrite_tac[] >> disch_then (mp_tac o MATCH_MP abi_decoder_loop_suffix_facts) >> simp[]
QED

Theorem ctor_checked_dynamic_array_bulk_run:
 ~(is_abi_dynamic ce.ce_struct_fields ty \/
   dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)) ==>
 (^C) (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
 disch_then (strip_assume_tac o SIMP_RULE bool_ss []) >>
 simp_tac bool_ss [] >> rpt gen_tac >>
 disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 drule abi_decoder_dynarray_metadata_shape >> strip_tac >> gnvs[Excl "enc_def"] >>
 `abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
   (type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Dynamic maxn)))
   (ListV avs) (ArrayV (DynArrayV vs))` by fs[abi_decoder_metadata_def] >>
 `abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi` by
   (Cases_on `src` >> Cases_on `dst` >> Cases_on `hi` >>
    fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
 `d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= initial.vs_alloca_next /\
  initial.vs_alloca_next < dimword (:256)` by
   (drule_all alloca_frontier_inv_bound >> strip_tac >> decide_tac) >>
 `abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
   (type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn))) (ListV avs) (ArrayV (DynArrayV vs))
   st st.cs_next_id src dst DLOAD hi sb d initial.vs_alloca_next 0
   (abi_decoder_prune_vars st.cs_next_var initial)` by
   (irule ctor_actual_bulk_empty_window_pre >>
    asm_simp_tac bool_ss [vyper_to_abi_type_def] >> goal_assum (drule_at Any)) >>
 qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _`
   (assume_tac o SIMP_RULE bool_ss [Once type_to_abi_dec_info_def]) >>
 qpat_x_assum `abi_decoder_recursive_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
   (assume_tac o SIMP_RULE bool_ss [Once type_to_abi_dec_info_def]) >>
 gnvs[Excl "enc_def"] >>
 `d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= initial.vs_alloca_next` by decide_tac >>
 drule_all (SIMP_RULE bool_ss [vyper_to_abi_type_def] ctor_checked_bulk_sequence) >>
 disch_then (qspec_then `ctx` strip_assume_tac) >>
 drule_all ctor_word_path_sim >> strip_tac >>
 `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
 drule_all abi_decoder_bulk_allocation_shape >> strip_tac >>
 drule_all abi_decoder_bulk_shape >> strip_tac >>
 drule_all ctor_actual_sequence_labels >> strip_tac >>
 drule_all ctor_actual_sequence_world >> strip_tac >>
 drule_all ctor_actual_scratch_free_effect >>
 disch_then (qspecl_then [`site`, `ctor_actual_sites func (frag_ids st st')`, `func`, `ctx`]
   strip_assume_tac) >>
 qexists `actual with vs_inst_idx := LENGTH st'.cs_current_insts` >>
 simp[] >> conj_tac
 >- (qpat_x_assum `abi_encoder_registered_effect _ _ _ _` mp_tac >>
     simp[abi_encoder_registered_effect_def]) >>
 conj_tac
 >- (qpat_x_assum `ctor_actual_scratch _ _ _ _ _` mp_tac >> simp[ctor_actual_scratch_def]) >>
 qpat_x_assum `abi_decode_frame _ _ _ _` mp_tac >>
 simp[abi_decode_frame_def] >> strip_tac >> simp[] >>
 reverse conj_tac
 >- (qpat_x_assum `fresh_vars_wrt _ actual` mp_tac >> simp[fresh_vars_wrt_def]) >>
 rpt strip_tac >>
 `abi_decoder_operand_live st.cs_next_var (Var x)` by
   (simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
    metis_tac[not_fresh_at_def]) >>
 `eval_operand (Var x) initial = SOME w` by simp[eval_operand_def] >>
 first_x_assum drule_all >> simp[eval_operand_def, lookup_var_def]
QED

Theorem ctor_checked_dynamic_array_run:
 (^C) ty tv ==> (^C) (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
 strip_tac >>
 Cases_on `is_abi_dynamic ce.ce_struct_fields ty \/
   dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)`
 >- (match_mp_tac ctor_checked_dynamic_array_loop_run >> asm_rewrite_tac[]) >>
 match_mp_tac ctor_checked_dynamic_array_bulk_run >> asm_rewrite_tac[]
QED

Theorem ctor_checked_array_run:
 (^C) ty tv ==> (^C) (ArrayT ty bd) (ArrayTV tv bd)
Proof
 Cases_on `bd`
 >- MATCH_ACCEPT_TAC ctor_checked_fixed_array_run >>
 MATCH_ACCEPT_TAC ctor_checked_dynamic_array_run
QED

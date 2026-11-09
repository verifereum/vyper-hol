(* Composition of canonical actual-site array setup and finite iteration. *)
Theory ctorAbiActualArrayRun
Ancestors
  ctorAbiActualArrayLayout ctorAbiActualArrayContext ctorAbiActualArrayEntry
  ctorAbiActualArrayFinite ctorAbiActualArrayInvariant
  abiDecoderRecursiveLoopContext abiDecoderRecursiveLoopLayout abiDecoderLoop abiDecoderContract
  abiDecoderTypedContract abiDecoderCorrectPrimitiveArray abiDecoderRecursiveArray
  abiCanonicalHeadSize abiDecoderArrayInvariant abiDecoderCoherence abiDecoderCode abiDecoderCounters
  abiDecoderArrayLoopInit abiDecoderArraySetupCode abiDecoderLoopEmit abiDecoderRecursiveLoopEntry
  abiDecoderIndexInit abiDecoderReentry allocaFrontierBound
  ctorAbiActualSites abiEncoderRegisteredEffect
  ctorAbiActualFrame exprLowering compileEnv venomWf venomInst venomState venomExecSemantics words list arithmetic

val C = ``\ty tv.
 !dst src hi st st' ctx func site initial limit_st sb d D N ids av v root_di.
 compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (type_to_abi_dec_info sf ce ty) st = ((),st') /\
 abi_decoder_coherent ce env sf ty tv /\
 abi_decoder_metadata ce env ty tv root_di av v /\
 eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
 sb + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
 mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av)) initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
 (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\ sb + LENGTH (enc (vyper_to_abi_type env ty) av) <= h /\ h < dimword (:256)) /\
 (!x. src = Var x \/ dst = Var x \/ hi = Var x ==> not_fresh_at st x) /\
 st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
 fn_has_code st st' func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = st'.cs_blocks \/ !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\ unit_alloca_budget ctx < dimword (:256) /\
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
 actual.vs_labels = initial.vs_labels``;

(* The loop's data baseline is prepared, not initial: ip exists only there. *)
val P = ``
 abi_decoder_recursive_loop_compiled ce sf ty func st middle end_st ops ip src dst DLOAD (Lit 0w) hi
   hdr exit_lbl hid header_var first last lo hi_id next limit_st slot_id /\
 abi_decoder_recursive_loop_data ce env sf ty tv maxn avs vs DLOAD (Lit 0w) hi ip src dst
   0 sb d slot b cap next prepared /\
 fn_inst_ids_distinct func /\
 mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
   prepared.vs_data_section = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
 unit_alloca_budget ctx < dimword (:256) /\
 D <= d /\ d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= D+N /\
 frag_ids st end_st SUBSET ids /\ slot_id NOTIN frag_ids middle end_st /\
 slot_id IN ctor_actual_sites func ids /\
 venomMemDefs$regions_disjoint (slot,32) (d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)))``;

Theorem ctor_actual_array_prepared_run:
 (^C) ty tv /\ ^P /\
 ctor_actual_array_observation ctx func site ids D N d
   (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) earlier limit_st
   tv vs slot_id slot initial 0 0 prepared /\ earlier <= next /\
 lookup_block prepared.vs_current_bb func.fn_blocks = SOME bb /\
 bb.bb_instructions = prefix ++ [mk_inst id JMP [Label hdr] []] /\
 lookup_block hdr func.fn_blocks = SOME hdr_bb /\
 phi_prefix_length hdr_bb.bb_instructions = 0 /\
 ~prepared.vs_halted /\ prepared.vs_inst_idx = LENGTH prefix /\
 abi_decode_sim ctx func initial prepared ==>
 ?actual.
   val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d actual.vs_memory /\
   ctor_actual_array_observation ctx func site ids D N d
     (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) earlier limit_st
     tv vs slot_id slot initial (LENGTH vs) (LENGTH vs) actual /\
   ~actual.vs_halted /\ actual.vs_current_bb = exit_lbl /\ actual.vs_inst_idx = 0 /\
   abi_decode_sim ctx func initial actual
Proof
 disch_then (CONJUNCTS_THEN2 (mk_asm "child") (MAP_EVERY assume_tac o CONJUNCTS)) >>
 `ctor_actual_array_observation ctx func site ids D N d
   (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
   tv vs slot_id slot prepared 0 0 prepared` by
   (irule ctor_actual_array_observation_self >> goal_assum (drule_at Any)) >>
 drule_all ctor_actual_array_entry_jump >>
 disch_then (qx_choose_then `h` (MAP_EVERY assume_tac o CONJUNCTS)) >>
 asm "child" assume_tac >>
 drule_all ctor_actual_array_loop_finite >>
 disch_then (qx_choose_then `actual` (MAP_EVERY assume_tac o CONJUNCTS)) >>
 `ctor_actual_array_observation ctx func site ids D N d
   (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) earlier limit_st
   tv vs slot_id slot initial (LENGTH vs) (LENGTH vs) actual` by
   (irule ctor_actual_array_observation_compose >> goal_assum (drule_at Any) >> simp[]) >>
 qexists `actual` >> asm_simp_tac bool_ss [] >> conj_tac
 >- (irule ctor_actual_array_observation_exit >> goal_assum (drule_at Any)) >>
 irule abi_decode_sim_trans >> qexists `prepared` >> asm_simp_tac bool_ss [] >>
 irule abi_decode_sim_trans >> qexists `h` >> simp[]
QED

Theorem ctor_actual_array_prefix_inputs:
 abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
 abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
   di (ListV avs) (ArrayV (DynArrayV vs)) /\
 eval_operand src initial = SOME (n2w sb) /\
 sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) < dimword (:256) /\
 mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
   initial.vs_data_section = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
 (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
   sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) <= h /\
   h < dimword (:256)) ==>
 abi_decode_load DLOAD (n2w sb : bytes32) initial = n2w (LENGTH vs) /\
 LENGTH vs <= maxn /\ maxn < dimword (:256) /\
 (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
   sb+32+LENGTH vs*abi_embedded_static_size ce.ce_struct_fields ty <= h /\
   h < dimword (:256))
Proof
 disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 drule abi_decoder_dynarray_values >> strip_tac >>
 drule abi_decoder_coherent_array_capacity >> strip_tac >>
 `abi_decoder_coherent ce env sf ty tv` by fs[abi_decoder_coherent_array_iff] >>
 `abi_embedded_static_size ce.ce_struct_fields ty = abi_member_head_size (vyper_to_abi_type env ty)` by
   metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
 `32 + LENGTH vs * abi_embedded_static_size ce.ce_struct_fields ty <=
   LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs))` by
   (drule abi_decoder_array_encoding_head_bound >> asm_simp_tac bool_ss []) >>
 `mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
   (abi_decode_source DLOAD initial) = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)` by
   simp[abi_decode_source_def, Excl "enc_def"] >>
 drule_all canonical_dynamic_array_count_load >> strip_tac >>
 asm_simp_tac bool_ss [] >>
 Cases_on `hi = Lit 0w` >- simp[] >>
 qpat_x_assum `hi = Lit 0w \/ _` mp_tac >> asm_rewrite_tac[] >> strip_tac >>
 qexists `h` >> asm_simp_tac bool_ss [] >>
 qpat_x_assum `32 + LENGTH vs * _ <= _` mp_tac >>
 asm_simp_tac bool_ss [] >> decide_tac
QED

Theorem ctor_actual_function_ids:
 fn_inst_ids_distinct func ==> ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts func))
Proof
 `!bbs. MAP (\i. i.inst_id) (fn_insts_blocks bbs) =
   FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs)` by
   (Induct >> simp[fn_insts_blocks_def]) >>
 simp[fn_inst_ids_distinct_def, fn_insts_def]
QED

Theorem ctor_operand_live[local]:
  (!x. op = Var x ==> not_fresh_at st x) ==>
  abi_decoder_operand_live st.cs_next_var op
Proof
  Cases_on `op` >>
  simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       not_fresh_at_def]
QED

Theorem ctor_actual_dynamic_array_loop_run:
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
 `compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi
    (DecDynArray (type_to_abi_dec_info sf ce ty)
      (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty)
      (is_abi_dynamic ce.ce_struct_fields ty) maxn) st = ((),st')` by
    (qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
     simp_tac bool_ss [Once type_to_abi_dec_info_def]) >>
 drule_all ctor_actual_array_loop_layout >> strip_tac >>
 drule_all ctor_actual_array_prefix_inputs >>
 disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 `abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi` by
   (rpt conj_tac >> irule ctor_operand_live >> rpt strip_tac >>
    qpat_x_assum `!x. src = Var x \/ dst = Var x \/ hi = Var x ==> _`
      irule >> simp[]) >>
 `loop_st.cs_next_var <= limit_st.cs_next_var` by
   fs[abi_decoder_recursive_loop_compiled_def] >>
 `32 <= type_memory_bytes ce (ArrayT ty (Dynamic maxn)) /\ d+32 <= D+N` by
   fs[Once type_memory_bytes_def] >>
 `d < dimword (:256)` by
   (drule_all alloca_frontier_inv_bound >> strip_tac >> decide_tac) >>
 `ctor_actual_scratch func (frag_ids st st') D N initial` by
   (irule ctor_actual_scratch_restrict >> goal_assum (drule_at Any) >> simp[]) >>
 `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts func))` by
   (irule ctor_actual_function_ids >> simp[]) >>
 drule_all ctor_actual_array_prefix_header_index_entry >>
 disch_then (qspec_then `tv`
   (qx_choose_then `prepared` (qx_choose_then `slot` (MAP_EVERY assume_tac o CONJUNCTS)))) >>
 `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
 `st.cs_next_var <= loop_st.cs_next_var` by
   (drule_all abi_decode_dynarray_checked_prefix_shape >> strip_tac >>
    drule_all abi_decode_array_header_shape >> strip_tac >>
    drule abi_decode_index_init_shape >> strip_tac >> decide_tac) >>
 drule_all ctor_actual_array_setup_context >>
 disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 drule_all abi_decoder_loop_phase_entry >> disch_tac >>
 drule_all abi_decoder_recursive_compiled_facts >> strip_tac >>
 `?bb. lookup_block prepared.vs_current_bb func.fn_blocks = SOME bb /\
   bb.bb_instructions = loop_st.cs_current_insts ++
     [mk_inst loop_st.cs_next_id JMP [Label (FST labels)] []]` by
   simp[] >>
 pop_assum strip_assume_tac >>
 asm_x "child" mp_tac >> simp_tac bool_ss [Abbr `Child`] >> disch_tac >>
 drule_all (BETA_RULE ctor_actual_array_prepared_run) >>
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

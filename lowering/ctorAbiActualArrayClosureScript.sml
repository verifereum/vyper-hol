(* Complete array consumers, isolated from loop producer simplification. *)
Theory ctorAbiActualArrayClosure
Ancestors
 ctorAbiActualArrayRun ctorAbiActualComplex abiDecoderFixedInputs
 abiDecoderFixedMemory abiDecoderMemberInfos rich_list
 vyperABI vyperTypeABI compileEnv loweringStateRelDefs abiCanonicalHeadSize
 ctorAbiActualBulk ctorAbiActualNarrowWord abiDecoderBulkReentry
 abiDecoderCorrectPrimitiveArray
 abiDecoderLoop abiDecoderTypedContract abiDecoderContract
 abiDecoderReentryPointer abiDecoderReentry abiEncoderRegisteredEffect
 abiEncoderProps allocaFrontierBound allocaBudgetProps venomState exprLowering

val C = ``\ty tv.
 !dst src hi st st' ctx func site initial limit_st sb d D N ids av v root_di.
 compile_abi_decode_to_buf dst src DLOAD hi (type_to_abi_dec_info sf ce ty) st = ((),st') /\
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

Theorem ctor_actual_fixed_array_run:
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
     `tvs` |-> `REPLICATE (LENGTH vs) tv`] (BETA_RULE ctor_actual_complex_execute))) >>
 disch_then (qx_choose_then `actual` (MAP_EVERY assume_tac o CONJUNCTS)) >>
 qexists `actual` >>
 qpat_x_assum `LENGTH vs = LENGTH avs` (fn th => rewrite_tac[GSYM th]) >>
 asm_simp_tac bool_ss [Once type_memory_bytes_def] >>
 irule abi_decoder_fixed_array_memory >> asm_simp_tac bool_ss []
QED

Theorem ctor_actual_dynamic_array_bulk_run:
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
    asm_simp_tac bool_ss [vyper_to_abi_type_def] >>
    goal_assum (drule_at Any)) >>
 qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _`
   (assume_tac o SIMP_RULE bool_ss [Once type_to_abi_dec_info_def]) >>
 qpat_x_assum `abi_decoder_recursive_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
   (assume_tac o SIMP_RULE bool_ss [Once type_to_abi_dec_info_def]) >>
 gnvs[Excl "enc_def"] >>
 drule_all ctor_actual_bulk_labels_fragment >>
 disch_then (qspecl_then [`site`, `func`, `ctx`] assume_tac) >>
 drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
 rename1 `abi_decode_sim ctx func initial actual` >>
 qpat_x_assum `frag_exec _ _ _ _ _ _` kall_tac >>
 `abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
   [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)))] initial actual` by
   (irule abi_encoder_registered_effect_enlarge >>
    qexistsl [`{}`, `[(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)))]`] >> simp[]) >>
 `ctor_actual_scratch func ids D N actual` by
   (drule ctor_actual_scratch_same_allocas >> simp[]) >>
 qpat_assum `abi_decode_frame _ _ _ _`
   (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decode_frame_def]) >>
 qexists `actual` >> asm_simp_tac bool_ss [] >> rpt strip_tac >>
 `abi_decoder_operand_live st.cs_next_var (Var x)` by
   (simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
    metis_tac[not_fresh_at_def]) >>
 `eval_operand (Var x) initial = SOME w` by simp[eval_operand_def] >>
 first_x_assum drule_all >> simp[eval_operand_def]
QED

Theorem ctor_actual_dynamic_array_run:
 (^C) ty tv ==> (^C) (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
 strip_tac >>
 Cases_on `is_abi_dynamic ce.ce_struct_fields ty \/
   dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)`
 >- (match_mp_tac ctor_actual_dynamic_array_loop_run >> asm_rewrite_tac[]) >>
 match_mp_tac ctor_actual_dynamic_array_bulk_run >> asm_rewrite_tac[]
QED

Theorem ctor_actual_array_run:
 (^C) ty tv ==> (^C) (ArrayT ty bd) (ArrayTV tv bd)
Proof
 Cases_on `bd`
 >- MATCH_ACCEPT_TAC ctor_actual_fixed_array_run >>
 MATCH_ACCEPT_TAC ctor_actual_dynamic_array_run
QED

Theory ctorDeployLoweringEntryCompleteNoAlloc
Ancestors
  loweringStateRelDefs
 ctorDeployLoweringEntryCompleteScalar ctorDeployLoweringEntryDecoder
 ctorDeployLoweringEntryRegistration ctorDeployLoweringEntryArrayFrame
 ctorDeployMemoryFrontier ctorAbiActualLabelBytes ctorAbiActualBulk
 ctorAbiActualObservations ctorAbiActualBytes ctorAbiActualNarrowWord
 abiDecoderVarSequence abiDecoderBytesTyped abiDecoderBytesFrame abiDecoderLoop
 abiDecoderBulkReentry abiDecoderBulkExecute abiDecoderBulk
 abiDecoderContract abiDecoderReentryPointer abiDecoderReentry
 abiDecoderTypedContract abiDecoderCoherence ctorAbiActualWorld
 abiEncoderRegisteredEffect abiEncoderProps allocaFrontierBound allocaBudgetProps
 fragExec instIdxIndep venomState venomExecSemantics venomInst
 compileEnv valueEncoding words list arithmetic finite_map venomMemDefs
 vyperABI vyperTypeABI exprLowering abiDecoderCorrectPrimitiveArray

Theorem deploy_ctor_bytestring_complete_fragment:
 compile_abi_decode_to_buf dst src DLOAD hi (DecBytestring n) st = ((),st') /\
 abi_decoder_coherent ce env sf ty tv /\
 type_to_abi_dec_info sf ce ty = DecBytestring n /\
 abi_decoder_metadata ce env ty tv root_di av v /\
 eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
 sb < dimword (:256) /\ d < dimword (:256) /\
 type_memory_bytes ce ty < dimword (:256) /\
 (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
   sb + LENGTH (enc (vyper_to_abi_type env ty) av) <= h /\ h < dimword (:256)) /\
 mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av)) initial.vs_data_section =
   enc (vyper_to_abi_type env ty) av /\
 abi_decoder_operand_live st.cs_next_var src /\
 abi_decoder_operand_live st.cs_next_var dst /\
 abi_decoder_operand_live st.cs_next_var hi /\
 st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
 frag_exec ctx st st' (\s. s = initial)
   (\t. val_in_memory tv v d t.vs_memory /\ fresh_vars_wrt limit_st t /\
     abi_decode_frame d (type_memory_bytes ce ty) initial t /\
     (!op w. abi_decoder_operand_live st.cs_next_var op /\
       eval_operand op initial = SOME w ==> eval_operand op t = SOME w) /\
     t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next /\
     abi_encoder_registered_effect {} [(d,type_memory_bytes ce ty)] initial t /\
     (alloca_inv t <=> alloca_inv initial) /\
     (alloca_frontier_inv ctx func site t <=> alloca_frontier_inv ctx func site initial) /\
     t.vs_labels = initial.vs_labels /\
     t.vs_gas_readings = initial.vs_gas_readings /\ t.vs_code = initial.vs_code /\
     t.vs_outcomes = initial.vs_outcomes /\ t.vs_tx_ctx = initial.vs_tx_ctx /\
     t.vs_block_ctx = initial.vs_block_ctx) (K F)
Proof
 disch_then (map_every assume_tac o CONJUNCTS) >>
 `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
 drule_all abi_decoder_bytes_shape >> strip_tac >>
 irule frag_exec_run_inst_seq >> simp[] >>
 drule_all ctor_actual_bytestring_ceiling_sequence >> strip_tac >>
 drule_all abi_decoder_bytes_reentry_code >> strip_tac >>
 drule_all deploy_ctor_decoder_sequence_observations >> strip_tac >>
 drule_all deploy_ctor_decoder_sequence_ambient >> strip_tac >>
 qexists `actual` >>
 gvs[fresh_vars_wrt_def, abi_decode_frame_def, eval_op_inst_idx,
   abi_encoder_registered_effect_def, alloca_inv_def, alloca_frontier_inv_def,
   remaining_alloca_budget_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
 metis_tac[]
QED

Theorem deploy_ctor_bulk_complete_fragment:
 compile_abi_decode_to_buf dst src DLOAD hi (DecDynArray ei abi_sz mem_sz F maxn)
   st = ((),st') /\ ~dec_info_needs_clamp ei /\
 abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
   (DecDynArray ei abi_sz mem_sz F maxn) (ListV avs) (ArrayV (DynArrayV vs))
   st last src dst DLOAD hi sb d b cap (abi_decoder_prune_vars st.cs_next_var initial) /\
 st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
 frag_exec ctx st st' (\s. s = initial)
   (\actual. val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d actual.vs_memory /\
     fresh_vars_wrt limit_st actual /\
     (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
       eval_operand op actual = SOME w) /\
     abi_decode_frame d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) initial actual /\
     actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
     abi_encoder_registered_effect {} [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)))] initial actual /\
     (alloca_inv actual <=> alloca_inv initial) /\
     (alloca_frontier_inv ctx func site actual <=> alloca_frontier_inv ctx func site initial) /\
     actual.vs_labels = initial.vs_labels /\
     actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code /\
     actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\
     actual.vs_block_ctx = initial.vs_block_ctx) (K F)
Proof
 disch_then (map_every assume_tac o CONJUNCTS) >>
 `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
 drule_all abi_decoder_bulk_shape >> strip_tac >>
 irule frag_exec_run_inst_seq >> simp[] >>
 drule_all abi_decoder_bulk_reentry_sequence >> strip_tac >>
 drule_all abi_decoder_bulk_allocation_shape >> strip_tac >>
 drule_all deploy_ctor_decoder_sequence_observations >> strip_tac >>
 drule_all deploy_ctor_decoder_sequence_ambient >> strip_tac >>
 drule_all ctor_actual_sequence_world >> strip_tac >>
 drule_all ctor_actual_scratch_free_effect >>
 disch_then (qspecl_then [`site`, `{}`, `func`, `ctx`] strip_assume_tac) >>
 qexists `actual` >>
 gvs[fresh_vars_wrt_def, abi_decode_frame_def, eval_op_inst_idx,
   abi_encoder_registered_effect_def, alloca_inv_def, alloca_frontier_inv_def,
   remaining_alloca_budget_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
 metis_tac[]
QED

(* Ambient-only contract: resource strengthening is a separate obligation. *)
val Ccomplete = ``\ty tv.
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
 alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\ k + unit_alloca_budget ctx < dimword (:256) /\
 D <= d /\ d + type_memory_bytes ce ty <= D+N /\ D+N <= initial.vs_alloca_next /\
 frag_ids st st' SUBSET ids /\ ctor_actual_scratch func ids D N initial /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?actual. val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st')) [(d,type_memory_bytes ce ty)] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
 ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
 actual.vs_data_section = initial.vs_data_section /\ actual.vs_call_ctx = initial.vs_call_ctx /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==> lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\
 actual.vs_labels = initial.vs_labels /\ actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code /\
 actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\ actual.vs_block_ctx = initial.vs_block_ctx``;

Theorem deploy_ctor_bytes_run_complete:
 type_to_abi_dec_info sf ce ty = DecBytestring n ==> (^Ccomplete) ty tv
Proof
 strip_tac >> BETA_TAC >> rpt gen_tac >>
 disch_then (map_every assume_tac o CONJUNCTS) >>
 `sb < dimword (:256) /\ d < dimword (:256) /\
  type_memory_bytes ce ty < dimword (:256)` by
   (drule_all deploy_ctor_shifted_frontier_bound >> strip_tac >> decide_tac) >>
 `abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi` by
   (Cases_on `src` >> Cases_on `dst` >> Cases_on `hi` >>
    simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
    metis_tac[not_fresh_at_def]) >>
 `compile_abi_decode_to_buf dst src DLOAD hi (DecBytestring n) st = ((),st')` by metis_tac[] >>
 irule deploy_ctor_noalloc_complete_run >> asm_rewrite_tac[] >>
 drule_all deploy_ctor_bytestring_complete_fragment >>
 simp[frag_exec_def] >> rpt strip_tac >>
 first_x_assum drule_all >> simp[] >>
 disch_then (qspecl_then [`site`, `func`, `ctx`] strip_assume_tac) >>
 qexists `t` >> asm_rewrite_tac[]
QED

Theorem deploy_ctor_dynamic_array_bulk_run_complete:
 ~(is_abi_dynamic ce.ce_struct_fields ty \/
   dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)) ==>
 (^Ccomplete) (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
 disch_then (strip_assume_tac o SIMP_RULE bool_ss []) >>
 simp_tac bool_ss [] >> rpt gen_tac >>
 disch_then (map_every assume_tac o CONJUNCTS) >>
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
   (drule_all deploy_ctor_shifted_frontier_bound >> strip_tac >> decide_tac) >>
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
 irule deploy_ctor_noalloc_complete_run >> asm_rewrite_tac[] >>
 drule_all deploy_ctor_bulk_complete_fragment >>
 simp[frag_exec_def] >> rpt strip_tac >>
 first_x_assum drule_all >> simp[] >>
 disch_then (qspecl_then [`site`, `func`, `ctx`] strip_assume_tac) >>
 qexists `actual` >> asm_rewrite_tac[]
QED

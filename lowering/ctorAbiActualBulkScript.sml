(* Allocation-free bulk decoding: the pure legacy window is empty. *)
Theory ctorAbiActualBulk
Ancestors
 ctorAbiActualObservations ctorAbiActualBytes abiDecoderBulkReentry
 abiDecoderBulkExecute abiDecoderBulk abiDecoderReentryPointer
 abiDecoderReentry abiDecoderTypedContract abiDecoderCoherence
 abiDecoderContract compileEnv valueEncoding venomState venomInst words arithmetic
 ctorAbiActualWorld abiEncoderRegisteredEffect allocaFrontierBound allocaBudgetProps
 fragExec instIdxIndep venomMemDefs

Theorem ctor_actual_bulk_empty_window_pre:
 abi_decoder_coherent ce env sf ty tv /\
 abi_decoder_metadata ce env ty tv root_di av v /\
 eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
 sb + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
 mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av)) initial.vs_data_section =
   enc (vyper_to_abi_type env ty) av /\
 (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
   sb + LENGTH (enc (vyper_to_abi_type env ty) av) <= h /\ h < dimword (:256)) /\
 abi_decoder_operand_live st.cs_next_var src /\
 abi_decoder_operand_live st.cs_next_var dst /\
 abi_decoder_operand_live st.cs_next_var hi /\
 d + type_memory_bytes ce ty <= initial.vs_alloca_next /\
 initial.vs_alloca_next < dimword (:256) ==>
 abi_decoder_recursive_pre ce env sf ty tv (type_to_abi_dec_info sf ce ty) av v
   st st.cs_next_id src dst DLOAD hi sb d initial.vs_alloca_next 0
   (abi_decoder_prune_vars st.cs_next_var initial)
Proof
 disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 simp_tac bool_ss [abi_decoder_recursive_pre_def, abi_decoder_pre_def,
   abi_decoder_ranges_def, abi_decoder_reservation_def,
   abi_decode_source_opcode_def, abi_decode_source_def] >>
 asm_simp_tac (srw_ss()) [abi_decoder_prune_vars_def,
   abi_decoder_prune_eval, abi_decoder_prune_fresh] >>
 conj_tac >- fs[abi_decoder_metadata_def] >>
 conj_tac >- (rpt strip_tac >> decide_tac) >> decide_tac
QED

Theorem ctor_actual_bulk_labels_fragment:
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
     actual.vs_labels = initial.vs_labels) (K F)
Proof
 disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
 drule_all abi_decoder_bulk_shape >> strip_tac >>
 irule frag_exec_run_inst_seq >> simp[] >>
 drule_all abi_decoder_bulk_reentry_sequence >> strip_tac >>
 drule_all abi_decoder_bulk_allocation_shape >> strip_tac >>
 drule_all ctor_actual_sequence_labels >> strip_tac >>
 drule_all ctor_actual_sequence_world >> strip_tac >>
 drule_all ctor_actual_scratch_free_effect >>
 disch_then (qspecl_then [`site`, `{}`, `func`, `ctx`] strip_assume_tac) >>
 qexists `actual` >>
 gvs[fresh_vars_wrt_def, abi_decode_frame_def, eval_op_inst_idx,
   abi_encoder_registered_effect_def, alloca_inv_def, alloca_frontier_inv_def,
   remaining_alloca_budget_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
 metis_tac[]
QED

(* Same-witness observations for allocation-free constructor decoders. *)
Theory ctorDeployLoweringEntryNoAlloc
Ancestors
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

Theorem deploy_ctor_bytestring_frame_fragment:
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
     t.vs_gas_readings = initial.vs_gas_readings /\ t.vs_code = initial.vs_code) (K F)
Proof
 disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
 drule_all abi_decoder_bytes_shape >> strip_tac >>
 irule frag_exec_run_inst_seq >> simp[] >>
 drule_all ctor_actual_bytestring_ceiling_sequence >> strip_tac >>
 drule_all abi_decoder_bytes_reentry_code >> strip_tac >>
 drule_all deploy_ctor_decoder_sequence_observations >> strip_tac >>
 qexists `actual` >>
 gvs[fresh_vars_wrt_def, abi_decode_frame_def, eval_op_inst_idx,
   abi_encoder_registered_effect_def, alloca_inv_def, alloca_frontier_inv_def,
   remaining_alloca_budget_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
 metis_tac[]
QED

Theorem deploy_ctor_bulk_frame_fragment:
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
     actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code) (K F)
Proof
 disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
 drule_all abi_decoder_bulk_shape >> strip_tac >>
 irule frag_exec_run_inst_seq >> simp[] >>
 drule_all abi_decoder_bulk_reentry_sequence >> strip_tac >>
 drule_all abi_decoder_bulk_allocation_shape >> strip_tac >>
 drule_all deploy_ctor_decoder_sequence_observations >> strip_tac >>
 drule_all ctor_actual_sequence_world >> strip_tac >>
 drule_all ctor_actual_scratch_free_effect >>
 disch_then (qspecl_then [`site`, `{}`, `func`, `ctx`] strip_assume_tac) >>
 qexists `actual` >>
 gvs[fresh_vars_wrt_def, abi_decode_frame_def, eval_op_inst_idx,
   abi_encoder_registered_effect_def, alloca_inv_def, alloca_frontier_inv_def,
   remaining_alloca_budget_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
 metis_tac[]
QED

(* Common allocation-free postcondition is consumed on a single execution. *)
Theorem deploy_ctor_noalloc_shifted_run:
 frag_exec ctx st st' (\s. s = initial)
   (\t. val_in_memory tv v d t.vs_memory /\ fresh_vars_wrt limit_st t /\
     abi_decode_frame d (type_memory_bytes ce ty) initial t /\
     (!op w. abi_decoder_operand_live st.cs_next_var op /\
       eval_operand op initial = SOME w ==> eval_operand op t = SOME w) /\
     t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next /\
     abi_encoder_registered_effect {} [(d,type_memory_bytes ce ty)] initial t /\
     t.vs_labels = initial.vs_labels /\
     t.vs_gas_readings = initial.vs_gas_readings /\ t.vs_code = initial.vs_code) (K F) /\
 fn_has_code st st' func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = st'.cs_blocks \/ !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
   phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
 ctor_actual_scratch func ids D N initial /\ D+N <= initial.vs_alloca_next /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?actual. val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
   [(d,type_memory_bytes ce ty)] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
 ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
 actual.vs_data_section = initial.vs_data_section /\ actual.vs_call_ctx = initial.vs_call_ctx /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==> lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
 actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\
 actual.vs_labels = initial.vs_labels /\
 actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code
Proof
 disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
 rename1 `abi_decode_sim ctx func initial actual` >>
 qpat_x_assum `frag_exec _ _ _ _ _ _` kall_tac >>
 `alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
  ctor_actual_scratch func ids D N actual` by
   (drule_all deploy_ctor_array_allocation_state >> simp[]) >>
 `abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
   [(d,type_memory_bytes ce ty)] initial actual` by
   (irule abi_encoder_registered_effect_enlarge >>
    qexistsl [`{}`, `[(d,type_memory_bytes ce ty)]`] >> simp[]) >>
 qpat_assum `abi_decode_frame _ _ _ _`
   (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decode_frame_def]) >>
 qexists `actual` >> asm_simp_tac bool_ss [] >> rpt strip_tac >>
 `abi_decoder_operand_live st.cs_next_var (Var x)` by
   (simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
    metis_tac[not_fresh_at_def]) >>
 `eval_operand (Var x) initial = SOME w` by simp[eval_operand_def] >>
 first_x_assum drule_all >> simp[eval_operand_def]
QED

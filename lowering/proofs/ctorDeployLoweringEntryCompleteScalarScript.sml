Theory ctorDeployLoweringEntryCompleteScalar
Ancestors
  loweringStateRelDefs
 ctorDeployLoweringEntryRegistration ctorDeployLoweringEntryNoAlloc
 ctorDeployLoweringEntryArrayFrame ctorAbiActualWorld ctorAbiActualNarrowWord
 ctorAbiActualWordRun abiDecoderClampedWord abiDecoderWordTyped
 abiDecoderReentry abiDecoderCoherence abiDecoderContract abiDecoderTypedContract
 abiDecoderLayout abiDecoderVarSequence abiDecoderReentryPointer abiDecoderLoop
 abiEncoderRegisteredEffect allocaFrontierBound allocaBudgetProps
 fragExec venomExecSemantics venomMemDefs venomState venomInst valueEncoding
 compileEnv exprLoweringProps instIdxIndep words finite_map list

Theorem deploy_ctor_decoder_step_ambient:
 abi_decoder_reentry_opcode inst.inst_opcode /\ step_inst_base inst s = OK t ==>
 t.vs_outcomes = s.vs_outcomes /\ t.vs_tx_ctx = s.vs_tx_ctx /\
 t.vs_block_ctx = s.vs_block_ctx
Proof
 strip_tac >> Cases_on `inst.inst_opcode` >>
 gvs[abi_decoder_reentry_opcode_def] >>
 qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
 pure_rewrite_tac[step_inst_base_def] >> asm_rewrite_tac[] >>
 pure_rewrite_tac[opcode_case_def] >>
 simp[exec_pure1_def, exec_pure2_def, exec_read1_def, exec_write2_def,
      exec_alloca_def] >> strip_tac >> gvs[AllCaseEqs()] >>
 simp[update_var_def, mstore_def, mcopy_def, write_memory_with_expansion_def,
      jump_to_def]
QED

Theorem deploy_ctor_decoder_sequence_ambient:
 !code s t. EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) code /\
 run_inst_seq code s = OK t ==>
 t.vs_outcomes = s.vs_outcomes /\ t.vs_tx_ctx = s.vs_tx_ctx /\
 t.vs_block_ctx = s.vs_block_ctx
Proof
 Induct >> simp[run_inst_seq_def] >> rpt strip_tac >>
 Cases_on `step_inst_base h s` >> gvs[] >>
 drule_all deploy_ctor_decoder_step_ambient >> strip_tac >>
 first_x_assum drule_all >> simp[]
QED

Theorem deploy_ctor_scalar_complete_fragment:
 compile_abi_decode_to_buf dst src DLOAD hi (DecPrimWord clamp) st = ((),st') /\
 abi_decoder_coherent ce env sf ty tv /\
 type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
 abi_decoder_metadata ce env ty tv root_di av v /\
 eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
 abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
 sb < dimword (:256) /\ d < dimword (:256) /\
 mem_bytes_at sb 32 initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
 st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
 frag_exec ctx st st' (\s. s = initial)
   (\t. val_in_memory tv v d t.vs_memory /\ fresh_vars_wrt limit_st t /\
     abi_decode_frame d 32 initial t /\
     (!op w. abi_decoder_operand_live st.cs_next_var op /\
       eval_operand op initial = SOME w ==> eval_operand op t = SOME w) /\
     t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next /\
     abi_encoder_registered_effect {} [(d,32)] initial t /\
     (alloca_inv t <=> alloca_inv initial) /\
     (alloca_frontier_inv ctx func site t <=> alloca_frontier_inv ctx func site initial) /\
     t.vs_labels = initial.vs_labels /\
     t.vs_gas_readings = initial.vs_gas_readings /\ t.vs_code = initial.vs_code /\
     t.vs_outcomes = initial.vs_outcomes /\ t.vs_tx_ctx = initial.vs_tx_ctx /\
     t.vs_block_ctx = initial.vs_block_ctx) (K F)
Proof
 strip_tac >>
 `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
 drule_all abi_decoder_clamped_word_shape >> strip_tac >>
 `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
   (emitted_insts st st')` by fs[EVERY_CONJ] >>
 irule frag_exec_run_inst_seq >> simp[] >>
 drule_all ctor_actual_word_ceiling_sequence >> strip_tac >>
 drule_all abi_decoder_word_reentry_code >> strip_tac >>
 drule_all deploy_ctor_decoder_sequence_observations >> strip_tac >>
 drule_all deploy_ctor_decoder_sequence_ambient >> strip_tac >>
 drule_all ctor_actual_sequence_world >> strip_tac >>
 drule_all ctor_actual_scratch_free_effect >>
 disch_then (qspecl_then [`site`, `{}`, `func`, `ctx`] assume_tac) >>
 qexists `actual` >>
 gvs[fresh_vars_wrt_def, abi_decode_frame_def, eval_op_inst_idx,
   abi_encoder_registered_effect_def, alloca_inv_def, alloca_frontier_inv_def,
   remaining_alloca_budget_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
 metis_tac[]
QED

Theorem deploy_ctor_noalloc_complete_run:
 frag_exec ctx st st' (\s. s = initial)
   (\t. val_in_memory tv v d t.vs_memory /\ fresh_vars_wrt limit_st t /\
     abi_decode_frame d (type_memory_bytes ce ty) initial t /\
     (!op w. abi_decoder_operand_live st.cs_next_var op /\
       eval_operand op initial = SOME w ==> eval_operand op t = SOME w) /\
     t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next /\
     abi_encoder_registered_effect {} [(d,type_memory_bytes ce ty)] initial t /\
     t.vs_labels = initial.vs_labels /\
     t.vs_gas_readings = initial.vs_gas_readings /\ t.vs_code = initial.vs_code /\
     t.vs_outcomes = initial.vs_outcomes /\ t.vs_tx_ctx = initial.vs_tx_ctx /\
     t.vs_block_ctx = initial.vs_block_ctx) (K F) /\
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
 actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code /\
 actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\
 actual.vs_block_ctx = initial.vs_block_ctx
Proof
 disch_then (map_every assume_tac o CONJUNCTS) >>
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
   (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decode_frame_def]) >>
 qexists `actual` >> asm_simp_tac bool_ss [] >> rpt strip_tac >>
 `abi_decoder_operand_live st.cs_next_var (Var x)` by
   (simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
    metis_tac[not_fresh_at_def]) >>
 `eval_operand (Var x) initial = SOME w` by simp[eval_operand_def] >>
 first_x_assum drule_all >> simp[eval_operand_def]
QED

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

Theorem deploy_ctor_primitive_run_complete:
 type_to_abi_dec_info sf ce ty = DecPrimWord clamp ==> (^Ccomplete) ty tv
Proof
 strip_tac >> BETA_TAC >> rpt gen_tac >>
 disch_then (map_every assume_tac o CONJUNCTS) >>
 drule abi_decoder_primitive_cases >> disch_then (qspec_then `clamp` mp_tac) >>
 asm_simp_tac bool_ss [] >> disch_then (map_every assume_tac o CONJUNCTS) >>
 `LENGTH (enc (vyper_to_abi_type env ty) av) = 32` by
   (qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
     (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
    drule_all abi_decoder_descended_encoding_length >> simp[]) >>
 `sb < dimword (:256) /\ d < dimword (:256)` by
   (drule_all deploy_ctor_shifted_frontier_bound >> strip_tac >> decide_tac) >>
 `abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst` by
   (Cases_on `src` >> Cases_on `dst` >>
    simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
    metis_tac[not_fresh_at_def]) >>
 `compile_abi_decode_to_buf dst src DLOAD hi (DecPrimWord clamp) st = ((),st') /\
  mem_bytes_at sb 32 initial.vs_data_section = enc (vyper_to_abi_type env ty) av` by metis_tac[] >>
 qpat_assum `type_memory_bytes ce ty = 32` (fn th =>
   irule (PURE_REWRITE_RULE [th] deploy_ctor_noalloc_complete_run)) >>
 asm_rewrite_tac[] >>
 drule_all deploy_ctor_scalar_complete_fragment >>
 simp[frag_exec_def] >> rpt strip_tac >>
 first_x_assum drule_all >> simp[] >>
 disch_then (qspecl_then [`site`, `func`, `ctx`] strip_assume_tac) >>
 qexists `t` >> asm_rewrite_tac[]
QED

(* Same-witness world-framed primitive decoder paths. *)
Theory ctorDeployMemoryRunMemEntryCheckedBaseWorld
Ancestors
  ctorDeployMemoryRunMemEntrySequenceWorld
  ctorDeployMemoryRunMemEntryWord ctorDeployMemoryRunMemEntryBytes
  ctorDeployMemoryRunMemEntryShiftedFrame ctorDeployMemoryFrontier
  ctorAbiActualWorld ctorAbiActualFrame ctorAbiActualObservations
  ctorAbiActualLabelWord ctorAbiActualLabelBytes
  abiDecoderPrimitiveCaller abiDecoderCoherence abiDecoderTypedContract
  abiDecoderWordTyped abiDecoderLayout abiDecoderClampedWord abiDecoderBytes
  abiDecoderBytesTyped abiDecoderBytesFrame
  abiDecoderVarSequence abiDecoderContract abiDecoderReentry abiDecoderReentryPointer
  abiEncoderRegisteredEffect abiDecoderLoop abiEncoderProps
  allocaBudgetProps allocaFrontierBound allocaHistory
  valueEncoding valueEncodingProps compileEnv exprLowering exprLoweringProps
  instIdxIndep emitHelperProps venomMemDefs venomState finite_map
  fragGasPathMem rich_list list words arithmetic

val Ckw = ``\ty tv.
 !k dst src hi st st' ctx func site initial limit_st sb d D N ids av v root_di.
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
 alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\ k + unit_alloca_budget ctx < dimword (:256) /\
 alloca_history func initial /\
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
 actual.vs_labels = initial.vs_labels /\
 gas_path_mem ctx func initial 0 (OK actual) /\ actual.vs_gas_readings = initial.vs_gas_readings /\
 alloca_history func actual /\
 actual.vs_tx_ctx = initial.vs_tx_ctx /\ actual.vs_block_ctx = initial.vs_block_ctx /\
 actual.vs_outcomes = initial.vs_outcomes``;

Theorem ctor_world_scratch_free_effect_from[local]:
  abi_decode_frame d n s t /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_logs = s.vs_logs /\ t.vs_requests = s.vs_requests /\
  t.vs_pending_deletions = s.vs_pending_deletions ==>
  abi_encoder_registered_effect ids [(d,n)] s t /\
  (alloca_inv t <=> alloca_inv s) /\
  (alloca_frontier_inv_from k ctx fn site t <=> alloca_frontier_inv_from k ctx fn site s)
Proof
  strip_tac >>
  conj_tac
  >- (gvs[abi_encoder_registered_effect_def, abi_decode_frame_def] >>
      rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  simp[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
    alloca_frontier_inv_from_def, remaining_alloca_budget_def]
QED

Theorem ctor_checked_word_world_run_from:
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp ==> (^Ckw) ty tv
Proof
  strip_tac >> BETA_TAC >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_primitive_cases >> disch_then (qspec_then `clamp` mp_tac) >>
  asm_simp_tac bool_ss [] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `LENGTH (enc (vyper_to_abi_type env ty) av) = 32` by
    (qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
       (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
     drule_all abi_decoder_descended_encoding_length >> simp[]) >>
  `sb < dimword (:256) /\ d < dimword (:256) /\ d + 32 <= initial.vs_alloca_next` by
    (drule_all alloca_frontier_inv_from_word_bound >> asm_simp_tac bool_ss [] >> decide_tac) >>
  `abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst` by
    (Cases_on `src` >> Cases_on `dst` >>
     simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     metis_tac[not_fresh_at_def]) >>
  `compile_abi_decode_to_buf dst src DLOAD hi (DecPrimWord clamp) st = ((),st') /\
   mem_bytes_at sb 32 initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
   sb + 32 <= LENGTH initial.vs_data_section` by metis_tac[] >>
  drule_all ctor_checked_word_sequence >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all ctor_word_path_sim >> strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_word_reentry_code >> strip_tac >>
  drule_all abi_decoder_clamped_word_shape >> strip_tac >>
  drule_all ctor_actual_sequence_labels >> strip_tac >>
  drule_all ctor_actual_sequence_world >> strip_tac >>
  drule_all ctor_decoder_sequence_context_world >> strip_tac >>
  drule_all ctor_world_scratch_free_effect_from >>
  disch_then (qspecl_then [`site`, `k`, `ctor_actual_sites func (frag_ids st st')`, `func`, `ctx`] strip_assume_tac) >>
  qexists `actual with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  simp[] >> conj_tac
  >- (qpat_x_assum `abi_encoder_registered_effect _ _ _ _` mp_tac >>
      simp[abi_encoder_registered_effect_def]) >>
  conj_tac
  >- (irule alloca_frontier_inv_from_frame >> qexists `initial` >> simp[] >> qexists `site` >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `ctor_actual_scratch _ _ _ _ _` mp_tac >>
      simp[ctor_actual_scratch_def]) >>
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

Theorem ctor_checked_bytes_world_run_from:
  type_to_abi_dec_info sf ce ty = DecBytestring n ==> (^Ckw) ty tv
Proof
  strip_tac >> BETA_TAC >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `sb < dimword (:256) /\ d < dimword (:256) /\
   type_memory_bytes ce ty < dimword (:256) /\
   d + type_memory_bytes ce ty <= initial.vs_alloca_next` by
    (drule_all alloca_frontier_inv_from_word_bound >> asm_simp_tac bool_ss [] >> decide_tac) >>
  `abi_decoder_operand_live st.cs_next_var src /\
   abi_decoder_operand_live st.cs_next_var dst /\
   abi_decoder_operand_live st.cs_next_var hi` by
    (Cases_on `src` >> Cases_on `dst` >> Cases_on `hi` >>
     simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     metis_tac[not_fresh_at_def]) >>
  `compile_abi_decode_to_buf dst src DLOAD hi (DecBytestring n) st = ((),st')` by metis_tac[] >>
  drule_all ctor_checked_bytes_sequence >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all ctor_word_path_sim >> strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bytes_reentry_code >> strip_tac >>
  drule_all abi_decoder_bytes_shape >> strip_tac >>
  drule_all ctor_actual_sequence_labels >> strip_tac >>
  drule_all ctor_actual_sequence_world >> strip_tac >>
  drule_all ctor_decoder_sequence_context_world >> strip_tac >>
  drule_all ctor_world_scratch_free_effect_from >>
  disch_then (qspecl_then [`site`, `k`, `ctor_actual_sites func (frag_ids st st')`, `func`, `ctx`] strip_assume_tac) >>
  qexists `actual with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  simp[] >> conj_tac
  >- (qpat_x_assum `abi_encoder_registered_effect _ _ _ _` mp_tac >>
      simp[abi_encoder_registered_effect_def]) >>
  conj_tac
  >- (irule alloca_frontier_inv_from_frame >> qexists `initial` >> simp[] >> qexists `site` >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `ctor_actual_scratch _ _ _ _ _` mp_tac >>
      simp[ctor_actual_scratch_def]) >>
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

Theorem ctor_checked_base_world_run_from:
  (^Ckw) (BaseT bt) (BaseTV bt)
Proof
  `(?clamp. type_to_abi_dec_info sf ce (BaseT bt) = DecPrimWord clamp) \/
   (?n. type_to_abi_dec_info sf ce (BaseT bt) = DecBytestring n)` by
    (Cases_on `bt` >> simp[type_to_abi_dec_info_def] >>
     rename1 `BytesT bound` >> Cases_on `bound` >> simp[type_to_abi_dec_info_def])
  >- (irule ctor_checked_word_world_run_from >> goal_assum (drule_at Any)) >>
  irule ctor_checked_bytes_world_run_from >> goal_assum (drule_at Any)
QED

Theorem ctor_checked_flag_world_run_from:
  (^Ckw) (FlagT nsid) (FlagTV n)
Proof
  irule ctor_checked_word_world_run_from >> simp[Once type_to_abi_dec_info_def]
QED

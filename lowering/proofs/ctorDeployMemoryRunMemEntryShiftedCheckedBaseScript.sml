(* Checked allocation-free decoder paths at a reserved-memory frontier. *)
Theory ctorDeployMemoryRunMemEntryShiftedCheckedBase
Ancestors
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

val Ck = ``\ty tv.
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
 alloca_history func actual``;

Theorem ctor_actual_scratch_free_effect_from[local]:
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

